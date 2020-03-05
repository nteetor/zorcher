is_list <- function(x) {
  length(class(x)) == 1 && class(x) == 'list'
}

car <- function(cons) {
  stopifnot(is.list(cons), length(cons) > 0)
  cons[[1]]
}

cdr <- function(cons) {
  stopifnot(is.list(cons), length(cons) > 0)
  cons[-1]
}

names2 <- function(x) {
  if (is.null(names(x))) rep.int("", length(x)) else names(x)
}

#
# the default attribute is used by `variables()` and `pair_off()` to know when
# to assign a variable its default value
#
get_default <- function(x) {
  attr(x, "default", exact = TRUE)
}

has_default <- function(x) {
  vapply(x, function(i) !is.null(get_default(i)), logical(1))
}

#
# append any default values onto the end of a list of values, used in
# `pair_off()` to extend the current set of values thereby avoiding an
# incorrect number of values error
#
add_defaults <- function(names, values, env) {
  where <- which(has_default(names))
  defaults <- lapply(names[where], get_default)[where > length(values)]
  evaled <- lapply(
    defaults,
    function(d) {
      deval <- eval(d, envir = env)

      if (is.null(deval)) {
        return(deval)
      }

      attr(deval, "default") <- TRUE
      deval
    }
  )

  append(values, evaled)
}

#
# variables on the lhs may rename a rhs value,
# c(x: y) %<-% ..
# In this case, x renames y
# The named value "y" of the rhs is assigned to x
#
get_named <- function(x) {
  attr(x, "named", exact = TRUE)
}

has_named <- function(x) {
  vapply(x, function(i) !is.null(get_named(i)), logical(1))
}

pad_named <- function(names, values) {
  is_named <- has_named(names)

  named_names <- vapply(names[is_named], get_named, character(1))
  named_i <- names(values) %in% named_names

  named_values <- values[named_i]
  asis_values <- values[!named_i]

  values <- vector("list", length(values))



  for_rename <- vapply(names[is_named], function(nm) {
    as.character(get_named(nm))
  }, character(1))

  indeces_rename <- names(values) %in% for_rename

  named_values <- values[indeces_rename]
  asis_values <- values[!indeces_rename]

  names2 <- vector("numeric", length(names))
  names2[indeces_rename] <- seq_along(named_values)
  names2[!indeces_rename] <- seq_along(asis_values)

  lapply(seq_along(is_named), function(i) {
    j <- names2[i]

    if (is_named[i]) {
      named_values[[j]]
    } else {
      asis_values[[j]]
    }
  })
}

shuffle_named <- function(x) {
  is_named <- has_named(x)
  seq_named <- seq_len(sum(is_named))

  x2 <- vector("list", length(x))
  x2[seq_named] <- lapply(
    x[is_named], `attr<-`, which = "named", value = NULL
  )
  x2[-seq_named] <- x[!is_named]

  x2
}

#
# traverse nested extract op calls to find the extractee, e.g. `x[[1]][[1]]`
#
traverse_to_extractee <- function(call) {
  if (is.language(call) && is.symbol(call)) {
    return(call)
  }
  traverse_to_extractee(call[[2]])
}

#
# used by multi_assign to confirm all extractees exist
#
check_extract_calls <- function(lhs, envir) {
  if (is.character(lhs)) {
    return()
  }

  if (is.language(lhs)) {
    extractee <- traverse_to_extractee(lhs)
    if (!exists(as.character(extractee), envir = envir, inherits = FALSE)) {
      stop_invalid_lhs(object_does_not_exist(extractee))
    } else {
      return()
    }
  }

  unlist(lapply(lhs, check_extract_calls, envir = envir))
}

is_extract_op <- function(x) {
  if (length(x) < 1) {
    return(FALSE)
  }

  (as.character(x) %in% c("[", "[[", "$"))
}

is_valid_call <- function(x) {
  if (length(x) < 1) {
    return(FALSE)
  }

  (x == "c" || x == "=" || x == ":" || is_extract_op(x))
}

#
# used by multi_assign to assign list elements in the calling environment
#
assign_extract <- function(call, value, envir = parent.frame()) {
  replacee <- call("<-", call, value)
  eval(replacee, envir = envir)
  invisible(value)
}

#
# parses a substituted expression to create a tree-like list structure,
# perserves calls to extract ops instead of converting them to lists
#
tree <- function(x) {
  if (length(x) == 1) {
    return(x)
  }

  if (is_extract_op(x[[1]])) {
    return(x)
  }

  lapply(
    seq_along(as.list(x)),
    function(i) {
      if (names2(x[i]) != "") {
        return(list(as.symbol("="), names2(x[i]), x[[i]]))
      } else {
        tree(x[[i]])
      }
    }
  )
}

#
# given a tree-like list structure returns a character vector of the function
# calls, used by multi_assign to determine if performing standard assignment or
# multiple assignment
#
calls <- function(x) {
  if (!is_list(x)) {
    return(NULL)
  }

  this <- car(x)

  if (!is_valid_call(this)) {
    stop_invalid_lhs(unexpected_call(this))
  }

  c(as.character(this), unlist(lapply(cdr(x), calls)))
}

#
# given a tree-like list structure, returns a nested list of the variables
# in the tree, will also associated default values with variables
#
variables <- function(x) {
  if (!is_list(x)) {
    if (x == "") {
      stop_invalid_lhs(empty_variable(x))
    }

    if (is.language(x) && length(x) > 1 && is_extract_op(x[[1]])) {
      return(x)
    }

    if (!is.symbol(x)) {
      stop_invalid_lhs(unexpected_variable(x))
    }

    return(as.character(x))
  }

  if (car(x) == "=") {
    var <- as.character(car(cdr(x)))
    default <- car(cdr(cdr(x)))

    if (is.null(default)) {
      default <- quote(pairlist())
    }

    attr(var, "default") <- default

    return(var)
  }

  if (car(x) == ":") {
    var <- as.character(car(cdr(x)))
    named <- car(cdr(cdr(x)))

    if (!is.name(named)) {
      stop_invalid_lhs(expected_name())
    }

    attr(var, "named") <- as.character(named)

    return(var)
  }

  lapply(cdr(x), variables)
}

#
# error helpers below
#

incorrect_number_of_values <- function() {
  "incorrect number of values"
}

object_does_not_exist <- function(obj) {
  paste0("object `", obj, "` does not exist in calling environment")
}

empty_variable <- function(obj) {
  paste("found empty variable, check for extraneous commas")
}

unexpected_variable <- function(obj) {
  paste("expected symbol, but found", class(obj))
}

unexpected_call <- function(obj) {
  paste0("unexpected call `", as.character(obj), "`")
}

expected_name <- function() {
  "expected symbol for named assignment"
}

# thank you Advanced R
condition <- function(subclass, message, call = sys.call(-1), ...) {
  structure(
    class = c(subclass, "condition"),
    list(message = message, call = call),
    ...
  )
}

stop_invalid_lhs <- function(message, call = sys.call(-1), ...) {
  cond <- condition(c("invalid_lhs", "error"), message, call, ...)
  stop(cond)
}

stop_invalid_rhs <- function(message, call = sys.call(-1), ...) {
  cond <- condition(c("invalid_rhs", "error"), message, call, ...)
  stop(cond)
}
