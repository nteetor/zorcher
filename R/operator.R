#' Multiple assignment operators
#'
#' Assign values to name(s).
#'
#' @param x A name structure, see section below.
#'
#' @param value A list of values, vector of values, or \R object to assign.
#'
#' @section Name Structure:
#'
#' **the basics**
#'
#' At its simplest, the name structure may be a single variable name, in which
#' case \code{\%<-\%} and \code{\%->\%} perform regular assignment, \code{x
#' \%<-\% list(1, 2, 3)} or \code{list(1, 2, 3) \%->\% x}.
#'
#' To specify multiple variable names use a call to `c()`, for example
#' \code{c(x, y, z) \%<-\% c(1, 2, 3)}.
#'
#' When `value` is neither an atomic vector nor a list, \code{\%<-\%} and
#' \code{\%->\%} will try to destructure `value` into a list before assigning
#' variables, see [destructure()].
#'
#' **object parts**
#'
#' Like assigning a variable, one may also assign part of an object, \code{c(x,
#' x[[1]]) \%<-\% list(list(), 1)}.
#'
#' **nested names**
#'
#' One can also nest calls to `c()` when needed, `c(x, c(y, z))`. This nested
#' structure is used to unpack nested values,
#' \code{c(x, c(y, z)) \%<-\% list(1, list(2, 3))}.
#'
#' **collector variables**
#'
#' To gather extra values from the beginning, middle, or end of `value` use a
#' collector variable. Collector variables are indicated with a `...`
#' prefix, \code{c(...start, z) \%<-\% list(1, 2, 3, 4)}.
#'
#' **skipping values**
#'
#' Use `.` in place of a variable name to skip a value without raising an error
#' or assigning the value, \code{c(x, ., z) \%<-\% list(1, 2, 3)}.
#'
#' Use `...` to skip multiple values without raising an error or assigning the
#' values, \code{c(w, ..., z) \%<-\% list(1, NA, NA, 4)}.
#'
#' **default values**
#'
#' Use `=` to specify a default value for a variable, \code{c(x, y = NULL)
#' \%<-\% tail(1, 2)}.
#'
#' When assigning part of an object a default value may not be specified because
#' of the syntax enforced by \R. The following would raise an `"unexpected '='
#' ..."` error, \code{c(x, x[[1]] = 1) \%<-\% list(list())}.
#'
#' @return
#'
#' \code{\%<-\%} and \code{\%->\%} invisibly return `value`.
#'
#' These operators are used primarily for their assignment side-effect.
#' \code{\%<-\%} and \code{\%->\%} assign into the environment in which they
#' are evaluated.
#'
#' @seealso
#'
#' For more on unpacking custom objects please refer to
#' [destructure()].
#'
#' @name operator
#' @export
#' @examples
#' # basic usage
#' c(a, b) %<-% list(0, 1)
#'
#' a  # 0
#' b  # 1
#'
#' # unpack and assign nested values
#' c(c(e, f), c(g, h)) %<-% list(list(2, 3), list(3, 4))
#'
#' e  # 2
#' f  # 3
#' g  # 4
#' h  # 5
#'
#' # can assign more than 2 values at once
#' c(j, k, l) %<-% list(6, 7, 8)
#'
#' # assign columns of data frame
#' c(erupts, wait) %<-% faithful
#'
#' erupts  # 3.600 1.800 3.333 ..
#' wait    # 79 54 74 ..
#'
#' # assign only specific columns, skip
#' # other columns
#' c(mpg, cyl, disp, ...) %<-% mtcars
#'
#' mpg   # 21.0 21.0 22.8 ..
#' cyl   # 6 6 4 ..
#' disp  # 160.0 160.0 108.0 ..
#'
#' # skip initial values, assign final value
#' TODOs <- list("make food", "pack lunch", "save world")
#'
#' c(..., task) %<-% TODOs
#'
#' task  # "save world"
#'
#' # assign first name, skip middle initial,
#' # assign last name
#' c(first, ., last) %<-% c("Ursula", "K", "Le Guin")
#'
#' first  # "Ursula"
#' last   # "Le Guin"
#'
#' # simple model and summary
#' mod <- lm(hp ~ gear, data = mtcars)
#'
#' # extract call and fstatistic from
#' # the summary
#' c(modcall, ..., modstat, .) %<-% summary(mod)
#'
#' modcall
#' modstat
#'
#' # unpack nested values w/ nested names
#' fibs <- list(1, list(2, list(3, list(5))))
#'
#' c(f2, c(f3, c(f4, c(f5)))) %<-% fibs
#'
#' f2  # 1
#' f3  # 2
#' f4  # 3
#' f5  # 5
#'
#' # unpack first numeric, leave rest
#' c(f2, fibcdr) %<-% fibs
#'
#' f2      # 1
#' fibcdr  # list(2, list(3, list(5)))
#'
#' # swap values without using temporary variables
#' c(a, b) %<-% c("eh", "bee")
#'
#' a  # "eh"
#' b  # "bee"
#'
#' c(a, b) %<-% c(b, a)
#'
#' a  # "bee"
#' b  # "eh"
#'
#' # unpack `strsplit` return value
#' names <- c("Nathan,Maria,Matt,Polly", "Smith,Peterson,Williams,Jones")
#'
#' c(firsts, lasts) %<-% strsplit(names, ",")
#'
#' firsts  # c("Nathan", "Maria", ..
#' lasts   # c("Smith", "Peterson", ..
#'
#' # handle missing values with default values
#' parse_time <- function(x) {
#'   strsplit(x, " ")[[1]]
#' }
#'
#' c(hour, period = NA) %<-% parse_time("10:00 AM")
#'
#' hour    # "10:00"
#' period  # "AM"
#'
#' c(hour, period = NA) %<-% parse_time("15:00")
#'
#' hour    # "15:00"
#' period  # NA
#'
#' # right operator
#' list(1, 2, "a", "b", "c") %->% c(x, y, ...chars)
#'
#' x      # 1
#' y      # 2
#' chars  # list("a", "b", "c")
#'
#' # magrittr chains, install.packages("magrittr") for this example
#' if (requireNamespace("magrittr", quietly = TRUE)) {
#'   library(magrittr)
#'
#'   c("hello", "world!") %>%
#'     paste0("\n") %>%
#'     lapply(toupper) %->%
#'     c(greeting, subject)
#'
#'   greeting  # "HELLO\n"
#'   subject   # "WORLD!\n"
#' }
#'
`%<-%` <- function(x, value) {
  tryCatch(
    multi_assign(substitute(x), value, parent.frame()),
    invalid_lhs = function(e) {
      stop("invalid `%<-%` left-hand side, ", e$message, call. = FALSE)
    },
    invalid_rhs = function(e) {
      stop("invalid `%<-%` right-hand side, ", e$message, call. = FALSE)
    }
  )
}

#' @rdname operator
#' @export
`%->%` <- function(value, x) {
  tryCatch(
    multi_assign(substitute(x), value, parent.frame()),
    invalid_lhs = function(e) {
      stop("invalid `%->%` right-hand side, ", e$message, call. = FALSE)
    },
    invalid_rhs = function(e) {
      stop("invalid `%->%` left-hand side, ", e$message, call. = FALSE)
    }
  )
}

# The real power behind %->% and %<-%
#
# Within the function `lhs` and `rhs` refer to the left- and right-hand side of
# a call to %<-% operator. For %->% the lhs and rhs from the original call are
# swapped when passed to `multi_assign`.
#
# @param x A name structure, converted into a tree-like structure with `tree`.
#
# @param value The values to assign.
#
# @param env The environment where the variables will be assigned.
#
multi_assign <- function(x, value, env) {
  ast <- tree(x)
  internals <- calls(ast)
  lhs <- variables(ast)
  rhs <- value

  #
  # all lists or environments referenced in lhs must already exist
  #
  check_extract_calls(lhs, env)

  #
  # standard assignment
  #
  if (is.null(internals)) {
    if (is.language(lhs)) {
      assign_extract(lhs, value, envir = env)
    } else {
      assign(lhs, value, envir = env)
    }
    return(invisible(value))
  }

  #
  # *error* multiple assignment, but sinle RHS value
  #
  if (length(value) == 0) {
    stop_invalid_rhs(incorrect_number_of_values())
  }

  #
  # edge cases when RHS is not a list
  #
  if (!is_list(value)) {
    if (is.atomic(value)) {
      rhs <- as.list(value)
    } else {
      rhs <- destructure(value)
    }
  }

  #
  # tuples in question are variable names and value to assign
  #
  tuples <- pair_off(lhs, rhs, env)

  for (t in tuples) {
    name <- t[["name"]]
    val <- t[["value"]]

    if (is.language(name)) {
      assign_extract(name, val, envir = env)
      next
    }

    if (is.atomic(value)) {
      if (is.null(attr(val, "default", TRUE))) {
        val <- unlist(val, recursive = FALSE)
      } else if (attr(val, "default", TRUE) == TRUE) {
        attr(val, "default") <- NULL
      }
    }

    assign(name, val, envir = env)
  }

  invisible(value)
}
