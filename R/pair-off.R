pair_off <- function(names, values, env) {
  if (is.character(names) || is.language(names)) {
    if (names == ".") {
      return()
    }

    attributes(names) <- NULL

    return(list(list(name = names, value = values)))
  }

  if (is_list(names) && length(names) == 0 &&
      is_list(values) && length(values) == 0) {
    return()
  }

  #
  # when using the named notation values may need to be shuffled around
  #
  if (any(has_named(names))) {
    # values <- pad_named(names, values)
    names <- shuffle_named(names)

    return(pair_off(names, values))
  }

  #
  # mismatch between variables and values
  #
  if (length(names) != length(values)) {
    if (any(has_default(names))) {
      values <- add_defaults(names, values, env)
      names <- lapply(names, `attributes<-`, value = NULL)

      return(pair_off(names, values))
    }

    #
    # mismatch could be resolved by destructuring the values, in this case
    # values must be a single element list
    #
    if (is_list(values) && length(values) == 1) {
      return(pair_off(names, destructure(car(values))))
    }

    #
    # if there is no collector the mismatch is a problem *or* if collector,
    # and still more variables than values the collector is useless and
    # mismatch is a problem
    #
    if (!has_collector(names) || length(names) > length(values)) {
      stop_invalid_rhs(incorrect_number_of_values())
    }
  }

  if (is_collector(car(names))) {
    collected <- collect(names, values)
    name <- sub("^\\.\\.\\.", "", car(names))

    #
    # skip unnamed collector variable and corresponding values
    #
    if (name == "") {
      return(pair_off(cdr(names), cdr(collected)))
    }

    return(
      c(pair_off(name, car(collected)), pair_off(cdr(names), cdr(collected)))
    )
  }

  #
  # multiple nested variables and nested vector of values same length, but
  # a nested vector is not unpacked, mismatch
  #
  if (is_list(names) && !is_list(values)) {
    stop_invalid_rhs(incorrect_number_of_values())
  }

  if (length(names) == 1) {
    return(pair_off(car(names), car(values)))
  }

  c(pair_off(car(names), car(values)), pair_off(cdr(names), cdr(values)))
}
