switch_format <- function(obj, format = "linear") {
  switch(format,
	 latex = obj$loadInit("maxima-init-tex.mac"),
	 linear = obj$loadInit("maxima-init-lin.mac"),
	 text2d = obj$loadInit("maxima-init-2d.mac"),
	 mathml = obj$loadInit("maxima-init-mathml.mac"),
	 default = {
	   obj$loadInit("maxima-init-lin.mac")
	   format <- "linear"
	 })

  return(format)
}

# internal function that takes a character vector "code"
# and joins adjacent elements to bring openning and closing 
# tokens on the same line

# test string
# a <- c("f = (1, ", "2, 3);", "", "g:=block([a=1, ", "\nb=2],", "\nprint(a),", "\nprint(b));")

#' @import stringr
join_code <- function(code, opener = c("(", "[", "{"), closer = c(")", "]", "}")) {
  mcode <- code[nchar(code) > 0]
  mcode <- str_trim(mcode, side = "both")

  if(length(opener) > 1)
    mcode <- join_code(code, 
		       opener[2:length(opener)], 
		       closer[2:length(closer)])

  #   count difference in number of 
  #   openers and closers 
  if(length(mcode) > 1) { 
    d <- str_count(string = mcode, pattern = fixed(opener[1])) - 
      str_count(string = mcode, pattern = fixed(closer[1]))

    d <- rev(cumsum(rev(d)))
    lbs <- as.logical(d)
    for(i in length(lbs):2)
      if(lbs[i])
	mcode[i-1] <- paste0(mcode[i-1], mcode[i])
  }
  mcode[!lbs]
}

#' @import stringr
collect_ends <- function(code) {
  if(length(code)>1){
    code <- str_trim(code, side = "both")
    a <- grepl(x = code, pattern = ";|\\$")
    lbs <- c(FALSE, as.logical(rev(cumsum(rev(diff(a))))))
    for(i in length(lbs):2)
      if(lbs[i]) 
	code[i-1] <- paste0(code[i-1], code[i])
    code[!lbs]
  }
  else code
}

# signify if provided character has a special meaning
# in R's regular expression functions
demetarize <- function(x) {
  if(nchar(x)>1)
    stop("Expected single character")

  if(is.metacharacter(x)) 
    escape(x)
  else 
    x
}

escape <- function(x) {
  paste0("\\", unlist(str_split(x, "")), collapse = "")
}

is.metacharacter <- function(x) {
  x %in% c("\x2e",	# .
	   "\x5c",	# \
	   "\x7e",	# |
	   "\x28",	# ( 
	 "\x29",	# )
	 "\x5b",	# [
	 "\x5d",	# ]
	 "\x7b",	# {
	 "\x7d",	# }
	 "\x24",	# $ 
	 "\x2d",	# -
	 "\x5e",	# ^
       "\x2a",	# *
       "\x2b",	# + 
     "\x3f")	# ?
}

#' @import stringr
str_strip_col <- function(x, n = 1, side = "left") {
  if(is.character(side)) {
    if(!(side %in% c("left", "right", "both"))) 
      side <- "left"
  } else 
    stop("Expected character vector")

    s <- str_split(string = x, 
		   pattern = "\\n", 
		   simplify = TRUE)[1, ]
    switch(side,
	   left = gsub(x = s, 
		       pattern = paste0("^[ |[:print:]]{", n, "}"), 
		       replacement = ""),
	   right = gsub(x = s, 
			pattern = paste0("[ |[:print:]]{", n, "}$"), 
			replacement = ""),
	   both = {
	     s <- gsub(x = s, 
		       pattern = paste0("^[ |[:print:]]{", n, "}"), 
		       replacement = "") 
	     gsub(x = s, 
		  pattern = paste0("[ |[:print:]]{", n, "}$"), 
		  replacement = "")
	   }
    )
}

# returns the label string 
label_length <- function(x, sub = "\\(%o\\d+\\)") {
  str_length(str_extract(string = x, pattern = sub))
}

#' @describeIn maxima.engine Sets the knitr engine format. It can be used both to set or get the current engine format. The current engine format is returned in both cases.
#' @param format Character vector of length 1 naming the output format to be used for the \code{knitr} engine
#' @export
maxima.engine.format <- function(format = "linear") {
  if(!missing(format)) {
    stopifnot(is.character(format))
    switch(format,
	   latex = {
	     maxima.env$engine.format <- format
	     maxima.env$display <- "maxima-init-tex"
	     knitr::opts_chunk$set(results = "asis")
	   },
	   linear = {
	     maxima.env$engine.format <- format
	     maxima.env$display <- "maxima-init-lin"
	     knitr::opts_chunk$set(results = "markup")
	   },
	   text2d = {
	     maxima.env$engine.format <- format
	     maxima.env$display <- "maxima-init-2d"
	     knitr::opts_chunk$set(results = "markup")
	   },
	   mathml = {
	     maxima.env$engine.format <- format
	     maxima.env$display <- "maxima-init-mathml"
	     knitr::opts_chunk$set(results = "asis")
	   },
	   {
	     maxima.env$engine.format <- "linear"
	     maxima.env$display <- "maxima-init-lin"
	     knitr::opts_chunk$set(results = "markup")
	     format <- "linear"
	   })
  }
  return(maxima.env$engine.format)
}