# rim 0.8.1
## Modifications
- removed test for plot3d() because of an error in Maxima calling gnuplot with an invalid argument, will be re-added with the next version of Maxima
- The unit test for the engine now calls explicitly `rim_global()` to evaluate the parsed expressions from Maxima (added a note in the doc page as well)
- changed the package startup message

# rim 0.8.0
## Modifications
- fixed NOTE for assigment into `globalenv()` when checking package

## Minor
- added REPL mode (`maxima.repl()`)

# rim 0.7.1
## Modifications
- R6 class finalize() now private, as required by package
- fixed failing example for `maxima.load()` under Fedora (#47) and added testing file

# rim 0.7.0
## Modification
- fixes faulty parsing of matrices
- re-factored printing method `maxima.print` and `iprint`, which now reliably detected whether called from interactive mode or from knitr engine, thus removed internal function `engine_print()` (Maxima S3 object now gained `from_engine` flag)
- running code chunks interactively (from RStudio) now works as expected using the "interactive" Maxima connection object it's options accordingly
- comment handling now works (both interactive and engine), fixed an infinite loop occurrence when sent command ended with a comment, comment-only lines of code inside code-chunks are now properly printed
- empty lines in code chunks are now preserved as inputted
- fixed engine test failure caused by different output code width settings and unneccessarily inserted linebreaks between code input and output

# rim 0.6.4
## Modification
- new options `max.attempts` and `sleep.seconds` to control repeated testing for finished rendering of images
- fixed issue #37

# rim 0.6.3
## Modification 
- fixed error under Fedora 36+ caused by Maxima image inclusion, when the image
  file isn't guaranteed to exist when it's file path is returned from Maxima

# rim 0.6.2
## Modification
- added more reliable detection for output document - Maxima knitr engine
  (fixes previous CRAN test failure for Fedora 36+).

# rim 0.6.1
## Modification
- fixed bug from CRAN check failure on Fedora and R-devel

# rim 0.6.0
## Minor
- added new function `maxima.eval()` that can either take a character string or an S3 object of class "maxima" (as returned from `maxima.get()`). In either case, the output result from Maxima (if not suppressed) is parsed into a R-expression and gets evaluated by this function. Objects returned from `maxima.get()` carry an attributed named "parsed" that is the unevaluted R-expression of the returned Maxima result. Parsing works for 
	- unary and binary operators
	- named function calls
	- function definitions
	- lambda function calls
	- memoizing array function definition (those are currently simply parsed into "normal" functions)
	- arrays: creating and setting
	- matrices: creation, multiplication, transposition, inversion, determinants
	- lists
	- conditionals
- added engine option `output.var` that can name a variable to capture parsed Maxima output into a named list. The names of this list are the output labels.

# rim 0.5.3
## Modification
- user can specify custom path to Maxima executable by setting environment variable "RIM_MAXIMA_PATH"

# rim 0.5.2
## Modification
- fixed tests to pass for Fedora 36
- built-in safeguards against infinite loops when Maxima couldn't be started or initialized (issue #29)
- reading process ID and version number now using class MReader

# rim 0.5.1
## Modification 
- `knitr`-engine now supports chunk options `echo`, `eval` and `include`, a description can be found in the documentation page
- fixed several issues related to changes with Maxima version 5.46.0

# rim 0.5.0
## Minor
- `knitr`-engine now supports plotting commands: plot2d(), plot3d(), draw(), draw2d(), draw3d() (and others that are based on those mentioned), depending on the output format (PDF or HTML), plots are saved as PDF or PNG respectively
- Added inline output function to be used when knitting `RMarkdown` documents.
- Restructured the return type of the get function: Instead of a character string, now a list is returned storing every output format of the result including both with and without reference labels.
- Added a global option handling function `maxima.options()` and removed individual option setting functions `maxima.setformat()`, `maxima.engine.format()` and friends
- Whether reference labels are printed or not when knitting a `RMarkdown` document can now be controlled by setting `maxima.options(engine.label)`

## Modification 
- Removed some unused utility functions from code
- Removed unnecessary C++17 compiler flag
- Improved documentation
- Updated heuristics for catching warnings and errors
- Improved typesetting of output labels when knitting `RMarkdown` documents 
- Improved warning/ error handling heuristics (fixing issue #20)

# rim 0.4.1
## Modification
- fixed issue #16. code chunks that contain commands spanning multiple lines are now printed as-is (except for empty lines, which are removed) with the preceding input reference label 
- fixed the issue #17, caused by a socket-read-write-concurrency conflict which led to split lines read from Maxima and a failure to validate it's output. This is achieved now by an internal helper R6 class `MReader` that stashes away incomplete lines and completes it upon re-calling.
- fixed reference manual that is generated by CRAN, but previously did not contain the package main functions
- Improved description in `DESCRIPTION` of `SystemRequirements`
- added exported function `maxima.isInstalled()` that is now used upon package attachment, where a message is signaled to install Maxima, if no installation was found.
- added exported function `maxima.version()` which is now used upon package attachment, where a message is signaled when the installed version is lower than the version with which this package has been tested
- Test file `tests/testthat/test-engine.R`: knitting test page now suppresses Warnings, which are subject of `tests/testthat/test-warnings.R` 

# rmaxima 0.4.0/ rim 0.4.0
- added `maxima.engine.format()` function that can be used to change the output format of the `knitr` engine
- fixed issue that arises when Maxima takes longer to start (which previously caused the interface to freeze)
- added functions to record the version number of Maxima that is being used
- renamed package to "rim" to avoid confusion with `maxima`'s `rmaxima`
- communication is now implemented using sockets and the processing is handles by two nested R6 classes
- return type is now a S3 class of type maxima. There are two methods `iprint()` and `oprint()` for printing an maxima S3 object: printing the input command and output respectively, including reference labels. 
- removed external C++ library dependencies (now using sockets for communicating with Maxima)
- `knitr` engine now prints output after each input line, it also prints the input reference label in front of the command

# rmaxima 0.0.0.9000

- removed dependency from boost (switched to libexecstream)
- maxima.get() returns character vector with added attributes for reference labels, format and it's originating command
- fixed Maxima error (message) forwarding to R
- implement `knitr`-engine for maxima using this interface
- Implement stop function to end maxima child process for debugging purposes
- Handles `asksign` and similar feedback interruptions
- Added interface to Maxima's apropos()-function
- Fixed: If command terminates with `\$` then this causes a segmentation fault, which kills the R process. The cause being that maxima returns immediately with the next input prompt
- added `roxygen2` documentation
- fixed `system.file` call inside constructor to work with `devtools::load_all()`
- Added a `NEWS.md` file to track changes to the package.
- Add test files
- implemented output display as `tex` (not yet user-friendly)
- added initialization files
- added function void `loadModule(const std::string &s)`
- Removed boost::regex linking dependency
- fixed pipe stream synchronization
