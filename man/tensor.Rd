\name{tensor}

\alias{tensor}
\alias{\%*t\%}
\alias{\%t*\%}
\alias{\%t*t\%}

\title{Tensor product of arrays}

\description{The tensor product of two arrays is notionally an
outer product of the arrays collapsed in specific extents by
summing along the appropriate diagonals.  For example, a matrix
product is the tensor product along the second extent of the
first matrix and the first extent of the second.  Thus \code{A
\%*\% B} could also be evaluated as \code{tensor(A, B, 2, 1)},
likewise \code{A \%*\% t(B)} could be \code{tensor(A, B, 2, 2)}.}

\usage{
tensor(A, B, alongA = integer(0), alongB = integer(0))
}

\arguments{
 \item{A, B}{Numerical vectors, matrices or arrays}
 \item{alongA}{Extents in \code{A} to be collapsed}
 \item{alongB}{Extents in \code{B} to be collapsed}
}

\details{This code does the `obvious' thing, which is to perm the
"along" extents to the end (for \code{A}) and beginning (for
\code{B}) of the two objects and then do a matrix multiplication
and reshape.}

\value{Generally, an array with dimension comprising the
remaining extents of \code{A} concatenated with the remaining
extents of \code{B}.

If both \code{A} and \code{B} are completely collapsed then the
result is a scalar \bold{without} a \code{dim} attribute.  This
is quite deliberate and consistent with the general rule that the
dimension of the result is the sum of the original dimensions
less the sum of the collapse dimensions (and so could be zero).
A 1D array of length 1 arises in a different set of
circumstances, eg if \code{A} is a 1 by 5 matrix and \code{B} is
a 5-vector then \code{tensor(A, B, 2, 1)} is a 1D array of length
1.}

\section{Shortcuts}{Some special cases of \code{tensor} may be
independently useful, and these have got shortcuts as follows.

\tabular{ll}{
\%*t\%	\tab	Matrix product \code{A \%*\% t(B)}	\cr
\%t*\%	\tab	Matrix product \code{t(A) \%*\% B}	\cr
\%t*t\%	\tab	Matrix product \code{t(A) \%*\% t(B)}	
}
}

\author{Jonathan Rougier, \email{J.C.Rougier@durham.ac.uk}}

\seealso{\code{\link{matmult}}, \code{\link{aperm}}}

\examples{
  A <- matrix(1:6, 2, 3)
  dimnames(A) <- list(happy = LETTERS[1:2], sad = NULL)
  B <- matrix(1:12, 4, 3)
  stopifnot(A \%*\% t(B) == tensor(A, B, 2, 2))

  A <- A \%o\% A
  C <- tensor(A, B, 2, 2)
  stopifnot(all(dim(C) == c(2, 2, 3, 4)))
  D <- tensor(C, B, c(4, 3), c(1, 2))
  stopifnot(all(dim(D) == c(2, 2)))

  E <- matrix(9:12, 2, 2)
  s <- tensor(D, E, 1:2, 1:2)
  stopifnot(s == sum(D * E), is.null(dim(s)))
}

\keyword{array}
