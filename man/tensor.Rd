\name{tensor}

\alias{tensor}
\alias{\%O\%}
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

\details{A straightforward implementation of \code{tensor} in \R
would be to perm the along extents to the end of each object,
reshape each object as a matrix with the columns corresponding to
the along extents, take the matrix product of the first object
with the transpose of the second, and then reshape the result.
This happens to be very expensive if the objects are large (and
people who want tensors often have large objects!).  But it is
recommended if speed is an issue and RAM is ample.

This \code{tensor} implements the tensor product without perming
or reshaping using the concept of `strides', which will be
familiar to numerical programmers in Python.  In other words, if
\code{A}, \code{B} and their required tensor product fit into the
available memory, then the calculation will complete (modulo a
few small objects created \emph{en route}).  All code is written
in "C", for speed.  \code{NA} is fully supported and the original
storage type of the objects (integer, double or complex) is
preserved, where possible.  This might be useful for matrix
products on integers (which \R promotes to doubles): see the
Section on Shortcuts below.}

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
\%O\%	\tab	Outer product of \code{A} and \code{B}	\cr
\%*t\%	\tab	Matrix product \code{A \%*\% t(B)}	\cr
\%t*\%	\tab	Matrix product \code{t(A) \%*\% B}	\cr
\%t*t\%	\tab	Matrix product \code{t(A) \%*\% t(B)}	
}}

\author{Jonathan Rougier, \email{J.C.Rougier@durham.ac.uk}}

\seealso{\code{\link{outer}}}

\examples{
  A <- matrix(1:6, 2, 3) # has storage mode "integer"
  dimnames(A) <- list(happy = LETTERS[1:2], sad = NULL) # just for fun!
  B <- matrix(1:12, 4, 3)
  all(A \%*\% t(B) == tensor(A, B, 2, 2)) # TRUE
  A \%*t\% B # same answer

  A <- A \%O\% A # now 2 by 3 by 2 by 3
  storage.mode(A) # still integer
  A <- A + 0.0 # storage mode now "double"
  C <- tensor(A, B, 2, 2) # will be 2 by 2 by 3 by 4
  D <- tensor(C, B, c(4, 3), c(1, 2)) # will be 2 by 2

  E <- matrix(9:12, 2, 2)
  s <- tensor(D, E, 1:2, 1:2) # scalar, NO dim attribute
  s == sum(D * E) # TRUE
}

\keyword{array}
