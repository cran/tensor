"tensor" <-
function(A, B, alongA = integer(0), alongB = integer(0))
  .Call("tensor", A, B, alongA, alongB)

"%O%" <- function(x, y) tensor(x, y)

"%*t%" <- function(x, y) tensor(x, y, 2, 2)

"%t*%" <- function(x, y) tensor(x, y, 1, 1)

"%t*t%" <- function(x, y) tensor(x, y, 1, 2)
