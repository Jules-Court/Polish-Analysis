COMMENT Fibo sans la déclaration de y
READ n
x := 0
IF n = 0
  PRINT 0
ELSE
  n := - n 1
  WHILE n > 0
    z := + x y
    x := y
    y := z
    n := - n 1
  PRINT y
