
1. test cases for benchmark 
2. paper restructure with FM 
3. highlight example. 

pure = true
y = 2
pure = y = 2
y = y + 1

pure = ex y1. y1 = 2 & y = y1 + 1

y = y + 5

pure = ex y1, y2. (y1 = 2 & y = y1 + 1)[y2/y] & y = (y + 5)[y2/y]
  == ex y1, y2. y1 = 2 & y2 = y1 + 1 & y = y2 + 5
  
  
  
  ----------------------
   forall y1. y1 = 2