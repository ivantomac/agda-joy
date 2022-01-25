{-# LANGUAGE TypeOperators #-}

-------------------- Stack, Concatenation and Literals ----

type a × b = (a, b)

(·) :: (a -> b) -> (b -> c) -> (a -> c)
(·) = flip (.)

infixr 0 ×
infixl 0 ·

l :: a -> s -> a × s
l = (,)

---------------------------------- Primitive Functions ----

true    :: s                -> Bool × s
false   :: s                -> Bool × s
dup     :: a × s            -> a × a × s
pop     :: a × s            -> s
swap    :: a × b × s        -> b × a × s
over    :: a × b × s        -> b × a × b × s
rot     :: a × b × c × s    -> c × a × b × s
i       :: (s -> t) × s     -> t
dip     :: (s -> t) × a × s -> a × t
stack   :: s                -> s × s
unstack :: t × s            -> t

true                  = l True
false                 = l False
dup  s @ (a, _)       = (a, s)
pop  (_, s)           = s
swap (a, (b, s))      = (b, (a, s))
over s @ (_, (b, _))  = (b, s)
rot  (a, (b, (c, s))) = (c, (a, (b, s)))
i    (f, s)           = f s
dip  (f, (x, s))      = (x, f s)
stack s               = (s, s)
unstack               = fst

branch :: (s -> t) × (s -> t) × Bool × s -> t
branch (ifFalse, (ifTrue, (cond, s))) =
    (if cond then ifTrue else ifFalse) s

ifte :: (s -> t) × (s -> t) × (s -> Bool × r) × s -> t
ifte (ifFalse, (ifTrue, test @ (_, s))) =
    (if fst $ i test then ifTrue else ifFalse) s

tailrec :: (s -> s) × (s -> t) × (s -> Bool × r) × s -> t
tailrec (rec, (end, (test, s))) =
    if fst $ (l test·i) s
       then (l end·i) s
       else (l rec·i·l test·l end·l rec·tailrec) s

binop :: (a -> a -> b) -> a × a × s -> b × s
binop f (x, (y, s)) = (f y x, s)

sub :: Num n => n × n × s -> n × s
mul :: Num n => n × n × s -> n × s
lt  :: Ord a => a × a × s -> Bool × s
gt  :: Ord a => a × a × s -> Bool × s

sub = binop (-)
mul = binop (*)
lt  = binop (<)
gt  = binop (>)

------------------------------------ Derived Functions ----

popd  :: a × b × s     -> a × s
dupd  :: a × b × s     -> a × b × b × s
swapd :: a × b × c × s -> a × c × b × s
x     :: (s -> t) × s  -> (s -> t) × t

popd  = l pop ·dip
dupd  = l dup ·dip
swapd = l swap·dip
x     = dup   ·dip

rotdrop :: a × b × c × s -> a × b × s
rotdrop = rot·pop

fact :: (Num n, Ord n) => n × s -> n × s
fact
    = l (l 0·gt)
    · l (dup·l 1·sub·fact·mul)
    · l (pop·l 1)
    · ifte

------------------------------------------------ Tests ----

testFact :: Int
testFact = fst $ fact (6, ())
