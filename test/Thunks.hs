import Debug.Trace

foo :: Int
foo = trace "static thunk evaled" $ 1+1


bar True thunk = thunk
bar False _ = 1
{-# NOINLINE bar #-}

test i = do
    let n = trace "dynamic thunk evaled" $ bar True i
    print $ bar True foo
    print $ bar True foo
    print $ bar True foo
    print $ bar True n
    print $ bar True n
    print $ bar True n
{-# NOINLINE test #-}


main = test 1
