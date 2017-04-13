import Debug.Trace

foo :: Int
foo = trace "static thunk evaled" $ 1+1


bar True thunk = thunk
bar False _ = 1


main = do
    let n = trace "dynamic thunk evaled" $ bar False undefined
    print $ bar True foo
    print $ bar True foo
    print $ bar True foo
    print $ bar True n
    print $ bar True n
    print $ bar True n
