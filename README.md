# Isabelle-Hello-World
Hello World in Isabelle, compiled to Haskell.


# Example

Isabelle
```Isabelle
definition main :: "unit io" where
  "main ≡ do {
               _ ← println (STR ''Hello World! What is your name?'');
               name ← getLine;
               println (STR ''Hello, '' + name + STR ''!'')
             }"
```

compiles to

```Haskell
main :: Prelude.IO ();
main =
  (StdIO.println
    "Hello World! What is your name?") >>= (\ _ ->
     StdIO.getLine >>= (\ name -> StdIO.println (("Hello, " ++ name) ++ "!")));
```

executes

```
$ runhaskell Main.hs
Hello World! What is your name?
Corny
Hello, Corny!
```


# Contributing
 * Keep it simple! I want simple, understandable, well-documented examples.
 * Don't rewrite simple examples to a super generic, highly abstract meta model.
   Feel free to push the super generic, highly abstract meta model in a separate file and explain *how* and *why* the
   base model needs to be extended.

# Things I'd like to see
 * Socket server.
 * String handling.
 * `println "foo" >> println "bar"` and a *proof* that I got `foo\nbar\n` on my STDOUT [[done]](HelloWorld_Proof.thy).
 * `now >>= \time -> println $ "the time is now " ++ time`.
 * Read a number from STDIN, increment the number and output it.
