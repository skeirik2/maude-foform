State-space Exploration
=======================

Here we instantiate all the above given components to a language suitable for
narrowing modulo SMT trace-based analysis.

```{.maude .state-space}
load msh

fmod STATE-EXPLORE is
  protecting MSH .

  var EXEC-COMMAND : Command{Modules=>State} .

  op explore-all-with : Command{Modules=>State} -> Program .
  ---------------------------------------------------------
  eq explore-all-with(EXEC-COMMAND) = extend
                                    ; while (not empty?) { EXEC-COMMAND
                                                         ; extend
                                                         ; load
                                                         } .
endfm
```
