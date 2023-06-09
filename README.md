# cagen

`cagen` is a prototypical helper for the work with contract automata. 

This program offers you the construction of proof obligations based on a system description and contract automata. 
There different proof obligations. 

We recommend you to use [nuXmv](https://nuxmv.fkb.eu), [cbmc]() and [seahorn]().

## Input Language

Note, that cagen tries to be a small, simple and flexible. Therefore, we  avoid implementing a complete language at the current. 
An impact is that there is no expression language for the pre- and post-condition of the contracts. We use a subset of SMV, 
that is easy to translate to C by string replacement. 

### Contract Automata 
```
contract <name> {
        
    refines <name> <binding>
    
    state -> state :: "pre" ==> "post"    
}

```

### System 

``` 
reactor Counter  {
    input  tick : bool
    output val : int
    state  down : bool

    contract UpDown[cnt <- val, tick <- tick]

    {=
        if(tick) {
        if(!down) {
            val += 1;
        } else {
            val -= 1;
        }

        if(val == 128 || val == -128) down = !down;
        }
    =}
}
```

A system is defined by the 