# cagen

`cagen` is a prototypical helper for the work with contract automata. 

This program offers you the construction of proof obligations based on a system description and contract automata. 
There different proof obligations. 

We recommend you to use [nuXmv](https://nuxmv.fkb.eu), [cbmc](https://www.cprover.org/cbmc/) and [seahorn](https://github.com/seahorn/seahorn).

## Input Language

Note, that cagen tries to be a small, simple and flexible. Therefore, we  avoid implementing a complete language for contracts at the moment. So expression are given in double quotes and are interpreted on a text base. Currently, you should use a subset of SMV expressions, 
which we can easily translate to C by string replacement, e.g., `0sd32_0` is replaced to `0`, or `TRUE` to `true`. Wie have implemented support to Booleans and Integer (32-bit signed) only. 


### Contract Automata 

In our model we have two entities. The first one are the contract automata defined
```
contract <name> {
    input <var> : <type>
    output <var> : <type>

    history <var>(<int>)

    refines <name> <binding>    

    <state> -> <state> :: "pre" ==> "post"    
}
```

A contract has a name and a signature (input and output variables). Additionally, a state storing the historical values requested by the `history` including the name and depth. A contract can refine another contract for this you can also define a mapping between those. A mapping looks like this `[x <- y, ...]`, where `x` is the variable in the refined contract, and `y` is the variable in the current contract. (No expression currently supported).

The special thing about contract automata are the states, which are defined via their mentioning in a transition. A transition goes from one state to the other, if the "pre" and "post" (given in double quotes) are fullfiled.

### System 

The second entity are the systems, which have to shapes: either their are given as a program fragment, quoted in `{= ... =}`, or as a composed system. A system also has a list of variables (input, output, and state). With `contract <name> <binding>` you can define a contract for a system.
Here is the example from the paper using a program:

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

A composed system instead is given by sub-systems and their interconnections.

```
reactor Top {


}
```


## Tool usage


## Case Study: iFM
