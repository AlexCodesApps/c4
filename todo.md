- [ ] Support const fns
    - [ ] Design and implement fn ir
    I have done some planning and I realize that
    const functions don't actually ensure that everything
    in its body is reduced on one pass, and that the IR
    should allow for "runtime" compile time errors, so that
    recursive fns can call each other sensibly while not
    being fully "reduced". Also the previous model is very useless
    This also entains having const variables in function scope
    in ``ensure_var_is_implemented`` doesn't make inability to reduce variables an error.
    Considering that decls are declared in the first impl pass, there doesn't seem to be any
    issues with reducing expressions here, but its more like an "early maybe not optimization"
    that could lead to more fragile code with duplicate logic here and there. therefore it should probably be factored out into another
    function. ``ensure_expr_is_reduced`` or smth. Also consider making distinct passes for each type of node
    because type safety (yay) and its just awkward to try and fit everything into one pass style and possible
    renables bugs that the model sought to defeat.
    - [X] Add support in syntax for const functions (and variables)
    - [ ] Implement const fn interpreter
- [ ] Revamp semantic error messages
    - [ ] Embed source information throughout sematic analysis trees
    - [ ] Write dedicated functions for reporting errors
        - [ ] Type(s) of expr(s) are wrong error
        - [ ] Unknown identifier error
- [X] Rewrite type and fn completion to use work queue
    - [X] Rewrite type completion to use work queue
    - [X] Rewrite fn completion to use work queue
- [X] Reimplement intern type with deduplicating complete types in mind
- [ ] Implement addition with ptr offset support
- [ ] Implement overflow checking and handling
