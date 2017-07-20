# cur-control
This is a prototype implementation of the control operators `shift` and `reset` as user-defined
extensions in [Cur](https://www.github.com/wilbowma/cur).
This is the implementation for the HOPE 2017 Talk [Only Control Effects and Dependent Types](http://icfp17.sigplan.org/event/hope-2017-papers-only-control-effects-and-dependent-types).

## Installing
Clone the repository and run `make install`.
Alternatively, run `raco pkg install https://github.com/wilbowma/cur-control`.

## Using
See `cur/control/shift-reset-cbv.rkt` for examples.
The current implementation only internalizes type-level contexts, so it is not useful
for programming as you may expect of `shift/reset`.
Proper documentation and usage guides to come.
