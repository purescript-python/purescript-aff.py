# purescript-aff.py

This is an initial implementation of Effect.Aff that copies the JavaScript implementation more or less verbatim.

There is still much to do:

- general bug fixing, as there are some subtle bugs due to copy and paste errors
- making the code more pythonic
- correctly guarding code with threading.Lock

The repo is in _alpha_ development. The code is not fit for anything other than experimental usage. It needs additional development and testing before being able to be incorporated into the official package-set for purescript.python.
