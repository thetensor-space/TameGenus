# TameGenus

A package for isomorphism testing of groups of tame genus for Magma V2.22 and 
beyond. 

This software was created by Peter A. Brooksbank, Joshua Maglione, and James B. 
Wilson, Copyright 2015--2019. Distributed under MIT License.

If you want a copy of the software under a different license, please contact the
authors. 

## Acknowledgement

TameGenus was developed by researchers at Bucknell U. and Colorado State University and partially supported by a National Science Foundation grant to Brooksbank and Wilson, and the Simons Foundation grant to Brooksbank.  We also acknowledge Kent State U. and U. Bielefeld, and U. Auckland where research was undertook and support provided for this package.

## Copying 

This program is free software: you can redistribute it and/or modify it 
under the terms of the MIT license.

This program is distributed in the hope that it will be useful, but WITHOUT 
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. 

## Package Contents 

  1. Spec file is `./TameGenus.spec`
  2. Source Code is contained in the folder `src`
  3. Examples are included in the folder `examples`
  4. Documentation is included as `TameGenus.pdf` in `doc`
  5. Example files are demonstrated in `TameGenus.pdf` and their file names 
     coincide with their example title in the text.
  6. Performance and debugging tests are contained in the folder `tests`


## Installation 

This package requires three other packages publicly available on GitHub.
  
  1. TensorSpace: <https://github.com/thetensor-space/TensorSpace>
  2. StarAlge: <https://github.com/thetensor-space/StarAlge>
  3. Sylver: <https://github.com/thetensor-space/Sylver>
  
  Attach the spec file during a Magma run and the intrinsics will be available to use.  To attach the spec file run the following, where `<location>` is the directory containing the TameGenus directory,

```
> AttachSpec("<location>/TameGenus/TameGenus.spec");
```


## Latest Versions 

Current version: 2.0.

Latest versions can be downloaded on GitHub at:
  <https://github.com/thetensor-space/TameGenus>


## Feedback, Bugs, and Contributions 

We welcome general feedback about the package and challenging examples. To report bugs, please create an "Issue" on TameGenus repository site on GitHub. Contributions are always welcome. To contribute, please fork a copy of TameGenus and create a pull request.
