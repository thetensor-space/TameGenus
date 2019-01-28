# TameGenus

A package for isomorphism testing of groups of tame genus for Magma V2.22 and 
beyond. 

This software was created by Peter A. Brooksbank, Joshua Maglione, and James B. 
Wilson, Copyright 2015--2019. Distributed under GNU GPLv3.

If you want a copy of the software under a different license, please contact the
authors. 


## Copying 

This program is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT 
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with this program. If not, see <http://www.gnu.org/licenses/>.


## Package Contents 

  1. Spec file is `./TameGenus.spec`
  2. Source Code is contained in the folder `src`
  3. Examples are included in the folder `examples`
  4. Documentation is included as `TameGenus.pdf` in `doc`
  5. Example files are demonstrated in `TameGenus.pdf` and their file names 
     coincide with their example title in the text.
  6. Performance and debugging tests are contained in the folder `tests`


## Installation 

This package requires two other packages publicly available on GitHub.
  
  1. eMAGma: <https://github.com/algeboy/eMAGma>
  2. StarAlge: <https://github.com/algeboy/StarAlge>
  
  Attach the spec file during a Magma run and the intrinsics will be available to use.  To attach the spec file run the following, where `<location>` is the directory containing the TameGenus directory,

```
  > AttachSpec("<location>/TameGenus/TameGenus.spec");
```


## Latest Versions 

Current version: 1.2.

Latest versions can be downloaded on GitHub at:
  <https://github.com/algeboy/TameGenus>


## Feedback, Bugs, and Contributions 

We welcome general feedback about the package and challenging examples. To report bugs, please create an "Issue" on TameGenus repository site on GitHub. Contributions are always welcome. To contribute, please fork a copy of TameGenus and create a pull request.
