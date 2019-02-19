# TameGenus

A package for isomorphism testing of groups and tensors of tame genus for  Magma 
V2.22 and beyond. 

This software was created by Peter A. Brooksbank, Joshua Maglione, and James B. 
Wilson, Copyright 2015--2019. Distributed under MIT License.

If you want a copy of the software under a different license, please contact 
the authors. 



## Acknowledgements

TameGenus was developed by researchers at Bucknell U. and Colorado State U. and
partially supported by a National Science Foundation grant to Brooksbank and 
Wilson, and the Simons Foundation grant to Brooksbank.  We also acknowledge 
Kent State U. and U. Bielefeld, and U. Auckland where research was undertook 
and support provided for this package.



## Our Team

We invite you explore the repository and join our team.  We welcome and encourage any contributions to the repository. If you need help getting started, please feel free to @-mention any of the contributors below or you can read the repository's [Projects](https://github.com/thetensor-space/TameGenus/projects) tab.

|                                                                              | Name                | Username                         | 
-------------------------------------------------------------------------------|---------------------|----------------------------------|
<img src="https://avatars.githubusercontent.com/galois60" height="50px"/>      | Peter A. Brooksbank | [`@galois60`](https://github.com/galois60)                |
<img src="https://avatars.githubusercontent.com/joshmaglione" height="50px"/>  | Joshua Maglione     | [`@joshmaglione`](https://github.com/joshmaglione)        |
<img src="https://avatars.githubusercontent.com/algeboy" height="50px"/>       | James B. Wilson     | [`@algeboy`](https://github.com/algeboy)                  |



## Copying 

This program is free software: you can redistribute it and/or modify it 
under the terms of the MIT license.

This program is distributed in the hope that it will be useful, but without any
warranty; without even the implied warranty of merchantability or fitness for a
particular purpose. 



## Repository Structure
```
TameGenus/
+  doc/                           Documentation folder of all LaTeX files
   +  TameGenus.pdf               The documentation for TameGenus
+  examples/                      Folder of examples demonstrated in documentation
+  src/                           Source code folder 
+  tests/                         Folder of performance and debugging tests
+  install.sh                     Shell file to install repo
+  TameGenus.spec                 Magma spec file
+  update.sh                      Shell file to update repo
```



## Install

#### Downloading Latest Releases

The latest release of TameGenus can be downloaded from 
[here](https://github.com/thetensor-space/TameGenus/releases/latest) 
as either a `tar.gz` or `zip` file.

#### Linux and Mac users

We will assume your directory for Magma packages is titled `my_magma_packages`. You can create this directory with
```
$ mkdir my_magma_packages
```
Download `TameGenus-x.y.tar.gz` file from the latest release into `my_magma_package`.
Then you could run the following to unzip TameGenus and install the package.
```
$ cd my_magma_packages
$ gzip TameGenus-x.y.zip
$ sh TameGenus/install.sh
```

This may install further packages necessary in `my_magma_packages`. It may also modify your Magma start file (`~/.magmarc`) so that these packages are available at the start of a Magma session. To avoid this, use the manual installation instructions below.


#### Manually

Currently, we do not have an install file compatible with Windows. 

This package requires three other packages publicly available on GitHub.
  1. [TensorSpace](https://github.com/thetensor-space/TensorSpace)
  2. [StarAlge](https://github.com/thetensor-space/StarAlge)
  3. [Sylver](https://github.com/thetensor-space/Sylver)

Check the README files to install each of the required packages.

Attach the spec file during a Magma run and the intrinsics will be available
to use.  To attach the spec file, run the following, where `<location>` is the directory containing TameGenus,
```
> AttachSpec("<location>/TameGenus/TameGenus.spec");
```



## Uninstall

This package can be removed entirely by deleting the folder into which it was 
downloaded and removing the following lines from your `~/.magmarc` file.
```
AttachSpec("<location>/TameGenus/TameGenus.spec");
```

To remove the dependencies, delete the folders for TensorSpace, StarAlge, and 
Sylver along with the following lines from your `~/.magmarc` file.
```
AttachSpec("<location>/TensorSpace/TensorSpace.spec");
AttachSpec("<location>/StarAlge/StarAlge.spec");
AttachSpec("<location>/Sylver/Sylver.spec");
```



## Feedback and Bugs

We welcome general feedback about the package and challenging examples. To report bugs, please create a [New Issue](https://github.com/thetensor-space/TameGenus/issues/new) under the [Issues](https://github.com/thetensor-space/TameGenus/issues) tab in the TameGenus repository, or @-mention any of the above contributors in your forked repository.

