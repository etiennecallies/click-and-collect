The repository contains
frontend and backend code
for an online by-click sequent prover.

# Deploy
- Install dependencies
```
sudo apt-get install opam
opam init
sudo apt-get install libgdbm-dev libsqlite3-dev
opam depext ocsigen-start
opam install ocsigen-start
```
- Clone this repository
- Add this nginx config (install it with `sudo apt install nginx`)
```
server {
    root /home/{username}/linearon;
    index index.html;
    server_name {hostname};

    location / {
        proxy_pass http://127.0.0.1:8080;
    }
}
```
- Allow https by adding a certificate `sudo certbot --nginx`
- Launch
```
cd linearon
make all # first time you'll need to comment ocaml dependencies
make test.byte
```

# Modify parser
Do not modify `parser.mli` or `parser.ml` neither `lexer.mll`, but just `parser.mly` and `lexer.mll` and then run
```
ocamllex lexer.mll && ocamlyacc parser.mly
```

# Files description

The following files in this directory have been generated by
eliom-distillery:

 - linearon.eliom
   This is your initial source file.

 - static/
   The content of this folder is statically served. Put your CSS or
   additional JavaScript files here!

 - Makefile.options
   Configure your project here!

 - linearon.conf.in
   This file is a template for the configuration file for
   ocsigenserver. You will rarely have to edit itself - it takes its
   variables from the Makefile.options. This way, the installation
   rules and the configuration files are synchronized with respect to
   the different folders.

 - Makefile
   This contains all rules necessary to build, test, and run your
   Eliom application. You better don't touch it ;) See below for the
   relevant targets.

 - local/
   This directory is the target of the temporary installation of
   your application, to test locally before doing a system-wide
   installation in /. Do not put anything manually here.

 - README
   Not completely describable here.


# Makefile targets

Here's some help on how to work with this basic distillery project:

 - Test your application by compiling it and running ocsigenserver locally
     $ make test.byte (or test.opt)

 - Compile it only
     $ make all (or byte or opt)

 - Deploy your project on your system
     $ sudo make install (or install.byte or install.opt)

 - Run the server on the deployed project
     $ sudo make run.byte (or run.opt)

   If WWWUSER in the Makefile.options is you, you don't need the
   `sudo'. If Eliom isn't installed globally, however, you need to
   re-export some environment variables to make this work:
     $ sudo PATH=$PATH OCAMLPATH=$OCAMLPATH LD_LIBRARY_PATH=$LD_LIBRARY_PATH make run.byte/run.opt

 - If you need a findlib package in your project, add it to the
   variables SERVER_PACKAGES and/or CLIENT_PACKAGES. The configuration
   file will be automatically updated.
