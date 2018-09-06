# Nextep

## Installation

**Please note that Nextep does not work on Windows systems yet. A Linux-based or MacOs-based system is required.**

Nextep is developed in [Racal](https://www.rascal-mpl.org/) and relies on the [AlleAlle library](https://github.com/cwi-swat/allealle) and the [Z3 theorem prover](https://github.com/Z3Prover/z3). The easiest way to get started with Nextep is to set-up an Eclipse installation with the appropriate components:

1. Make sure your system has a Java JDK (not JRE!) Version 8 or higher installed
2. Download the [Eclipse Photon IDE for Java Developers](https://www.eclipse.org/downloads/packages/release/photon/r/eclipse-ide-java-developers)
3. Download and install the [Z3 theorem prover](https://github.com/Z3Prover/z3) on your system (preferably using your package manager, e.g., `apt-get install z3` or `pacman -S z3`)
4. Take note of the path to the `z3` executable on your system (e.g. `/usr/bin/z3`). On Linux systems, you can get this information by running the command `which z3` in a console.
4. Unzip the Eclipse archive and append a new line at the end to the `eclipse.ini` file it contains:
    * `-Dsolver.z3.path=/usr/bin`. The path must point to the folder containing the `z3` executable
5. Open Eclipse and install the Rascal meta-programming environment
    * Go to `Help -> Install New Software...`, use `https://update.rascal-mpl.org/unstable/` as the update site URL in the `Work with:` textbox, and then check the `Rascal` feature. Follow the instructions to install Rascal (`Next -> Next -> Finish`), and restart Eclipse when asked.

## Getting the source and examples

1. In the folder of your choice, clone the `AlleAlle` and `live-modeling` repositories:
     * `git clone https://github.com/cwi-swat/allealle/`
     * `git clone https://github.com/cwi-swat/live-modeling/`
2. In Eclipse, open the `Rascal` perspective (`Window -> Perspective -> Open Perspective -> Other -> Rascal`)
3. navigate to `File -> Import` and select `Existing Projects into Workspace`
4. In the `Select root directory` box, select the directory containing the `AlleAlle` and `live-modeling` projects you just cloned
5. Make sure the three projects `allealle`, `nextstep`, and `playground` are checked in the `Projects:` list, and click `Finish`.
6. Wait for the workspace to build the projects

## Playing with the examples
