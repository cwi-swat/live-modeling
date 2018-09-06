# Nextep

## Installation

### Option 1: Virtual Machine

Nextep and its dependencies have been packaged in a Debian VM image that can be downloaded from here: [Nextep-VM](https://www.dropbox.com/s/21wtakq2plkbx5h/Nextep-VM.ova?dl=0). Refer to the [VirtualBox documentation](https://docs.oracle.com/cd/E26217_01/E26796/html/qs-import-vm.html) for instructions on how to import the image in your host system.

The VM comes with default user and administrator accounts:

| Username | Password |
| -------- | -------- |
|  nextep  |  nextep  |
|  root    |  nextep  |

In the VM, run the Eclipse shortcut on the desktop to access a pre-configured Nextep environment. From this point, follow the [Playing with the Examples](#playing-with-the-examples) instructions below.

### Option 2: Manual installation

**_Disclaimer_: Please note that Nextep does not work on Windows systems yet. A Linux-based or MacOS-based system is required. Nextep does not play well with Z3 version 4.4.1. A more recent version of Z3 is required.**

#### Setting up the Environment

Nextep is developed in [Racal](https://www.rascal-mpl.org/) and relies on the [AlleAlle library](https://github.com/cwi-swat/allealle) and the [Z3 theorem prover](https://github.com/Z3Prover/z3). The easiest way to get started with Nextep is to set-up an Eclipse installation with the appropriate components:

1. Make sure your system has a Java JDK (not JRE!) Version 8 installed and properly configured
2. Download the appropriate [Eclipse Photon IDE for Java Developers](https://www.eclipse.org/downloads/packages/release/photon/r/eclipse-ide-java-developers) for your platform
3. Download and install the [Z3 theorem prover](https://github.com/Z3Prover/z3) on your system (preferably using your package manager, e.g., `apt-get install z3`, `pacman -S z3`, etc.)
4. Take note of the path to the `z3` executable on your system (e.g. `/usr/bin/z3`). On Linux systems, this information can be retrieved by running the command `which z3` in a console.
4. Unzip the Eclipse archive and append a new line at the very end to the `eclipse.ini` file it contains:
    * `-Dsolver.z3.path=/usr/bin`. The path must point to the *folder* containing the `z3` executable, *not the full path of the `z3` executable*
5. Open Eclipse and install the Rascal meta-programming environment:
    * Go to `Help -> Install New Software...`, use `https://update.rascal-mpl.org/unstable/` as the update site URL in the `Work with:` textbox, and then check the `Rascal` feature. Follow the instructions to install Rascal (`Next -> Next -> Finish`), and restart Eclipse when asked. In case of any errors, please check instructions on the [Rascal download page](https://www.rascal-mpl.org/start/)

#### Getting the Source Code and Examples

1. In the folder of your choice, clone the `AlleAlle` and `live-modeling` repositories:
     * `git clone https://github.com/cwi-swat/allealle/`
     * `git clone https://github.com/cwi-swat/live-modeling/`
2. In Eclipse, open the `Rascal` perspective (`Window -> Perspective -> Open Perspective -> Other -> Rascal`)
3. Navigate to `File -> Import` and select `Existing Projects into Workspace`
4. In the `Select root directory` box, select the directory containing the `AlleAlle` and `live-modeling` projects you just cloned
5. Make sure the two projects `allealle` and `nextstep` are checked in the `Projects:` list, and click `Finish`
6. Wait for Eclipse to build the workspace with the two projects

## Playing with the Examples

### Nextep Specifications

The Nextep specifications for the state machine example and the robotic arm example are located in the `nextstep -> input` directory.

To automatically translate Nextep specifications to AlleAlle, then to Z3, and explore the results, follow these instructions:

1. Select (click on) the `nextstep` project in the workspace explorer on the left
2. In the top menu, click on `Rascal -> Start Console`
3. In the `Terminal` view that appears in the bottom, type `import Pipeline;`
4. Wait for the `rascal>` prompt to come back (ignore the warnings):
     * To run the state machine example (scenario II from the paper), type `runNextepSM();`
     * To run the robotic arm example, type `runNextepRoboticArm();` 
5. In both cases, a new Model Visualizer window will open, displaying the results in the form of tables
6. All the tables prefixed with `xn_` correspond to the newly found runtime state. For instance, in the state machine example, the `xn_Runtime_current` table displays the `current` state for the new version of the state machine `doors` as inferred by the solver

The interested reader can refer to the `Pipeline.rsc` file located in the `src` folder of the `nextstep` project to learn more about how Nextep specifications are translated to AlleAlle.

### Manually-written AlleAlle Specifications

The `nextstep -> output` directory contains manually-written version of the AlleAlle specifications for the two example DSLs. They are better formatted than the automatically-generated version and contain additional documentation for the different constraints and relations.

## Benchmarks

The benchmarks for the state machine example presented in the paper can be reproduced in the following way:

1. Select (click on) the `nextstep` project in the workspace explorer on the left
2. In the top menu, click on `Rascal -> Start Console`
3. In the `Terminal` view that appears in the bottom, type `import benchmark::statemachine::StateMachineBenchmark;`
4. Run the benchmark by entering `runBothScenarios();`
5. When the `rascal>` prompt comes back, the results are written in the `nextstep/benchmark/` directory
