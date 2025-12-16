# Rez-Mež
Measures the resistance of countermodels to iteratively applying families of extensive operators to the original formula.
## Running
- Modify Makefile.
  - CADICAL_INC should find src of CaDiCaL, and CADICAL_LIB_DIR its build.
- To measure resistance:
  - `make rez-mež`
  - `./rez-mež <input> [options]`
- To convert to DNF:
  - `make to_dnf`
  - `./to_dnf <CNF>`
## Not All Countermodels Are Equal
- Commands
  - $\delta_H$ `./rez-mež <input> -a`
  - $\nu_o$ `./rez-mež <input> -c`
- DNF Instances
  - [Zenodo](https://zenodo.org/uploads/17913232)

## Licensing
This software has been developed for the project BLaSST. It is released under the terms of the GNU LGPL v3.0 licence.

BLaSST is a project funded by ANR, the French research agency. It involves the VeriDis team of Inria in Nancy, the CRIL laboratory of University of Artois in Lens, the CLEARSY company, and the Montefiore Institute of University of Liège in Belgium. BLaSST was selected for funding as project ANR-21-CE25-0010.