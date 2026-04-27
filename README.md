# lin-lattice

Chao Wang (Southwest University), Ruijia Li (Southwest University), Yang Zhou (Southwest University), Peng Wu (Institute of Software, Chinese Academy of Sciences), Yi Lv (Institute of Software, Chinese Academy of Sciences), Jianwei Liao (Southwest University), Jim Woodcock (Southwest University; State Key Laboratory of Intelligent Vehicle Technology; Aarhus University; University of York), Zhiming Liu (Southwest University).

Artifact package accompanying our CONCUR 2026 submission:

**A Forward Simulation-Based Hierarchy of Linearizable Concurrent Objects**

The formal proofs in this repository were co-developed by Yi Lv, Ruijia Li, Yang Zhou, and Chao Wang. For a detailed breakdown of individual contributions, please refer to the AUTHORS file.

## Introduction

This repository contains the Isabelle/HOL development for the machine-verified results reported in our CONCUR 2026 submission *A Forward Simulation-Based Hierarchy of Linearizable Concurrent Objects*.

The development studies forward simulation relations between linearizable concurrent objects, and includes formal proofs for the following case studies:

- the Herlihy-Wing queue is simulated by U<sup>s</sup><sub>Queue</sub>;
- the time-stamped queue simulates the Herlihy-Wing queue;
- the time-stamped queue is not simulated by the Herlihy-Wing queue.

The repository is organized into two main proof directories:

- `HWQ-U/`: proofs for the simulation from the Herlihy-Wing queue to U<sup>s</sup><sub>Queue</sub>;
- `HWQ-TSQ/`: proofs for the simulation from the time-stamped queue to the Herlihy-Wing queue, and for the non-simulation result in the opposite direction.

## Repository Structure

### `HWQ-U/`

This directory contains the Isabelle/HOL development for the proof that the Herlihy-Wing queue is simulated by U<sup>s</sup><sub>Queue</sub>.

Its main files are organized as follows:

- `Model.thy`: core definitions of states, histories, linearizations, invariants, and transition rules of Herlihy-Wing queue;
- `PureLib.thy`, `StateLib.thy`, `DistLib.thy`, `EnqLib.thy`, `DeqLib.thy`: shared auxiliary lemmas and proof infrastructure;
- `Termination.thy`: auxiliary termination-related lemmas used in this development;
- `L0Lemmas.thy`, `E1Lemmas.thy`, `E2Lemmas.thy`, `E3Lemmas.thy`, `D3Lemmas.thy`, `D4Lemmas.thy`: transition-specific auxiliary lemmas;
- `L0Proof.thy`, `E1Proof.thy`, `E2Proof.thy`, `E3Proof.thy`, `D1Proof.thy`, `D2Proof.thy`, `D3Proof.thy`, `D4Proof.thy`: preservation proofs for individual transition cases;
- `SysInvProof.thy`: preservation of the global system invariant;
- `ULinProof.thy`: the main proof connecting the Herlihy-Wing queue to U<sup>s</sup><sub>Queue</sub>.


### `HWQ-TSQ/`

This directory contains the Isabelle/HOL development for the simulation and non-simulation results between the Herlihy-Wing queue and the time-stamped queue.

Its main files are organized as follows:

- `TSQModel.thy`: core definitions for the time-stamped queue model;
- `SimLemmas.thy`: auxiliary lemmas used in the simulation proof;
- `SimProof.thy`: global step simulation theorem;
- `TraceInv.thy`: invariants over traces used in the simulation development;
- `TraceProof.thy`: the main proof that the time-stamped queue simulates the Herlihy-Wing queue;
- `NotSimLemmas.thy`: auxiliary lemmas for the non-simulation argument;
- `NotSimProof.thy`: the main proof that the time-stamped queue is not simulated by the Herlihy-Wing queue.

## Requirements

This artifact has been developed and tested with Isabelle2025-2.

Other platforms and editor setups may also work, provided that Isabelle2025-2 is installed correctly.

## Installation

Clone or download this repository, and make sure Isabelle2025-2 is available on your machine.

No additional external dependencies are required beyond Isabelle2025-2.

## Usage

The session defined in this repository is `LinLattice`.

To build the full development, run the following command from the repository root (the directory containing `ROOT`):

```bash
isabelle build -D .
```

## Evaluation

If the build command finishes successfully, then the Isabelle/HOL proofs in this repository have been checked successfully.

In particular, a successful build confirms the formalization of the following results from the paper:

- the Herlihy-Wing queue is simulated by U<sup>s</sup><sub>Queue</sub>;
- the time-stamped queue simulates the Herlihy-Wing queue;
- the time-stamped queue is not simulated by the Herlihy-Wing queue.

## Correspondence to the Paper

The correspondence between the paper and the formal development is as follows:

- **Section on U<sup>s</sup><sub>Queue</sub> and the Herlihy-Wing queue case study**  
  Formalized mainly in `HWQ-U/`.

- **Section on the simulation from the time-stamped queue to the Herlihy-Wing queue**  
  Formalized mainly in `HWQ-TSQ/SimLemmas.thy` , `HWQ-TSQ/SimProof.thy` and  `HWQ-TSQ/TraceProof.thy`.

- **Section on the non-simulation result**  
  Formalized mainly in `HWQ-TSQ/NotSimLemmas.thy` and `HWQ-TSQ/NotSimProof.thy`.

## Acknowledgments

During the conceptualization and development of the formal proofs, the authors utilized the web interfaces of several large language models, including Gemini, ChatGPT, and DeepSeek, to brainstorm verification strategies and explore tactical structures. All resulting proof scripts were mechanically verified by Isabelle/HOL to ensure strict mathematical correctness.
