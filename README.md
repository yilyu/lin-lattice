# lin-lattice

The formal proofs in this repository were co-developed by Yi Lv, Ruijia Li, Yang Zhou, and Chao Wang. For a detailed breakdown of individual contributions, please refer to the `AUTHORS` file.

## Introduction

This repository contains the Isabelle/HOL development for the machine-verified results reported in the revised arXiv version of *A Forward Simulation-Based Hierarchy of Linearizable Concurrent Objects*.

The development studies forward-simulation relations between linearizable concurrent objects and contains formal proofs for the following case studies:

- the Herlihy-Wing queue (HWQ) is simulated by $\mathcal{U}_{Queue}$;
- the time-stamped queue (TSQ) simulates the Herlihy-Wing queue;
- the time-stamped queue is not forward simulated by the Herlihy-Wing queue.

The repository is organized into two main proof directories:

- `HWQ-U/`: the HWQ-to-$\mathcal{U}_{Queue}$ development, together with queue-specification, history-transfer, $\mathcal{U}_{Queue}$-membership, and final simulation results;
- `HWQ-TSQ/`: the TSQ/HWQ simulation and non-simulation developments.

## HWQ enqueue/dequeue correspondence

The HWQ model in this repository follows the taking-effect convention used in the current paper version:

- `E1` (`C_E1` / `Sys_E1`) reserves a slot by reading/incrementing `X`; the abstract $\mathcal{U}_{Queue}$ state stutters and `lin_seq` is unchanged.
- `E2` (`C_E2` / `Sys_E2`) publishes the enqueue value into `Q[i]`; this is paired with `U_E2`, which appends the enqueue operation to `u_lin_seq` and records it in `u_eff_ops`. Thus the enqueue takes effect at `E2`.
- A successful `D3` step (the scanned slot contains a non-`BOT` value) is paired with `U_D2`; this is the taking-effect step for that dequeue. A `D3` step that reads `BOT` leaves the abstract state unchanged.

This distinction is important for the correspondence with the revised paper: `E1` is a reservation step, whereas the enqueue's abstract effect occurs at `E2`.

## Repository structure

### `HWQ-U/`

This directory contains the Isabelle/HOL development for the HWQ-to-$\mathcal{U}_{Queue}$ proof.

The main files are:

- `Model.thy`: concrete/abstract states, histories, linearization sequences, invariants, and HWQ/$\mathcal{U}_{Queue}$ transition rules;
- `PureLib.thy`, `StateLib.thy`, `DistLib.thy`, `EnqLib.thy`, `DeqLib.thy`: shared auxiliary lemmas and proof infrastructure;
- `Termination.thy`: termination-related auxiliary lemmas;
- `L0Lemmas.thy`, `E1Lemmas.thy`, `E2Lemmas.thy`, `E3Lemmas.thy`, `D3Lemmas.thy`, `D4Lemmas.thy`: transition-specific auxiliary lemmas;
- `L0Proof.thy`, `E1Proof.thy`, `E2Proof.thy`, `E3Proof.thy`, `D1Proof.thy`, `D2Proof.thy`, `D3Proof.thy`, `D4Proof.thy`: invariant-preservation proofs for individual transition cases;
- `SysInvProof.thy`: preservation of the global system invariant;
- `ULinProof.thy`: core HWQ/$\mathcal{U}_{Queue}$ simulation and recorded-history linearizability results;
- `QueueSpecLemmas.thy`, `QueueSpecTransfer.thy`: transfer from the auxiliary queue predicates to the queue specification used by the paper;
- `HistoryTransferLemmas.thy`, `HistoryTransferProof.thy`: transfer from the recorded history/linearization to the projected real history;
- `USpecMembershipLemmas.thy`, `USpecMembership.thy`: $\mathcal{U}_{Queue}$ membership consequences of the invariant;
- `HWQQueueLemmas.thy`, `HWQQueueProof.thy`: final HWQ-to-$\mathcal{U}_{Queue}$ theorem layer, including `HWQ_is_CR_simulated_by_UQueue`.

Some helper theorem names retain historical `E1` prefixes for compatibility with the established proof dependency graph. Their statements do not make `E1` the enqueue taking-effect step; the actual abstract enqueue update is `Sys_E2` / `U_E2`.

### `HWQ-TSQ/`

This directory contains the Isabelle/HOL development for the simulation and non-simulation results between TSQ and HWQ.

Its main files are:

- `TSQModel.thy`: core definitions for the time-stamped queue model;
- `SimLemmas.thy`: auxiliary lemmas used in the simulation proof;
- `SimProof.thy`: global step-simulation development, aligned with the HWQ `E1`-stutter / `E2`-effect convention;
- `TraceInv.thy`: trace invariants used by the simulation development;
- `TraceProof.thy`: the TSQ-to-HWQ simulation/refinement layer, including `HWQ_is_weakly_simulated_by_TSQ` and `Trace_Refinement`;
- `NotSimLemmas.thy`: auxiliary lemmas for the non-simulation argument;
- `NotSimProof.thy`: the opposite-direction non-simulation result, culminating in `TSQ_not_forward_simulated_by_HWQ_2proc`.

## Requirements

This artifact is intended for Isabelle2025-2 and uses `HOL-Library`.

No additional external dependencies are required beyond Isabelle2025-2.

## Usage

The Isabelle session defined in `ROOT` is `LinLattice`.

From the repository root, the full session can be checked with:

```bash
isabelle build -D . LinLattice
```

For interactive checking, open the repository as the `LinLattice` session in Isabelle/jEdit; imported theories are processed automatically by Isabelle/PIDE.

## Main mechanically checked results

The development contains theorem endpoints for the three paper-level relationships:

- HWQ is simulated by $\mathcal{U}_{Queue}$: `HWQ-U/HWQQueueProof.thy`;
- TSQ simulates HWQ / trace refinement: `HWQ-TSQ/TraceProof.thy`;
- TSQ is not forward simulated by HWQ in the two-process witness: `HWQ-TSQ/NotSimProof.thy`.

The `ROOT` session also includes the queue-specification, history-transfer, and $\mathcal{U}_{Queue}$-membership layers used by the revised HWQ-U development.

## Correspondence to the paper

- **$\mathcal{U}_{Queue}$ and the Herlihy-Wing queue case study:** mainly `HWQ-U/`.
- **Simulation from TSQ to HWQ:** mainly `HWQ-TSQ/SimLemmas.thy`, `HWQ-TSQ/SimProof.thy`, and `HWQ-TSQ/TraceProof.thy`.
- **Non-simulation in the opposite direction:** mainly `HWQ-TSQ/NotSimLemmas.thy` and `HWQ-TSQ/NotSimProof.thy`.

## Use of generative AI assistance

During the conceptualization and development of the formal proofs, the authors used the web interfaces of several large language models, including Gemini, ChatGPT, and DeepSeek, to brainstorm verification strategies, discuss proof organization, and explore possible tactical structures.

The authors retained full responsibility for all scientific claims, definitions, theorems, and proof scripts. All Isabelle/HOL proof scripts included in this artifact were reviewed by the authors and mechanically checked with Isabelle/HOL.
