# Physics in Lean 4

Formalization of a 1D tight-binding chain in Lean 4 using Mathlib, accompanying the seminar **"Introduction to Lean 4 for Physicists"** by Michał Pacholski.

## Overview

`TightBinding.lean` formalizes a quantum particle on an $N$-site periodic ring (`Fin N`) with onsite potential $\mu \in \mathbb{R}$ and nearest-neighbor hopping $t \in \mathbb{C}$[cite: 1]:
- **Hamiltonian & Hermiticity:** Constructs the $N \times N$ tight-binding matrix (`hamiltonian`) and proves it is Hermitian (`isHermitian_hamiltonian`)[cite: 1].
- **Bloch Eigenstates:** Defines normalized plane waves (`planeWave`) parameterized by $N$-th roots of unity (`rootsOfUnity N ℂ`) and proves the eigenvalue equation $H \psi_u = (\mu + t u^{-1} + t^* u) \psi_u$ (`isEigenvector_planeWave`)[cite: 1].
- **Complete Orthonormal Basis:** Proves orthonormality (`orthonormal_planeWaves`) via the geometric series formula and constructs a complete `OrthonormalBasis` of $\mathbb{C}^N$ (`planeWaveOrthonormalBasis`)[cite: 1].

## Quick Start

### 1. Install Lean 4 & VS Code Extension
Install [VS Code](https://code.visualstudio.com/) and the official **`lean4`** extension (`leanprover.lean4`), or install `elan` (the Lean version manager) directly:

```bash
curl [https://elan.lean-lang.org/elan-init.sh](https://elan.lean-lang.org/elan-init.sh) -sSf | sh

```

### 2. Clone the Repository & Fetch Mathlib Cache

Always download precompiled Mathlib binaries with `lake exe cache get` before building so you do not compile Mathlib from source:

```bash
git clone [https://github.com/mpacholski/physics_in_lean.git](https://github.com/mpacholski/physics_in_lean.git)
cd physics_in_lean
lake exe cache get
lake build

```

### 3. Explore Interactively

Open the `physics_in_lean` folder in VS Code (`code .`), open `TightBinding.lean`, and toggle the **Lean Infoview** (`Ctrl+Shift+Enter` / `Cmd+Shift+Enter`) to inspect the proof states step by step.
