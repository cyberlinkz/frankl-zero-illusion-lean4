# Frankl Lab: Clean Release & Academic Preprint Package

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.8.0-blue)](https://leanprover.github.io/)
[![Zero Sorry](https://img.shields.io/badge/sorry-0-brightgreen)](lean/)
[![Pytest](https://img.shields.io/badge/tests-187%20passed-brightgreen)](python/)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

Official publication release package accompanying the academic preprint:
> **"Quotient-Fiber Stratification, Universal Top-Fiber Absorption, and Machine-Verified Structural Resolutions for the Union-Closed Sets Conjecture in Lean 4"**  
> *Ahmad Hasanov (Frankl Lab, October 2026)*

---

## 1. Directory Structure

```text
arxiv_release/
├── lean/                               # Standalone Lean 4.8.0 package (0 sorry)
│   ├── lakefile.lean                  # Canonical Lake configuration
│   ├── lean-toolchain                 # leanprover/lean4:v4.8.0
│   ├── Frankl_Concrete_Bridge.lean    # Finite-list bridge & Master Resolution
│   ├── Frankl_Poonen_Breaker.lean     # Quotient-fiber stratification & pincer trap
│   ├── Frankl_Universal_Certificates.lean # Unconditional non-biclosed certificates
│   ├── Frankl_Biclosed.lean           # Unconditional biclosed Frankl theorem
│   └── Frankl_a018.lean               # Algebraic projection-balance identities
├── python/                             # Python verification & solvers (187 tests)
│   ├── poonen_obstruction_breaker.py  # Quotient-complement transfer & k=3 analyzer
│   ├── universal_frankl_resolver.py   # Universal 4-tier certificate solver
│   ├── test_poonen_obstruction_breaker.py # 169 unit & property tests
│   ├── test_universal_frankl_resolver.py  # 18 property tests
│   └── union_closed_search.py         # Bitmask union-closed generator
├── paper/                              # Academic preprint source
│   └── main.tex                       # Complete LaTeX article
└── README.md                           # This reproduction guide & theorem mapping
```

---

## 2. Quick Reproduction Guide

### A. Lean 4 Formalization (`arxiv_release/lean/`)

The Lean formalization is completely self-contained with **zero external dependencies** (no Mathlib required; uses pure core Lean 4 tactics such as `omega`).

```bash
cd arxiv_release/lean

# Build all libraries
lake build

# Output:
# Build completed successfully (0 errors, 0 warnings, 0 sorry)
```

#### Axiom Audit
To verify that the proofs rely strictly on the standard foundation of mathematics without smuggled axioms or `sorryAx`, run:

```bash
lake env lean --run - << 'EOF'
import Frankl_Concrete_Bridge

#print axioms FranklConcreteBridge.concrete_frankl_master_structural_resolution
#print axioms FranklConcreteBridge.concrete_k3_slice_deficit_le_one
#print axioms FranklConcreteBridge.concrete_k3_slice_deficit_one_forces_nine_mass
#print axioms FranklConcreteBridge.concrete_exact_secant_factorization_identity
#print axioms FranklConcreteBridge.concrete_dense_quotient_carrier_bound
EOF
```
**Expected Output:** Each theorem depends strictly on:
```text
[propext, Classical.choice, Quot.sound]
```
No `sorryAx` appears anywhere in the codebase.

---

### B. Python Verification & Algorithmic Solvers (`arxiv_release/python/`)

Requires Python 3.9+ and `pytest`.

```bash
cd arxiv_release/python

# Run complete test suite (187 tests)
pytest -q

# Expected Output:
# ........................................................................ [ 38%]
# ........................................................................ [ 77%]
# ...........................................                              [100%]
# 187 passed in ~4.3s
```

#### Audit the $k=3$ Slice Deficit Cap & 9x Mass Multiplier
Verifies all 90 union-closed families on $[3]$:
```bash
python poonen_obstruction_breaker.py --verify-k3-slice-deficit
```
**Output Summary:**
```text
==============================================================================
K=3 INTRA-FIBER SLICE DEFICIT CAP (LE 1) & 9X MASS MULTIPLIER AUDIT
==============================================================================
  Total Union-Closed Families on [3]: 90
  Singletons <= Pairs + 1: True
  Sub-3 Deficit Negativity (s0=0 => delta <= -2): True
  Deficit Cap (delta <= 1): True
  Delta = 1 Forces 9x Mass: True
  Delta Distribution: {-3: 18, 0: 17, -2: 12, -4: 15, 1: 6, -1: 15, -5: 6, -6: 1}
  All Verified: True
==============================================================================
```

#### Run Universal 4-Tier Certificate Solver
```bash
python universal_frankl_resolver.py
```
**Output:** Verifies 1000/1000 adversarial non-biclosed families with exact certificates.

---

### C. LaTeX Paper Compilation (`arxiv_release/paper/`)

```bash
cd arxiv_release/paper
pdflatex main.tex
pdflatex main.tex   # second pass for cross-references
```

---

## 3. Machine-Verified Theorem Mapping

The following table provides the exact line-by-line mapping between mathematical theorems in `paper/main.tex` and machine-checked Lean 4 declarations in `lean/`.

| Paper Theorem | Mathematical Content | Lean 4 Identifier | Source File | Line | Axioms |
|:---|:---|:---|:---|:---:|:---:|
| **Theorem 2.3** | Quotient Lattice Union-Closure | `quotient_union_closed` | `Frankl_Poonen_Breaker.lean` | L161 | `propext, Classical.choice, Quot.sound` |
| **Theorem 2.4** | Universal Top-Slice Embedding | `top_slice_in_family` | `Frankl_Poonen_Breaker.lean` | L110 | `propext, Classical.choice, Quot.sound` |
| **Theorem 2.5** | Empty-Fiber Uniqueness ($m(\emptyset)=1$) | `concrete_top_fiber_slice_k_weight` | `Frankl_Concrete_Bridge.lean` | L1788 | `propext, Classical.choice, Quot.sound` |
| **Theorem 3.1** | Refined Fiber-Base Balance | `concrete_refined_fiber_base_balance` | `Frankl_Concrete_Bridge.lean` | L1791 | `propext, Classical.choice, Quot.sound` |
| **Theorem 3.2** | Dense Regime Resolution ($c \le k$) | `concrete_dense_quotient_carrier_bound` | `Frankl_Concrete_Bridge.lean` | L1822 | `propext, Classical.choice, Quot.sound` |
| **Theorem 3.3** | Volume-Bonus Extended Dense Witness | `concrete_volume_bonus_extended_dense_witness` | `Frankl_Concrete_Bridge.lean` | L1880 | `propext, Classical.choice, Quot.sound` |
| **Theorem 3.4** | Rényi-2 Quotient Mass Collision Law | `concrete_quotient_mass_collision_lower_bound` | `Frankl_Concrete_Bridge.lean` | L1843 | `propext, Classical.choice, Quot.sound` |
| **Theorem 4.2** | Sub-Critical Fiber Positivity ($2q \le k$) | `concrete_subcritical_fiber_positivity_strict` | `Frankl_Concrete_Bridge.lean` | L1853 | `propext, Classical.choice, Quot.sound` |
| **Theorem 4.3** | Distinct Slice Weight Bound & Cap | `concrete_refined_deficit_cap` | `Frankl_Concrete_Bridge.lean` | L1909 | `propext, Classical.choice, Quot.sound` |
| **Theorem 4.4** | Supercritical Fiber Mass Multiplier | `concrete_supercritical_fiber_mass_multiplier` | `Frankl_Concrete_Bridge.lean` | L1912 | `propext` |
| **Theorem 4.5 (1)** | $k=3$: $s_1 \le s_2 + 1$ Singletons Bound | `concrete_k3_singletons_le_pairs_plus_one` | `Frankl_Concrete_Bridge.lean` | L1928 | `propext, Classical.choice, Quot.sound` |
| **Theorem 4.5 (3)** | $k=3$: Sub-3 Fiber Deficit Negativity | `concrete_k3_slice_deficit_sub_three_negative` | `Frankl_Concrete_Bridge.lean` | L1931 | `propext, Classical.choice, Quot.sound` |
| **Theorem 4.5 (4)** | $k=3$: Universal Slice Deficit Cap ($\le 1$) | `concrete_k3_slice_deficit_le_one` | `Frankl_Concrete_Bridge.lean` | L1934 | `propext, Classical.choice, Quot.sound` |
| **Theorem 4.5 (5)** | $k=3$: 9x Mass-Deficit Multiplier Surge | `concrete_k3_slice_deficit_one_forces_nine_mass` | `Frankl_Concrete_Bridge.lean` | L1937 | `propext, Classical.choice, Quot.sound` |
| **Theorem 5.1** | Exact Secant Factorization Identity | `concrete_exact_secant_factorization_identity` | `Frankl_Concrete_Bridge.lean` | L1703 | `propext, Classical.choice, Quot.sound` |
| **Theorem 5.2** | Dispersion-Entropy Pincer Trap | `concrete_pincer_trap_adversary_concentration_forced` | `Frankl_Concrete_Bridge.lean` | L1654 | `propext, Classical.choice, Quot.sound` |
| **Theorem 6.1** | **Unified Master Structural Resolution** | `concrete_frankl_master_structural_resolution` | `Frankl_Concrete_Bridge.lean` | L1944 | `propext, Classical.choice, Quot.sound` |

---

## 4. Scientific Integrity & Boundary Characterization

Under the **Zero-Illusion Prover Protocol**, we explicitly differentiate machine-verified truth from open frontiers:

### Formally Verified Regimes (100% Machine-Checked, 0 Sorry)
1. **Singleton ($k=1$) & Doubleton ($k=2$)**: Fully resolved unconditionally.
2. **Biclosed Families**: Fully resolved unconditionally.
3. **Local Minimal Set Success**: Fully resolved whenever $2W \ge k|\mathcal{F}|$.
4. **Dense Regime ($n \le 2k \iff c \le k$)**: Fully resolved unconditionally via refined fiber-base balance.
5. **Volume-Bonus Extended Dense Regime ($(c-k)|\mathcal{F}| \le 2 \sum_Q |Q|$)**: Fully resolved unconditionally.
6. **$k=3$ Poonen Obstruction Elimination**: The slice deficit cap $\delta(Q) \le 1$ and $9\times$ mass surge $m(Q)|Q| \ge 9 \delta(Q)$ are verified across all 90 union-closed families on $[3]$.
7. **Dispersion-Entropy Compression**: The exact cubic secant identity and pincer trap effective dimension bounds are verified.

### The Remaining Open Frontier ($k \ge 4, n \gg 2k$)
Frankl's conjecture remains formally open in the following precisely circumscribed regime:
$$\boxed{k \ge 4, \quad n \gg 2k, \quad 2 W < k |\mathcal{F}|, \quad \text{and} \quad \sum_{Q \in \mathcal{Q}} |Q| < \frac{(c - k)|\mathcal{F}|}{2}}.$$
In this regime, the minimal set size is at least 4, the universe is much larger than $2k$, local averaging fails strictly on $A_{\min}$, and the total quotient volume is small, so that single-fiber bounds alone do not automatically force global carrier frequencies above $1/2$.
