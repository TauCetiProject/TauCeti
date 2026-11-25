/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Algebra.Order.Floor.Extended
import TauCeti.Data.EReal.Operations

/-!
# Topological pressure of maps

For a map `T : X → X` of a uniform space and a potential `φ : X → ℝ`, the topological pressure
`P(T, φ)` is

```text
P(T, φ) = ⨆ U ∈ 𝓤 X, limsup_{n → ∞} (1/n) log sup { ∑_{x ∈ s} exp (birkhoffSum T φ n x) |
                                                      s finite, IsDynNetIn T univ U n s }.
```

The inner supremum is `TauCeti.pressureNetSum T φ U n`, and the exponential growth rate of these
sums is `TauCeti.netPressureEntourage T φ U`. Pressure is valued in `EReal`, like Mathlib's
topological entropy `Dynamics.coverEntropy`, which it generalizes: the weights `exp (birkhoffSum T φ
n x)` are all `1` for `φ = 0`.

## Main definitions

* `TauCeti.pressureNetSum T φ U n` — the supremum over finite `(U, n)`-dynamical nets `s` of
  `∑ x ∈ s, exp (birkhoffSum T φ n x)`, in `ℝ≥0∞`.
* `TauCeti.netPressureEntourage T φ U` — the exponential growth rate (`limsup`) of
  `pressureNetSum T φ U n`.
* `TauCeti.topologicalPressure T φ` — the supremum over entourages of `netPressureEntourage`.

## Main results

* `TauCeti.topologicalPressure_zero` — `P(T, 0)` is the topological entropy `coverEntropy T univ`.
* `TauCeti.topologicalPressure_mono` — pressure is monotone in the potential.
* `TauCeti.topologicalPressure_add_const` — `P(T, φ + c) = P(T, φ) + c`.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Chapter 9: §9.1 defines the pressure through separated and spanning sets, and Theorem 9.7
  proves `P(T, 0) = h(T)`, monotonicity in the potential and `P(T, φ + c) = P(T, φ) + c`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped ENNReal Uniformity

variable {X : Type*} {T : X → X} {φ ψ : X → ℝ} {U : SetRel X X} {n : ℕ}

/-- The pressure sum at entourage `U` and time `n`: the supremum, over finite `(U, n)`-dynamical
nets `s` of `X`, of `∑ x ∈ s, exp (birkhoffSum T φ n x)`. -/
noncomputable def pressureNetSum (T : X → X) (φ : X → ℝ) (U : SetRel X X) (n : ℕ) : ℝ≥0∞ :=
  ⨆ (s : Finset X) (_ : IsDynNetIn T univ U n s),
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x))

/-- The pressure of a potential at the entourage `U`: the exponential growth rate (`limsup`) of the
pressure sums `pressureNetSum T φ U n`. -/
noncomputable def netPressureEntourage (T : X → X) (φ : X → ℝ) (U : SetRel X X) : EReal :=
  expGrowthSup (pressureNetSum T φ U)

/-- The topological pressure `P(T, φ)` of a map `T` and a potential `φ`: the supremum over
entourages `U` of the exponential growth rate of `pressureNetSum T φ U n`, the supremum over
finite `(U, n)`-dynamical nets of the sums of `exp (birkhoffSum T φ n x)`. -/
noncomputable def topologicalPressure [UniformSpace X] (T : X → X) (φ : X → ℝ) : EReal :=
  ⨆ U ∈ 𝓤 X, netPressureEntourage T φ U

/-- Each net sum is at most the pressure sum. -/
theorem _root_.Dynamics.IsDynNetIn.sum_le_pressureNetSum {s : Finset X}
    (hs : IsDynNetIn T univ U n s) :
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) ≤ pressureNetSum T φ U n :=
  le_iSup₂ (f := fun (s : Finset X) (_ : IsDynNetIn T univ U n s) ↦
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x))) s hs

/-- The pressure sums are antitone in the entourage. -/
theorem pressureNetSum_antitone (T : X → X) (φ : X → ℝ) (n : ℕ) :
    Antitone fun U : SetRel X X ↦ pressureNetSum T φ U n :=
  fun _ _ U_V ↦ biSup_mono fun _ h ↦ h.of_entourage_subset U_V

/-- The pressure at an entourage is antitone in the entourage. -/
theorem netPressureEntourage_antitone (T : X → X) (φ : X → ℝ) :
    Antitone (netPressureEntourage T φ) :=
  fun _ _ U_V ↦ expGrowthSup_monotone fun n ↦ pressureNetSum_antitone T φ n U_V

/-- The pressure at an entourage of the uniformity is at most the topological pressure. -/
theorem netPressureEntourage_le_topologicalPressure [UniformSpace X] (h : U ∈ 𝓤 X) :
    netPressureEntourage T φ U ≤ topologicalPressure T φ :=
  le_iSup₂ (f := fun U (_ : U ∈ 𝓤 X) ↦ netPressureEntourage T φ U) U h

/-- The topological pressure is at most `a` exactly when the pressure at every entourage of the
uniformity is. -/
theorem topologicalPressure_le_iff [UniformSpace X] {a : EReal} :
    topologicalPressure T φ ≤ a ↔ ∀ U ∈ 𝓤 X, netPressureEntourage T φ U ≤ a :=
  iSup₂_le_iff

/-- For the zero potential the pressure sum is the maximal cardinality `netMaxcard T univ U n` of a
`(U, n)`-dynamical net. -/
@[simp]
theorem pressureNetSum_zero (T : X → X) (U : SetRel X X) (n : ℕ) :
    pressureNetSum T 0 U n = netMaxcard T univ U n := by
  simp [pressureNetSum, netMaxcard, Pi.zero_def, ENat.toENNReal_iSup]

/-- For the zero potential the pressure at an entourage is Mathlib's net entropy. -/
@[simp]
theorem netPressureEntourage_zero (T : X → X) (U : SetRel X X) :
    netPressureEntourage T 0 U = netEntropyEntourage T univ U := by
  rw [netPressureEntourage, netEntropyEntourage]
  exact congrArg expGrowthSup (funext fun n ↦ pressureNetSum_zero T U n)

/-- The pressure of the zero potential is the topological entropy. -/
@[simp]
theorem topologicalPressure_zero [UniformSpace X] (T : X → X) :
    topologicalPressure T 0 = coverEntropy T univ := by
  simp only [topologicalPressure, netPressureEntourage_zero,
    coverEntropy_eq_iSup_netEntropyEntourage]

/-- The pressure sums are monotone in the potential. -/
theorem pressureNetSum_mono (h : φ ≤ ψ) (U : SetRel X X) (n : ℕ) :
    pressureNetSum T φ U n ≤ pressureNetSum T ψ U n := by
  refine iSup₂_mono fun s _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  exact Finset.sum_le_sum fun k _ ↦ h _

/-- Pressure is monotone in the potential. -/
theorem topologicalPressure_mono [UniformSpace X] (h : φ ≤ ψ) :
    topologicalPressure T φ ≤ topologicalPressure T ψ :=
  iSup₂_mono fun U _ ↦ expGrowthSup_monotone fun n ↦ pressureNetSum_mono h U n

/-- Adding a constant `c` to the potential multiplies the pressure sum at time `n` by
`exp (n * c)`. -/
theorem pressureNetSum_add_const (T : X → X) (φ : X → ℝ) (c : ℝ) (U : SetRel X X) (n : ℕ) :
    pressureNetSum T (fun x ↦ φ x + c) U n =
      ENNReal.ofReal (Real.exp (n * c)) * pressureNetSum T φ U n := by
  rw [← Pi.add_def φ fun _ ↦ c]
  simp only [pressureNetSum, ENNReal.mul_iSup, Finset.mul_sum, birkhoffSum_add_apply,
    birkhoffSum_const, Pi.smul_apply, nsmul_eq_mul, Real.exp_add]
  refine iSup_congr fun s ↦ iSup_congr fun _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  rw [mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Adding a constant `c` to the potential adds `c` to the pressure at every entourage. -/
theorem netPressureEntourage_add_const (T : X → X) (φ : X → ℝ) (c : ℝ) (U : SetRel X X) :
    netPressureEntourage T (fun x ↦ φ x + c) U = netPressureEntourage T φ U + c := by
  have hfn : (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (n * c))) =
      fun n : ℕ ↦ EReal.exp ((c : EReal) * n) := funext fun n ↦ by
    rw [show ((c : EReal) * (n : EReal)) = ((n * c : ℝ) : EReal) by norm_cast; rw [mul_comm],
      EReal.exp_coe]
  have hexp : expGrowthSup (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (n * c))) = c :=
    hfn ▸ expGrowthSup_exp
  have hexp' : expGrowthInf (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (n * c))) = c :=
    hfn ▸ expGrowthInf_exp
  have hfun : pressureNetSum T (fun x ↦ φ x + c) U =
      (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (n * c))) * pressureNetSum T φ U :=
    funext fun n ↦ pressureNetSum_add_const T φ c U n
  rw [netPressureEntourage, netPressureEntourage, hfun, add_comm]
  refine le_antisymm ?_ ?_
  · refine (expGrowthSup_mul_le ?_ ?_).trans_eq (by rw [hexp]) <;>
      simp [hexp, EReal.coe_ne_top, EReal.coe_ne_bot]
  · exact (le_expGrowthSup_mul').trans_eq' (by rw [hexp'])

/-- Adding a constant `c` to the potential adds `c` to the pressure. -/
theorem topologicalPressure_add_const [UniformSpace X] (T : X → X) (φ : X → ℝ) (c : ℝ) :
    topologicalPressure T (fun x ↦ φ x + c) = topologicalPressure T φ + c := by
  simp only [topologicalPressure, netPressureEntourage_add_const, EReal.iSup_add_coe]

end TauCeti
