/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Algebra.Order.Floor.Extended

/-!
# Topological pressure of maps

For a map `T : X → X` of a uniform space and a potential `φ : X → ℝ`, the topological pressure
`P(T, φ)` is

```text
P(T, φ) = ⨆ U ∈ 𝓤 X, limsup_{n → ∞} (1/n) log sup { ∑_{x ∈ s} exp (birkhoffSum T φ n x) |
                                                      s finite, IsDynNetIn T univ U n s }.
```

The inner supremum is `TauCeti.pressureNetSum T φ U n`, and the exponential growth rate of these
sums is `TauCeti.pressureNetEntourage T φ U`. Pressure is valued in `EReal`, like Mathlib's
topological entropy `Dynamics.coverEntropy`, which it generalizes: the weights `exp (birkhoffSum T φ
n x)` are all `1` for `φ = 0`.

## Main definitions

* `TauCeti.pressureNetSum T φ U n` — the supremum over finite `(U, n)`-dynamical nets `s` of
  `∑ x ∈ s, exp (birkhoffSum T φ n x)`, in `ℝ≥0∞`.
* `TauCeti.pressureNetEntourage T φ U` — the exponential growth rate (`limsup`) of
  `pressureNetSum T φ U n`.
* `TauCeti.topologicalPressure T φ` — the supremum over entourages of `pressureNetEntourage`.

## Main results

* `TauCeti.topologicalPressure_zero` — `P(T, 0)` is the topological entropy `coverEntropy T univ`.
* `TauCeti.topologicalPressure_mono` — pressure is monotone in the potential.
* `TauCeti.topologicalPressure_add_const` — `P(T, φ + c) = P(T, φ) + c`.
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
noncomputable def pressureNetEntourage (T : X → X) (φ : X → ℝ) (U : SetRel X X) : EReal :=
  expGrowthSup (pressureNetSum T φ U)

/-- The topological pressure `P(T, φ)` of a map `T` and a potential `φ`: the supremum over
entourages `U` of the exponential growth rate of the sums of `exp (birkhoffSum T φ n x)` over
maximal `(U, n)`-dynamical nets. -/
noncomputable def topologicalPressure [UniformSpace X] (T : X → X) (φ : X → ℝ) : EReal :=
  ⨆ U ∈ 𝓤 X, pressureNetEntourage T φ U

/-- Each net sum is at most the pressure sum. -/
theorem IsDynNetIn.sum_le_pressureNetSum {s : Finset X} (hs : IsDynNetIn T univ U n s) :
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) ≤ pressureNetSum T φ U n :=
  le_iSup₂ (f := fun (s : Finset X) (_ : IsDynNetIn T univ U n s) ↦
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x))) s hs

private lemma birkhoffSum_const_apply (T : X → X) (c : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (fun _ ↦ c) n x = n * c := by
  simp [birkhoffSum]

/-- For the zero potential the pressure sum counts the points of a maximal dynamical net. -/
theorem pressureNetSum_zero (T : X → X) (U : SetRel X X) (n : ℕ) :
    pressureNetSum T 0 U n = netMaxcard T univ U n := by
  have h : (0 : X → ℝ) = fun _ ↦ 0 := rfl
  simp [pressureNetSum, netMaxcard, h, birkhoffSum_const_apply, ENat.toENNReal_iSup]

/-- For the zero potential the pressure at an entourage is Mathlib's net entropy. -/
theorem pressureNetEntourage_zero (T : X → X) (U : SetRel X X) :
    pressureNetEntourage T 0 U = netEntropyEntourage T univ U := by
  rw [pressureNetEntourage, netEntropyEntourage]
  exact congrArg expGrowthSup (funext fun n ↦ pressureNetSum_zero T U n)

/-- The pressure of the zero potential is the topological entropy. -/
theorem topologicalPressure_zero [UniformSpace X] (T : X → X) :
    topologicalPressure T 0 = coverEntropy T univ := by
  simp only [topologicalPressure, pressureNetEntourage_zero,
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
  have h : (fun x ↦ φ x + c) = φ + fun _ ↦ c := rfl
  simp only [pressureNetSum, ENNReal.mul_iSup, Finset.mul_sum, h, birkhoffSum_add_apply,
    birkhoffSum_const_apply, Real.exp_add]
  refine iSup_congr fun s ↦ iSup_congr fun _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  rw [mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Adding a constant `c` to the potential adds `c` to the pressure at every entourage. -/
theorem pressureNetEntourage_add_const (T : X → X) (φ : X → ℝ) (c : ℝ) (U : SetRel X X) :
    pressureNetEntourage T (fun x ↦ φ x + c) U = pressureNetEntourage T φ U + c := by
  have hexp : expGrowthSup (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (n * c))) = c := by
    have h := expGrowthSup_exp (a := (c : EReal))
    refine Eq.trans (congrArg expGrowthSup (funext fun n ↦ ?_)) h
    rw [show ((c : EReal) * (n : EReal)) = ((n * c : ℝ) : EReal) by norm_cast; rw [mul_comm],
      EReal.exp_coe]
  have hexp' : expGrowthInf (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (n * c))) = c := by
    have h := expGrowthInf_exp (a := (c : EReal))
    refine Eq.trans (congrArg expGrowthInf (funext fun n ↦ ?_)) h
    rw [show ((c : EReal) * (n : EReal)) = ((n * c : ℝ) : EReal) by norm_cast; rw [mul_comm],
      EReal.exp_coe]
  have hfun : pressureNetSum T (fun x ↦ φ x + c) U =
      (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (n * c))) * pressureNetSum T φ U :=
    funext fun n ↦ pressureNetSum_add_const T φ c U n
  rw [pressureNetEntourage, pressureNetEntourage, hfun, add_comm]
  refine le_antisymm ?_ ?_
  · refine (expGrowthSup_mul_le ?_ ?_).trans_eq (by rw [hexp]) <;>
      simp [hexp, EReal.coe_ne_top, EReal.coe_ne_bot]
  · exact (le_expGrowthSup_mul').trans_eq' (by rw [hexp'])

/-- Adding a constant `c` to the potential adds `c` to the pressure. -/
theorem topologicalPressure_add_const [UniformSpace X] (T : X → X) (φ : X → ℝ) (c : ℝ) :
    topologicalPressure T (fun x ↦ φ x + c) = topologicalPressure T φ + c := by
  let e : EReal ≃o EReal :=
    { toFun x := x + c
      invFun x := x - c
      left_inv _ := EReal.add_sub_cancel_right
      right_inv _ := EReal.sub_add_cancel
      map_rel_iff' {x y} := by
        refine ⟨fun h ↦ ?_, fun h ↦ add_le_add_left h _⟩
        simpa [EReal.add_sub_cancel_right] using EReal.sub_le_sub h (le_refl (c : EReal)) }
  simp only [topologicalPressure, pressureNetEntourage_add_const]
  exact (e.map_iSup₂ _).symm

end TauCeti
