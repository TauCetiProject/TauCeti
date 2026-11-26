/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Algebra.Order.Floor.Extended
import TauCeti.Analysis.Asymptotics.ExpGrowth
import TauCeti.Data.EReal.Quantale

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
* `TauCeti.topologicalPressure_id` — for the identity of a nonempty finite space,
  `P(id, φ) = max_x φ x`.

The net-based definitions and their antitonicity lemmas are modelled on `netMaxcard` and
`netEntropyEntourage` in Mathlib's `Mathlib/Dynamics/TopologicalEntropy/NetEntropy.lean`
(D. Thomine, P. Monticone).

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

/-- The pressure sum is at most `a` exactly when every net sum is. -/
theorem pressureNetSum_le_iff {a : ℝ≥0∞} :
    pressureNetSum T φ U n ≤ a ↔ ∀ s : Finset X, IsDynNetIn T univ U n s →
      ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) ≤ a :=
  iSup₂_le_iff

/-- The pressure sum is the supremum, over finite `(U, n)`-dynamical nets `s`, of the sums of
`exp (birkhoffSum T φ n x)` over `s`. -/
theorem pressureNetSum_def :
    pressureNetSum T φ U n = ⨆ (s : Finset X) (_ : IsDynNetIn T univ U n s),
      ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) :=
  (rfl)

/-- The pressure at an entourage is the upper exponential growth rate of the pressure sums. -/
theorem netPressureEntourage_def :
    netPressureEntourage T φ U = expGrowthSup (pressureNetSum T φ U) :=
  (rfl)

/-- The topological pressure is the supremum over entourages of the uniformity of the pressure at
each entourage. -/
theorem topologicalPressure_def [UniformSpace X] :
    topologicalPressure T φ = ⨆ U ∈ 𝓤 X, netPressureEntourage T φ U :=
  (rfl)

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
  have hfun : pressureNetSum T (fun x ↦ φ x + c) U =
      fun n : ℕ ↦ EReal.exp (c * n) * pressureNetSum T φ U n := funext fun n ↦ by
    simp [pressureNetSum_add_const, ← EReal.exp_coe, mul_comm]
  rw [netPressureEntourage_def, netPressureEntourage_def, hfun, expGrowthSup_exp_mul, add_comm]

/-- Adding a constant `c` to the potential adds `c` to the pressure. -/
theorem topologicalPressure_add_const [UniformSpace X] (T : X → X) (φ : X → ℝ) (c : ℝ) :
    topologicalPressure T (fun x ↦ φ x + c) = topologicalPressure T φ + c := by
  simp only [topologicalPressure, netPressureEntourage_add_const, iSup_subtype',
    AddQuantale.iSup_add_distrib]

/-- The pressure of the identity of a nonempty finite uniform space is the maximum of the
potential: `P(id, φ) = max_x φ x`. -/
@[simp]
theorem topologicalPressure_id [UniformSpace X] [Fintype X] [Nonempty X] (φ : X → ℝ) :
    topologicalPressure id φ = (Finset.univ.sup' Finset.univ_nonempty φ : ℝ) := by
  set M := Finset.univ.sup' Finset.univ_nonempty φ with hM
  have hexp : ∀ n x, ENNReal.ofReal (Real.exp (birkhoffSum id φ n x)) = EReal.exp (φ x * n) :=
    fun n x ↦ by
      rw [birkhoffSum_apply_of_comp_eq (f := id) (φ := φ) rfl, nsmul_eq_mul, mul_comm]
      simp [← EReal.exp_coe]
  apply le_antisymm
  · -- Every net has at most `card X` points, each of weight at most `exp (n * M)`.
    rw [topologicalPressure_le_iff]
    intro U _
    rw [netPressureEntourage_def]
    refine (expGrowthSup_le_of_eventually_le (b := Fintype.card X) (ENNReal.natCast_ne_top _)
      (v := fun n : ℕ ↦ EReal.exp (M * n)) (Eventually.of_forall fun n ↦ ?_)).trans_eq
      (expGrowthSup_exp (a := M))
    rw [pressureNetSum_le_iff]
    intro s _
    calc ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum id φ n x))
        ≤ ∑ _x ∈ s, EReal.exp (M * n) := Finset.sum_le_sum fun x _ ↦ by
          rw [hexp]
          exact EReal.exp_monotone (by gcongr; exact Finset.le_sup' φ (Finset.mem_univ x))
      _ = s.card * EReal.exp (M * n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card X * EReal.exp (M * n) := by
          gcongr
          exact_mod_cast s.card_le_univ
  · -- A singleton net at a maximizer gives the lower bound.
    obtain ⟨x₀, -, hx₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty φ
    refine le_trans ?_ (netPressureEntourage_le_topologicalPressure (U := univ)
      Filter.univ_mem)
    rw [netPressureEntourage_def, hM, hx₀]
    refine Frequently.le_expGrowthSup (Eventually.of_forall fun n ↦ ?_).frequently
    have hnet : IsDynNetIn (id : X → X) univ univ n ({x₀} : Finset X) :=
      ⟨subset_univ _, by simp⟩
    simpa only [Finset.sum_singleton, hexp] using hnet.sum_le_pressureNetSum (φ := φ)

end TauCeti
