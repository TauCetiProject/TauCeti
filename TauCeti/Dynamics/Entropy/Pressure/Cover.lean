/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
public import TauCeti.Dynamics.Entropy.Pressure
import Mathlib.Algebra.Order.Floor.Extended
import TauCeti.Analysis.Asymptotics.ExpGrowth
import TauCeti.Data.EReal.Quantale
import TauCeti.Dynamics.TopologicalEntropy.NetCover

/-!
# The spanning-set form of topological pressure

`TauCeti.topologicalPressure T φ` is defined through dynamical nets (separated sets). This file
defines the spanning-set version, with infima over dynamical covers in place of suprema over nets,

```text
P_cover(T, φ) = ⨆ U ∈ 𝓤 X, limsup_{n → ∞} (1/n) log inf { ∑_{x ∈ s} exp (birkhoffSum T φ n x) |
                                                      s finite, IsDynCoverOf T univ U n s },
```

and proves that the two agree for a uniformly continuous map `T` and a uniformly continuous
potential `φ` on a compact uniform space (`TauCeti.coverPressure_eq_topologicalPressure`).

* A net of maximal cardinality for `U` is a dynamical cover for `U ○ U`
  (`Dynamics.IsDynNetIn.isDynCoverOf_comp`, the argument of Mathlib's
  `Dynamics.coverMincard_le_netMaxcard`), so the cover sum for `U ○ U` is at most the net sum for
  `U` (`TauCeti.pressureCoverSum_comp_le_pressureNetSum`).
* If `V ⊆ U` and `φ` varies by at most `δ` across `V`, sending each point of a `(U, n)`-net to a
  point of a `(V, n)`-cover that shadows it is injective, and the Birkhoff sums at the two points
  differ by at most `n δ`, so the net sum for `U` is at most `exp (n δ)` times the cover sum for
  `V` (`TauCeti.pressureNetSum_le_pressureCoverSum_add_const`). The injection is the argument of
  Mathlib's `Dynamics.IsDynNetIn.card_le_card_of_isDynCoverOf`. Letting `δ → 0` uses uniform
  continuity of `φ`.

## Main definitions

* `TauCeti.pressureCoverSum T φ U n` — the infimum over finite `(U, n)`-dynamical covers `s` of
  `X` of `∑ x ∈ s, exp (birkhoffSum T φ n x)`, in `ℝ≥0∞`.
* `TauCeti.coverPressureEntourage T φ U` — the exponential growth rate (`limsup`) of these sums.
* `TauCeti.coverPressure T φ` — the supremum over entourages of `coverPressureEntourage`.

## Main results

* `TauCeti.coverPressure_le_topologicalPressure`: `P_cover(T, φ) ≤ P(T, φ)` for uniformly
  continuous `T` on a compact space.
* `TauCeti.topologicalPressure_le_coverPressure`: `P(T, φ) ≤ P_cover(T, φ)` for uniformly
  continuous `φ`.
* `TauCeti.coverPressure_eq_topologicalPressure`: the two agree.
* `TauCeti.coverPressure_zero`: for the zero potential the spanning form is Mathlib's
  `Dynamics.coverEntropy`.
* `TauCeti.coverPressure_mono`, `TauCeti.coverPressure_add_const`: the spanning form is monotone
  in the potential, and adding a constant to the potential adds it to the spanning form.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Chapter 9: §9.1 defines the pressure through separated and spanning sets.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped ENNReal Uniformity SetRel

variable {X : Type*} {T : X → X} {φ ψ : X → ℝ} {U V : SetRel X X} {n : ℕ}

/-- The spanning pressure sum at entourage `U` and time `n`: the infimum, over finite
`(U, n)`-dynamical covers `s` of `X`, of `∑ x ∈ s, exp (birkhoffSum T φ n x)`. -/
noncomputable def pressureCoverSum (T : X → X) (φ : X → ℝ) (U : SetRel X X) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (s : Finset X) (_ : IsDynCoverOf T univ U n s),
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x))

/-- The spanning pressure of a potential at the entourage `U`: the exponential growth rate
(`limsup`) of the spanning pressure sums. -/
noncomputable def coverPressureEntourage (T : X → X) (φ : X → ℝ) (U : SetRel X X) : EReal :=
  expGrowthSup (pressureCoverSum T φ U)

/-- The spanning-set form of the topological pressure: the supremum over entourages of the
uniformity of `coverPressureEntourage`. -/
noncomputable def coverPressure [UniformSpace X] (T : X → X) (φ : X → ℝ) : EReal :=
  ⨆ U ∈ 𝓤 X, coverPressureEntourage T φ U

/-- The spanning pressure sum is at most the sum over any finite dynamical cover. -/
theorem _root_.Dynamics.IsDynCoverOf.pressureCoverSum_le {s : Finset X}
    (hs : IsDynCoverOf T univ U n s) :
    pressureCoverSum T φ U n ≤ ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) :=
  iInf₂_le (f := fun (s : Finset X) (_ : IsDynCoverOf T univ U n s) ↦
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x))) s hs

/-- The spanning pressure sum is at least `a` exactly when every cover sum is. -/
theorem le_pressureCoverSum_iff {a : ℝ≥0∞} :
    a ≤ pressureCoverSum T φ U n ↔ ∀ s : Finset X, IsDynCoverOf T univ U n s →
      a ≤ ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) :=
  le_iInf₂_iff

theorem pressureCoverSum_def :
    pressureCoverSum T φ U n = ⨅ (s : Finset X) (_ : IsDynCoverOf T univ U n s),
      ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) :=
  (rfl)

theorem coverPressureEntourage_def :
    coverPressureEntourage T φ U = expGrowthSup (pressureCoverSum T φ U) :=
  (rfl)

theorem coverPressure_def [UniformSpace X] :
    coverPressure T φ = ⨆ U ∈ 𝓤 X, coverPressureEntourage T φ U :=
  (rfl)

/-- The spanning pressure sums are antitone in the entourage. -/
theorem pressureCoverSum_antitone (T : X → X) (φ : X → ℝ) (n : ℕ) :
    Antitone fun U : SetRel X X ↦ pressureCoverSum T φ U n :=
  fun _ _ U_V ↦ biInf_mono fun _ h ↦ h.of_entourage_subset U_V

/-- The spanning pressure at an entourage is antitone in the entourage. -/
theorem coverPressureEntourage_antitone (T : X → X) (φ : X → ℝ) :
    Antitone (coverPressureEntourage T φ) :=
  fun _ _ U_V ↦ expGrowthSup_monotone fun n ↦ pressureCoverSum_antitone T φ n U_V

/-- The spanning pressure at an entourage of the uniformity is at most the spanning pressure. -/
theorem coverPressureEntourage_le_coverPressure [UniformSpace X] (h : U ∈ 𝓤 X) :
    coverPressureEntourage T φ U ≤ coverPressure T φ :=
  le_iSup₂ (f := fun U (_ : U ∈ 𝓤 X) ↦ coverPressureEntourage T φ U) U h

/-- The spanning pressure is at most `a` exactly when the spanning pressure at every entourage of
the uniformity is. -/
theorem coverPressure_le_iff [UniformSpace X] {a : EReal} :
    coverPressure T φ ≤ a ↔ ∀ U ∈ 𝓤 X, coverPressureEntourage T φ U ≤ a :=
  iSup₂_le_iff

/-- For the zero potential the spanning pressure sum is the minimal cardinality
`coverMincard T univ U n` of a `(U, n)`-dynamical cover. -/
@[simp]
theorem pressureCoverSum_zero (T : X → X) (U : SetRel X X) (n : ℕ) :
    pressureCoverSum T 0 U n = coverMincard T univ U n := by
  simp [pressureCoverSum, coverMincard, Pi.zero_def, ENat.toENNReal_iInf]

/-- For the zero potential the spanning pressure at an entourage is Mathlib's cover entropy. -/
@[simp]
theorem coverPressureEntourage_zero (T : X → X) (U : SetRel X X) :
    coverPressureEntourage T 0 U = coverEntropyEntourage T univ U :=
  congrArg expGrowthSup (funext (pressureCoverSum_zero T U))

/-- For the zero potential the spanning pressure is Mathlib's topological entropy. -/
@[simp]
theorem coverPressure_zero [UniformSpace X] (T : X → X) :
    coverPressure T 0 = coverEntropy T univ := by
  simp only [coverPressure, coverPressureEntourage_zero, coverEntropy]

/-- The spanning pressure sums are monotone in the potential. -/
theorem pressureCoverSum_mono (h : φ ≤ ψ) (U : SetRel X X) (n : ℕ) :
    pressureCoverSum T φ U n ≤ pressureCoverSum T ψ U n := by
  refine iInf₂_mono fun s _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  exact Finset.sum_le_sum fun k _ ↦ h _

/-- The spanning pressure is monotone in the potential. -/
theorem coverPressure_mono [UniformSpace X] (h : φ ≤ ψ) :
    coverPressure T φ ≤ coverPressure T ψ :=
  iSup₂_mono fun U _ ↦ expGrowthSup_monotone fun n ↦ pressureCoverSum_mono h U n

/-- Adding a constant `c` to the potential multiplies the spanning pressure sum at time `n` by
`exp (n * c)`. -/
theorem pressureCoverSum_add_const (T : X → X) (φ : X → ℝ) (c : ℝ) (U : SetRel X X) (n : ℕ) :
    pressureCoverSum T (fun x ↦ φ x + c) U n =
      ENNReal.ofReal (Real.exp (n * c)) * pressureCoverSum T φ U n := by
  have h0 : ENNReal.ofReal (Real.exp (n * c)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  rw [← Pi.add_def φ fun _ ↦ c]
  simp only [pressureCoverSum, ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top, Finset.mul_sum,
    birkhoffSum_add_apply, birkhoffSum_const, Pi.smul_apply, nsmul_eq_mul, Real.exp_add]
  refine iInf_congr fun s ↦ iInf_congr fun _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  rw [mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Adding a constant `c` to the potential multiplies the spanning pressure sum at time `n` by
`EReal.exp (c * n)`: the form of `pressureCoverSum_add_const` used with growth rates. -/
theorem pressureCoverSum_add_const_eq_exp_mul (T : X → X) (φ : X → ℝ) (c : ℝ) (U : SetRel X X)
    (n : ℕ) :
    pressureCoverSum T (fun x ↦ φ x + c) U n = EReal.exp (c * n) * pressureCoverSum T φ U n := by
  simp [pressureCoverSum_add_const, ← EReal.exp_coe, mul_comm]

/-- Adding a constant `c` to the potential adds `c` to the spanning pressure at every
entourage. -/
theorem coverPressureEntourage_add_const (T : X → X) (φ : X → ℝ) (c : ℝ) (U : SetRel X X) :
    coverPressureEntourage T (fun x ↦ φ x + c) U = coverPressureEntourage T φ U + c := by
  rw [coverPressureEntourage_def, coverPressureEntourage_def,
    funext (pressureCoverSum_add_const_eq_exp_mul T φ c U), expGrowthSup_exp_mul, add_comm]

/-- Adding a constant `c` to the potential adds `c` to the spanning pressure. -/
theorem coverPressure_add_const [UniformSpace X] (T : X → X) (φ : X → ℝ) (c : ℝ) :
    coverPressure T (fun x ↦ φ x + c) = coverPressure T φ + c := by
  simp only [coverPressure, coverPressureEntourage_add_const, iSup_subtype',
    AddQuantale.iSup_add_distrib]

/-- If some `(U, n)`-dynamical net has maximal cardinality, the spanning pressure sum for `U ○ U`
is at most the pressure sum for `U`. -/
theorem pressureCoverSum_comp_le_pressureNetSum [U.IsRefl] [U.IsSymm]
    (h : netMaxcard T univ U n < ⊤) :
    pressureCoverSum T φ (U ○ U) n ≤ pressureNetSum T φ U n := by
  obtain ⟨s, s_net, s_card⟩ := (netMaxcard_finite_iff T univ U n).1 h
  exact (s_net.isDynCoverOf_comp s_card).pressureCoverSum_le.trans s_net.sum_le_pressureNetSum

/-- **Nets inject into covers.** If `V ⊆ U` and `φ a ≤ φ b + δ` whenever `(a, b) ∈ V`, the pressure
sum for `U` is at most the spanning pressure sum for `V` of the potential `φ + δ`. The injection
from a net into a cover is the argument of Mathlib's
`Dynamics.IsDynNetIn.card_le_card_of_isDynCoverOf`. -/
theorem pressureNetSum_le_pressureCoverSum_add_const (hVU : V ⊆ U) {δ : ℝ}
    (hφ : ∀ a b, (a, b) ∈ V → φ a ≤ φ b + δ) :
    pressureNetSum T φ U n ≤ pressureCoverSum T (fun x ↦ φ x + δ) V n := by
  classical
  refine pressureNetSum_le_iff.2 fun s s_net ↦ le_pressureCoverSum_iff.2 fun t t_cover ↦ ?_
  -- Send each point of the net to a point of the cover that shadows it.
  have hf : ∀ x ∈ s, ∃ y ∈ t, (x, y) ∈ dynEntourage T V n := fun x _ ↦ by
    obtain ⟨y, hy, hxy⟩ := t_cover (mem_univ x)
    exact ⟨y, hy, hxy⟩
  choose! f hft hxf using hf
  have hinj : Set.InjOn f s := by
    intro x hx x' hx' hxx'
    by_contra hne
    have h1 : f x ∈ (dynEntourage T U n).inv.ball x := dynEntourage_monotone T n hVU (hxf x hx)
    have h2 : f x ∈ (dynEntourage T U n).inv.ball x' := by
      rw [hxx']
      exact dynEntourage_monotone T n hVU (hxf x' hx')
    exact Set.disjoint_left.1 (s_net.2 hx hx' hne) h1 h2
  have hbirk : ∀ x ∈ s, birkhoffSum T φ n x ≤ birkhoffSum T (fun x ↦ φ x + δ) n (f x) := by
    intro x hx
    simp only [birkhoffSum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    exact hφ _ _ (mem_dynEntourage.1 (hxf x hx) k (Finset.mem_range.1 hk))
  calc ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T φ n x))
      ≤ ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum T (fun x ↦ φ x + δ) n (f x))) :=
        Finset.sum_le_sum fun x hx ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hbirk x hx))
    _ = ∑ y ∈ s.image f, ENNReal.ofReal (Real.exp (birkhoffSum T (fun x ↦ φ x + δ) n y)) :=
        (Finset.sum_image (f := fun y ↦
          ENNReal.ofReal (Real.exp (birkhoffSum T (fun x ↦ φ x + δ) n y))) hinj).symm
    _ ≤ ∑ y ∈ t, ENNReal.ofReal (Real.exp (birkhoffSum T (fun x ↦ φ x + δ) n y)) :=
        Finset.sum_le_sum_of_subset (Finset.image_subset_iff.2 hft)

variable [UniformSpace X]

/-- **Spanning form below the net form.** For a uniformly continuous map of a compact uniform
space, `P_cover(T, φ) ≤ P(T, φ)`. -/
theorem coverPressure_le_topologicalPressure [CompactSpace X] (hT : UniformContinuous T)
    (φ : X → ℝ) : coverPressure T φ ≤ topologicalPressure T φ := by
  refine iSup₂_le fun W hW ↦ ?_
  obtain ⟨U, hU, hsymm, hUW⟩ := comp_symm_mem_uniformity_sets hW
  have := isRefl_of_mem_uniformity hU
  refine (coverPressureEntourage_antitone T φ hUW).trans ?_
  refine le_trans ?_ (netPressureEntourage_le_topologicalPressure hU)
  rw [coverPressureEntourage_def, netPressureEntourage_def]
  refine expGrowthSup_monotone fun n ↦ pressureCoverSum_comp_le_pressureNetSum (U := U) ?_
  exact (netMaxcard_le_coverMincard T univ n).trans_lt
    (coverMincard_finite_of_isCompact_uniformContinuous isCompact_univ hT hU n)

/-- **Net form below the spanning form.** For a uniformly continuous potential,
`P(T, φ) ≤ P_cover(T, φ)`. -/
theorem topologicalPressure_le_coverPressure (hφ : UniformContinuous φ) (T : X → X) :
    topologicalPressure T φ ≤ coverPressure T φ := by
  have key : ∀ δ : ℝ, 0 < δ → topologicalPressure T φ ≤ coverPressure T φ + δ := by
    intro δ hδ
    refine topologicalPressure_le_iff.2 fun U hU ↦ ?_
    have hV : {p : X × X | dist (φ p.1) (φ p.2) < δ} ∈ 𝓤 X :=
      hφ (Metric.dist_mem_uniformity hδ)
    have hφV : ∀ a b, (a, b) ∈ U ∩ {p : X × X | dist (φ p.1) (φ p.2) < δ} →
        φ a ≤ φ b + δ := fun a b hab ↦ by
      have := hab.2
      simp only [mem_ofPred_eq, Real.dist_eq] at this
      linarith [le_abs_self (φ a - φ b)]
    rw [netPressureEntourage_def]
    calc expGrowthSup (pressureNetSum T φ U)
        ≤ coverPressureEntourage T (fun x ↦ φ x + δ)
            (U ∩ {p : X × X | dist (φ p.1) (φ p.2) < δ}) :=
          expGrowthSup_monotone fun n ↦
            pressureNetSum_le_pressureCoverSum_add_const inter_subset_left hφV
      _ = coverPressureEntourage T φ (U ∩ {p : X × X | dist (φ p.1) (φ p.2) < δ}) + δ :=
          coverPressureEntourage_add_const T φ δ _
      _ ≤ coverPressure T φ + δ :=
          add_le_add (coverPressureEntourage_le_coverPressure (inter_mem hU hV)) le_rfl
  exact EReal.le_of_forall_pos_le_add key

/-- **Separated and spanning forms agree.** For a uniformly continuous map `T` of a compact
uniform space and a uniformly continuous potential `φ`, the spanning-set form of the pressure is
the topological pressure. -/
theorem coverPressure_eq_topologicalPressure [CompactSpace X] (hT : UniformContinuous T)
    (hφ : UniformContinuous φ) : coverPressure T φ = topologicalPressure T φ :=
  (coverPressure_le_topologicalPressure hT φ).antisymm (topologicalPressure_le_coverPressure hφ T)

end TauCeti
