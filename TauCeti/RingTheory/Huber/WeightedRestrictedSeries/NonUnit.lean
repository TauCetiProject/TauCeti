/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.MvPowerSeries.Inverse

/-!
# Generators of the unit ideal of `A⟨X⟩` that are not units

In a Tate ring an ideal is open exactly when it is the unit ideal
(`TauCeti.Huber.IsTateRing.isOpen_iff_eq_top`). So a finite set `T` generates an open ideal, as
in the definition of the rational subsets `R(T/s)`, exactly when it generates the unit ideal.
This does not make any element of `T` a unit. In the ring `A⟨X₁, …, Xₖ⟩` of restricted power
series over a nonzero Hausdorff ring `A` the two elements `Xᵢ` and `1 - Xᵢ` sum to `1`, but
neither is a unit. When `A` is a Tate ring so is `A⟨X₁, …, Xₖ⟩`
(`TauCeti.Huber.isTateRing_weightedRestrictedSubring`), which gives the counterexample. Over a
complete nonarchimedean field `K`, with `T = {X, 1 - X}`, the two rational subsets `R(T/X)` and
`R(T/(1 - X))` of the closed unit disc `Spa(K⟨X⟩, K⟨X⟩°)` cover it (Wedhorn, Corollary 7.53),
although neither denominator is a unit.

The variable `Xᵢ` has constant coefficient `0`, so it is not a unit for any weights. The inverse
of `1 - Xᵢ` in the ring of all power series is the geometric series `∑ₙ Xᵢⁿ`, whose coefficients
are all `1` and so do not tend to `0`; this is why `A` is assumed Hausdorff, and why the unit
weight is used.

## Main results

* `TauCeti.Huber.not_isUnit_weightedX`: `Xᵢ` is not a unit of `A⟨X⟩_T`.
* `TauCeti.Huber.not_isUnit_one_sub_weightedX`: `1 - Xᵢ` is not a unit of `A⟨X⟩` when `A` is
  nonzero and Hausdorff.
* `TauCeti.Huber.span_weightedX_one_sub_weightedX_eq_top`: `Xᵢ` and `1 - Xᵢ` generate the unit
  ideal.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark 7.30, for rational subsets of Tate rings.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] {k : ℕ}

/-- **The variable `Xᵢ` is not a unit** of the ring `A⟨X⟩_T` of weighted restricted power series
over a nonzero ring: its constant coefficient is `0`. -/
theorem not_isUnit_weightedX [Nontrivial A] {T : Fin k → Set A} {hT : IsWeightFamily T}
    (i : Fin k) : ¬IsUnit (weightedX T hT i) := fun h ↦ by
  simpa using MvPowerSeries.isUnit_constantCoeff _ (h.map (weightedRestrictedSubring T hT).subtype)

/-- **`1 - Xᵢ` is not a unit of `A⟨X⟩`** over a nonzero Hausdorff ring `A`: its inverse among all
power series is the geometric series `∑ₙ Xᵢⁿ`, whose coefficients do not tend to `0`. -/
theorem not_isUnit_one_sub_weightedX [T0Space A] [Nontrivial A] (i : Fin k) :
    ¬IsUnit (1 - weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i) := by
  rintro ⟨u, hu⟩
  set g := ((u⁻¹ : (weightedRestrictedSubring _ isWeightFamily_one_weight)ˣ) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
  have hg : (1 - MvPowerSeries.X i) * (g : MvPowerSeries (Fin k) A) = 1 := by
    have := congrArg Subtype.val u.mul_inv
    rw [hu] at this
    simpa using this
  -- The coefficients of `g` tend to `0`, so along the monomials `Xᵢⁿ` the constant `1` does.
  have hlim := (isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp g.2)).comp
    ((Finsupp.single_injective i).tendsto_cofinite)
  simp only [Function.comp_def,
    MvPowerSeries.coeff_single_eq_one_of_one_sub_X_mul_eq_one hg] at hlim
  exact one_ne_zero (tendsto_const_nhds_iff.mp hlim)

/-- **`Xᵢ` and `1 - Xᵢ` generate the unit ideal** of `A⟨X⟩_T`: they sum to `1`. -/
theorem span_weightedX_one_sub_weightedX_eq_top {T : Fin k → Set A} {hT : IsWeightFamily T}
    (i : Fin k) : Ideal.span {weightedX T hT i, 1 - weightedX T hT i} = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _
    (Ideal.add_mem _ (Ideal.subset_span (Set.mem_insert _ _))
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
    (by simp)

/-- Over a nontrivially normed field `K` with an ultrametric norm, the Tate ring `K⟨X⟩` contains
the finite set `{X, 1 - X}`, which generates an open ideal although neither of its elements is a
unit. -/
example (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] :
    IsTateRing (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
        isWeightFamily_one_weight) ∧
      IsOpen (SetLike.coe (Ideal.span {weightedX _ isWeightFamily_one_weight 0,
        1 - weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0})) ∧
      ¬IsUnit (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) ∧
      ¬IsUnit (1 - weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) := by
  refine ⟨inferInstance, ?_, not_isUnit_weightedX 0, not_isUnit_one_sub_weightedX 0⟩
  rw [span_weightedX_one_sub_weightedX_eq_top, Submodule.top_coe]
  exact isOpen_univ

end TauCeti.Huber
