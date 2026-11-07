/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Space
public import Mathlib.MeasureTheory.Function.LpOrder
import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.Analysis.BoundedVariation.Submodularity
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Lattice operations on functions of bounded variation

For real functions `u` and `v` that are locally integrable on an open set `Ω`, the pointwise
maximum and minimum satisfy

`|D(u ⊔ v)|(Ω) + |D(u ⊓ v)|(Ω) ≤ |Du|(Ω) + |Dv|(Ω)`,

where both sides may be infinite. At every level `t`, the superlevel sets `{t < u ⊔ v}` and
`{t < u ⊓ v}` are the union and the intersection of `{t < u}` and `{t < v}`. The inequality is
therefore submodularity of the perimeter, `TauCeti.perimeter_union_add_perimeter_inter_le`,
integrated over all levels by the coarea formula `TauCeti.totalVariationOn_eq_lintegral_perimeter`.
It is the functional form of submodularity: for indicators of null-measurable sets it is that
inequality again.

Consequently the maximum and minimum of two functions of bounded variation are of bounded
variation, and the Banach space `TauCeti.BV μ Ω` is a lattice. Its order is the almost-everywhere
order on `Ω`, and its lattice operations are those of `L¹`, computed pointwise almost everywhere.
The order is compatible with addition, so `BV μ Ω` is a lattice-ordered group. Its norm is not
solid, since a function bounded by a constant can have arbitrarily large variation, so no
normed-lattice structure is asserted.

All variations are the variational quantity `TauCeti.totalVariationOn`, against an additive Haar
measure on a finite-dimensional real inner product space.

## Main results

* `TauCeti.totalVariationOn_sup_add_totalVariationOn_inf_le`: the inequality above.
* `TauCeti.totalVariationOn_sup_le_add` and `TauCeti.totalVariationOn_inf_le_add`: the variation of
  a maximum or minimum is at most the sum of the variations.
* `TauCeti.MemBV.sup` and `TauCeti.MemBV.inf`: BV membership of maxima and minima.
* `TauCeti.BV.instLattice` and `TauCeti.BV.instIsOrderedAddMonoid`: the lattice-ordered group
  structure of `TauCeti.BV μ Ω`, with `TauCeti.BV.coeFn_sup`, `TauCeti.BV.coeFn_inf`,
  `TauCeti.BV.coeFn_abs` and `TauCeti.BV.coeFn_le`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.40 and Proposition 3.38.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Lemma 12.22.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {u v : E → ℝ}

section TotalVariation

variable [μ.IsAddHaarMeasure]

/-- **Submodularity of the total variation under lattice operations.** For `u` and `v` locally
integrable on `Ω`, `|D(u ⊔ v)|(Ω) + |D(u ⊓ v)|(Ω) ≤ |Du|(Ω) + |Dv|(Ω)`. Both sides may be
infinite. -/
theorem totalVariationOn_sup_add_totalVariationOn_inf_le (hu : LocallyIntegrableOn u Ω μ)
    (hv : LocallyIntegrableOn v Ω μ) :
    totalVariationOn μ Ω (u ⊔ v) + totalVariationOn μ Ω (u ⊓ v) ≤
      totalVariationOn μ Ω u + totalVariationOn μ Ω v := by
  rw [totalVariationOn_eq_lintegral_perimeter (hu.sup hv),
    totalVariationOn_eq_lintegral_perimeter (hu.inf hv), totalVariationOn_eq_lintegral_perimeter hu,
    totalVariationOn_eq_lintegral_perimeter hv,
    ← lintegral_add_left (measurable_perimeter_setOf_lt hu.aestronglyMeasurable.aemeasurable)]
  refine (le_lintegral_add _ _).trans (lintegral_mono fun t => ?_)
  have hsup : {x | t < (u ⊔ v) x} = {x | t < u x} ∪ {x | t < v x} := by
    ext x
    simp [lt_max_iff]
  have hinf : {x | t < (u ⊓ v) x} = {x | t < u x} ∩ {x | t < v x} := by
    ext x
    simp [lt_min_iff]
  rw [hsup, hinf]
  exact perimeter_union_add_perimeter_inter_le
    (nullMeasurableSet_lt aemeasurable_const hu.aestronglyMeasurable.aemeasurable)
    (nullMeasurableSet_lt aemeasurable_const hv.aestronglyMeasurable.aemeasurable)

/-- The variation of the maximum of two locally integrable functions is at most the sum of their
variations. -/
theorem totalVariationOn_sup_le_add (hu : LocallyIntegrableOn u Ω μ)
    (hv : LocallyIntegrableOn v Ω μ) :
    totalVariationOn μ Ω (u ⊔ v) ≤ totalVariationOn μ Ω u + totalVariationOn μ Ω v :=
  le_self_add.trans (totalVariationOn_sup_add_totalVariationOn_inf_le hu hv)

/-- The variation of the minimum of two locally integrable functions is at most the sum of their
variations. -/
theorem totalVariationOn_inf_le_add (hu : LocallyIntegrableOn u Ω μ)
    (hv : LocallyIntegrableOn v Ω μ) :
    totalVariationOn μ Ω (u ⊓ v) ≤ totalVariationOn μ Ω u + totalVariationOn μ Ω v :=
  le_add_self.trans (totalVariationOn_sup_add_totalVariationOn_inf_le hu hv)

/-- The maximum of two BV functions belongs to BV. -/
theorem MemBV.sup (hu : MemBV μ Ω u) (hv : MemBV μ Ω v) : MemBV μ Ω (u ⊔ v) := by
  rcases memBV_iff.mp hu with ⟨hu, hufinite⟩
  rcases memBV_iff.mp hv with ⟨hv, hvfinite⟩
  exact memBV_iff.mpr ⟨Integrable.sup hu hv,
    (totalVariationOn_sup_le_add hu.locallyIntegrableOn hv.locallyIntegrableOn).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hufinite, hvfinite⟩)⟩

/-- The minimum of two BV functions belongs to BV. -/
theorem MemBV.inf (hu : MemBV μ Ω u) (hv : MemBV μ Ω v) : MemBV μ Ω (u ⊓ v) := by
  rcases memBV_iff.mp hu with ⟨hu, hufinite⟩
  rcases memBV_iff.mp hv with ⟨hv, hvfinite⟩
  exact memBV_iff.mpr ⟨Integrable.inf hu hv,
    (totalVariationOn_inf_le_add hu.locallyIntegrableOn hv.locallyIntegrableOn).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hufinite, hvfinite⟩)⟩

end TotalVariation

namespace BV

instance instLE : LE (BV μ Ω) := ⟨fun u v => u.toL1 ≤ v.toL1⟩
instance instLT : LT (BV μ Ω) := ⟨fun u v => u.toL1 < v.toL1⟩

/-- BV classes are ordered as their `L¹` classes. -/
@[simp]
theorem toL1_le_toL1 {u v : BV μ Ω} : u.toL1 ≤ v.toL1 ↔ u ≤ v := (Iff.rfl)

/-- BV classes are strictly ordered as their `L¹` classes. -/
@[simp]
theorem toL1_lt_toL1 {u v : BV μ Ω} : u.toL1 < v.toL1 ↔ u < v := (Iff.rfl)

/-- The order of BV classes is the almost-everywhere order of their representatives on `Ω`. -/
theorem coeFn_le {u v : BV μ Ω} : (u : E → ℝ) ≤ᵐ[μ.restrict Ω] v ↔ u ≤ v :=
  Lp.coeFn_le u.toL1 v.toL1

variable [μ.IsAddHaarMeasure]

instance instMax : Max (BV μ Ω) := ⟨fun u v => ofFunction (u ⊔ v) (u.memBV.sup v.memBV)⟩
instance instMin : Min (BV μ Ω) := ⟨fun u v => ofFunction (u ⊓ v) (u.memBV.inf v.memBV)⟩

/-- The representative of a maximum is almost everywhere the maximum of the representatives. -/
theorem coeFn_sup (u v : BV μ Ω) : (u ⊔ v : BV μ Ω) =ᵐ[μ.restrict Ω] (u : E → ℝ) ⊔ v :=
  coeFn_ofFunction _ _

/-- The representative of a minimum is almost everywhere the minimum of the representatives. -/
theorem coeFn_inf (u v : BV μ Ω) : (u ⊓ v : BV μ Ω) =ᵐ[μ.restrict Ω] (u : E → ℝ) ⊓ v :=
  coeFn_ofFunction _ _

/-- The `L¹` class of a maximum is the maximum of the `L¹` classes. -/
@[simp]
theorem toL1_sup (u v : BV μ Ω) : (u ⊔ v).toL1 = u.toL1 ⊔ v.toL1 :=
  Lp.ext ((coeFn_sup u v).trans (Lp.coeFn_sup u.toL1 v.toL1).symm)

/-- The `L¹` class of a minimum is the minimum of the `L¹` classes. -/
@[simp]
theorem toL1_inf (u v : BV μ Ω) : (u ⊓ v).toL1 = u.toL1 ⊓ v.toL1 :=
  Lp.ext ((coeFn_inf u v).trans (Lp.coeFn_inf u.toL1 v.toL1).symm)

/-- BV is a lattice, with the lattice operations of `L¹`. -/
instance instLattice : Lattice (BV μ Ω) :=
  toL1_injective.lattice _ toL1_le_toL1 toL1_lt_toL1 toL1_sup toL1_inf

/-- The order of BV is compatible with addition. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (BV μ Ω) :=
  Function.Injective.isOrderedAddMonoid toL1 toL1_add toL1_le_toL1

/-- The `L¹` class of an absolute value is the absolute value of the `L¹` class. -/
@[simp]
theorem toL1_abs (u : BV μ Ω) : |u|.toL1 = |u.toL1| := by
  rw [abs, abs, toL1_sup, toL1_neg]

/-- The representative of an absolute value is almost everywhere the absolute value of the
representative. -/
theorem coeFn_abs (u : BV μ Ω) : (|u| : BV μ Ω) =ᵐ[μ.restrict Ω] fun x => |u x| := by
  rw [toL1_abs]
  exact Lp.coeFn_abs u.toL1

end BV

end TauCeti
