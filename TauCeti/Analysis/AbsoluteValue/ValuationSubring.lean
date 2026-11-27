/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
public import TauCeti.RingTheory.Valuation.AbsoluteValue
public import TauCeti.Topology.Algebra.Valued.NormedValued

/-!
# The valuation subring of a nonarchimedean absolute value

A nonarchimedean absolute value `w` on a field `K` has a valuation subring
`{x | w x ≤ 1}`, whose maximal ideal is `{x | w x < 1}`. This file constructs it and relates it to
the other descriptions of the same object that Mathlib and Tau Ceti already have, so that a finite
place can be read either as an absolute value or as a valuation subring.

The values of `w` may lie in any linearly ordered field `S`. The nonarchimedean hypothesis is an
explicit argument, as in `AbsoluteValue.nonarchRpow`, rather than an instance.

## Main definitions

* `AbsoluteValue.valuationSubring`: the valuation subring `{x | w x ≤ 1}` of a nonarchimedean
  absolute value `w` on a field.

## Main results

* `AbsoluteValue.valuationSubring_toValuation`: the valuation subring of the valuation
  `AbsoluteValue.toValuation` attached to a nonarchimedean real absolute value is
  `AbsoluteValue.valuationSubring`.
* `AbsoluteValue.mem_nonunits_valuationSubring_iff`,
  `AbsoluteValue.mem_maximalIdeal_valuationSubring_iff`,
  `AbsoluteValue.isUnit_valuationSubring_iff`: the nonunits of the valuation subring are the
  elements with `w x < 1` and its units are the elements with `w x = 1`.
* `AbsoluteValue.residue_eq_zero_iff`, `AbsoluteValue.charP_residueField`: the residue map kills
  exactly the elements with `w x < 1`, so the residue field has characteristic `p` when
  `w p < 1` for a prime `p`.
* `AbsoluteValue.valuationSubring_eq_top_iff`: the valuation subring is the whole field if and only
  if `w` is trivial.
* `AbsoluteValue.isEquiv_iff_valuationSubring`: two nonarchimedean absolute values are equivalent
  if and only if they have the same valuation subring. This is the analogue of Mathlib's
  `Valuation.isEquiv_iff_valuationSubring`, and needs no nontriviality hypothesis.
* `AbsoluteValue.valuationSubring_comp`, `AbsoluteValue.valuationSubring_under`,
  `AbsoluteValue.LiesOver.valuationSubring_eq_comap`: restricting an absolute value along a field
  homomorphism pulls back its valuation subring.
* Comparisons with the existing constructions in the other direction:
  `Valuation.valuationSubring_toAbsoluteValue` (Tau Ceti's absolute value of a valuation),
  `Valuation.valuationSubring_absoluteValue` (Mathlib's absolute value of a valuation of rank at
  most one) and `NormedField.valuationSubring_toAbsoluteValue` (the norm of a nonarchimedean
  normed field, through `NormedField.toValuation_toAbsoluteValue`).

The action of a group on absolute values and the corresponding equivariance of
`AbsoluteValue.valuationSubring` are not treated here.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §3.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press, 1967,
  Chapter II, §§1 to 4.
-/

public section

open IsLocalRing

open scoped NNReal

namespace AbsoluteValue

section Field

variable {K S : Type*} [Field K] [Semifield S] [LinearOrder S] [IsStrictOrderedRing S]
  {w : AbsoluteValue K S}

/-- The valuation subring `{x | w x ≤ 1}` of a nonarchimedean absolute value `w` on a field. -/
def valuationSubring (hw : IsNonarchimedean w) : ValuationSubring K where
  carrier := {x | w x ≤ 1}
  mul_mem' {x y} hx hy := by
    simpa only [Set.mem_ofPred_eq, map_mul, mul_one] using
      mul_le_mul hx hy (w.nonneg y) zero_le_one
  one_mem' := by simp
  add_mem' {x y} hx hy := (hw x y).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by
    -- `S` need not be a ring, so compare the squares `w (-x) * w (-x) = w x * w x` instead.
    have h : w (-x) = w x := (mul_self_inj (w.nonneg _) (w.nonneg _)).1 <| by
      rw [← map_mul, ← map_mul, neg_mul_neg]
    simpa only [Set.mem_ofPred_eq, h] using hx
  mem_or_inv_mem' x := (le_total (w x) 1).imp id fun h ↦ by
    simpa only [Set.mem_ofPred_eq, map_inv₀] using inv_le_one_of_one_le₀ h

/-- An element lies in the valuation subring of `w` if and only if `w x ≤ 1`. -/
@[simp]
theorem mem_valuationSubring_iff (hw : IsNonarchimedean w) {x : K} :
    x ∈ w.valuationSubring hw ↔ w x ≤ 1 :=
  Iff.rfl

/-- The nonunits of the valuation subring of `w`, as a subset of the field, are the elements
with `w x < 1`. -/
@[simp]
theorem mem_nonunits_valuationSubring_iff (hw : IsNonarchimedean w) {x : K} :
    x ∈ (w.valuationSubring hw).nonunits ↔ w x < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [hx, map_inv₀, one_lt_inv₀ (w.pos hx)]

/-- The maximal ideal of the valuation subring of `w` consists of the elements with
`w x < 1`. -/
theorem mem_maximalIdeal_valuationSubring_iff (hw : IsNonarchimedean w)
    {a : w.valuationSubring hw} : a ∈ maximalIdeal (w.valuationSubring hw) ↔ w a < 1 := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, mem_nonunits_valuationSubring_iff]

/-- The units of the valuation subring of `w` are the elements with `w x = 1`. -/
@[simp]
theorem isUnit_valuationSubring_iff (hw : IsNonarchimedean w) {a : w.valuationSubring hw} :
    IsUnit a ↔ w a = 1 := by
  rw [← not_iff_not, ← mem_nonunits_iff, ← mem_maximalIdeal,
    mem_maximalIdeal_valuationSubring_iff]
  exact ⟨fun h ↦ h.ne, fun h ↦ lt_of_le_of_ne a.property h⟩

/-- The residue map of the valuation subring of `w` kills exactly the elements with
`w x < 1`. -/
theorem residue_eq_zero_iff (hw : IsNonarchimedean w) {a : w.valuationSubring hw} :
    residue (w.valuationSubring hw) a = 0 ↔ w a < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_valuationSubring_iff]

/-- If `w p < 1` for a prime `p`, then the residue field of the valuation subring of `w` has
characteristic `p`. -/
theorem charP_residueField (hw : IsNonarchimedean w) {p : ℕ} (hp : p.Prime) (hwp : w p < 1) :
    CharP (ResidueField (w.valuationSubring hw)) p := by
  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (residue (w.valuationSubring hw)),
    residue_eq_zero_iff]
  simpa using hwp

/-- The valuation subring of `w` is the whole field if and only if `w` is trivial. -/
theorem valuationSubring_eq_top_iff (hw : IsNonarchimedean w) :
    w.valuationSubring hw = ⊤ ↔ ¬ w.IsNontrivial := by
  rw [not_isNontrivial_iff, eq_top_iff]
  refine ⟨fun h x hx ↦ (h (ValuationSubring.mem_top x)).antisymm ?_, fun h x _ ↦ ?_⟩
  · have hinv : w x⁻¹ ≤ 1 := h (ValuationSubring.mem_top x⁻¹)
    rwa [map_inv₀, inv_le_one₀ (w.pos hx)] at hinv
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (h x hx).le

/-- Two nonarchimedean absolute values are equivalent if and only if they have the same
valuation subring. -/
theorem isEquiv_iff_valuationSubring {v : AbsoluteValue K S} (hv : IsNonarchimedean v)
    (hw : IsNonarchimedean w) : v.IsEquiv w ↔ v.valuationSubring hv = w.valuationSubring hw := by
  refine ⟨fun h ↦ ValuationSubring.ext _ _ fun x ↦ h.le_one_iff, fun h ↦ ?_⟩
  refine isEquiv_iff_lt_one_iff.2 fun x ↦ ?_
  rw [← mem_nonunits_valuationSubring_iff hv, ← mem_nonunits_valuationSubring_iff hw, h]

/-- Equivalent nonarchimedean absolute values have the same valuation subring. -/
theorem IsEquiv.valuationSubring_eq {v : AbsoluteValue K S} (h : v.IsEquiv w)
    (hv : IsNonarchimedean v) (hw : IsNonarchimedean w) :
    v.valuationSubring hv = w.valuationSubring hw :=
  (isEquiv_iff_valuationSubring hv hw).1 h

/-- Restricting a nonarchimedean absolute value along a field homomorphism pulls back its
valuation subring. -/
theorem valuationSubring_comp {L : Type*} [Field L] (hw : IsNonarchimedean w) {f : L →+* K}
    (hf : Function.Injective f) :
    (w.comp hf).valuationSubring (isNonarchimedean_comp hw hf) =
      (w.valuationSubring hw).comap f := by
  ext
  simp [ValuationSubring.mem_comap, mem_valuationSubring_iff, comp_apply]

/-- The valuation subring of the restriction of `w` to a subfield `L` is the intersection of the
valuation subring of `w` with `L`. -/
theorem valuationSubring_under {L : Type*} [Field L] [Algebra L K] (hw : IsNonarchimedean w) :
    (w.under L).valuationSubring (isNonarchimedean_comp hw _) =
      (w.valuationSubring hw).comap (algebraMap L K) :=
  valuationSubring_comp hw _

/-- If `w` lies over `v`, the valuation subring of `v` is the intersection of the valuation
subring of `w` with `L`. -/
theorem LiesOver.valuationSubring_eq_comap {L : Type*} [Field L] [Algebra L K]
    {v : AbsoluteValue L S} [w.LiesOver v] (hv : IsNonarchimedean v) (hw : IsNonarchimedean w) :
    v.valuationSubring hv = (w.valuationSubring hw).comap (algebraMap L K) := by
  obtain rfl := LiesOver.under_eq w v
  exact valuationSubring_under hw

end Field

section Real

variable {K : Type*} [Field K] {w : AbsoluteValue K ℝ}

/-- The valuation subring of the valuation attached to `w` is the valuation subring of `w`. -/
@[simp]
theorem valuationSubring_toValuation (hw : IsNonarchimedean w) :
    (w.toValuation hw).valuationSubring = w.valuationSubring hw := by
  ext x
  simp [← NNReal.coe_le_coe]

end Real

end AbsoluteValue

namespace Valuation

/-- The absolute value obtained from a valuation through a strictly monotone realization has the
same valuation subring as the valuation. -/
theorem valuationSubring_toAbsoluteValue {K S Γ₀ : Type*} [Field K] [Semifield S] [LinearOrder S]
    [IsStrictOrderedRing S] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (f : Γ₀ →*₀ S) (hf : StrictMono f) (hf_zero : ∀ a, f a = 0 ↔ a = 0)
    (hv_zero : ∀ x, v x = 0 ↔ x = 0) :
    (v.toAbsoluteValue f hf.monotone hf_zero hv_zero).valuationSubring
        (v.isNonarchimedean_toAbsoluteValue f hf.monotone hf_zero hv_zero) =
      v.valuationSubring := by
  ext x
  simp [← hf.le_iff_le]

section RankLeOne

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
  [hv : RankLeOne v]

/-- Mathlib's absolute value of a valuation of rank at most one has the same valuation subring as
the valuation. -/
theorem valuationSubring_absoluteValue :
    v.absoluteValue.valuationSubring v.isNonarchimedean_absoluteValue = v.valuationSubring := by
  ext x
  simpa [norm_def, restrict_le_one_iff] using hv.strictMono'.le_iff_le (a := v.restrict x) (b := 1)

end RankLeOne

end Valuation

namespace NormedField

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- The valuation subring of the norm of a nonarchimedean normed field is the valuation subring
of Mathlib's valuation of the field. -/
theorem valuationSubring_toAbsoluteValue :
    (toAbsoluteValue K).valuationSubring (isNonarchimedean_toAbsoluteValue K) =
      valuation.valuationSubring := by
  rw [← toValuation_toAbsoluteValue, AbsoluteValue.valuationSubring_toValuation]

end NormedField
