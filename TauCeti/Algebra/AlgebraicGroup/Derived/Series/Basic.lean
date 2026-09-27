/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Functoriality

/-!
# The scheme-theoretic derived series

Starting with an affine group, repeatedly take the derived closed subgroup. We keep the
defining ideals in the original coordinate algebra, pulling back from each quotient at the
successor step. These ideals increase, since the closed subgroups decrease.

The comparison with the abstract derived series of rational points is in
`TauCeti.Algebra.AlgebraicGroup.Derived.Series.PointClosure`. The resulting solvability
characterization is in `TauCeti.Algebra.AlgebraicGroup.Solvable.Derived.Series`.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

namespace CommHopfAlgCat

noncomputable section

open CategoryTheory TauCeti TauCeti.CommHopfAlgCat WithConv

variable {R : Type*} [CommRing R] (H : _root_.CommHopfAlgCat R)

/-- The defining ideal of the `n`th scheme-theoretic derived subgroup, viewed as a closed
subgroup of the original affine group. -/
def derivedSeriesDefiningIdeal : ℕ → HopfIdeal R H
  | 0 => ⊥
  | n + 1 => (derivedDefiningIdeal (quotient H (derivedSeriesDefiningIdeal n))).comapOfSurjective
      (mkQuotient H (derivedSeriesDefiningIdeal n)).hom (mkQuotient_surjective _ _)

/-- The series starts at the ambient group itself, whose defining ideal is `⊥`. -/
@[simp] theorem derivedSeriesDefiningIdeal_zero : derivedSeriesDefiningIdeal H 0 = ⊥ := (rfl)

/-- The next term is the derived subgroup of the current closed subgroup, included back
into the original group. -/
@[simp] theorem derivedSeriesDefiningIdeal_succ (n : ℕ) :
    derivedSeriesDefiningIdeal H (n + 1) =
      (derivedDefiningIdeal (quotient H (derivedSeriesDefiningIdeal H n))).comapOfSurjective
        (mkQuotient H (derivedSeriesDefiningIdeal H n)).hom (mkQuotient_surjective _ _) := (rfl)

/-- The first derived-series term is the usual derived closed subgroup. -/
@[simp↓] theorem derivedSeriesDefiningIdeal_one :
    derivedSeriesDefiningIdeal H 1 = derivedDefiningIdeal H := by
  rw [derivedSeriesDefiningIdeal_succ, derivedSeriesDefiningIdeal_zero]
  simpa only [CategoryTheory.Iso.symm_hom, quotientBotIso_inv] using
    comapOfSurjective_derivedDefiningIdeal (quotientBotIso H).symm

/-- An isomorphism of coordinate Hopf algebras preserves every derived-series term. -/
@[simp] theorem comapOfSurjective_derivedSeriesDefiningIdeal
    {H K : _root_.CommHopfAlgCat R} (e : H ≅ K) (n : ℕ) :
    (derivedSeriesDefiningIdeal K n).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 = derivedSeriesDefiningIdeal H n := by
  induction n with
  | zero =>
      ext x
      simp only [derivedSeriesDefiningIdeal_zero, HopfIdeal.mem_comapOfSurjective,
        HopfIdeal.mem_bot]
      exact map_eq_zero_iff e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).1
  | succ n ih =>
      rw [derivedSeriesDefiningIdeal_succ, derivedSeriesDefiningIdeal_succ, ← ih]
      let q := quotientIsoOfIso e (derivedSeriesDefiningIdeal K n)
      have hq := comapOfSurjective_derivedDefiningIdeal q
      ext x
      have hx := congrArg (fun I : HopfIdeal R _ =>
        (mkQuotient H _).hom x ∈ I) hq
      have hcomm := congrArg (fun f : H ⟶ quotient K (derivedSeriesDefiningIdeal K n) =>
        f.hom x) (mkQuotient_comp_quotientIsoOfIso_hom e (derivedSeriesDefiningIdeal K n))
      simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at hcomm
      simpa only [HopfIdeal.mem_comapOfSurjective, q, hcomm] using iff_of_eq hx

/-- The defining ideals increase along the derived series. -/
theorem derivedSeriesDefiningIdeal_monotone : Monotone (derivedSeriesDefiningIdeal H) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  rw [derivedSeriesDefiningIdeal_succ, HopfIdeal.mem_comapOfSurjective,
    (mkQuotient_eq_zero_iff H _ x).mpr hx]
  exact (derivedDefiningIdeal _).toIdeal.zero_mem

/-- Once the derived series reaches the identity, every later term is the identity. -/
theorem derivedSeriesDefiningIdeal_eq_augmentation_of_le {m n : ℕ} (hmn : m ≤ n)
    (hm : derivedSeriesDefiningIdeal H m = HopfIdeal.augmentation R H) :
    derivedSeriesDefiningIdeal H n = HopfIdeal.augmentation R H := by
  apply le_antisymm (HopfIdeal.le_augmentation R H _)
  rw [← hm]
  exact derivedSeriesDefiningIdeal_monotone H hmn

end

end CommHopfAlgCat
