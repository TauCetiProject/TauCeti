/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.Solvable
public import TauCeti.Algebra.AlgebraicGroup.Derived.PointClosure

/-!
# The scheme-theoretic derived series

Starting with an affine group, repeatedly take the derived closed subgroup. We keep the
defining ideals in the original coordinate algebra, pulling back from each quotient at the
successor step. These ideals increase, since the closed subgroups decrease.

For a reduced finite-type affine group over an algebraically closed field, the `n`th ideal
is the vanishing ideal of the `n`th abstract derived subgroup of rational points. The resulting
solvability characterization is in `TauCeti.Algebra.AlgebraicGroup.Solvable.DerivedSeries`.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

namespace TauCeti

noncomputable section

open TauCeti.CommHopfAlgCat WithConv

section CommRing

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
theorem derivedSeriesDefiningIdeal_one :
    derivedSeriesDefiningIdeal H 1 = derivedDefiningIdeal H := by
  rw [derivedSeriesDefiningIdeal_succ, derivedSeriesDefiningIdeal_zero]
  simpa only [CategoryTheory.Iso.symm_hom, quotientBotIso_inv] using
    comapOfSurjective_derivedDefiningIdeal (quotientBotIso H).symm

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

end CommRing

variable {k : Type*} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat k)
  [Algebra.FiniteType k H] [IsReduced H]

/-- Each scheme-theoretic derived subgroup is the reduced closure of the corresponding
abstract derived subgroup of rational points. -/
theorem derivedSeriesDefiningIdeal_eq_vanishingIdeal_derivedSeries (n : ℕ) :
    derivedSeriesDefiningIdeal H n =
      HopfIdeal.vanishingIdeal (derivedSeries (WithConv (H →ₐ[k] k)) n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [derivedSeriesDefiningIdeal_succ, ih,
        comapOfSurjective_derivedDefiningIdeal_quotient_vanishingIdeal_eq_vanishingIdeal_commutator,
        derivedSeries_succ]

end

end TauCeti
