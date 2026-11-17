/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Algebra.Homology.SpectralObject.Abutment
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.SuccPred.Int
import TauCeti.Algebra.Category.FGModuleCat.Exact
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Finiteness and rank of filtered abutments of spectral objects of modules

Let `X` be a spectral object indexed by `EInt` in `ModuleCat R`. Each filtration inclusion
`X.abutmentFiltrationMap q n : F_q H^n ⟶ F_{q+1} H^n` is a monomorphism fitting into a short exact
sequence with its cokernel via `TauCeti.cokernelSequence_shortExact`.

Specializing `CategoryTheory.Abelian.SpectralObject.prop_abutmentFiltration_of_forall_prop_cokernel`
and `CategoryTheory.Abelian.SpectralObject.prop_abutment_of_forall_prop_cokernel` to the
extension-closed property `ModuleCat.isFG R` shows that over any ring `R`, finite generation passes
from `F_a H^n` and the graded pieces on `Ico a b` to `F_b H^n`
(`CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration_of_forall_finite_cokernel`) and,
when the filtration exhausts the abutment at `b`, to `X.abutment n`
(`CategoryTheory.Abelian.SpectralObject.finite_abutment_of_forall_finite_cokernel`).

Over a ring satisfying `StrongRankCondition` and `HasRankNullity` (such as a division ring or a
commutative domain), additivity of `Module.finrank` on short exact sequences
(`CategoryTheory.ShortComplex.ShortExact.moduleCat_finrank_eq_add`) yields by induction that when
`F_a H^n` vanishes and every graded piece on `Ico a b` is finitely generated, `finrank R (F_b H^n)`
and (when exhaustive at `b`) `finrank R (X.abutment n)` equal the sum of the ranks of the graded
pieces over `Ico a b`
(`CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum_Ico`,
`CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`).

## Main results

* `CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration_of_forall_finite_cokernel` and
  `CategoryTheory.Abelian.SpectralObject.finite_abutment_of_forall_finite_cokernel`: finite
  generation of a finitely filtered abutment from its starting piece and graded pieces.
* `CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum_Ico` and
  `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`: rank of a finitely filtered
  abutment as the sum of the ranks of its graded pieces.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Chapter 2.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace CategoryTheory.Abelian.SpectralObject

variable {R : Type u} [Ring R] (X : SpectralObject (ModuleCat.{v} R) EInt)

/-- Over any ring `R`, if `F_a H^n` and every graded piece `F_{q+1} H^n / F_q H^n` for `a ≤ q < b`
are finitely generated, then `F_b H^n` is finitely generated. -/
theorem finite_abutmentFiltration_of_forall_finite_cokernel {a b n : ℤ} (hab : a ≤ b)
    (ha : Module.Finite R (X.abutmentFiltration a n))
    (hcok : ∀ q ∈ Finset.Ico a b, Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n))) :
    Module.Finite R (X.abutmentFiltration b n) :=
  (ModuleCat.isFG_iff _).1 <|
    X.prop_abutmentFiltration_of_forall_prop_cokernel (ModuleCat.isFG.{v, u} R) hab
      ((ModuleCat.isFG_iff _).2 ha) fun q hq ↦ (ModuleCat.isFG_iff _).2 (hcok q hq)

/-- Over any ring `R`, if the filtration of `X.abutment n` has finitely generated starting piece at
`a`, exhausts the abutment at `b ≥ a`, and has finitely generated graded pieces on `Ico a b`, then
`X.abutment n` is finitely generated. -/
theorem finite_abutment_of_forall_finite_cokernel {a b n : ℤ} (hab : a ≤ b)
    (ha : Module.Finite R (X.abutmentFiltration a n)) (hb : IsIso (X.abutmentFiltrationι b n))
    (hcok : ∀ q ∈ Finset.Ico a b, Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n))) :
    Module.Finite R (X.abutment n) :=
  (ModuleCat.isFG_iff _).1 <|
    X.prop_abutment_of_forall_prop_cokernel (ModuleCat.isFG.{v, u} R) hab
      ((ModuleCat.isFG_iff _).2 ha) hb fun q hq ↦ (ModuleCat.isFG_iff _).2 (hcok q hq)

/-- Over a ring satisfying `StrongRankCondition` and `HasRankNullity`, if `F_a H^n` is zero and
every graded piece `F_{q+1} H^n / F_q H^n` for `a ≤ q < b` is finitely generated, then the rank of
`F_b H^n` is the sum of the ranks of those graded pieces. -/
theorem finrank_abutmentFiltration_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b n : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a n))
    (hcok : ∀ q ∈ Finset.Ico a b, Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n))) :
    finrank R (X.abutmentFiltration b n) =
      ∑ q ∈ Finset.Ico a b, finrank R ↥(cokernel (X.abutmentFiltrationMap q n)) := by
  have hfin_a : Module.Finite R (X.abutmentFiltration a n) :=
    have := ModuleCat.subsingleton_of_isZero ha
    inferInstance
  induction b, hab using Int.leInduction with
  | base =>
    simp [ModuleCat.finrank_eq_zero_of_isZero ha]
  | succ q haq ih =>
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap q n)).X₂ :=
      X.finite_abutmentFiltration_of_forall_finite_cokernel (Int.le_add_one haq) hfin_a hcok
    have hadd :=
      (TauCeti.cokernelSequence_shortExact (X.abutmentFiltrationMap q n)).moduleCat_finrank_eq_add
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one haq,
      ← ih (fun i hi ↦ hcok i (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hi))]
    exact hadd

/-- Over a ring satisfying `StrongRankCondition` and `HasRankNullity`, if the filtration of
`X.abutment n` starts at `0` at `a`, exhausts the abutment at `b ≥ a`, and has finitely generated
graded pieces on `Ico a b`, then the rank of `X.abutment n` is the sum of the ranks of those graded
pieces. -/
theorem finrank_abutment_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b n : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a n))
    (hb : IsIso (X.abutmentFiltrationι b n))
    (hcok : ∀ q ∈ Finset.Ico a b, Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n))) :
    finrank R (X.abutment n) =
      ∑ q ∈ Finset.Ico a b, finrank R ↥(cokernel (X.abutmentFiltrationMap q n)) := by
  have := hb
  rw [← (asIso (X.abutmentFiltrationι b n)).toLinearEquiv.finrank_eq]
  exact X.finrank_abutmentFiltration_eq_sum_Ico hab ha hcok

end CategoryTheory.Abelian.SpectralObject
