/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.SpectralObject.Abutment
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.SuccPred.Int
import TauCeti.Algebra.Homology.SpectralObject.ModuleCat

/-!
# Dimensions along the filtration of the abutment of a spectral object

Let `X` be a spectral object indexed by `EInt` in the category of modules over a ring `R` with the
strong rank condition (`StrongRankCondition`) and the rank-nullity property (`HasRankNullity`), such
as a division ring or `ℤ`. Its abutment `H^n(⊥ ≤ ⊤)` in degree `n` is filtered by the pieces
`F_q H^n` (`CategoryTheory.Abelian.SpectralObject.abutmentFiltration`), whose graded pieces
`F_{q+1} H^n / F_q H^n` are the limit objects `E∞` of the spectral sequence
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`). When the starting stage `F_a H^m` and
the graded pieces for `a ≤ q < b` are finitely generated, `Module.finrank` is additive along this
filtration: `finrank R (F_b H^m)` equals `finrank R (F_a H^m)` plus the sum of the ranks of the
graded pieces (`CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_add_sum_Ico`),
and when `F_a H^m = 0` and `F_b H^m` is the whole abutment, `finrank R (H^m)` equals that sum
(`CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`). Over a Noetherian ring, a
finitely generated abutment guarantees finite generation of all filtration pieces
(`CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration`).

For a convergent spectral sequence this is the numerical form of convergence: the dimension of
the abutment is the sum of the dimensions of the objects of total degree `n` on a late enough page.
For the spectral sequence of a finite filtration of a space this says that the dimension of the
singular homology of the space is the sum of the dimensions of the limit page in that degree
(`Monotone.finrank_singularHomology_eq_sum_finrank_filteredSpaceSpectralSequence_page_X`).

## Main results

* `CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration`: over a Noetherian ring, every
  filtration piece is finitely generated when the abutment is.
* `CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_add_sum_Ico`: the rank of a
  piece of a filtration is the rank of an earlier piece plus the sum of the ranks of the graded
  pieces between them.
* `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`: the rank of the abutment
  is the sum of the ranks of the graded pieces of a finite filtration.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, convergence of the spectral sequence of a filtered complex.
-/

public section

universe u v

namespace CategoryTheory.Abelian.SpectralObject

open Limits Module

section Noetherian

variable {k : Type*} [Ring k] [IsNoetherianRing k] (X : SpectralObject (ModuleCat.{v} k) EInt)

/-- The `q`th piece of the filtration of the abutment embeds into the abutment, so it is finitely
generated when the abutment is. -/
instance finite_abutmentFiltration (q n : ℤ) [Module.Finite k (X.abutment n)] :
    Module.Finite k (X.abutmentFiltration q n) :=
  Module.Finite.of_injective (X.abutmentFiltrationι q n).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

end Noetherian

section Finrank

variable {R : Type u} [Ring R] (X : SpectralObject (ModuleCat.{v} R) EInt)
  [StrongRankCondition R] [HasRankNullity.{v} R]

/-- Over a ring satisfying the strong rank condition and rank--nullity, if `F_a H^m` and every
graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b` are finitely generated, then for any `a ≤ b`
the rank of `F_b H^m` is the rank of `F_a H^m` plus the sum of the ranks of those graded pieces. -/
theorem finrank_abutmentFiltration_eq_add_sum_Ico
    {a b m : ℤ} (hab : a ≤ b) [Module.Finite R (X.abutmentFiltration a m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    finrank R (X.abutmentFiltration b m) =
      finrank R (X.abutmentFiltration a m) +
        ∑ q ∈ Finset.Ico a b, finrank R ↑(cokernel (X.abutmentFiltrationMap q m)) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ s has ih =>
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap s m)).X₂ := by
      rw [ShortComplex.cokernelSequence_X₂]
      exact X.finite_abutmentFiltration_of_finite_cokernel (Int.le_add_one has) hfin
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one has, ← add_assoc,
      ← ih fun q hq ↦ hfin q (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hq)]
    exact (TauCeti.cokernelSequence_shortExact
      (X.abutmentFiltrationMap s m)).moduleCat_finrank_eq_add

/-- **Rank of the abutment from its graded pieces.** Over a ring satisfying the strong rank
condition and rank--nullity, if the filtration of `X.abutment m` starts at `0` at `a`, reaches the
whole abutment at `b`, and has finitely generated graded pieces for `a ≤ q < b`, then the rank of
`X.abutment m` is the sum of the ranks of those graded pieces. -/
theorem finrank_abutment_eq_sum_Ico
    {a b m : ℤ} (ha : IsZero (X.abutmentFiltration a m))
    [IsIso (X.abutmentFiltrationι b m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    finrank R (X.abutment m) =
      ∑ q ∈ Finset.Ico a b, finrank R ↑(cokernel (X.abutmentFiltrationMap q m)) := by
  rw [← (asIso (X.abutmentFiltrationι b m)).toLinearEquiv.finrank_eq]
  rcases le_total a b with hab | hba
  · have := ModuleCat.subsingleton_of_isZero ha
    rw [X.finrank_abutmentFiltration_eq_add_sum_Ico hab hfin,
      ModuleCat.finrank_eq_zero_of_isZero ha, zero_add]
  · rw [Finset.Ico_eq_empty_of_le hba, Finset.sum_empty,
      ModuleCat.finrank_eq_zero_of_isZero (X.isZero_abutmentFiltration_of_le hba ha)]

end Finrank

end CategoryTheory.Abelian.SpectralObject
