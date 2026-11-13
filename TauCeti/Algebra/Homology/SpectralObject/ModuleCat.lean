/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Finsupp
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.SpectralObject.Abutment

/-!
# Finiteness and rank of the abutment of a spectral object of modules

For a spectral object `X` in `ModuleCat R` indexed by `EInt`, each step
`0 ⟶ F_q H^m ⟶ F_{q+1} H^m ⟶ cokernel (X.abutmentFiltrationMap q m) ⟶ 0` of the abutment filtration
is short exact
(`CategoryTheory.Abelian.SpectralObject.shortExact_cokernelSequence_abutmentFiltrationMap`).
Inducting across a finite filtration `a ≤ q < b` starting at `0` therefore passes finite generation
and, over any ring satisfying the strong rank condition and rank--nullity, additivity of
`Module.finrank` from the graded pieces to the filtration stages and to the abutment:

* `CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration_of_finite_cokernel` and
  `CategoryTheory.Abelian.SpectralObject.finite_abutment_of_finite_cokernel`: over any ring `R`,
  finite generation of the graded pieces on `Finset.Ico a b` implies finite generation of
  `X.abutmentFiltration b m` and of `X.abutment m`.
* `CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum_Ico` and
  `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`: over a ring `R` with
  `[StrongRankCondition R]` and `[HasRankNullity R]`, the `finrank` of `X.abutmentFiltration b m`
  (and of `X.abutment m` when `X.abutmentFiltrationι b m` is an isomorphism) equals the sum over
  `q ∈ Finset.Ico a b` of the `finrank`s of `cokernel (X.abutmentFiltrationMap q m)`.

## References

* Jean-Pierre Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54
  (1951), 425--505, Chapter II, Section 4.
* John McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.6 and Exercise 1.1.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace CategoryTheory.Abelian.SpectralObject

variable {R : Type u} [Ring R] (X : SpectralObject (ModuleCat.{v} R) EInt)

/-- Over any ring, if `F_a H^m = 0` and every graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b`
is finitely generated, then `F_b H^m` is finitely generated. -/
theorem finite_abutmentFiltration_of_finite_cokernel {a b m : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a m))
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    Module.Finite R (X.abutmentFiltration b m) := by
  revert hfin
  induction b, hab using Int.leInduction with
  | base =>
    intro _
    have := ModuleCat.subsingleton_of_isZero ha
    infer_instance
  | succ s has ih =>
    intro hfin
    have hS := X.shortExact_cokernelSequence_abutmentFiltrationMap s m
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap s m)).X₁ :=
      ih fun q hq ↦ hfin q (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hq)
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap s m)).X₃ :=
      hfin s (Finset.mem_Ico.2 ⟨has, by lia⟩)
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact)
      hS.moduleCat_surjective_g

/-- Over any ring, if the filtration of `X.abutment m` starts at `0` at `a`, reaches the whole
abutment at `b`, and has finitely generated graded pieces for `a ≤ q < b`, then `X.abutment m` is
finitely generated. -/
theorem finite_abutment_of_finite_cokernel {a b m : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a m)) [IsIso (X.abutmentFiltrationι b m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    Module.Finite R (X.abutment m) := by
  have := X.finite_abutmentFiltration_of_finite_cokernel hab ha hfin
  exact Module.Finite.equiv (asIso (X.abutmentFiltrationι b m)).toLinearEquiv

/-- Over a ring satisfying the strong rank condition and rank--nullity, if `F_a H^m = 0` and every
graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b` is finitely generated, then the rank of
`F_b H^m` is the sum of the ranks of those graded pieces. -/
theorem finrank_abutmentFiltration_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b m : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a m))
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    finrank R (X.abutmentFiltration b m) =
      ∑ q ∈ Finset.Ico a b, finrank R ↑(cokernel (X.abutmentFiltrationMap q m)) := by
  revert hfin
  induction b, hab using Int.leInduction with
  | base =>
    intro _
    simp [ModuleCat.finrank_eq_zero_of_isZero ha]
  | succ s has ih =>
    intro hfin
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap s m)).X₂ :=
      X.finite_abutmentFiltration_of_finite_cokernel (Int.le_add_one has) ha hfin
    rw [show Finset.Ico a (s + 1) = insert s (Finset.Ico a s) by grind,
      Finset.sum_insert Finset.right_notMem_Ico,
      ← ih fun q hq ↦ hfin q (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hq)]
    exact ((X.shortExact_cokernelSequence_abutmentFiltrationMap s m).moduleCat_finrank_eq_add).trans
      (add_comm _ _)

/-- **Rank of the abutment from its graded pieces.** Over a ring satisfying the strong rank
condition and rank--nullity, if the filtration of `X.abutment m` starts at `0` at `a`, reaches the
whole abutment at `b`, and has finitely generated graded pieces for `a ≤ q < b`, then the rank of
`X.abutment m` is the sum of the ranks of those graded pieces. -/
theorem finrank_abutment_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b m : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a m))
    [IsIso (X.abutmentFiltrationι b m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    finrank R (X.abutment m) =
      ∑ q ∈ Finset.Ico a b, finrank R ↑(cokernel (X.abutmentFiltrationMap q m)) := by
  rw [← (asIso (X.abutmentFiltrationι b m)).toLinearEquiv.finrank_eq]
  exact X.finrank_abutmentFiltration_eq_sum_Ico hab ha hfin

end CategoryTheory.Abelian.SpectralObject
