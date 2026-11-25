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

/-!
# Dimensions along the filtration of the abutment of a spectral object

Let `X` be a spectral object indexed by `EInt` in the category of modules over a Noetherian ring
`k` with the rank-nullity property (`HasRankNullity`), such as a division ring or `ℤ`. Its
abutment `H^n(⊥ ≤ ⊤)` in degree `n` is filtered by the pieces `F_q H^n`
(`CategoryTheory.Abelian.SpectralObject.abutmentFiltration`), whose graded pieces
`F_{q+1} H^n / F_q H^n` are the limit objects `E∞` of the spectral sequence
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`). When the abutment is finitely
generated, `Module.finrank` is additive along this filtration: if `F_a H^n = 0`, then
`dim F_b H^n` is the sum of the dimensions of the graded pieces `F_{q+1} H^n / F_q H^n` for
`a ≤ q < b` (`CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum`), and if
moreover `F_b H^n` is the whole abutment, so is `dim H^n`
(`CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum`).

For a convergent spectral sequence this is the numerical form of convergence: the dimension of
the abutment is the sum of the dimensions of the objects of total degree `n` on a late enough page.
For the spectral sequence of a finite filtration of a space this says that the dimension of the
singular homology of the space is the sum of the dimensions of the limit page in that degree
(`Monotone.finrank_singularHomology_eq_sum_finrank_filteredSpaceSpectralSequence_page_X`).

## Main results

* `CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum`: the dimension of a
  piece of a filtration starting at zero is the sum of the dimensions of the graded pieces below
  it.
* `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum`: the dimension of the abutment
  is the sum of the dimensions of the graded pieces of a finite filtration.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, convergence of the spectral sequence of a filtered complex.
-/

public section

universe v

namespace CategoryTheory.Abelian.SpectralObject

open Limits Module

variable {k : Type*} [Ring k] [IsNoetherianRing k] (X : SpectralObject (ModuleCat.{v} k) EInt)

/-- The `q`th piece of the filtration of the abutment embeds into the abutment, so it is finitely
generated when the abutment is. -/
instance finite_abutmentFiltration (q n : ℤ) [Module.Finite k (X.abutment n)] :
    Module.Finite k (X.abutmentFiltration q n) :=
  Module.Finite.of_injective (X.abutmentFiltrationι q n).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

variable [StrongRankCondition k] [HasRankNullity.{v} k]

/-- **Dimensions along the filtration of the abutment.** If the abutment of `X` in degree `n` is
finitely generated and the `a`th piece `F_a H^n` of its filtration vanishes, then for `a ≤ b` the
dimension of `F_b H^n` is the sum, over `a ≤ q < b`, of the dimensions of the graded pieces
`F_{q+1} H^n / F_q H^n`. -/
theorem finrank_abutmentFiltration_eq_sum {a b n : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a n)) [Module.Finite k (X.abutment n)] :
    finrank k (X.abutmentFiltration b n) =
      ∑ q ∈ Finset.Ico a b, finrank k (cokernel (X.abutmentFiltrationMap q n) : ModuleCat k) := by
  induction b, hab using Int.leInduction with
  | base => simp [ModuleCat.finrank_eq_zero_of_isZero ha]
  | succ b hab ih =>
    -- `F_b H^n ⟶ F_{b+1} H^n ⟶ F_{b+1} H^n / F_b H^n` is short exact.
    have hS : (ShortComplex.mk _ _ (cokernel.condition (X.abutmentFiltrationMap b n))).ShortExact :=
      { exact := ShortComplex.exact_cokernel _ }
    rw [hS.moduleCat_finrank_eq_add, ← Finset.sum_Ico_add_eq_sum_Ico_add_one hab, ← ih]

/-- **The dimension of the abutment of a finite filtration.** If the abutment of `X` in degree `n`
is finitely generated, the `a`th piece `F_a H^n` of its filtration vanishes and the `b`th piece is
the whole abutment, then for `a ≤ b` the dimension of the abutment is the sum, over `a ≤ q < b`,
of the dimensions of the graded pieces `F_{q+1} H^n / F_q H^n`. -/
theorem finrank_abutment_eq_sum {a b n : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a n))
    (hb : IsIso (X.abutmentFiltrationι b n)) [Module.Finite k (X.abutment n)] :
    finrank k (X.abutment n) =
      ∑ q ∈ Finset.Ico a b, finrank k (cokernel (X.abutmentFiltrationMap q n) : ModuleCat k) := by
  rw [← (asIso (X.abutmentFiltrationι b n)).toLinearEquiv.finrank_eq,
    X.finrank_abutmentFiltration_eq_sum hab ha]

end CategoryTheory.Abelian.SpectralObject
