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
import TauCeti.Algebra.Category.FGModuleCat.Exact
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Finiteness and dimensions along the filtration of the abutment of a spectral object

Let `X` be a spectral object indexed by `EInt` in `ModuleCat R`. Its abutment `H^n(⊥ ≤ ⊤)` in
degree `n` is filtered by the pieces `F_q H^n`
(`CategoryTheory.Abelian.SpectralObject.abutmentFiltration`), whose graded pieces
`F_{q+1} H^n / F_q H^n` are the limit objects `E∞` of the spectral sequence
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`).

Specializing `CategoryTheory.Abelian.SpectralObject.prop_abutmentFiltration_of_forall_prop_cokernel`
and `CategoryTheory.Abelian.SpectralObject.prop_abutment_of_forall_prop_cokernel` to the
extension-closed property `ModuleCat.isFG R` shows that over any ring `R`, finite generation passes
from `F_a H^n` and the graded pieces on `Ico a b` to `F_b H^n`
(`CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration_of_forall_finite_cokernel`) and,
when the filtration exhausts the abutment at `b`, to `X.abutment n`
(`CategoryTheory.Abelian.SpectralObject.finite_abutment_of_forall_finite_cokernel`). Over a ring
satisfying `StrongRankCondition` and `HasRankNullity` (such as a division ring or a commutative
domain, with no Noetherianity hypothesis), when `F_a H^n = 0` and every graded piece on `Ico a b`
is finitely generated, `finrank R (F_b H^n)` and (when exhaustive at `b`) `finrank R (X.abutment n)`
equal the sum of the ranks of the graded pieces over `Ico a b`
(`CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum_Ico`,
`CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`).

Conversely, over a Noetherian ring `k`, when the abutment itself is finitely generated, every
filtration piece `F_q H^n` and graded piece is finitely generated
(`CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration`), giving
`CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum` and
`CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum` directly from
`[Module.Finite k (X.abutment n)]`.

For a convergent spectral sequence this is the numerical form of convergence: the dimension of
the abutment is the sum of the dimensions of the objects of total degree `n` on a late enough page.
For the spectral sequence of a finite filtration of a space this says that the dimension of the
singular homology of the space is the sum of the dimensions of the limit page in that degree
(`Monotone.finrank_singularHomology_eq_sum_finrank_filteredSpaceSpectralSequence_page_X`).

## Main results

* `CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration_of_forall_finite_cokernel` and
  `CategoryTheory.Abelian.SpectralObject.finite_abutment_of_forall_finite_cokernel`: finite
  generation of a finitely filtered abutment from its starting piece and graded pieces.
* `CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum_Ico` and
  `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`: rank of a finitely filtered
  abutment from finitely generated graded pieces, without Noetherianity.
* `CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_sum` and
  `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum`: the same over a Noetherian ring
  assuming `[Module.Finite k (X.abutment n)]`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, convergence of the spectral sequence of a filtered complex.
-/

public section

universe u v

namespace CategoryTheory.Abelian.SpectralObject

open Limits Module

section Ring

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

end Ring

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
      ∑ q ∈ Finset.Ico a b, finrank k (cokernel (X.abutmentFiltrationMap q n) : ModuleCat k) :=
  X.finrank_abutmentFiltration_eq_sum_Ico hab ha fun q _ ↦
    Module.Finite.of_surjective (cokernel.π (X.abutmentFiltrationMap q n)).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)

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
