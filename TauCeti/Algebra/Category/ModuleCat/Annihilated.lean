/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Modules annihilated by an idempotent ideal

For an idempotent ideal `I` of a commutative ring `R`, modules annihilated by `I` form a
Serre class. This supplies the Serre class of almost zero modules used to construct the
almost category. No flatness assumption on `I` or its tensor square is needed.

Idempotence is necessary: closure under extensions, applied to the kernel sequence of
`R / I² → R / I`, forces `I` to annihilate `R / I²`, hence `I ⊆ I²`.
Thus annihilation by an ideal is a Serre property exactly for idempotent ideals.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §2.2, (2.2.2).
* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2.
-/

public section

universe u v

open CategoryTheory

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Modules killed by an idempotent ideal form a Serre class, in any module universe. -/
theorem isSerreClass_isTorsionBySet (I : Ideal R) (hI : IsIdempotentElem I) :
    ObjectProperty.IsSerreClass
      (fun M : ModuleCat.{v} R ↦ Module.IsTorsionBySet R M (I : Set R)) where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    fun _ _ ↦ Subsingleton.elim _ _⟩
  prop_of_mono {M N} f hf hN := by
    rw [Module.isTorsionBySet_iff_subset_annihilator] at hN ⊢
    exact hN.trans (f.hom.annihilator_le_of_injective (ModuleCat.mono_iff_injective f |>.mp hf))
  prop_of_epi {M N} f hf hM := by
    rw [Module.isTorsionBySet_iff_subset_annihilator] at hM ⊢
    exact hM.trans (f.hom.annihilator_le_of_surjective (ModuleCat.epi_iff_surjective f |>.mp hf))
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [Module.isTorsionBySet_iff_subset_annihilator]
    rw [← hI.eq]
    refine mul_le.mpr fun a ha b hb ↦ Module.mem_annihilator.mpr fun x ↦ ?_
    obtain ⟨y, hy⟩ := S.moduleCat_exact_iff.mp hS.exact (b • x) (by
      rw [map_smul]
      exact h₃ (a := ⟨b, hb⟩))
    rw [mul_smul, ← hy, ← map_smul, h₁ (a := ⟨a, ha⟩), map_zero]

/-- If modules killed by `I` are closed under extensions, then `I` is idempotent.
The kernel sequence of `R / I² → R / I` detects the obstruction. -/
theorem isIdempotentElem_of_isClosedUnderExtensions_isTorsionBySet (I : Ideal R)
    (h : ObjectProperty.IsClosedUnderExtensions
      (fun M : ModuleCat.{u} R ↦ Module.IsTorsionBySet R M (I : Set R))) : IsIdempotentElem I := by
  let f := (Quotient.factorₐ R (mul_le_left : I * I ≤ I)).toLinearMap
  have hf (r : R) : f (Quotient.mk (I * I) r) = Quotient.mk I r :=
    Quotient.factorₐ_apply_mk R (mul_le_left : I * I ≤ I) r
  have hker : Module.IsTorsionBySet R (LinearMap.ker f) (I : Set R) := by
    intro x a
    apply Subtype.ext
    obtain ⟨r, hr⟩ := Quotient.mk_surjective (x : R ⧸ (I * I))
    have hrI : r ∈ I := Quotient.eq_zero_iff_mem.mp (by
      rw [← hf, hr]
      exact x.2)
    simpa [← hr, Algebra.smul_def] using
      (Quotient.eq_zero_iff_mem.mpr (mul_mem_mul a.2 hrI))
  have hquot : Module.IsTorsionBySet R (R ⧸ I) (I : Set R) :=
    (Module.isTorsionBySet_quotient_iff I (I : Set R)).mpr fun r a ha ↦ I.mul_mem_right r ha
  have hmid : Module.IsTorsionBySet R (R ⧸ (I * I)) (I : Set R) :=
    h.prop_X₂_of_shortExact
      (LinearMap.shortExact_shortComplexKer (f := f)
        (Quotient.factor_surjective (mul_le_left : I * I ≤ I))) hker hquot
  exact (mul_le_left.antisymm fun r hr ↦ Quotient.eq_zero_iff_mem.mp (by
    simpa [Algebra.smul_def] using
      (hmid (x := Quotient.mk (I * I) 1) (a := ⟨r, hr⟩))) : I * I = I)

/-- Modules annihilated by `I` form a Serre class exactly when `I` is idempotent. -/
theorem isSerreClass_isTorsionBySet_iff (I : Ideal R) :
    ObjectProperty.IsSerreClass
      (fun M : ModuleCat.{u} R ↦ Module.IsTorsionBySet R M (I : Set R)) ↔
      IsIdempotentElem I :=
  ⟨fun h ↦ I.isIdempotentElem_of_isClosedUnderExtensions_isTorsionBySet
    h.toIsClosedUnderExtensions, I.isSerreClass_isTorsionBySet⟩

end Ideal
