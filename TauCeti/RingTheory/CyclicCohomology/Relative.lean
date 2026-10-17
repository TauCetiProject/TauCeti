/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import Mathlib.Algebra.Algebra.Unitization

/-!
# Relative cyclic cohomology of a nonunital algebra

For a nonunital algebra `A`, its cyclic cohomology is not the cohomology of the cyclic cochains
on `A` itself. It is the relative theory of the forced unitization `Unitization R A` with respect
to its scalar subalgebra. In degree `n`, the relative cyclic cochains are the kernel of restriction
along the scalar inclusion

`R → Unitization R A`.

The Hochschild coboundary preserves this kernel, so the relative cochains form a cochain complex.
The augmentation `Unitization R A → R` splits scalar restriction; this records explicitly the
contravariant splitting used by the relative theory.

## Main definitions

* `TauCeti.unitizationScalarRestriction`: restriction of cyclic cochains to the scalar subalgebra.
* `TauCeti.relativeCyclicCochains`: the kernel of scalar restriction.
* `TauCeti.relativeCyclicHochschildCoboundary`: the Hochschild coboundary on relative cochains.
* `TauCeti.relativeCyclicCochainComplex`: the relative cyclic cochain complex.
* `TauCeti.relativeCyclicCohomology`: the relative cyclic cohomology of a nonunital algebra.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §1.4.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

section Cochains

variable (R : Type*) (A : Type u) (M : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Restriction of cyclic cochains on the forced unitization to its scalar subalgebra. -/
def unitizationScalarRestriction (n : ℕ) :
    cyclicCochains R (Unitization R A) M n →ₗ[R] cyclicCochains R R M n :=
  cyclicCochainsMap M
    ((Algebra.ofId R (Unitization R A)).toNonUnitalAlgHom :
      R →ₗ[R] Unitization R A) n

/-- Pullback of scalar cyclic cochains along the augmentation of the forced unitization. -/
def unitizationAugmentationPullback (n : ℕ) :
    cyclicCochains R R M n →ₗ[R] cyclicCochains R (Unitization R A) M n :=
  cyclicCochainsMap M ((Unitization.fstHom R A).toNonUnitalAlgHom :
    Unitization R A →ₗ[R] R) n

/-- Scalar restriction evaluates a cochain on scalar arguments. -/
@[simp]
theorem unitizationScalarRestriction_apply (n : ℕ)
    (phi : cyclicCochains R (Unitization R A) M n) (a : Fin (n + 1) → R) :
    (unitizationScalarRestriction R A M n phi :
        MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) a =
      (phi : MultilinearMap R (fun _ : Fin (n + 1) ↦ Unitization R A) M)
        (fun i ↦ algebraMap R (Unitization R A) (a i)) := by
  simp only [unitizationScalarRestriction, coe_cyclicCochainsMap_apply,
    MultilinearMap.compLinearMap_apply]
  congr 1

/-- Pullback along the augmentation evaluates a scalar cochain on the scalar components. -/
@[simp]
theorem unitizationAugmentationPullback_apply (n : ℕ) (phi : cyclicCochains R R M n)
    (a : Fin (n + 1) → Unitization R A) :
    (unitizationAugmentationPullback R A M n phi :
        MultilinearMap R (fun _ : Fin (n + 1) ↦ Unitization R A) M) a =
      (phi : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) (fun i ↦ (a i).fst) := by
  simp only [unitizationAugmentationPullback, coe_cyclicCochainsMap_apply,
    MultilinearMap.compLinearMap_apply]
  rfl

/-- Pullback along the augmentation is a right inverse to scalar restriction. -/
@[simp]
theorem unitizationScalarRestriction_comp_unitizationAugmentationPullback (n : ℕ) :
    unitizationScalarRestriction R A M n ∘ₗ unitizationAugmentationPullback R A M n =
      LinearMap.id := by
  apply LinearMap.ext
  intro phi
  apply Subtype.ext
  apply MultilinearMap.ext
  intro a
  simp [Unitization.algebraMap_eq_inl]

/-- Scalar restriction is surjective, split by pullback along the augmentation. -/
theorem unitizationScalarRestriction_surjective (n : ℕ) :
    Function.Surjective (unitizationScalarRestriction R A M n) :=
  Function.RightInverse.surjective (LinearMap.congr_fun
    (unitizationScalarRestriction_comp_unitizationAugmentationPullback R A M n))

/-- The relative cyclic `n`-cochains of a nonunital algebra: cyclic cochains on its forced
unitization which vanish when all arguments are scalar. -/
def relativeCyclicCochains (n : ℕ) :
    Submodule R (cyclicCochains R (Unitization R A) M n) :=
  LinearMap.ker (unitizationScalarRestriction R A M n)

/-- A cyclic cochain on the forced unitization is relative exactly when its scalar restriction
vanishes. -/
@[simp]
theorem mem_relativeCyclicCochains_iff {n : ℕ}
    {phi : cyclicCochains R (Unitization R A) M n} :
    phi ∈ relativeCyclicCochains R A M n ↔ unitizationScalarRestriction R A M n phi = 0 :=
  LinearMap.mem_ker

/-- The Hochschild coboundary of a relative cyclic cochain is relative. -/
theorem cyclicHochschildCoboundary_mem_relativeCyclicCochains {n : ℕ}
    (phi : relativeCyclicCochains R A M n) :
    cyclicHochschildCoboundary R (Unitization R A) M n phi ∈
      relativeCyclicCochains R A M (n + 1) := by
  rw [mem_relativeCyclicCochains_iff]
  have hphi : cyclicCochainsMap M
      ((Algebra.ofId R (Unitization R A)).toNonUnitalAlgHom :
        R →ₗ[R] Unitization R A) n phi = 0 := by
    simpa only [unitizationScalarRestriction] using
      (mem_relativeCyclicCochains_iff (R := R) (A := A) (M := M)).mp phi.property
  rw [unitizationScalarRestriction,
    ← cyclicHochschildCoboundary_cyclicCochainsMap
    (Algebra.ofId R (Unitization R A)).toNonUnitalAlgHom, hphi, map_zero]

/-- The Hochschild coboundary restricted to relative cyclic cochains. -/
def relativeCyclicHochschildCoboundary (n : ℕ) :
    relativeCyclicCochains R A M n →ₗ[R] relativeCyclicCochains R A M (n + 1) where
  toFun phi := ⟨cyclicHochschildCoboundary R (Unitization R A) M n phi,
    cyclicHochschildCoboundary_mem_relativeCyclicCochains R A M phi⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The relative Hochschild coboundary has the ordinary cyclic Hochschild coboundary as its
underlying cochain. -/
@[simp]
theorem coe_relativeCyclicHochschildCoboundary_apply (n : ℕ)
    (phi : relativeCyclicCochains R A M n) :
    (relativeCyclicHochschildCoboundary R A M n phi :
      cyclicCochains R (Unitization R A) M (n + 1)) =
      cyclicHochschildCoboundary R (Unitization R A) M n phi :=
  by simp [relativeCyclicHochschildCoboundary]

/-- The relative Hochschild coboundary squares to zero. -/
theorem relativeCyclicHochschildCoboundary_relativeCyclicHochschildCoboundary (n : ℕ)
    (phi : relativeCyclicCochains R A M n) :
    relativeCyclicHochschildCoboundary R A M (n + 1)
        (relativeCyclicHochschildCoboundary R A M n phi) = 0 := by
  apply Subtype.ext
  exact cyclicHochschildCoboundary_cyclicHochschildCoboundary
    R (Unitization R A) M (phi : cyclicCochains R (Unitization R A) M n)

/-- The relative Hochschild coboundary squares to zero as a composite of linear maps. -/
theorem relativeCyclicHochschildCoboundary_comp_relativeCyclicHochschildCoboundary (n : ℕ) :
    relativeCyclicHochschildCoboundary R A M (n + 1) ∘ₗ
      relativeCyclicHochschildCoboundary R A M n = 0 := by
  apply LinearMap.ext
  intro phi
  exact relativeCyclicHochschildCoboundary_relativeCyclicHochschildCoboundary R A M n phi

end Cochains

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The relative cyclic cochain complex of a nonunital algebra. Its degree-`n` term is the kernel
of scalar restriction on cyclic cochains of the forced unitization. -/
def relativeCyclicCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (relativeCyclicCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (relativeCyclicHochschildCoboundary R A M n))
    fun n ↦ ModuleCat.hom_ext
      (relativeCyclicHochschildCoboundary_comp_relativeCyclicHochschildCoboundary R A M n)

/-- The degree-`n` term of the relative cyclic cochain complex is the module of relative cyclic
`n`-cochains. -/
def relativeCyclicCochainComplexXIso (n : ℕ) :
    (relativeCyclicCochainComplex R A M).X n ≅
      ModuleCat.of R (relativeCyclicCochains R A M n) :=
  Iso.refl _

/-- Under the canonical identifications of the terms, the differential of the relative cyclic
cochain complex is the relative Hochschild coboundary. -/
@[reassoc, elementwise]
theorem relativeCyclicCochainComplex_d (n : ℕ) :
    (relativeCyclicCochainComplex R A M).d n (n + 1) ≫
        (relativeCyclicCochainComplexXIso R A M (n + 1)).hom =
      (relativeCyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (relativeCyclicHochschildCoboundary R A M n) := by
  simp [relativeCyclicCochainComplex, relativeCyclicCochainComplexXIso]

/-- The relative cyclic cohomology of a nonunital algebra, defined as the cohomology of the
kernel of scalar restriction on the cyclic cochain complex of its forced unitization. -/
abbrev relativeCyclicCohomology (n : ℕ) : ModuleCat R :=
  (relativeCyclicCochainComplex R A M).homology n

end Complex


section ComplexSplitting

variable (R A M : Type u) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Restriction of cyclic cochain complexes along the scalar inclusion. -/
def unitizationScalarRestrictionComplexMap :
    cyclicCochainComplex R (Unitization R A) M ⟶ cyclicCochainComplex R R M :=
  cyclicCochainComplexMap M (Algebra.ofId R (Unitization R A)).toNonUnitalAlgHom

/-- Pullback of cyclic cochain complexes along the augmentation. -/
def unitizationAugmentationPullbackComplexMap :
    cyclicCochainComplex R R M ⟶ cyclicCochainComplex R (Unitization R A) M :=
  cyclicCochainComplexMap M (Unitization.fstHom R A).toNonUnitalAlgHom

/-- Pullback along the augmentation splits scalar restriction as a cochain map. -/
@[simp]
theorem unitizationAugmentationPullbackComplexMap_comp_unitizationScalarRestrictionComplexMap :
    unitizationAugmentationPullbackComplexMap R A M ≫
        unitizationScalarRestrictionComplexMap R A M =
      𝟙 (cyclicCochainComplex R R M) := by
  simp only [unitizationAugmentationPullbackComplexMap,
    unitizationScalarRestrictionComplexMap]
  rw [← cyclicCochainComplexMap_comp]
  have h : (Unitization.fstHom R A).toNonUnitalAlgHom.comp
      (Algebra.ofId R (Unitization R A)).toNonUnitalAlgHom = NonUnitalAlgHom.id R R := by
    ext r
    change (algebraMap R (Unitization R A) r).fst = r
    simp only [Unitization.algebraMap_eq_inl, Unitization.fst_inl]
  rw [h, cyclicCochainComplexMap_id]

end ComplexSplitting

end TauCeti
