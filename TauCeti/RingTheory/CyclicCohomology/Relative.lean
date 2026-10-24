/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Algebra.Homology.ModuleCat.Basic

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
* `TauCeti.relativeCyclicCochainComplexι`: its inclusion as the kernel of scalar restriction.
* `TauCeti.relativeCyclicCocycles`, `TauCeti.relativeCyclicCoboundaries`: concrete cocycles and
  coboundaries.
* `TauCeti.relativeCyclicCohomology`: the relative cyclic cohomology of a nonunital algebra.
* `TauCeti.relativeCyclicCohomology.mk`: the class of a relative cyclic cocycle.
* `TauCeti.relativeCyclicCochainComplexMap`, `TauCeti.relativeCyclicCohomology.map`: pullback along
  a homomorphism of nonunital algebras.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §1.4.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace TauCeti

universe u v w

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
  -- The nonunital algebra homomorphism underlying `Algebra.ofId` evaluates as the scalar inclusion.
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
  -- The linear map underlying `Unitization.fstHom` evaluates as the first projection.
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
theorem mem_relativeCyclicCochains_iff {n : ℕ}
    {phi : cyclicCochains R (Unitization R A) M n} :
    phi ∈ relativeCyclicCochains R A M n ↔ unitizationScalarRestriction R A M n phi = 0 :=
  LinearMap.mem_ker

/-- A cyclic cochain on the forced unitization is relative exactly when it vanishes whenever all
its arguments are scalars. -/
@[simp]
theorem mem_relativeCyclicCochains_iff_forall {n : ℕ}
    {phi : cyclicCochains R (Unitization R A) M n} :
    phi ∈ relativeCyclicCochains R A M n ↔ ∀ a : Fin (n + 1) → R,
      (phi : MultilinearMap R (fun _ : Fin (n + 1) ↦ Unitization R A) M)
        (fun i ↦ algebraMap R (Unitization R A) (a i)) = 0 := by
  rw [mem_relativeCyclicCochains_iff, Subtype.ext_iff, MultilinearMap.ext_iff]
  simp

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
    relativeCyclicCochains R A M n →ₗ[R] relativeCyclicCochains R A M (n + 1) :=
  (cyclicHochschildCoboundary R (Unitization R A) M n).restrict fun phi hphi ↦
    cyclicHochschildCoboundary_mem_relativeCyclicCochains R A M ⟨phi, hphi⟩

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

section Cocycles

variable (R : Type*) (A : Type u) (M : Type*) [CommSemiring R] [NonUnitalSemiring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The relative cyclic `n`-cocycles: relative cochains annihilated by the relative Hochschild
coboundary. -/
def relativeCyclicCocycles (n : ℕ) : Submodule R (relativeCyclicCochains R A M n) :=
  LinearMap.ker (relativeCyclicHochschildCoboundary R A M n)

/-- A relative cyclic cochain is a cocycle exactly when its relative Hochschild coboundary
vanishes. -/
@[simp]
theorem mem_relativeCyclicCocycles_iff {n : ℕ} {φ : relativeCyclicCochains R A M n} :
    φ ∈ relativeCyclicCocycles R A M n ↔
      relativeCyclicHochschildCoboundary R A M n φ = 0 :=
  LinearMap.mem_ker

/-- The relative cyclic coboundaries: zero in degree zero, and in positive degree the image of the
relative Hochschild coboundary. -/
def relativeCyclicCoboundaries : (n : ℕ) → Submodule R (relativeCyclicCochains R A M n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (relativeCyclicHochschildCoboundary R A M n)

/-- There are no nonzero relative cyclic coboundaries in degree zero. -/
@[simp]
theorem relativeCyclicCoboundaries_zero : relativeCyclicCoboundaries R A M 0 = ⊥ := (rfl)

/-- In positive degree the relative cyclic coboundaries are the image of the relative Hochschild
coboundary. -/
theorem relativeCyclicCoboundaries_succ (n : ℕ) :
    relativeCyclicCoboundaries R A M (n + 1) =
      LinearMap.range (relativeCyclicHochschildCoboundary R A M n) :=
  (rfl)

/-- A relative cyclic cochain in positive degree is a coboundary exactly when it is the relative
Hochschild coboundary of a cochain in the preceding degree. -/
@[simp]
theorem mem_relativeCyclicCoboundaries_succ_iff {n : ℕ}
    {φ : relativeCyclicCochains R A M (n + 1)} :
    φ ∈ relativeCyclicCoboundaries R A M (n + 1) ↔
      ∃ ψ : relativeCyclicCochains R A M n,
        relativeCyclicHochschildCoboundary R A M n ψ = φ := by
  rw [relativeCyclicCoboundaries_succ, LinearMap.mem_range]

/-- Every relative cyclic coboundary is a relative cyclic cocycle. -/
theorem relativeCyclicCoboundaries_le_relativeCyclicCocycles (n : ℕ) :
    relativeCyclicCoboundaries R A M n ≤ relativeCyclicCocycles R A M n := by
  cases n with
  | zero => simp
  | succ n =>
    exact LinearMap.range_le_ker_iff.2
      (relativeCyclicHochschildCoboundary_comp_relativeCyclicHochschildCoboundary R A M n)

end Cocycles

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Relative cyclic cochains inherit their additive group structure from cyclic cochains. -/
instance relativeCyclicCochainsAddCommGroup (n : ℕ) :
    AddCommGroup (relativeCyclicCochains R A M n) :=
  (relativeCyclicCochains R A M n).addCommGroup

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

private theorem mem_relativeCyclicCocycles_iff_complex (n : ℕ)
    (φ : relativeCyclicCochains R A M n) :
    φ ∈ relativeCyclicCocycles R A M n ↔
      (relativeCyclicCochainComplex R A M).d n (n + 1)
        ((relativeCyclicCochainComplexXIso R A M n).inv φ) = 0 := by
  rw [mem_relativeCyclicCocycles_iff,
    (relativeCyclicCochainComplex R A M).moduleCat_d_inv_eq_zero_iff
      (relativeCyclicHochschildCoboundary R A M) (relativeCyclicCochainComplex_d R A M)]

private theorem mem_relativeCyclicCoboundaries_iff_complex (n : ℕ)
    (φ : relativeCyclicCochains R A M n) :
    φ ∈ relativeCyclicCoboundaries R A M n ↔
      ∃ y : (relativeCyclicCochainComplex R A M).X ((ComplexShape.up ℕ).prev n),
        (relativeCyclicCochainComplex R A M).d ((ComplexShape.up ℕ).prev n) n y =
          (relativeCyclicCochainComplexXIso R A M n).inv φ :=
  (relativeCyclicCochainComplex R A M).moduleCat_mem_iff_exists_d_eq_inv
    (relativeCyclicCoboundaries R A M) (relativeCyclicHochschildCoboundary R A M)
    (relativeCyclicCochainComplex_d R A M) (relativeCyclicCoboundaries_zero R A M)
    (relativeCyclicCoboundaries_succ R A M) n φ

private abbrev relativeToCycles (n : ℕ) (φ : relativeCyclicCocycles R A M n) :=
  (relativeCyclicCochainComplex R A M).moduleCatCyclesMk
    ((relativeCyclicCochainComplexXIso R A M n).inv φ.1) (n + 1) (CochainComplex.next ℕ n)
    ((mem_relativeCyclicCocycles_iff_complex R A M n φ.1).1 φ.2)

private theorem relative_iCycles_toCycles (n : ℕ) (φ : relativeCyclicCocycles R A M n) :
    (relativeCyclicCochainComplex R A M).iCycles n (relativeToCycles R A M n φ) =
      (relativeCyclicCochainComplexXIso R A M n).inv φ.1 :=
  (relativeCyclicCochainComplex R A M).iCycles_moduleCatCyclesMk _ _ _ _ _

namespace relativeCyclicCohomology

/-- The relative cyclic cohomology class of a relative cyclic cocycle. -/
def mk (n : ℕ) :
    relativeCyclicCocycles R A M n →ₗ[R] relativeCyclicCohomology R A M n :=
  (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (relativeCyclicCochainComplexXIso R A M)
    (mem_relativeCyclicCocycles_iff_complex R A M) n

private theorem mk_apply (n : ℕ) (φ : relativeCyclicCocycles R A M n) :
    mk R A M n φ =
      (relativeCyclicCochainComplex R A M).homologyπ n (relativeToCycles R A M n φ) :=
  (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_apply
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (relativeCyclicCochainComplexXIso R A M)
    (mem_relativeCyclicCocycles_iff_complex R A M) n φ

/-- Every relative cyclic cohomology class is represented by a relative cyclic cocycle. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) := by
  exact (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (relativeCyclicCochainComplexXIso R A M)
    (mem_relativeCyclicCocycles_iff_complex R A M) n

/-- A relative cyclic cocycle has zero cohomology class exactly when it is a relative cyclic
coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (φ : relativeCyclicCocycles R A M n) :
    mk R A M n φ = 0 ↔
      (φ : relativeCyclicCochains R A M n) ∈ relativeCyclicCoboundaries R A M n := by
  exact (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (relativeCyclicCoboundaries R A M) (relativeCyclicCochainComplexXIso R A M)
    (mem_relativeCyclicCocycles_iff_complex R A M)
    (mem_relativeCyclicCoboundaries_iff_complex R A M) n φ

/-- Two relative cyclic cocycles have the same class exactly when they differ by a relative
cyclic coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (φ ψ : relativeCyclicCocycles R A M n) :
    mk R A M n φ = mk R A M n ψ ↔
      (φ : relativeCyclicCochains R A M n) - ψ ∈ relativeCyclicCoboundaries R A M n := by
  exact (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_iff
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (relativeCyclicCoboundaries R A M) (relativeCyclicCochainComplexXIso R A M)
    (mem_relativeCyclicCocycles_iff_complex R A M)
    (mem_relativeCyclicCoboundaries_iff_complex R A M) n φ ψ

end relativeCyclicCohomology

end Complex

section Map

variable {R : Type*} {A : Type u} {B : Type v} {C : Type w} {M : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  [AddCommGroup M] [Module R M]

/-- Pullback along the induced map of unitizations preserves relative cyclic cochains. -/
theorem cyclicCochainsMap_mem_relativeCyclicCochains (f : A →ₙₐ[R] B) {n : ℕ}
    (φ : relativeCyclicCochains R B M n) :
    cyclicCochainsMap M ((Unitization.map (R := R) f).toLinearMap) n φ ∈
      relativeCyclicCochains R A M n := by
  rw [mem_relativeCyclicCochains_iff]
  apply Subtype.ext
  apply MultilinearMap.ext
  intro a
  rw [unitizationScalarRestriction_apply]
  simp only [coe_cyclicCochainsMap_apply, MultilinearMap.compLinearMap_apply,
    AlgHom.toLinearMap_apply, AlgHom.commutes]
  have hφ := (mem_relativeCyclicCochains_iff (R := R) (A := B) (M := M)).mp φ.2
  simpa only [unitizationScalarRestriction_apply, ZeroMemClass.coe_zero, zero_apply] using congrArg
      (fun ψ : cyclicCochains R R M n ↦
        (ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) a) hφ

variable (M) in
/-- Pullback of relative cyclic cochains along a homomorphism of nonunital algebras. -/
def relativeCyclicCochainsMap (f : A →ₙₐ[R] B) (n : ℕ) :
    relativeCyclicCochains R B M n →ₗ[R] relativeCyclicCochains R A M n :=
  LinearMap.codRestrict (relativeCyclicCochains R A M n)
    ((cyclicCochainsMap M ((Unitization.map (R := R) f).toLinearMap) n).comp
      (relativeCyclicCochains R B M n).subtype)
    (cyclicCochainsMap_mem_relativeCyclicCochains (R := R) (M := M) f)

/-- The underlying cyclic cochain of a relative pullback is the ordinary pullback along the
induced map of unitizations. -/
@[simp]
theorem coe_relativeCyclicCochainsMap_apply (f : A →ₙₐ[R] B) (n : ℕ)
    (φ : relativeCyclicCochains R B M n) :
    (relativeCyclicCochainsMap M f n φ : cyclicCochains R (Unitization R A) M n) =
      cyclicCochainsMap M ((Unitization.map (R := R) f).toLinearMap) n φ :=
  (rfl)

/-- Pullback along the identity is the identity on relative cyclic cochains. -/
@[simp]
theorem relativeCyclicCochainsMap_id (n : ℕ) :
    relativeCyclicCochainsMap M (NonUnitalAlgHom.id R A) n = LinearMap.id := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  simp [relativeCyclicCochainsMap]

/-- Pullback of relative cyclic cochains is contravariantly functorial. -/
theorem relativeCyclicCochainsMap_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) (n : ℕ) :
    relativeCyclicCochainsMap M (g.comp f) n =
      relativeCyclicCochainsMap M f n ∘ₗ relativeCyclicCochainsMap M g n := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  simp only [coe_relativeCyclicCochainsMap_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [Unitization.map_comp]
  exact LinearMap.congr_fun
    (cyclicCochainsMap_comp M (Unitization.map (R := R) f).toLinearMap
      (Unitization.map (R := R) g).toLinearMap n) φ

/-- Relative pullback commutes with the relative Hochschild coboundary. -/
theorem relativeCyclicHochschildCoboundary_relativeCyclicCochainsMap
    (f : A →ₙₐ[R] B) (n : ℕ) (φ : relativeCyclicCochains R B M n) :
    relativeCyclicHochschildCoboundary R A M n (relativeCyclicCochainsMap M f n φ) =
      relativeCyclicCochainsMap M f (n + 1)
        (relativeCyclicHochschildCoboundary R B M n φ) := by
  apply Subtype.ext
  exact cyclicHochschildCoboundary_cyclicCochainsMap
    (Unitization.map (R := R) f).toNonUnitalAlgHom
    (φ : cyclicCochains R (Unitization R B) M n)

/-- Pullback of a relative cyclic cocycle is a relative cyclic cocycle. -/
theorem relativeCyclicCochainsMap_mem_relativeCyclicCocycles (f : A →ₙₐ[R] B) {n : ℕ}
    (φ : relativeCyclicCocycles R B M n) :
    relativeCyclicCochainsMap M f n φ ∈ relativeCyclicCocycles R A M n := by
  rw [mem_relativeCyclicCocycles_iff,
    relativeCyclicHochschildCoboundary_relativeCyclicCochainsMap, φ.2, map_zero]

end Map

section ComplexMap

variable {R : Type*} {A B C : Type u} {M : Type*} [CommRing R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  [AddCommGroup M] [Module R M]

variable (M) in
/-- The cochain map between relative cyclic cochain complexes induced contravariantly by a
homomorphism of nonunital algebras. -/
def relativeCyclicCochainComplexMap (f : A →ₙₐ[R] B) :
    relativeCyclicCochainComplex R B M ⟶ relativeCyclicCochainComplex R A M where
  f n := ModuleCat.ofHom (relativeCyclicCochainsMap M f n)
  comm' := by
    rintro n _ rfl
    ext φ : 2
    simp only [relativeCyclicCochainComplex, CochainComplex.of_d, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom]
    exact relativeCyclicHochschildCoboundary_relativeCyclicCochainsMap
      (R := R) (M := M) f n φ

/-- The components of the relative cochain-complex map are the pullback maps on relative
cochains. -/
@[reassoc, elementwise]
theorem relativeCyclicCochainComplexMap_f (f : A →ₙₐ[R] B) (n : ℕ) :
    (relativeCyclicCochainComplexMap M f).f n ≫
        (relativeCyclicCochainComplexXIso R A M n).hom =
      (relativeCyclicCochainComplexXIso R B M n).hom ≫
        ModuleCat.ofHom (relativeCyclicCochainsMap M f n) :=
  (rfl)

/-- The identity homomorphism induces the identity relative cochain map. -/
@[simp]
theorem relativeCyclicCochainComplexMap_id :
    relativeCyclicCochainComplexMap M (NonUnitalAlgHom.id R A) =
      𝟙 (relativeCyclicCochainComplex R A M) := by
  ext n : 1
  dsimp only [relativeCyclicCochainComplexMap, HomologicalComplex.id_f]
  exact (congrArg ModuleCat.ofHom (relativeCyclicCochainsMap_id (M := M) n)).trans
    ModuleCat.ofHom_id

/-- Relative cochain-complex pullback is contravariantly functorial. -/
theorem relativeCyclicCochainComplexMap_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    relativeCyclicCochainComplexMap M (g.comp f) =
      relativeCyclicCochainComplexMap M g ≫ relativeCyclicCochainComplexMap M f := by
  ext n : 1
  dsimp only [relativeCyclicCochainComplexMap, HomologicalComplex.comp_f]
  exact (congrArg ModuleCat.ofHom
    (relativeCyclicCochainsMap_comp (M := M) f g n)).trans
    (ModuleCat.ofHom_comp _ _)

namespace relativeCyclicCohomology

variable (M) in
/-- The map on relative cyclic cohomology induced contravariantly by a homomorphism of nonunital
algebras. -/
def map (f : A →ₙₐ[R] B) (n : ℕ) :
    relativeCyclicCohomology R B M n ⟶ relativeCyclicCohomology R A M n :=
  HomologicalComplex.homologyMap (relativeCyclicCochainComplexMap M f) n

/-- The induced map sends the class of a relative cocycle to the class of its pullback. -/
@[simp]
theorem map_mk (f : A →ₙₐ[R] B) {n : ℕ} (φ : relativeCyclicCocycles R B M n) :
    map M f n (mk R B M n φ) =
      mk R A M n
        ⟨relativeCyclicCochainsMap M f n φ,
          relativeCyclicCochainsMap_mem_relativeCyclicCocycles (R := R) (M := M) f φ⟩ := by
  rw [map, mk_apply, mk_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
  congr 1
  apply (relativeCyclicCochainComplex R A M).moduleCat_iCycles_injective n
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.comp_apply, relative_iCycles_toCycles, relative_iCycles_toCycles]
  -- Both sides reduce to `relativeCyclicCochainsMap` applied to the cocycle carrier.
  rfl

/-- The identity homomorphism induces the identity on relative cyclic cohomology. -/
@[simp]
theorem map_id (n : ℕ) : map M (NonUnitalAlgHom.id R A) n = 𝟙 _ := by
  rw [map, relativeCyclicCochainComplexMap_id, HomologicalComplex.homologyMap_id]

/-- Relative cyclic cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) (n : ℕ) :
    map M (g.comp f) n = map M g n ≫ map M f n := by
  rw [map, map, map, relativeCyclicCochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp]

end relativeCyclicCohomology

end ComplexMap


section ComplexSplitting

variable (R A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Restriction of cyclic cochain complexes along the scalar inclusion. -/
def unitizationScalarRestrictionComplexMap :
    cyclicCochainComplex R (Unitization R A) M ⟶ cyclicCochainComplex R R M :=
  cyclicCochainComplexMap M (Algebra.ofId R (Unitization R A)).toNonUnitalAlgHom

/-- Under the identifications `cyclicCochainComplexXIso`, the components of scalar restriction of
cyclic cochain complexes are scalar restriction of cyclic cochains. -/
@[reassoc, elementwise]
theorem unitizationScalarRestrictionComplexMap_f (n : ℕ) :
    (unitizationScalarRestrictionComplexMap R A M).f n ≫ (cyclicCochainComplexXIso R R M n).hom =
      (cyclicCochainComplexXIso R (Unitization R A) M n).hom ≫
        ModuleCat.ofHom (unitizationScalarRestriction R A M n) := by
  rw [unitizationScalarRestrictionComplexMap, cyclicCochainComplexMap_f,
    unitizationScalarRestriction]

/-- The inclusion of the relative cyclic cochain complex into the cyclic cochain complex of the
forced unitization. -/
def relativeCyclicCochainComplexι :
    relativeCyclicCochainComplex R A M ⟶ cyclicCochainComplex R (Unitization R A) M where
  f n := (relativeCyclicCochainComplexXIso R A M n).hom ≫
    ModuleCat.ofHom (relativeCyclicCochains R A M n).subtype ≫
    (cyclicCochainComplexXIso R (Unitization R A) M n).inv
  comm' := by
    rintro n _ rfl
    rw [← cancel_mono (cyclicCochainComplexXIso R (Unitization R A) M (n + 1)).hom]
    simp only [Category.assoc, cyclicCochainComplex_d, Iso.inv_hom_id_assoc,
      relativeCyclicCochainComplex_d_assoc, Iso.inv_hom_id, Category.comp_id]
    apply (cancel_epi (relativeCyclicCochainComplexXIso R A M n).hom).1
    exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦
      (coe_relativeCyclicHochschildCoboundary_apply R A M n φ).symm)

/-- The components of the relative-complex inclusion are the inclusions of relative cochains. -/
@[reassoc, elementwise]
theorem relativeCyclicCochainComplexι_f (n : ℕ) :
    (relativeCyclicCochainComplexι R A M).f n ≫
        (cyclicCochainComplexXIso R (Unitization R A) M n).hom =
      (relativeCyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (relativeCyclicCochains R A M n).subtype :=
  by simp [relativeCyclicCochainComplexι, Category.assoc]

/-- The relative-complex inclusion followed by scalar restriction is zero. -/
@[reassoc (attr := simp)]
theorem relativeCyclicCochainComplexι_comp_unitizationScalarRestrictionComplexMap :
    relativeCyclicCochainComplexι R A M ≫ unitizationScalarRestrictionComplexMap R A M = 0 := by
  apply HomologicalComplex.hom_ext _ _
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    ← cancel_mono (cyclicCochainComplexXIso R R M n).hom, Category.assoc,
    unitizationScalarRestrictionComplexMap, cyclicCochainComplexMap_f, zero_comp]
  simp only [relativeCyclicCochainComplexι, Category.assoc, Iso.inv_hom_id_assoc]
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ φ.2)

private def relativeCyclicCochainComplexLift
    {K : CochainComplex (ModuleCat R) ℕ}
    (e : K ⟶ cyclicCochainComplex R (Unitization R A) M)
    (he : e ≫ unitizationScalarRestrictionComplexMap R A M = 0) :
    K ⟶ relativeCyclicCochainComplex R A M where
  f n := ModuleCat.ofHom (LinearMap.codRestrict (relativeCyclicCochains R A M n)
    (e.f n ≫ (cyclicCochainComplexXIso R (Unitization R A) M n).hom).hom fun x ↦ by
      rw [mem_relativeCyclicCochains_iff]
      have hn : e.f n ≫ (unitizationScalarRestrictionComplexMap R A M).f n = 0 := by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun q ↦ q.f n) he
      have hmap : e.f n ≫ (cyclicCochainComplexXIso R (Unitization R A) M n).hom ≫
          ModuleCat.ofHom (unitizationScalarRestriction R A M n) = 0 := by
        rw [← unitizationScalarRestrictionComplexMap_f, ← Category.assoc, hn, zero_comp]
      exact ConcreteCategory.congr_hom hmap x) ≫
        (relativeCyclicCochainComplexXIso R A M n).inv
  comm' := by
    rintro n _ rfl
    rw [← cancel_mono (relativeCyclicCochainComplexXIso R A M (n + 1)).hom]
    simp only [Category.assoc, relativeCyclicCochainComplex_d, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply]
    apply Subtype.ext
    rw [coe_relativeCyclicHochschildCoboundary_apply]
    rw [LinearMap.codRestrict_apply, LinearMap.codRestrict_apply, LinearMap.comp_apply,
      LinearMap.comp_apply]
    -- The goal applies morphisms through `ModuleCat.Hom.hom`, while the elementwise lemmas use
    -- `ConcreteCategory.hom`, which is `ModuleCat.Hom.hom` for `ModuleCat`.
    exact (cyclicCochainComplex_d_apply R (Unitization R A) M n (e.f n x)).symm.trans
      (congrArg (cyclicCochainComplexXIso R (Unitization R A) M (n + 1)).hom
        (HomologicalComplex.Hom.comm_apply e n (n + 1) x))

/-- The relative cyclic cochain complex is the kernel of scalar restriction on the cyclic cochain
complex of the forced unitization. -/
def relativeCyclicCochainComplexIsKernel :
    IsLimit (KernelFork.ofι (relativeCyclicCochainComplexι R A M)
      (relativeCyclicCochainComplexι_comp_unitizationScalarRestrictionComplexMap R A M)) :=
  KernelFork.IsLimit.ofι _ _
    (fun e he ↦ relativeCyclicCochainComplexLift R A M e he)
    (fun e he ↦ by
      apply HomologicalComplex.hom_ext _ _
      intro n
      rw [← cancel_mono (cyclicCochainComplexXIso R (Unitization R A) M n).hom]
      simp only [relativeCyclicCochainComplexLift, relativeCyclicCochainComplexι,
        HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
      exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ by
        simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
          Function.comp_apply]
        -- `LinearMap.codRestrict` preserves the underlying value of the restricted map.
        rfl))
    (fun e he m hm ↦ by
      apply HomologicalComplex.hom_ext _ _
      intro n
      apply (cancel_mono (relativeCyclicCochainComplexXIso R A M n).hom).1
      let _ : Mono (ModuleCat.ofHom (relativeCyclicCochains R A M n).subtype) :=
        (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
      apply (cancel_mono (ModuleCat.ofHom
        (relativeCyclicCochains R A M n).subtype)).1
      have hn := congrArg (fun q ↦ q.f n) hm
      calc
        m.f n ≫ (relativeCyclicCochainComplexXIso R A M n).hom ≫
            ModuleCat.ofHom (relativeCyclicCochains R A M n).subtype =
            e.f n ≫ (cyclicCochainComplexXIso R (Unitization R A) M n).hom := by
          simpa [HomologicalComplex.comp_f, relativeCyclicCochainComplexι,
            Category.assoc] using congrArg
              (fun q ↦ q ≫ (cyclicCochainComplexXIso R (Unitization R A) M n).hom) hn
        _ = (relativeCyclicCochainComplexLift R A M e he).f n ≫
            (relativeCyclicCochainComplexXIso R A M n).hom ≫
              ModuleCat.ofHom (relativeCyclicCochains R A M n).subtype := by
          symm
          simp only [relativeCyclicCochainComplexLift, Category.assoc,
            Iso.inv_hom_id_assoc]
          -- After the subtype inclusion, `LinearMap.codRestrict` is the original linear map.
          exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

/-- Pullback of cyclic cochain complexes along the augmentation. -/
def unitizationAugmentationPullbackComplexMap :
    cyclicCochainComplex R R M ⟶ cyclicCochainComplex R (Unitization R A) M :=
  cyclicCochainComplexMap M (Unitization.fstHom R A).toNonUnitalAlgHom

/-- Under the identifications `cyclicCochainComplexXIso`, the components of pullback along the
augmentation are pullback of cyclic cochains along the augmentation. -/
@[reassoc, elementwise]
theorem unitizationAugmentationPullbackComplexMap_f (n : ℕ) :
    (unitizationAugmentationPullbackComplexMap R A M).f n ≫
        (cyclicCochainComplexXIso R (Unitization R A) M n).hom =
      (cyclicCochainComplexXIso R R M n).hom ≫
        ModuleCat.ofHom (unitizationAugmentationPullback R A M n) := by
  rw [unitizationAugmentationPullbackComplexMap, cyclicCochainComplexMap_f,
    unitizationAugmentationPullback]

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
    -- The available computation lemmas concern the underlying unitization element, so expose
    -- that element after extensionality has reduced the composite homomorphism equality.
    change (algebraMap R (Unitization R A) r).fst = r
    simp only [Unitization.algebraMap_eq_inl, Unitization.fst_inl]
  rw [h, cyclicCochainComplexMap_id]

end ComplexSplitting

end TauCeti
