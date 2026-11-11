/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Reduced
public import TauCeti.Algebra.Algebra.Unitization

/-!
# Relative cyclic cohomology of a nonunital algebra

For a nonunital algebra `A`, its cyclic cohomology is not the cohomology of the cyclic cochains
on `A` itself. It is the relative theory of the forced unitization `Unitization R A` with respect
to its scalar subalgebra, that is, the reduced cyclic cohomology of `Unitization R A`
(`TauCeti.reducedCyclicCohomology`). In degree `n`, the relative cyclic cochains are the kernel
of restriction along the scalar inclusion

`R → Unitization R A`,

which is the module of reduced cyclic cochains of the forced unitization, and the relative cyclic
cochain complex is its reduced cyclic cochain complex. Consequently the reduced API (Hochschild
coboundary, functoriality, inclusion into the full cyclic complex, identification as the kernel of
scalar restriction) applies verbatim to the relative theory.

What is specific to the forced unitization is the augmentation `Unitization R A → R`, which
splits scalar restriction; this records explicitly the contravariant splitting used by the
relative theory. The cocycles, coboundaries, classes and the map to the cyclic cohomology of the
forced unitization are the reduced ones (`TauCeti.reducedCyclicCocycles`,
`TauCeti.reducedCyclicCohomology.mk`, `TauCeti.reducedCyclicCohomology.toCyclic`) at
`Unitization R A`, and pullback along a homomorphism of nonunital algebras is reduced pullback
along the induced map of forced unitizations.

## Main definitions

* `TauCeti.relativeCyclicCochains`: the reduced cyclic cochains of the forced unitization.
* `TauCeti.unitizationAugmentationPullback`: pullback along the augmentation, a splitting of
  scalar restriction on the forced unitization.
* `TauCeti.relativeCyclicCochainComplex`: the relative cyclic cochain complex.
* `TauCeti.relativeCyclicCohomology`: the relative cyclic cohomology of a nonunital algebra.
* `TauCeti.relativeCyclicCohomology.map`: pullback along a homomorphism of nonunital algebras.
* `TauCeti.relativeCyclicCohomology.toCyclic_map_unitization`: naturality of the map to the cyclic
  cohomology of the forced unitization.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §1.4.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u v

section Cochains

variable (R : Type*) (A : Type u) (M : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Pullback of scalar cyclic cochains along the augmentation of the forced unitization. -/
def unitizationAugmentationPullback (n : ℕ) :
    cyclicCochains R R M n →ₗ[R] cyclicCochains R (Unitization R A) M n :=
  cyclicCochainsMap M ((Unitization.fstHom R A).toNonUnitalAlgHom :
    Unitization R A →ₗ[R] R) n

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

/-- Pullback along the augmentation is a right inverse to scalar restriction on the forced
unitization. -/
@[simp]
theorem scalarCyclicRestriction_comp_unitizationAugmentationPullback (n : ℕ) :
    scalarCyclicRestriction R (Unitization R A) M n ∘ₗ unitizationAugmentationPullback R A M n =
      LinearMap.id := by
  apply LinearMap.ext
  intro phi
  apply Subtype.ext
  apply MultilinearMap.ext
  intro a
  simp [Unitization.algebraMap_eq_inl]

/-- Scalar restriction on the forced unitization is surjective, split by pullback along the
augmentation. -/
theorem scalarCyclicRestriction_unitization_surjective (n : ℕ) :
    Function.Surjective (scalarCyclicRestriction R (Unitization R A) M n) :=
  Function.RightInverse.surjective (LinearMap.congr_fun
    (scalarCyclicRestriction_comp_unitizationAugmentationPullback R A M n))

/-- The relative cyclic `n`-cochains of a nonunital algebra: the reduced cyclic cochains of its
forced unitization, that is, cyclic cochains on the forced unitization which vanish when all
arguments are scalar. -/
abbrev relativeCyclicCochains (n : ℕ) :
    Submodule R (cyclicCochains R (Unitization R A) M n) :=
  reducedCyclicCochains R (Unitization R A) M n

end Cochains

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The relative cyclic cochain complex of a nonunital algebra: the reduced cyclic cochain complex
of its forced unitization, whose degree-`n` term is the kernel of scalar restriction on cyclic
cochains of the forced unitization. -/
abbrev relativeCyclicCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  reducedCyclicCochainComplex R (Unitization R A) M

/-- The relative cyclic cohomology of a nonunital algebra: the reduced cyclic cohomology of its
forced unitization, the cohomology of the kernel of scalar restriction on the cyclic cochain
complex of the forced unitization. -/
abbrev relativeCyclicCohomology (n : ℕ) : ModuleCat R :=
  reducedCyclicCohomology R (Unitization R A) M n

end Complex

section Map

variable {R : Type*} {A B C : Type u} {M : Type*} [CommRing R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  [AddCommGroup M] [Module R M]

namespace relativeCyclicCohomology

variable (M) in
/-- The map on relative cyclic cohomology induced contravariantly by a homomorphism of nonunital
algebras: the map on reduced cyclic cohomology induced by the induced map of forced
unitizations. -/
def map (f : A →ₙₐ[R] B) (n : ℕ) :
    relativeCyclicCohomology R B M n ⟶ relativeCyclicCohomology R A M n :=
  reducedCyclicCohomology.map M (Unitization.map f) n

/-- The induced map sends the class of a relative cocycle to the class of its pullback along the
induced map of forced unitizations. -/
@[simp]
theorem map_mk (f : A →ₙₐ[R] B) {n : ℕ} (φ : reducedCyclicCocycles R (Unitization R B) M n) :
    map M f n (reducedCyclicCohomology.mk R (Unitization R B) M n φ) =
      reducedCyclicCohomology.mk R (Unitization R A) M n
        ⟨reducedCyclicCochainsMap M (Unitization.map f) n φ,
          reducedCyclicCochainsMap_mem_reducedCyclicCocycles (R := R) (M := M)
            (Unitization.map f) φ⟩ := by
  rw [map, reducedCyclicCohomology.map_mk]

/-- The identity homomorphism induces the identity on relative cyclic cohomology. -/
@[simp]
theorem map_id (n : ℕ) : map M (NonUnitalAlgHom.id R A) n = 𝟙 _ := by
  rw [map, Unitization.map_id, reducedCyclicCohomology.map_id]

/-- Relative cyclic cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) (n : ℕ) :
    map M (g.comp f) n = map M g n ≫ map M f n := by
  rw [map, map, map, Unitization.map_comp, reducedCyclicCohomology.map_comp]

end relativeCyclicCohomology

end Map

section ToUnitization

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

namespace relativeCyclicCohomology

variable {R A M} in
/-- The map to the cyclic cohomology of the forced unitization is natural for homomorphisms of
nonunital algebras. -/
theorem toCyclic_map_unitization {B : Type u} [NonUnitalRing B] [Module R B] [IsScalarTower R B B]
    [SMulCommClass R B B] (f : A →ₙₐ[R] B) (n : ℕ) (c : relativeCyclicCohomology R B M n) :
    reducedCyclicCohomology.toCyclic R (Unitization R A) M n (map M f n c) =
      cyclicCohomology.map M (Unitization.map f : Unitization R A →ₙₐ[R] Unitization R B) n
        (reducedCyclicCohomology.toCyclic R (Unitization R B) M n c) := by
  rw [map, reducedCyclicCohomology.toCyclic_map]

end relativeCyclicCohomology

end ToUnitization

section ComplexSplitting

variable (R A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

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

/-- Pullback along the augmentation splits scalar restriction on the forced unitization as a
cochain map. -/
@[simp]
theorem unitizationAugmentationPullbackComplexMap_comp_scalarCyclicRestrictionComplexMap :
    unitizationAugmentationPullbackComplexMap R A M ≫
        scalarCyclicRestrictionComplexMap R (Unitization R A) M =
      𝟙 (cyclicCochainComplex R R M) := by
  apply HomologicalComplex.hom_ext _ _
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ← cancel_mono (cyclicCochainComplexXIso R R M n).hom, Category.assoc,
    scalarCyclicRestrictionComplexMap_f, unitizationAugmentationPullbackComplexMap_f_assoc,
    Category.id_comp, ← ModuleCat.ofHom_comp,
    scalarCyclicRestriction_comp_unitizationAugmentationPullback, ModuleCat.ofHom_id,
    Category.comp_id]

end ComplexSplitting

end TauCeti
