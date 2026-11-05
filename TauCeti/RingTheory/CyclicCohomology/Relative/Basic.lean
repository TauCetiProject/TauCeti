/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Reduced
public import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Relative cyclic cohomology of a nonunital algebra

For a nonunital algebra `A`, its cyclic cohomology is not the cohomology of the cyclic cochains
on `A` itself. It is the relative theory of the forced unitization `Unitization R A` with respect
to its scalar subalgebra, that is, the reduced cyclic cohomology of `Unitization R A`
(`TauCeti.reducedCyclicCohomology`). In degree `n`, the relative cyclic cochains are the kernel
of restriction along the scalar inclusion

`R → Unitization R A`,

which is the module of reduced cyclic cochains of the forced unitization, and the relative cyclic
cochain complex is its reduced cyclic cochain complex. The reduced theory of a unital algebra is
therefore used at `Unitization R A` rather than built again: its Hochschild coboundary,
functoriality, inclusion into the full cyclic complex and identification as the kernel of scalar
restriction all apply verbatim.

What is specific to the forced unitization is the augmentation `Unitization R A → R`, which
splits scalar restriction; this records explicitly the contravariant splitting used by the
relative theory. The cocycles, coboundaries and classes of the relative theory, pullback along a
homomorphism of nonunital algebras, and the map to the cyclic cohomology of the forced unitization
are recorded here as well.

## Main definitions

* `TauCeti.relativeCyclicCochains`: the reduced cyclic cochains of the forced unitization.
* `TauCeti.unitizationAugmentationPullback`: pullback along the augmentation, a splitting of
  scalar restriction on the forced unitization.
* `TauCeti.relativeCyclicCochainComplex`: the relative cyclic cochain complex.
* `TauCeti.relativeCyclicCocycles`, `TauCeti.relativeCyclicCoboundaries`: concrete cocycles and
  coboundaries.
* `TauCeti.relativeCyclicCohomology`: the relative cyclic cohomology of a nonunital algebra.
* `TauCeti.relativeCyclicCohomology.mk`: the class of a relative cyclic cocycle.
* `TauCeti.relativeCyclicCohomology.map`: pullback along a homomorphism of nonunital algebras.
* `TauCeti.relativeCyclicCohomology.toUnitization`: the map from relative cyclic cohomology to the
  cyclic cohomology of the forced unitization.

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

section Cocycles

variable (R : Type*) (A : Type u) (M : Type*) [CommSemiring R] [NonUnitalSemiring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The relative cyclic `n`-cocycles: relative cochains annihilated by the reduced Hochschild
coboundary of the forced unitization. -/
def relativeCyclicCocycles (n : ℕ) : Submodule R (relativeCyclicCochains R A M n) :=
  LinearMap.ker (reducedCyclicHochschildCoboundary R (Unitization R A) M n)

/-- A relative cyclic cochain is a cocycle exactly when its reduced Hochschild coboundary
vanishes. -/
@[simp]
theorem mem_relativeCyclicCocycles_iff {n : ℕ} {φ : relativeCyclicCochains R A M n} :
    φ ∈ relativeCyclicCocycles R A M n ↔
      reducedCyclicHochschildCoboundary R (Unitization R A) M n φ = 0 :=
  LinearMap.mem_ker

variable {R A M} in
/-- A relative cyclic cochain is a cyclic cocycle of the forced unitization exactly when it is a
relative cyclic cocycle. -/
theorem coe_mem_cyclicCocycles_iff_mem_relativeCyclicCocycles {n : ℕ}
    {φ : relativeCyclicCochains R A M n} :
    (φ : cyclicCochains R (Unitization R A) M n) ∈ cyclicCocycles R (Unitization R A) M n ↔
      φ ∈ relativeCyclicCocycles R A M n := by
  simp [mem_cyclicCocycles_iff, mem_relativeCyclicCocycles_iff, Subtype.ext_iff,
    coe_reducedCyclicHochschildCoboundary_apply, coe_cyclicHochschildCoboundary_apply]

/-- The relative cyclic coboundaries: zero in degree zero, and in positive degree the image of the
reduced Hochschild coboundary of the forced unitization. -/
def relativeCyclicCoboundaries : (n : ℕ) → Submodule R (relativeCyclicCochains R A M n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (reducedCyclicHochschildCoboundary R (Unitization R A) M n)

/-- There are no nonzero relative cyclic coboundaries in degree zero. -/
@[simp]
theorem relativeCyclicCoboundaries_zero : relativeCyclicCoboundaries R A M 0 = ⊥ := (rfl)

/-- In positive degree the relative cyclic coboundaries are the image of the reduced Hochschild
coboundary of the forced unitization. -/
theorem relativeCyclicCoboundaries_succ (n : ℕ) :
    relativeCyclicCoboundaries R A M (n + 1) =
      LinearMap.range (reducedCyclicHochschildCoboundary R (Unitization R A) M n) :=
  (rfl)

/-- A relative cyclic cochain in positive degree is a coboundary exactly when it is the reduced
Hochschild coboundary of a relative cochain in the preceding degree. -/
@[simp]
theorem mem_relativeCyclicCoboundaries_succ_iff {n : ℕ}
    {φ : relativeCyclicCochains R A M (n + 1)} :
    φ ∈ relativeCyclicCoboundaries R A M (n + 1) ↔
      ∃ ψ : relativeCyclicCochains R A M n,
        reducedCyclicHochschildCoboundary R (Unitization R A) M n ψ = φ := by
  rw [relativeCyclicCoboundaries_succ, LinearMap.mem_range]

/-- Every relative cyclic coboundary is a relative cyclic cocycle. -/
theorem relativeCyclicCoboundaries_le_relativeCyclicCocycles (n : ℕ) :
    relativeCyclicCoboundaries R A M n ≤ relativeCyclicCocycles R A M n := by
  cases n with
  | zero => simp
  | succ n =>
    exact LinearMap.range_le_ker_iff.2
      (reducedCyclicHochschildCoboundary_comp_reducedCyclicHochschildCoboundary
        R (Unitization R A) M n)

end Cocycles

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

private theorem mem_relativeCyclicCocycles_iff_complex (n : ℕ)
    (φ : relativeCyclicCochains R A M n) :
    φ ∈ relativeCyclicCocycles R A M n ↔
      (relativeCyclicCochainComplex R A M).d n (n + 1)
        ((reducedCyclicCochainComplexXIso R (Unitization R A) M n).inv φ) = 0 := by
  rw [mem_relativeCyclicCocycles_iff,
    (relativeCyclicCochainComplex R A M).moduleCat_d_inv_eq_zero_iff
      (reducedCyclicHochschildCoboundary R (Unitization R A) M)
      (reducedCyclicCochainComplex_d R (Unitization R A) M)]

private theorem mem_relativeCyclicCoboundaries_iff_complex (n : ℕ)
    (φ : relativeCyclicCochains R A M n) :
    φ ∈ relativeCyclicCoboundaries R A M n ↔
      ∃ y : (relativeCyclicCochainComplex R A M).X ((ComplexShape.up ℕ).prev n),
        (relativeCyclicCochainComplex R A M).d ((ComplexShape.up ℕ).prev n) n y =
          (reducedCyclicCochainComplexXIso R (Unitization R A) M n).inv φ :=
  (relativeCyclicCochainComplex R A M).moduleCat_mem_iff_exists_d_eq_inv
    (V := fun n ↦ relativeCyclicCochains R A M n)
    (e := reducedCyclicCochainComplexXIso R (Unitization R A) M)
    (relativeCyclicCoboundaries R A M) (reducedCyclicHochschildCoboundary R (Unitization R A) M)
    (reducedCyclicCochainComplex_d R (Unitization R A) M) (relativeCyclicCoboundaries_zero R A M)
    (relativeCyclicCoboundaries_succ R A M) n φ

private abbrev relativeToCycles (n : ℕ) (φ : relativeCyclicCocycles R A M n) :=
  (relativeCyclicCochainComplex R A M).moduleCatCyclesMk
    ((reducedCyclicCochainComplexXIso R (Unitization R A) M n).inv φ.1) (n + 1)
    (CochainComplex.next ℕ n)
    ((mem_relativeCyclicCocycles_iff_complex R A M n φ.1).1 φ.2)

private theorem relative_iCycles_toCycles (n : ℕ) (φ : relativeCyclicCocycles R A M n) :
    (relativeCyclicCochainComplex R A M).iCycles n (relativeToCycles R A M n φ) =
      (reducedCyclicCochainComplexXIso R (Unitization R A) M n).inv φ.1 :=
  (relativeCyclicCochainComplex R A M).iCycles_moduleCatCyclesMk _ _ _ _ _

namespace relativeCyclicCohomology

/-- The relative cyclic cohomology class of a relative cyclic cocycle. -/
def mk (n : ℕ) :
    relativeCyclicCocycles R A M n →ₗ[R] relativeCyclicCohomology R A M n :=
  (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (reducedCyclicCochainComplexXIso R (Unitization R A) M)
    (mem_relativeCyclicCocycles_iff_complex R A M) n

private theorem mk_apply (n : ℕ) (φ : relativeCyclicCocycles R A M n) :
    mk R A M n φ =
      (relativeCyclicCochainComplex R A M).homologyπ n (relativeToCycles R A M n φ) :=
  (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_apply
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (reducedCyclicCochainComplexXIso R (Unitization R A) M)
    (mem_relativeCyclicCocycles_iff_complex R A M) n φ

/-- Every relative cyclic cohomology class is represented by a relative cyclic cocycle. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) := by
  exact (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (reducedCyclicCochainComplexXIso R (Unitization R A) M)
    (mem_relativeCyclicCocycles_iff_complex R A M) n

/-- A relative cyclic cocycle has zero cohomology class exactly when it is a relative cyclic
coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (φ : relativeCyclicCocycles R A M n) :
    mk R A M n φ = 0 ↔
      (φ : relativeCyclicCochains R A M n) ∈ relativeCyclicCoboundaries R A M n := by
  exact (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (relativeCyclicCoboundaries R A M) (reducedCyclicCochainComplexXIso R (Unitization R A) M)
    (mem_relativeCyclicCocycles_iff_complex R A M)
    (mem_relativeCyclicCoboundaries_iff_complex R A M) n φ

/-- Two relative cyclic cocycles have the same class exactly when they differ by a relative
cyclic coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (φ ψ : relativeCyclicCocycles R A M n) :
    mk R A M n φ = mk R A M n ψ ↔
      (φ : relativeCyclicCochains R A M n) - ψ ∈ relativeCyclicCoboundaries R A M n := by
  exact (relativeCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_iff
    (fun n ↦ relativeCyclicCochains R A M n) (relativeCyclicCocycles R A M)
    (relativeCyclicCoboundaries R A M) (reducedCyclicCochainComplexXIso R (Unitization R A) M)
    (mem_relativeCyclicCocycles_iff_complex R A M)
    (mem_relativeCyclicCoboundaries_iff_complex R A M) n φ ψ

end relativeCyclicCohomology

end Complex

section Map

variable {R : Type*} {A : Type u} {B : Type v} {M : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [AddCommGroup M] [Module R M]

/-- Pullback along the induced map of forced unitizations sends relative cyclic cocycles to
relative cyclic cocycles. -/
theorem reducedCyclicCochainsMap_unitizationMap_mem_relativeCyclicCocycles (f : A →ₙₐ[R] B)
    {n : ℕ} (φ : relativeCyclicCocycles R B M n) :
    reducedCyclicCochainsMap M (Unitization.map f) n φ ∈ relativeCyclicCocycles R A M n := by
  rw [mem_relativeCyclicCocycles_iff, reducedCyclicHochschildCoboundary_reducedCyclicCochainsMap,
    φ.2, map_zero]

end Map

section ComplexMap

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
  HomologicalComplex.homologyMap (reducedCyclicCochainComplexMap M (Unitization.map f)) n

/-- The induced map sends the class of a relative cocycle to the class of its pullback along the
induced map of forced unitizations. -/
@[simp]
theorem map_mk (f : A →ₙₐ[R] B) {n : ℕ} (φ : relativeCyclicCocycles R B M n) :
    map M f n (mk R B M n φ) =
      mk R A M n
        ⟨reducedCyclicCochainsMap M (Unitization.map f) n φ,
          reducedCyclicCochainsMap_unitizationMap_mem_relativeCyclicCocycles
            (R := R) (M := M) f φ⟩ := by
  rw [map, mk_apply, mk_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
  congr 1
  apply (relativeCyclicCochainComplex R A M).moduleCat_iCycles_injective n
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.comp_apply, relative_iCycles_toCycles, relative_iCycles_toCycles,
    ← Iso.hom_inv_id_apply (reducedCyclicCochainComplexXIso R (Unitization R A) M n)
      ((reducedCyclicCochainComplexMap M (Unitization.map f)).f n _),
    reducedCyclicCochainComplexMap_f_apply, Iso.inv_hom_id_apply]

/-- The identity homomorphism induces the identity on relative cyclic cohomology. -/
@[simp]
theorem map_id (n : ℕ) : map M (NonUnitalAlgHom.id R A) n = 𝟙 _ := by
  rw [map, Unitization.map_id, reducedCyclicCochainComplexMap_id,
    HomologicalComplex.homologyMap_id]

/-- Relative cyclic cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) (n : ℕ) :
    map M (g.comp f) n = map M g n ≫ map M f n := by
  rw [map, map, map, Unitization.map_comp, reducedCyclicCochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp]

end relativeCyclicCohomology

end ComplexMap

section ToUnitization

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

namespace relativeCyclicCohomology

/-- The map `HCⁿ(A; M) → HCⁿ(A⁺; M)` from relative cyclic cohomology to the cyclic cohomology of
the forced unitization `A⁺ = Unitization R A`, induced by the inclusion of relative cyclic
cochains. -/
def toUnitization (n : ℕ) :
    relativeCyclicCohomology R A M n ⟶ cyclicCohomology R (Unitization R A) M n :=
  HomologicalComplex.homologyMap (reducedCyclicCochainComplexι R (Unitization R A) M) n

variable {R A M}

/-- The class of a relative cyclic cocycle maps to its class as a cyclic cocycle of the forced
unitization. -/
@[simp]
theorem toUnitization_mk {n : ℕ} (φ : relativeCyclicCocycles R A M n) :
    toUnitization R A M n (mk R A M n φ) =
      cyclicCohomology.mk R (Unitization R A) M n
        ⟨_, coe_mem_cyclicCocycles_iff_mem_relativeCyclicCocycles.2 φ.2⟩ := by
  rw [toUnitization, mk_apply]
  refine (HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk _ _ _ _ _).trans
    (cyclicCohomology.mk_eq_homologyπ R (Unitization R A) M _ _ ?_).symm
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, reducedCyclicCochainComplexι_f_apply,
    Iso.inv_hom_id_apply]

/-- The map to the cyclic cohomology of the forced unitization is natural for homomorphisms of
nonunital algebras. -/
theorem toUnitization_map {B : Type u} [NonUnitalRing B] [Module R B] [IsScalarTower R B B]
    [SMulCommClass R B B] (f : A →ₙₐ[R] B) (n : ℕ) (c : relativeCyclicCohomology R B M n) :
    toUnitization R A M n (map M f n c) =
      cyclicCohomology.map M (Unitization.map f : Unitization R A →ₙₐ[R] Unitization R B) n
        (toUnitization R B M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R B M n c
  simp only [map_mk, toUnitization_mk, cyclicCohomology.map_mk]
  refine congrArg _ (Subtype.ext ?_)
  rw [coe_reducedCyclicCochainsMap_apply]
  -- Both sides pull back along the underlying linear map of `Unitization.map f`, read once through
  -- the algebra homomorphism and once through the nonunital algebra homomorphism.
  rfl

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
