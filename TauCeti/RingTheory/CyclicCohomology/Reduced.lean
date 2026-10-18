/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Reduced cyclic cohomology of a unital algebra

For a unital algebra `A` over `R`, reduced cyclic cochains are cyclic cochains on `A` whose
restriction to the scalar subalgebra vanishes. Thus they are the kernel of restriction along the
unit-preserving scalar inclusion `R → A`. The Hochschild coboundary preserves this kernel and
defines the reduced cyclic cochain complex.

This construction is different from relative cyclic cohomology of a possibly nonunital algebra.
The latter first passes to the forced unitization and takes the kernel of its augmentation
splitting; the reduced theory here uses the given unit of `A`. In particular, the reduced complex
of the ground ring is zero, whereas relative forced-unitization cohomology recovers the full cyclic
theory of a unital algebra.

## Main definitions

* `TauCeti.scalarCyclicRestriction`: restriction to the scalar subalgebra.
* `TauCeti.reducedCyclicCochains`: the kernel of scalar restriction.
* `TauCeti.reducedCyclicCochainComplex`: the reduced cyclic cochain complex.
* `TauCeti.reducedCyclicCohomology`: reduced cyclic cohomology.
* `TauCeti.reducedCyclicCochainsMap`: contravariant pullback along a unital algebra homomorphism.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace TauCeti

universe u v w

section Cochains

variable (R : Type*) (A : Type u) (M : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- Restriction of cyclic cochains on a unital algebra to its scalar subalgebra. -/
def scalarCyclicRestriction (n : ℕ) :
    cyclicCochains R A M n →ₗ[R] cyclicCochains R R M n :=
  cyclicCochainsMap M
    ((Algebra.ofId R A).toNonUnitalAlgHom : R →ₗ[R] A) n

/-- Scalar restriction evaluates a cochain on arguments coming from the scalar subalgebra. -/
@[simp]
theorem scalarCyclicRestriction_apply (n : ℕ) (phi : cyclicCochains R A M n)
    (a : Fin (n + 1) → R) :
    (scalarCyclicRestriction R A M n phi :
        MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) a =
      (phi : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
        (fun i ↦ algebraMap R A (a i)) := by
  simp only [scalarCyclicRestriction, coe_cyclicCochainsMap_apply,
    MultilinearMap.compLinearMap_apply]
  congr 1

/-- The reduced cyclic `n`-cochains of a unital algebra: cyclic cochains which vanish on the
scalar subalgebra. -/
def reducedCyclicCochains (n : ℕ) : Submodule R (cyclicCochains R A M n) :=
  LinearMap.ker (scalarCyclicRestriction R A M n)

/-- A cyclic cochain is reduced exactly when its scalar restriction vanishes. -/
theorem mem_reducedCyclicCochains_iff {n : ℕ} {phi : cyclicCochains R A M n} :
    phi ∈ reducedCyclicCochains R A M n ↔ scalarCyclicRestriction R A M n phi = 0 :=
  LinearMap.mem_ker

/-- A cyclic cochain is reduced exactly when it vanishes whenever all its arguments are
scalars. -/
@[simp]
theorem mem_reducedCyclicCochains_iff_forall {n : ℕ} {phi : cyclicCochains R A M n} :
    phi ∈ reducedCyclicCochains R A M n ↔ ∀ a : Fin (n + 1) → R,
      (phi : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
        (fun i ↦ algebraMap R A (a i)) = 0 := by
  rw [mem_reducedCyclicCochains_iff, Subtype.ext_iff, MultilinearMap.ext_iff]
  simp

/-- The Hochschild coboundary of a reduced cyclic cochain is reduced. -/
theorem cyclicHochschildCoboundary_mem_reducedCyclicCochains {n : ℕ}
    (phi : reducedCyclicCochains R A M n) :
    cyclicHochschildCoboundary R A M n phi ∈ reducedCyclicCochains R A M (n + 1) := by
  rw [mem_reducedCyclicCochains_iff]
  have hphi : cyclicCochainsMap M
      ((Algebra.ofId R A).toNonUnitalAlgHom : R →ₗ[R] A) n phi = 0 := by
    simpa only [scalarCyclicRestriction] using
      (mem_reducedCyclicCochains_iff (R := R) (A := A) (M := M)).mp phi.property
  calc
    cyclicCochainsMap M ((Algebra.ofId R A).toNonUnitalAlgHom : R →ₗ[R] A) (n + 1)
        (cyclicHochschildCoboundary R A M n phi) =
      cyclicHochschildCoboundary R R M n
        (cyclicCochainsMap M
          ((Algebra.ofId R A).toNonUnitalAlgHom : R →ₗ[R] A) n phi) :=
          (cyclicHochschildCoboundary_cyclicCochainsMap
            (Algebra.ofId R A).toNonUnitalAlgHom
            (phi : cyclicCochains R A M n)).symm
    _ = 0 := by rw [hphi, map_zero]

/-- The Hochschild coboundary restricted to reduced cyclic cochains. -/
def reducedCyclicHochschildCoboundary (n : ℕ) :
    reducedCyclicCochains R A M n →ₗ[R] reducedCyclicCochains R A M (n + 1) where
  toFun phi := ⟨cyclicHochschildCoboundary R A M n phi,
    cyclicHochschildCoboundary_mem_reducedCyclicCochains R A M phi⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The reduced Hochschild coboundary has the ordinary cyclic Hochschild coboundary as its
underlying cochain. -/
@[simp]
theorem coe_reducedCyclicHochschildCoboundary_apply (n : ℕ)
    (phi : reducedCyclicCochains R A M n) :
    (reducedCyclicHochschildCoboundary R A M n phi : cyclicCochains R A M (n + 1)) =
      cyclicHochschildCoboundary R A M n phi := by
  simp [reducedCyclicHochschildCoboundary]

/-- The reduced Hochschild coboundary squares to zero. -/
theorem reducedCyclicHochschildCoboundary_reducedCyclicHochschildCoboundary (n : ℕ)
    (phi : reducedCyclicCochains R A M n) :
    reducedCyclicHochschildCoboundary R A M (n + 1)
        (reducedCyclicHochschildCoboundary R A M n phi) = 0 := by
  apply Subtype.ext
  exact cyclicHochschildCoboundary_cyclicHochschildCoboundary
    R A M (phi : cyclicCochains R A M n)

/-- The reduced Hochschild coboundary squares to zero as a composite of linear maps. -/
theorem reducedCyclicHochschildCoboundary_comp_reducedCyclicHochschildCoboundary (n : ℕ) :
    reducedCyclicHochschildCoboundary R A M (n + 1) ∘ₗ
      reducedCyclicHochschildCoboundary R A M n = 0 := by
  apply LinearMap.ext
  intro phi
  exact reducedCyclicHochschildCoboundary_reducedCyclicHochschildCoboundary R A M n phi

end Cochains

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Semiring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- Reduced cyclic cochains inherit their additive group structure from cyclic cochains. -/
instance reducedCyclicCochainsAddCommGroup (n : ℕ) :
    AddCommGroup (reducedCyclicCochains R A M n) :=
  (reducedCyclicCochains R A M n).addCommGroup

/-- The reduced cyclic cochain complex of a unital algebra. Its degree-`n` term is the kernel of
restriction from cyclic cochains on the algebra to cyclic cochains on the ground ring. -/
def reducedCyclicCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (reducedCyclicCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (reducedCyclicHochschildCoboundary R A M n))
    fun n ↦ ModuleCat.hom_ext
      (reducedCyclicHochschildCoboundary_comp_reducedCyclicHochschildCoboundary R A M n)

/-- The degree-`n` term of the reduced cyclic cochain complex is the module of reduced cyclic
`n`-cochains. -/
def reducedCyclicCochainComplexXIso (n : ℕ) :
    (reducedCyclicCochainComplex R A M).X n ≅ ModuleCat.of R (reducedCyclicCochains R A M n) :=
  Iso.refl _

/-- Under the canonical identifications of the terms, the differential of the reduced cyclic
cochain complex is the reduced Hochschild coboundary. -/
@[reassoc, elementwise]
theorem reducedCyclicCochainComplex_d (n : ℕ) :
    (reducedCyclicCochainComplex R A M).d n (n + 1) ≫
        (reducedCyclicCochainComplexXIso R A M (n + 1)).hom =
      (reducedCyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (reducedCyclicHochschildCoboundary R A M n) := by
  simp [reducedCyclicCochainComplex, reducedCyclicCochainComplexXIso]

/-- Reduced cyclic cohomology of a unital algebra. -/
abbrev reducedCyclicCohomology (n : ℕ) : ModuleCat R :=
  (reducedCyclicCochainComplex R A M).homology n

end Complex

section Map

variable {R : Type*} {A : Type u} {B : Type v} {C : Type w} {M : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
  [AddCommGroup M] [Module R M]

/-- Pullback along a unital algebra homomorphism preserves reduced cyclic cochains. -/
theorem cyclicCochainsMap_mem_reducedCyclicCochains (f : A →ₐ[R] B) {n : ℕ}
    (phi : reducedCyclicCochains R B M n) :
    cyclicCochainsMap M f.toLinearMap n phi ∈ reducedCyclicCochains R A M n := by
  rw [mem_reducedCyclicCochains_iff_forall]
  intro a
  simp only [coe_cyclicCochainsMap_apply, MultilinearMap.compLinearMap_apply,
    AlgHom.toLinearMap_apply, AlgHom.commutes]
  exact (mem_reducedCyclicCochains_iff_forall (R := R) (A := B) (M := M)).mp phi.property a

variable (M) in
/-- Pullback of reduced cyclic cochains along a unital algebra homomorphism. -/
def reducedCyclicCochainsMap (f : A →ₐ[R] B) (n : ℕ) :
    reducedCyclicCochains R B M n →ₗ[R] reducedCyclicCochains R A M n :=
  LinearMap.codRestrict (reducedCyclicCochains R A M n)
    ((cyclicCochainsMap M f.toLinearMap n).comp (reducedCyclicCochains R B M n).subtype)
    (cyclicCochainsMap_mem_reducedCyclicCochains (R := R) (M := M) f)

/-- The underlying cyclic cochain of a reduced pullback is ordinary pullback. -/
@[simp]
theorem coe_reducedCyclicCochainsMap_apply (f : A →ₐ[R] B) (n : ℕ)
    (phi : reducedCyclicCochains R B M n) :
    (reducedCyclicCochainsMap M f n phi : cyclicCochains R A M n) =
      cyclicCochainsMap M f.toLinearMap n phi :=
  (rfl)

/-- Pullback along the identity is the identity on reduced cyclic cochains. -/
@[simp]
theorem reducedCyclicCochainsMap_id (n : ℕ) :
    reducedCyclicCochainsMap M (AlgHom.id R A) n = LinearMap.id := by
  apply LinearMap.ext
  intro phi
  apply Subtype.ext
  simp [reducedCyclicCochainsMap]

/-- Pullback of reduced cyclic cochains is contravariantly functorial. -/
theorem reducedCyclicCochainsMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (n : ℕ) :
    reducedCyclicCochainsMap M (g.comp f) n =
      reducedCyclicCochainsMap M f n ∘ₗ reducedCyclicCochainsMap M g n := by
  apply LinearMap.ext
  intro phi
  apply Subtype.ext
  exact LinearMap.congr_fun (cyclicCochainsMap_comp M f.toLinearMap g.toLinearMap n) phi

/-- Reduced pullback commutes with the reduced Hochschild coboundary. -/
theorem reducedCyclicHochschildCoboundary_reducedCyclicCochainsMap
    (f : A →ₐ[R] B) (n : ℕ) (phi : reducedCyclicCochains R B M n) :
    reducedCyclicHochschildCoboundary R A M n (reducedCyclicCochainsMap M f n phi) =
      reducedCyclicCochainsMap M f (n + 1)
        (reducedCyclicHochschildCoboundary R B M n phi) := by
  apply Subtype.ext
  exact cyclicHochschildCoboundary_cyclicCochainsMap f.toNonUnitalAlgHom
    (phi : cyclicCochains R B M n)

end Map

section ComplexMap

variable {R : Type*} {A B C : Type u} {M : Type*} [CommRing R]
  [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
  [AddCommGroup M] [Module R M]

variable (M) in
/-- The cochain map between reduced cyclic complexes induced contravariantly by a unital algebra
homomorphism. -/
def reducedCyclicCochainComplexMap (f : A →ₐ[R] B) :
    reducedCyclicCochainComplex R B M ⟶ reducedCyclicCochainComplex R A M where
  f n := ModuleCat.ofHom (reducedCyclicCochainsMap M f n)
  comm' := by
    rintro n _ rfl
    ext phi : 2
    simp only [reducedCyclicCochainComplex, CochainComplex.of_d, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom]
    exact reducedCyclicHochschildCoboundary_reducedCyclicCochainsMap
      (R := R) (M := M) f n phi

/-- The components of reduced pullback are the pullback maps on reduced cyclic cochains. -/
@[reassoc, elementwise]
theorem reducedCyclicCochainComplexMap_f (f : A →ₐ[R] B) (n : ℕ) :
    (reducedCyclicCochainComplexMap M f).f n ≫
        (reducedCyclicCochainComplexXIso R A M n).hom =
      (reducedCyclicCochainComplexXIso R B M n).hom ≫
        ModuleCat.ofHom (reducedCyclicCochainsMap M f n) :=
  (rfl)

/-- The identity homomorphism induces the identity reduced cochain map. -/
@[simp]
theorem reducedCyclicCochainComplexMap_id :
    reducedCyclicCochainComplexMap M (AlgHom.id R A) =
      𝟙 (reducedCyclicCochainComplex R A M) := by
  ext n : 1
  dsimp only [reducedCyclicCochainComplexMap, HomologicalComplex.id_f]
  exact (congrArg ModuleCat.ofHom (reducedCyclicCochainsMap_id (M := M) n)).trans
    ModuleCat.ofHom_id

/-- Reduced cochain-complex pullback is contravariantly functorial. -/
theorem reducedCyclicCochainComplexMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    reducedCyclicCochainComplexMap M (g.comp f) =
      reducedCyclicCochainComplexMap M g ≫ reducedCyclicCochainComplexMap M f := by
  ext n : 1
  dsimp only [reducedCyclicCochainComplexMap, HomologicalComplex.comp_f]
  exact (congrArg ModuleCat.ofHom (reducedCyclicCochainsMap_comp (M := M) f g n)).trans
    (ModuleCat.ofHom_comp _ _)

namespace reducedCyclicCohomology

variable (M) in
/-- The map on reduced cyclic cohomology induced contravariantly by a unital algebra
homomorphism. -/
def map (f : A →ₐ[R] B) (n : ℕ) :
    reducedCyclicCohomology R B M n ⟶ reducedCyclicCohomology R A M n :=
  HomologicalComplex.homologyMap (reducedCyclicCochainComplexMap M f) n

/-- The identity homomorphism induces the identity on reduced cyclic cohomology. -/
@[simp]
theorem map_id (n : ℕ) : map M (AlgHom.id R A) n = 𝟙 _ := by
  rw [map, reducedCyclicCochainComplexMap_id, HomologicalComplex.homologyMap_id]

/-- Reduced cyclic cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (n : ℕ) :
    map M (g.comp f) n = map M g n ≫ map M f n := by
  rw [map, map, map, reducedCyclicCochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp]

end reducedCyclicCohomology

end ComplexMap

section ComplexKernel

variable (R A : Type u) (M : Type*) [CommRing R] [Semiring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- Restriction of cyclic cochain complexes along the scalar inclusion. -/
def scalarCyclicRestrictionComplexMap :
    cyclicCochainComplex R A M ⟶ cyclicCochainComplex R R M :=
  cyclicCochainComplexMap M (Algebra.ofId R A).toNonUnitalAlgHom

/-- The components of scalar restriction of cyclic cochain complexes are scalar restriction of
cyclic cochains. -/
@[reassoc, elementwise]
theorem scalarCyclicRestrictionComplexMap_f (n : ℕ) :
    (scalarCyclicRestrictionComplexMap R A M).f n ≫
        (cyclicCochainComplexXIso R R M n).hom =
      (cyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (scalarCyclicRestriction R A M n) := by
  rw [scalarCyclicRestrictionComplexMap, cyclicCochainComplexMap_f,
    scalarCyclicRestriction]

/-- The inclusion of the reduced cyclic cochain complex into the full cyclic cochain complex. -/
def reducedCyclicCochainComplexι :
    reducedCyclicCochainComplex R A M ⟶ cyclicCochainComplex R A M where
  f n := (reducedCyclicCochainComplexXIso R A M n).hom ≫
    ModuleCat.ofHom (reducedCyclicCochains R A M n).subtype ≫
    (cyclicCochainComplexXIso R A M n).inv
  comm' := by
    rintro n _ rfl
    rw [← cancel_mono (cyclicCochainComplexXIso R A M (n + 1)).hom]
    simp only [Category.assoc, cyclicCochainComplex_d, Iso.inv_hom_id_assoc,
      reducedCyclicCochainComplex_d_assoc, Iso.inv_hom_id, Category.comp_id]
    apply (cancel_epi (reducedCyclicCochainComplexXIso R A M n).hom).1
    exact ModuleCat.hom_ext (LinearMap.ext fun phi ↦
      (coe_reducedCyclicHochschildCoboundary_apply R A M n phi).symm)

/-- The components of the reduced-complex inclusion are the inclusions of reduced cochains. -/
@[reassoc, elementwise]
theorem reducedCyclicCochainComplexι_f (n : ℕ) :
    (reducedCyclicCochainComplexι R A M).f n ≫
        (cyclicCochainComplexXIso R A M n).hom =
      (reducedCyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (reducedCyclicCochains R A M n).subtype := by
  simp [reducedCyclicCochainComplexι, Category.assoc]

/-- The reduced-complex inclusion followed by scalar restriction is zero. -/
@[reassoc (attr := simp)]
theorem reducedCyclicCochainComplexι_comp_scalarCyclicRestrictionComplexMap :
    reducedCyclicCochainComplexι R A M ≫ scalarCyclicRestrictionComplexMap R A M = 0 := by
  apply HomologicalComplex.hom_ext _ _
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    ← cancel_mono (cyclicCochainComplexXIso R R M n).hom, Category.assoc,
    scalarCyclicRestrictionComplexMap, cyclicCochainComplexMap_f, zero_comp]
  simp only [reducedCyclicCochainComplexι, Category.assoc, Iso.inv_hom_id_assoc]
  exact ModuleCat.hom_ext (LinearMap.ext fun phi ↦ phi.2)

private def reducedCyclicCochainComplexLift
    {K : CochainComplex (ModuleCat R) ℕ} (e : K ⟶ cyclicCochainComplex R A M)
    (he : e ≫ scalarCyclicRestrictionComplexMap R A M = 0) :
    K ⟶ reducedCyclicCochainComplex R A M where
  f n := ModuleCat.ofHom (LinearMap.codRestrict (reducedCyclicCochains R A M n)
    (e.f n ≫ (cyclicCochainComplexXIso R A M n).hom).hom fun x ↦ by
      rw [mem_reducedCyclicCochains_iff]
      have hn : e.f n ≫ (scalarCyclicRestrictionComplexMap R A M).f n = 0 := by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun q ↦ q.f n) he
      have hmap : e.f n ≫ (cyclicCochainComplexXIso R A M n).hom ≫
          ModuleCat.ofHom (scalarCyclicRestriction R A M n) = 0 := by
        rw [← scalarCyclicRestrictionComplexMap_f, ← Category.assoc, hn, zero_comp]
      exact ConcreteCategory.congr_hom hmap x) ≫
        (reducedCyclicCochainComplexXIso R A M n).inv
  comm' := by
    rintro n _ rfl
    rw [← cancel_mono (reducedCyclicCochainComplexXIso R A M (n + 1)).hom]
    simp only [Category.assoc, reducedCyclicCochainComplex_d, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply]
    apply Subtype.ext
    rw [coe_reducedCyclicHochschildCoboundary_apply, LinearMap.codRestrict_apply,
      LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    exact (cyclicCochainComplex_d_apply R A M n (e.f n x)).symm.trans
      (congrArg (cyclicCochainComplexXIso R A M (n + 1)).hom
        (HomologicalComplex.Hom.comm_apply e n (n + 1) x))

/-- The reduced cyclic cochain complex is the kernel of scalar restriction on the full cyclic
cochain complex. -/
def reducedCyclicCochainComplexIsKernel :
    IsLimit (KernelFork.ofι (reducedCyclicCochainComplexι R A M)
      (reducedCyclicCochainComplexι_comp_scalarCyclicRestrictionComplexMap R A M)) :=
  KernelFork.IsLimit.ofι _ _
    (fun e he ↦ reducedCyclicCochainComplexLift R A M e he)
    (fun e he ↦ by
      apply HomologicalComplex.hom_ext _ _
      intro n
      rw [← cancel_mono (cyclicCochainComplexXIso R A M n).hom]
      simp only [reducedCyclicCochainComplexLift, reducedCyclicCochainComplexι,
        HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))
    (fun e he m hm ↦ by
      apply HomologicalComplex.hom_ext _ _
      intro n
      apply (cancel_mono (reducedCyclicCochainComplexXIso R A M n).hom).1
      let _ : Mono (ModuleCat.ofHom (reducedCyclicCochains R A M n).subtype) :=
        (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
      apply (cancel_mono (ModuleCat.ofHom (reducedCyclicCochains R A M n).subtype)).1
      have hn := congrArg (fun q ↦ q.f n) hm
      calc
        m.f n ≫ (reducedCyclicCochainComplexXIso R A M n).hom ≫
            ModuleCat.ofHom (reducedCyclicCochains R A M n).subtype =
            e.f n ≫ (cyclicCochainComplexXIso R A M n).hom := by
          simpa [HomologicalComplex.comp_f, reducedCyclicCochainComplexι,
            Category.assoc] using congrArg
              (fun q ↦ q ≫ (cyclicCochainComplexXIso R A M n).hom) hn
        _ = (reducedCyclicCochainComplexLift R A M e he).f n ≫
            (reducedCyclicCochainComplexXIso R A M n).hom ≫
              ModuleCat.ofHom (reducedCyclicCochains R A M n).subtype := by
          symm
          simp only [reducedCyclicCochainComplexLift, Category.assoc,
            Iso.inv_hom_id_assoc]
          exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

end ComplexKernel

section Vanishing

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Semiring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

private theorem isZero_reducedCyclicCochainComplex_of_subsingleton_terms
    (hsub : ∀ n, Subsingleton (reducedCyclicCochains R A M n)) :
    IsZero (reducedCyclicCochainComplex R A M) := by
  have hX (n : ℕ) : Subsingleton ((reducedCyclicCochainComplex R A M).X n) := by
    simpa only [reducedCyclicCochainComplex, CochainComplex.of_X] using hsub n
  refine ⟨fun K ↦ ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩, fun K ↦ ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩⟩
  · apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [@Subsingleton.elim _ (hX n) x 0, map_zero]
    rfl
  · apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact @Subsingleton.elim _ (hX n) _ _

end Vanishing

section GroundRing

variable (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- Restriction from the ground ring to its own scalar subalgebra is the identity. -/
@[simp]
theorem scalarCyclicRestriction_self (n : ℕ) :
    scalarCyclicRestriction R R M n = LinearMap.id := by
  apply LinearMap.ext
  intro phi
  apply Subtype.ext
  apply MultilinearMap.ext
  intro a
  simp

/-- Every reduced cyclic cochain on the ground ring is zero. -/
@[simp]
theorem reducedCyclicCochains_self (n : ℕ) : reducedCyclicCochains R R M n = ⊥ := by
  rw [reducedCyclicCochains, scalarCyclicRestriction_self, LinearMap.ker_id]

/-- The reduced cyclic cochain complex of the ground ring is a zero object. -/
theorem isZero_reducedCyclicCochainComplex_self :
    IsZero (reducedCyclicCochainComplex R R M) := by
  have hsub (n : ℕ) : Subsingleton (reducedCyclicCochains R R M n) := by
    rw [reducedCyclicCochains_self]
    infer_instance
  exact isZero_reducedCyclicCochainComplex_of_subsingleton_terms R R M hsub

/-- Reduced cyclic cohomology of the ground ring vanishes in every degree. -/
theorem isZero_reducedCyclicCohomology_self (n : ℕ) :
    IsZero (reducedCyclicCohomology R R M n) := by
  exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).map_isZero
    (isZero_reducedCyclicCochainComplex_self R M)

end GroundRing

section ZeroAlgebra

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Semiring A] [Algebra R A]
  [Subsingleton A] [AddCommGroup M] [Module R M]

/-- Every reduced cyclic cochain on a zero algebra is zero. -/
@[simp]
theorem reducedCyclicCochains_of_subsingleton (n : ℕ) :
    reducedCyclicCochains R A M n = ⊥ := by
  apply bot_unique
  intro phi _
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply MultilinearMap.ext
  intro a
  simp [@Subsingleton.elim _ (Pi.instSubsingleton) a 0]

/-- The reduced cyclic cochain complex of a zero algebra is a zero object. -/
theorem isZero_reducedCyclicCochainComplex_of_subsingleton :
    IsZero (reducedCyclicCochainComplex R A M) := by
  apply isZero_reducedCyclicCochainComplex_of_subsingleton_terms R A M
  intro n
  rw [reducedCyclicCochains_of_subsingleton]
  infer_instance

/-- Reduced cyclic cohomology of a zero algebra vanishes in every degree. -/
theorem isZero_reducedCyclicCohomology_of_subsingleton (n : ℕ) :
    IsZero (reducedCyclicCohomology R A M n) := by
  exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).map_isZero
    (isZero_reducedCyclicCochainComplex_of_subsingleton R A M)

end ZeroAlgebra

end TauCeti
