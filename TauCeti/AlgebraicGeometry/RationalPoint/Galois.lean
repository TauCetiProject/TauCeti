/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import TauCeti.FieldTheory.KrullTopology
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Galois action on field-valued points

A field automorphism of `L/K` acts on the `L`-valued points of a scheme over `K` by
precomposition with its spectrum morphism. The two contravariances give a left action.
For a scheme locally of finite type and an algebraic extension, every point has a locally
constant orbit map for the Krull topology: on an affine neighbourhood it is determined by
finitely many coordinates in `L`. The affine neighbourhood argument follows
`AlgebraicGeometry.Scheme.Hom.finite_points`, and local constancy uses
`IsLocallyConstant.of_mul_eq_of_fixes`.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

namespace CategoryTheory.Over

variable (X : Over (Spec (.of K)))

/-- The Galois action on the `L`-valued points of a scheme over `K`. -/
noncomputable scoped instance pointGaloisAction :
    MulAction (L ≃ₐ[K] L) (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X) where
  smul σ x := (algSpec (.of K)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ x
  one_smul x := by
    have h : CommAlgCat.ofHom ((1 : L ≃ₐ[K] L).toAlgHom) = 𝟙 (CommAlgCat.of K L) := by
      ext a
      rfl
    -- Expose scalar multiplication while constructing the instance.
    change (algSpec (.of K)).map (CommAlgCat.ofHom ((1 : L ≃ₐ[K] L).toAlgHom)).op ≫ x = x
    simp only [h, op_id, Functor.map_id]
    exact Category.id_comp x
  mul_smul σ τ x := by
    -- The two precompositions compose in the opposite order from the field automorphisms.
    have h : CommAlgCat.ofHom (σ * τ).toAlgHom =
        CommAlgCat.ofHom τ.toAlgHom ≫ CommAlgCat.ofHom σ.toAlgHom := by
      ext a
      rfl
    -- Expose the precomposition maps in the scalar action under construction.
    change (algSpec (.of K)).map (CommAlgCat.ofHom (σ * τ).toAlgHom).op ≫ x =
      (algSpec (.of K)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
        (algSpec (.of K)).map (CommAlgCat.ofHom τ.toAlgHom).op ≫ x
    rw [h, op_comp, Functor.map_comp]
    exact Category.assoc _ _ x

/-- The Galois action precomposes a point with the spectrum of the field automorphism. -/
theorem pointGaloisAction_smul (σ : L ≃ₐ[K] L)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X) :
    σ • x = (algSpec (.of K)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ x :=
  (rfl)

/-- On underlying scheme morphisms, the Galois action precomposes with `Spec σ`. -/
@[simp]
theorem pointGaloisAction_smul_left (σ : L ≃ₐ[K] L)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X) :
    (σ • x).left = Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ x.left :=
  (rfl)

/-- The Galois orbit of a point of a locally finite type scheme over a field is locally
constant for the Krull topology if the point takes values in an algebraic extension. -/
theorem isLocallyConstant_pointGaloisAction [LocallyOfFiniteType X.hom]
    [Algebra.IsIntegral K L]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X) :
    IsLocallyConstant fun σ : L ≃ₐ[K] L ↦ σ • x := by
  classical
  obtain ⟨_, ⟨U, hUmem, rfl⟩, hxU, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x.left (IsLocalRing.closedPoint L))) isOpen_univ
  have hU : IsAffineOpen U := hUmem
  have hx : Set.range x.left ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    have hp := @Subsingleton.elim (Spec (.of L)) inferInstance p (IsLocalRing.closedPoint L)
    rwa [hp]
  let : Algebra K Γ(X.left, U) := X.hom.sectionsAlgebra U
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hchart := X.hom.fromSpec_toSpec hU
  have : Algebra.FiniteType K Γ(X.left, U) := by
    have h : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X.left, U)))) := by
      rw [← hchart]
      infer_instance
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)
  let y := IsOpenImmersion.lift hU.fromSpec x.left hx
  have hy : y ≫ Spec.algebraMap K Γ(X.left, U) = Spec.algebraMap K L := by
    rw [Spec.algebraMap, ← hchart, IsOpenImmersion.lift_fac_assoc]
    exact Over.w x
  obtain ⟨φ, hφ⟩ := TauCeti.AlgebraicGeometry.exists_algHom_SpecMap_eq y hy
  have hfactor : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec = x.left := by
    rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨generators, hgen⟩ := Algebra.FiniteType.out (R := K) (A := Γ(X.left, U))
  refine IsLocallyConstant.of_mul_eq_of_fixes (generators.image φ)
    (fun a _ ↦ Algebra.IsIntegral.isIntegral a) fun σ τ hτ ↦ ?_
  have hfix : τ.toAlgHom.comp φ = φ := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro a ha
    exact hτ (φ a) (Finset.mem_image_of_mem φ ha)
  have hτx : τ • x = x := by
    apply Over.OverMorphism.ext
    have hring : (τ : L →+* L).comp φ.toRingHom = φ.toRingHom :=
      congrArg AlgHom.toRingHom hfix
    rw [pointGaloisAction_smul_left, ← hfactor, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hring]
  rw [mul_smul, hτx]

end CategoryTheory.Over
