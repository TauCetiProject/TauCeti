/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver.Basic
public import TauCeti.AlgebraicGeometry.Limits.Coproduct
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction

/-!
# Finite coproducts of projective schemes

A finite family of schemes projective over a commutative ring has a projective coproduct over
that ring. The ambient module is the finite product of the modules of homogeneous coordinates
of the summands. Projection onto a coordinate block induces a closed immersion of its projective
spectrum; different blocks have disjoint images. The coproduct of these embeddings is a closed
immersion, without any reducedness or flatness assumption on the coefficient ring.

The structure morphism of the coproduct is the descent of the structure morphisms of its
summands. In particular, the result concerns projectivity over the specified affine base.
The coordinate maps use `SymmetricAlgebra.gradedMap`, the graded lift of the linear
projections, together with `Proj.map` and `Proj.isClosedImmersion_map`.
-/

public section

universe u v

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.SymmetricAlgebra

namespace TauCeti.SymmetricAlgebra

variable (R : Type u) [CommRing R] {ι : Type}
  (M : ι → Type u) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The embedding of the projective spectrum of one coordinate block in that of the full
product of coordinate modules. -/
noncomputable def projPiι (i : ι) :
    Proj (homogeneousSubmodule R (M i)) ⟶ Proj (homogeneousSubmodule R (∀ i, M i)) :=
  Proj.map (SymmetricAlgebra.gradedMap R (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i))
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (by
      simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
        SymmetricAlgebra.map_surjective R (LinearMap.proj i) (Function.surjective_eval i)))

/-- Each coordinate block is a closed projective subspace. -/
instance isClosedImmersion_projPiι (i : ι) : IsClosedImmersion (projPiι R M i) :=
  Proj.isClosedImmersion_map _ _ (by
    simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
      SymmetricAlgebra.map_surjective R (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i)
        (Function.surjective_eval i))

/-- Coordinate-block embeddings preserve the specified coefficient morphisms. -/
@[reassoc (attr := simp)]
theorem projPiι_projToSpec (i : ι) :
    projPiι R M i ≫ projToSpec R (∀ i, M i) = projToSpec R (M i) :=
  Proj.map_gradedMap_projToSpec R _ _

/-- Pulling back a standard open along a coordinate-block embedding evaluates its linear
coordinate in that block. -/
@[simp]
theorem projPiι_preimage_basicOpen_ι (i : ι) (m : ∀ i, M i) :
    projPiι R M i ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule R (∀ i, M i))
      (SymmetricAlgebra.ι R (∀ i, M i) m) =
        Proj.basicOpen (homogeneousSubmodule R (M i)) (SymmetricAlgebra.ι R (M i) (m i)) := by
  simp [projPiι]

/-- Distinct coordinate blocks have disjoint images in the projective spectrum of their
product. This holds over every commutative ring, including nonreduced rings. -/
theorem pairwise_disjoint_range_projPiι :
    Pairwise fun i j ↦ Disjoint (Set.range (projPiι R M i)) (Set.range (projPiι R M j)) := by
  classical
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hxy⟩
  have hcover := iSup_basicOpen_ι_eq_top R (M i) (id : M i → M i)
    (by simp)
  simp only [id_eq] at hcover
  have hx : x ∈ ⨆ m : M i, Proj.basicOpen (homogeneousSubmodule R (M i))
      (SymmetricAlgebra.ι R (M i) m) := by rw [hcover]; trivial
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let v : ∀ i, M i := Pi.single i m
  let U := Proj.basicOpen (homogeneousSubmodule R (∀ i, M i))
    (SymmetricAlgebra.ι R (∀ i, M i) v)
  have hxU : projPiι R M i x ∈ U := by
    have heq := projPiι_preimage_basicOpen_ι R M i v
    exact (congrArg (fun W ↦ x ∈ W) heq).mpr (by simpa [v] using hm)
  have hyU : y ∈ projPiι R M j ⁻¹ᵁ U := by simpa [hxy] using hxU
  have heq := projPiι_preimage_basicOpen_ι R M j v
  have : y ∈ Proj.basicOpen (homogeneousSubmodule R (M j)) (0 : SymmetricAlgebra R (M j)) := by
    simpa [U, v, hij.symm] using (congrArg (fun W ↦ y ∈ W) heq).mp hyU
  simp at this

end TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

variable (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
  (X : ι → Scheme.{u}) [∀ i, (X i).Over (Spec (.of R))]

/-- A finite coproduct of schemes projective over `Spec R` is projective over `Spec R`, with
structure morphism the descent of the structure morphisms of its summands. -/
theorem IsProjectiveOver.sigma [∀ i, (X i).IsProjectiveOver R] :
    let sigmaXOver : (∐ X).Over (Spec (.of R)) := ⟨Sigma.desc fun i ↦ X i ↘ Spec (.of R)⟩
    (∐ X).IsProjectiveOver R := by
  classical
  let sigmaXOver : (∐ X).Over (Spec (.of R)) := ⟨Sigma.desc fun i ↦ X i ↘ Spec (.of R)⟩
  -- Reindex by a finite type in Type so the ambient product stays in the ring universe.
  let Y : Shrink.{0} ι → Scheme.{u} := X ∘ (equivShrink.{0} ι).symm
  have : Finite (Shrink.{0} ι) := Finite.of_equiv ι (equivShrink.{0} ι)
  let : ∀ i, (Y i).Over (Spec (.of R)) := by
    dsimp only [Y, Function.comp_apply]
    infer_instance
  have : ∀ i, (Y i).IsProjectiveOver R := by
    dsimp only [Y, Function.comp_apply]
    infer_instance
  let sigmaYOver : (∐ Y).Over (Spec (.of R)) := ⟨Sigma.desc fun i ↦ Y i ↘ Spec (.of R)⟩
  have hY : (∐ Y).IsProjectiveOver R := by
    choose M _ _ _ f hf hfR using fun i ↦
      IsProjectiveOver.exists_isClosedImmersion (R := R) (X := Y i)
    let g (i : Shrink.{0} ι) := f i ≫ projPiι R M i
    have hdisj : Pairwise fun i j ↦ Disjoint (Set.range (g i)) (Set.range (g j)) := by
      intro i j hij
      apply (pairwise_disjoint_range_projPiι R M hij).mono
      · rintro _ ⟨x, rfl⟩
        exact ⟨f i x, by simp [g]⟩
      · rintro _ ⟨x, rfl⟩
        exact ⟨f j x, by simp [g]⟩
    have : ∀ i, IsClosedImmersion (g i) := fun _ ↦ inferInstance
    have : IsClosedImmersion (Sigma.desc g) := isClosedImmersion_sigmaDesc g hdisj
    refine ⟨⟨(∀ i, M i), inferInstance, inferInstance, inferInstance, Sigma.desc g,
      inferInstance, ⟨?_⟩⟩⟩
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc]
    dsimp only [g]
    rw [Category.assoc, over_eq_projToSpec, projPiι_projToSpec,
      ← over_eq_projToSpec, comp_over]
    exact (Sigma.ι_comp_desc (fun i ↦ Y i ↘ Spec (.of R)) i).symm
  let e : (∐ Y) ≅ ∐ X := Sigma.reindex (equivShrink.{0} ι).symm X
  have : e.hom.IsOver (Spec (.of R)) := by
    constructor
    -- The two coproduct structure morphisms were chosen by descent.
    dsimp only [CategoryTheory.over, sigmaXOver, sigmaYOver, OverClass.hom]
    apply Sigma.hom_ext
    intro i
    dsimp only [e]
    rw [Sigma.ι_reindex_hom_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
  exact IsProjectiveOver.of_isClosedImmersion R e.inv

end AlgebraicGeometry.Scheme
