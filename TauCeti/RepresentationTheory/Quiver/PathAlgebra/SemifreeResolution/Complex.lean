/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BimoduleResolution.Grading
public import TauCeti.Algebra.Homology.GradedCochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The small path-algebra resolution as a sequence of complexes

For an integer-weight-graded path algebra with a DG differential killing the vertex
idempotents, the twisted arrow-term differential and the vertex-term differential raise
weight by one. Thus the standard bimodule sequence is a short exact sequence of cochain
complexes of scalar modules, not just an ungraded exact sequence equipped with square-zero
endomorphisms. The arrow generators retain their arrow weights.

This is the underlying sequence of complexes used to form the small resolution of a
semifree DG path algebra, including the two-dimensional Ginzburg algebra. No semifreeness,
cofibrancy, or Hochschild comparison is asserted here.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  for the small resolution in the Hochschild calculation.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.PathAlgebra

universe u v w

variable (k : Type w) [CommRing k] (Q : Type u) [Quiver.{v} Q] [Fintype Q]
  (wt : ∀ {i j : Q}, (i ⟶ j) → ℤ) (d : pathAlgebra k Q →ₗ[k] pathAlgebra k Q)
  (hd : IsDGAlgebra (gradeBy k wt) d) (hdε : ∀ i, d (vertexIdempotent k i) = 0)

local notation "A" => pathAlgebra k Q
include hd hdε

/-- The differential on the vertex term raises total arrow weight by one. -/
theorem isHomogeneous_vertexTensorBimoduleDifferential :
    LinearMap.IsHomogeneous (vertexTensorBimoduleDifferential wt d)
      (vertexTensorGrading k Q wt).piece (vertexTensorGrading k Q wt).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro n x hx
  rw [mem_vertexTensorGrading_piece_iff, coe_vertexTensorBimoduleDifferential hd hdε]
  have h := isHomogeneous_envelopeDifferential
    (InternalGrading.mk (gradeBy k wt) (isInternal_gradeBy k wt)) rfl
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ hd.map_mem hx) 0
  exact h.map_mem ((mem_vertexTensorGrading_piece_iff k Q wt).mp hx)

/-- The vertex term with its total-weight grading and enveloping differential. -/
noncomputable abbrev vertexTensorComplex : CochainComplex (ModuleCat k) ℤ :=
  gradedCochainComplex (M := vertexTensorBimodule k Q) (vertexTensorGrading k Q wt).piece
    (vertexTensorBimoduleDifferential wt d)
    (isHomogeneous_vertexTensorBimoduleDifferential k Q wt d hd hdε)
    (fun _ x ↦ vertexTensorBimoduleDifferential_vertexTensorBimoduleDifferential hd hdε x)

variable [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]

/-- The twisted differential on the arrow term raises total arrow weight by one. -/
theorem isHomogeneous_arrowTensorBimoduleDifferential :
    LinearMap.IsHomogeneous (arrowTensorBimoduleDifferential wt d)
      (arrowTensorGrading k Q wt).piece (arrowTensorGrading k Q wt).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro n x hx
  rw [mem_arrowTensorGrading_piece_iff,
    coe_arrowTensorDifferential_arrowTensorBimoduleDifferential hd hdε]
  have h := (isHomogeneous_vertexTensorBimoduleDifferential k Q wt d hd hdε).map_mem
    ((isHomogeneous_arrowTensorDifferential k Q wt).map_mem hx)
  simpa only [add_zero, mem_vertexTensorGrading_piece_iff,
    coe_vertexTensorBimoduleDifferential hd hdε] using h

/-- The arrow term with its arrow-weight grading and twisted differential. -/
noncomputable abbrev arrowTensorComplex : CochainComplex (ModuleCat k) ℤ :=
  gradedCochainComplex (M := arrowTensorBimodule k Q) (arrowTensorGrading k Q wt).piece
    (arrowTensorBimoduleDifferential wt d)
    (isHomogeneous_arrowTensorBimoduleDifferential k Q wt d hd hdε)
    (fun _ x ↦ arrowTensorBimoduleDifferential_arrowTensorBimoduleDifferential hd hdε x)

local notation "K" => gradedCochainComplex (gradeBy k wt) d
  (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ hd.map_mem hx)
  (fun _ x ↦ hd.sq_zero x)

/-- The boundary of the standard resolution as a map of cochain complexes. -/
noncomputable def arrowTensorDifferentialComplexHom :
    arrowTensorComplex k Q wt d hd hdε ⟶ vertexTensorComplex k Q wt d hd hdε :=
  gradedCochainComplexHom ((arrowTensorDifferential k Q).restrictScalars k)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦
      (isHomogeneous_arrowTensorDifferential k Q wt).map_mem hx)
    (LinearMap.ext fun x ↦ (arrowTensorDifferential_arrowTensorBimoduleDifferential hd hdε x).symm)

/-- Multiplication, identifying the diagonal bimodule with the original path algebra,
as a map of cochain complexes. -/
noncomputable def vertexTensorComplexAugmentation :
    vertexTensorComplex k Q wt d hd hdε ⟶ K :=
  gradedCochainComplexHom
    ((Bimodule.of (AlgHom.id k A)).symm.toLinearMap ∘ₗ
      (vertexTensorMul k Q).restrictScalars k)
    (by
      rw [LinearMap.isHomogeneous_def]
      intro n x hx
      have h := (isHomogeneous_vertexTensorMul k Q wt).map_mem hx
      simpa only [add_zero, InternalGrading.mem_map_piece_iff, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearMap.restrictScalars_apply] using h)
    (by
      ext x
      simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
        congrArg (Bimodule.of (AlgHom.id k A)).symm
          (vertexTensorMul_vertexTensorBimoduleDifferential hd hdε x).symm)

/-- The boundary acts by the existing arrow-tensor boundary on every homogeneous piece. -/
@[simp]
theorem arrowTensorDifferentialComplexHom_f_apply (n : ℤ)
    (x : (arrowTensorComplex k Q wt d hd hdε).X n) :
    (gradedCochainComplexXEquiv n
      (((arrowTensorDifferentialComplexHom k Q wt d hd hdε).f n).hom x) :
        vertexTensorBimodule k Q) =
      arrowTensorDifferential k Q (gradedCochainComplexXEquiv n x) := by
  simp only [arrowTensorDifferentialComplexHom,
    gradedCochainComplexXEquiv_gradedCochainComplexHom_f_apply, LinearMap.restrictScalars_apply]

omit [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)] in
/-- The augmentation multiplies the two tensor factors on every homogeneous piece. -/
@[simp]
theorem vertexTensorComplexAugmentation_f_apply (n : ℤ)
    (x : (vertexTensorComplex k Q wt d hd hdε).X n) :
    (gradedCochainComplexXEquiv n
      (((vertexTensorComplexAugmentation k Q wt d hd hdε).f n).hom x) : A) =
      (Bimodule.of (AlgHom.id k A)).symm
        (vertexTensorMul k Q (gradedCochainComplexXEquiv n x)) := by
  simp only [vertexTensorComplexAugmentation,
    gradedCochainComplexXEquiv_gradedCochainComplexHom_f_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]

/-- The universal derivation relative to the vertex subalgebra, as a map of cochain complexes.
It has degree zero before suspending the arrow term in the small resolution. -/
noncomputable def arrowTensorDerivationComplexHom :
    K ⟶ arrowTensorComplex k Q wt d hd hdε :=
  gradedCochainComplexHom (arrowTensorDerivation k Q)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦
      (isHomogeneous_arrowTensorDerivation k Q wt).map_mem hx)
    (LinearMap.ext fun x ↦ arrowTensorBimoduleDifferential_arrowTensorDerivation hd hdε x)

/-- On each homogeneous piece the complex-level derivation is the universal derivation. -/
@[simp]
theorem arrowTensorDerivationComplexHom_f_apply (n : ℤ) (x : (K).X n) :
    (gradedCochainComplexXEquiv n
      (((arrowTensorDerivationComplexHom k Q wt d hd hdε).f n).hom x) :
        arrowTensorBimodule k Q) =
      arrowTensorDerivation k Q (gradedCochainComplexXEquiv n x) := by
  simp only [arrowTensorDerivationComplexHom,
    gradedCochainComplexXEquiv_gradedCochainComplexHom_f_apply]

/-- The standard path-algebra bimodule sequence, viewed as scalar cochain complexes. -/
noncomputable def standardResolutionSequence :
    ShortComplex (CochainComplex (ModuleCat k) ℤ) where
  X₁ := arrowTensorComplex k Q wt d hd hdε
  X₂ := vertexTensorComplex k Q wt d hd hdε
  X₃ := K
  f := arrowTensorDifferentialComplexHom k Q wt d hd hdε
  g := vertexTensorComplexAugmentation k Q wt d hd hdε
  zero := by
    apply gradedCochainComplex_hom_ext
    intro n x
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
      ModuleCat.hom_comp, LinearMap.comp_apply,
      vertexTensorComplexAugmentation_f_apply, arrowTensorDifferentialComplexHom_f_apply,
      vertexTensorMul_arrowTensorDifferential, ModuleCat.hom_zero, LinearMap.zero_apply,
      map_zero, ZeroMemClass.coe_zero]

/-- The arrow-to-vertex boundary followed by multiplication is zero as a complex map. -/
@[reassoc (attr := simp)]
theorem arrowTensorDifferentialComplexHom_comp_vertexTensorComplexAugmentation :
    arrowTensorDifferentialComplexHom k Q wt d hd hdε ≫
      vertexTensorComplexAugmentation k Q wt d hd hdε = 0 :=
  (standardResolutionSequence k Q wt d hd hdε).zero

@[simp]
theorem standardResolutionSequence_X₁ :
    (standardResolutionSequence k Q wt d hd hdε).X₁ = arrowTensorComplex k Q wt d hd hdε := (rfl)

@[simp]
theorem standardResolutionSequence_X₂ :
    (standardResolutionSequence k Q wt d hd hdε).X₂ = vertexTensorComplex k Q wt d hd hdε := (rfl)

@[simp]
theorem standardResolutionSequence_X₃ :
    (standardResolutionSequence k Q wt d hd hdε).X₃ = K := (rfl)

/-- The first map of the sequence is the boundary, under its component identifications.
The transports are needed because the sequence's object fields are not exposed. -/
@[simp]
theorem standardResolutionSequence_f :
    (standardResolutionSequence k Q wt d hd hdε).f =
      eqToHom (standardResolutionSequence_X₁ k Q wt d hd hdε) ≫
        arrowTensorDifferentialComplexHom k Q wt d hd hdε ≫
          eqToHom (standardResolutionSequence_X₂ k Q wt d hd hdε).symm := (rfl)

/-- The second map of the sequence is multiplication, under its component identifications.
The transports are needed because the sequence's object fields are not exposed. -/
@[simp]
theorem standardResolutionSequence_g :
    (standardResolutionSequence k Q wt d hd hdε).g =
      eqToHom (standardResolutionSequence_X₂ k Q wt d hd hdε) ≫
        vertexTensorComplexAugmentation k Q wt d hd hdε ≫
          eqToHom (standardResolutionSequence_X₃ k Q wt d hd hdε).symm := (rfl)

/-- The standard resolution sequence is short exact as a sequence of cochain complexes.
In particular, its exactness holds in every cohomological degree, with the twisted arrow
differential rather than an unrelated grading on the ungraded sequence. -/
theorem shortExact_standardResolutionSequence :
    (standardResolutionSequence k Q wt d hd hdε).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact
    (C := ModuleCat.{max u v w} k) (c := ComplexShape.up ℤ)
    (standardResolutionSequence k Q wt d hd hdε) ?_
  intro n
  dsimp only [standardResolutionSequence, ShortComplex.map, HomologicalComplex.eval_obj,
    HomologicalComplex.eval_map]
  apply ModuleCat.shortComplex_shortExact
  · -- Exactness lifts from the ungraded sequence: the boundary detects the degree of its preimage.
    intro y
    constructor
    · intro hy
      have hy0 : vertexTensorMul k Q (gradedCochainComplexXEquiv n y) = 0 := by
        apply (Bimodule.of (AlgHom.id k A)).symm.injective
        simpa only [vertexTensorComplexAugmentation_f_apply,
          map_zero, ZeroMemClass.coe_zero] using congrArg
          (fun z ↦ (gradedCochainComplexXEquiv n z : A)) hy
      obtain ⟨x, hx⟩ := (exact_arrowTensorDifferential_vertexTensorMul _).mp hy0
      have hxdeg : x ∈ (arrowTensorGrading k Q wt).piece n := by
        rw [mem_arrowTensorGrading_piece_iff, hx]
        exact (mem_vertexTensorGrading_piece_iff k Q wt).mp
          (gradedCochainComplexXEquiv n y).2
      refine ⟨(gradedCochainComplexXEquiv n).symm ⟨x, hxdeg⟩, ?_⟩
      apply (gradedCochainComplexXEquiv n).injective
      apply Subtype.ext
      simpa only [arrowTensorDifferentialComplexHom_f_apply, LinearEquiv.apply_symm_apply] using hx
    · rintro ⟨x, rfl⟩
      have hzero := ((standardResolutionSequence k Q wt d hd hdε).map
        (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℤ) n)).zero
      exact congr($(hzero) x)
  · intro x y h
    apply (gradedCochainComplexXEquiv n).injective
    apply Subtype.ext
    apply arrowTensorDifferential_injective
    simpa only [arrowTensorDifferentialComplexHom_f_apply] using congrArg
      (fun z ↦ (gradedCochainComplexXEquiv n z : vertexTensorBimodule k Q)) h
  · -- Multiplication is onto in each degree.
    intro x
    obtain ⟨z, hz⟩ := exists_vertexTensorMul_eq_of_mem k Q wt (gradedCochainComplexXEquiv n x).2
    refine ⟨(gradedCochainComplexXEquiv n).symm z, ?_⟩
    apply (gradedCochainComplexXEquiv n).injective
    apply Subtype.ext
    simp only [vertexTensorComplexAugmentation_f_apply,
      LinearEquiv.apply_symm_apply, hz, LinearEquiv.symm_apply_apply]

end TauCeti.PathAlgebra
