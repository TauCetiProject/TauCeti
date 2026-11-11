/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.Complex
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# The augmented small resolution of a DG path algebra

For an arrow-weight-graded path algebra with a DG differential killing the vertex
idempotents, the cone of the arrow-to-vertex boundary is quasi-isomorphic to the path
algebra. Its degree `n` term is the sum of the arrow term in degree `n + 1` and the
vertex term in degree `n`. In particular, an arrow of weight `r` gives a suspended
universal differential in degree `r - 1`.

The augmentation is multiplication on the vertex term and zero on the suspended arrow
term. The suspended universal derivation records the cone differential, including the
minus sign on the arrow-term differential. These are underlying complexes of scalar
modules: no DG bimodule structure or cofibrancy assertion is made here. The construction
applies, in particular, to the non-completed two-dimensional Ginzburg DG algebra.

The quasi-isomorphism uses Mathlib's `CochainComplex.mappingCone.quasiIso_descShortComplex`
and the degreewise exact standard path-algebra sequence.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  for the small resolution used to compute Hochschild cohomology.
-/

public section

open CategoryTheory CochainComplex HomComplex

namespace TauCeti.PathAlgebra

universe u v w

variable (k : Type w) [CommRing k] (Q : Type u) [Quiver.{v} Q] [Fintype Q]
  [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]
  (wt : ∀ {i j : Q}, (i ⟶ j) → ℤ) (d : pathAlgebra k Q →ₗ[k] pathAlgebra k Q)
  (hd : IsDGAlgebra (gradeBy k wt) d) (hdε : ∀ i, d (vertexIdempotent k i) = 0)

local notation "K" => gradedCochainComplex (gradeBy k wt) d
  (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ hd.map_mem hx)
  (fun _ x ↦ hd.sq_zero x)

local notation "∂" => arrowTensorDifferentialComplexHom k Q wt d hd hdε

/-- The small resolution as a scalar cochain complex: the mapping cone of the standard
arrow-to-vertex boundary. The native mapping-cone inclusions and projections apply to it. -/
noncomputable abbrev standardResolution : CochainComplex (ModuleCat k) ℤ :=
  mappingCone ∂

/-- The augmentation of the small resolution, equal to multiplication on the vertex term
and zero on the suspended arrow term. -/
noncomputable def standardResolutionAugmentation :
    standardResolution k Q wt d hd hdε ⟶ K :=
  mappingCone.desc ∂ 0 (vertexTensorComplexAugmentation k Q wt d hd hdε) (by simp)

/-- On the vertex term the augmentation is the existing multiplication map. -/
@[reassoc (attr := simp)]
theorem inr_standardResolutionAugmentation :
    mappingCone.inr ∂ ≫ standardResolutionAugmentation k Q wt d hd hdε =
      vertexTensorComplexAugmentation k Q wt d hd hdε := by
  simp [standardResolutionAugmentation]

/-- The augmentation kills the suspended arrow term. -/
@[reassoc (attr := simp)]
theorem inl_v_standardResolutionAugmentation_f (i j : ℤ) (h : i + (-1) = j) :
    (mappingCone.inl ∂).v i j h ≫
      (standardResolutionAugmentation k Q wt d hd hdε).f j = 0 := by
  simp [standardResolutionAugmentation]

/-- The small resolution resolves the DG path algebra: its augmentation induces an
isomorphism in every cohomological degree. No restriction on the arrow weights or on the
number of arrows is needed. -/
instance quasiIso_standardResolutionAugmentation :
    QuasiIso (standardResolutionAugmentation k Q wt d hd hdε) := by
  let S := ShortComplex.mk ∂ (vertexTensorComplexAugmentation k Q wt d hd hdε)
    (arrowTensorDifferentialComplexHom_comp_vertexTensorComplexAugmentation k Q wt d hd hdε)
  -- Transport the opaque short-complex object fields to the explicitly named terms.
  let e : standardResolutionSequence k Q wt d hd hdε ≅ S := ShortComplex.isoMk
    (eqToIso (standardResolutionSequence_X₁ k Q wt d hd hdε))
    (eqToIso (standardResolutionSequence_X₂ k Q wt d hd hdε))
    (eqToIso (standardResolutionSequence_X₃ k Q wt d hd hdε))
    (by simp [S]) (by simp [S])
  simpa only [S, standardResolutionAugmentation, mappingCone.descShortComplex] using
    mappingCone.quasiIso_descShortComplex
      (ShortComplex.shortExact_of_iso e (shortExact_standardResolutionSequence k Q wt d hd hdε))

/-- The universal derivation into the suspended arrow term of the small resolution,
as a cochain of degree `-1`. -/
noncomputable def standardResolutionDerivation :
    Cochain K (standardResolution k Q wt d hd hdε) (-1) :=
  (Cochain.ofHom (arrowTensorDerivationComplexHom k Q wt d hd hdε)).comp
    (mappingCone.inl ∂) (by omega)

/-- The suspended derivation on a homogeneous piece is the universal derivation followed
by the left cone inclusion. -/
@[simp]
theorem standardResolutionDerivation_v (i j : ℤ) (h : i + (-1) = j) :
    (standardResolutionDerivation k Q wt d hd hdε).v i j h =
      (arrowTensorDerivationComplexHom k Q wt d hd hdε).f i ≫
        (mappingCone.inl ∂).v i j h := by
  simp [standardResolutionDerivation]

/-- The differential of the suspended universal derivation is its boundary in the vertex
term. Equivalently, on homogeneous elements the cone differential is boundary minus the
suspended differential of the universal derivation. -/
@[simp]
theorem δ_standardResolutionDerivation :
    δ (-1) 0 (standardResolutionDerivation k Q wt d hd hdε) =
      Cochain.ofHom (arrowTensorDerivationComplexHom k Q wt d hd hdε ≫
        ∂ ≫ mappingCone.inr ∂) := by
  simp [standardResolutionDerivation]

end TauCeti.PathAlgebra
