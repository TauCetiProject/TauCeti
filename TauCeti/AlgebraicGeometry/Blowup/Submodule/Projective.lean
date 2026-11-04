/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Submodule.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange

/-!
# Projectivity of the blowup of a submodule

For a `C`-algebra `B` and a finite set `F ⊆ B`, the blowup of `J = span C F` is a projective
scheme over `C`. Its closed embedding into `Proj (Sym_C (F →₀ C))` is induced by the graded
surjection sending the free coordinate indexed by `f` to `f T` in `R(J)`. The embedding preserves
the structure morphism to `Spec C`, and the standard coordinate opens pull back to `D₊(f T)`.
These identities retain the projective presentation used in coherent-cohomology arguments.

The embedding itself is defined for arbitrary `F`; finiteness is needed only for projectivity
over the base. Neither noetherianity of `C` nor generation of the unit ideal of `B` is required.

The construction uses `submoduleBlowup.presentation`, the symmetric-algebra presentation of
the existing coefficient subalgebra, and `Proj.isClosedImmersion_map` for graded quotients.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of Theorem 2.5, Case I, diagram (1.1).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, §§2 and 7, projective spectra and projective
  embeddings.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.submoduleBlowup

universe u

variable (C : Type u) {B : Type u} [CommRing C] [CommRing B] [Algebra C B] (F : Set B)

/-- The closed embedding of the submodule blowup into the projective spectrum on the free
coordinates indexed by `F`, induced by sending the coordinate `f` to `f T`. -/
noncomputable def projectiveEmbedding :
    submoduleBlowup C F ⟶ Proj (SymmetricAlgebra.homogeneousSubmodule C (F →₀ C)) :=
  Proj.map (presentation C F)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (presentation_surjective C))

/-- The projective embedding is the `Proj.map` induced by the graded presentation. -/
theorem projectiveEmbedding_def :
    projectiveEmbedding C F = Proj.map (presentation C F)
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (presentation_surjective C)) := (rfl)

/-- The projective presentation is a closed immersion, even for an infinite generating set. -/
instance isClosedImmersion_projectiveEmbedding : IsClosedImmersion (projectiveEmbedding C F) :=
  Proj.isClosedImmersion_map _ _ (presentation_surjective C)

/-- The projective embedding is a morphism over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem projectiveEmbedding_projToSpec :
    projectiveEmbedding C F ≫ SymmetricAlgebra.projToSpec C (F →₀ C) = toSpec C F := by
  simpa only [projectiveEmbedding, SymmetricAlgebra.projToSpec_def, toSpec_def,
    Proj.toSpecCoeff_def] using
    Proj.map_toSpecCoeff (SymmetricAlgebra.homogeneousSubmodule C (F →₀ C)) (presentation C F)
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (presentation_surjective C))
      (presentation_gradedZeroRingHom_algebraMap C)

/-- A coordinate open pulls back to the corresponding standard open of the submodule blowup. -/
@[simp]
theorem projectiveEmbedding_preimage_basicOpen (f : F) :
    projectiveEmbedding C F ⁻¹ᵁ
        Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule C (F →₀ C))
          (_root_.SymmetricAlgebra.ι C (F →₀ C) (Finsupp.single f 1)) =
      Proj.basicOpen (gradedRing C F) (monomialDegreeOne C f.2) := by
  rw [projectiveEmbedding, Proj.map_preimage_basicOpen, presentation_ι_single, one_smul]

/-- The projective embedding commutes with the specified structure maps to `Spec C`. -/
instance isOver_projectiveEmbedding : (projectiveEmbedding C F).IsOver (Spec (.of C)) where
  comp_over := projectiveEmbedding_projToSpec C F

/-- **The blowup of a finitely generated submodule is projective over the coefficient ring.**
The ambient projective space has one homogeneous coordinate for each generator in `F`. -/
theorem isProjectiveOver (hF : F.Finite) : (submoduleBlowup C F).IsProjectiveOver C := by
  have := hF.to_subtype
  exact Scheme.IsProjectiveOver.of_isClosedImmersion C (projectiveEmbedding C F)

end TauCeti.AlgebraicGeometry.submoduleBlowup
