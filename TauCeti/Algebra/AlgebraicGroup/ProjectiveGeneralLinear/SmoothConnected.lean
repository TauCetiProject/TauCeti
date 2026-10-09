/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Reduced
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected

/-!
# Smoothness and geometric connectedness of the projective general linear group

The represented group `PGLₙ = Aut(Mₙ)` is smooth and geometrically connected over every field.
These are the ambient geometric conditions needed to study its reductivity and its adjoint
semisimple form. Both results include rank zero and impose no restriction on the characteristic.

The coordinate embedding for conjugation `GLₙ → PGLₙ` already proves geometric reducedness of
`O(PGLₙ)`. Smoothness follows from the finite-type Hopf-algebra criterion
`TauCeti.smoothCommHopfAlgProperty_of_geometricallyReduced`, which uses Mathlib's
`AlgebraicGeometry.smooth_of_grpObj`. Geometric connectedness descends along the same embedding
from `GLₙ`, using `TauCeti.geometricallyConnectedCommHopfAlgProperty.of_injective`.

The results are supplied both for coordinate Hopf algebras and for the structural morphism of
the named group scheme, through the existing affine Hopf/group-scheme dictionary.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 5.49.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.ProjectiveGeneralLinear

universe u

noncomputable section

variable (n : ℕ) (k : Type u) [Field k]

/-- The coordinate algebra of `PGLₙ` is smooth over every field, in every rank and
characteristic. -/
instance instSmoothCoordinateHopfAlgebra :
    Algebra.Smooth k (coordinateHopfAlgebra n k) := by
  apply (smoothCommHopfAlgProperty_iff _).mp
  apply smoothCommHopfAlgProperty_of_geometricallyReduced
  rw [geometricallyReducedCommHopfAlgProperty_iff]
  intro K _ _
  have hGL := geometricallyReducedCommHopfAlgProperty_of_smooth k
    (GeneralLinear.coordinateHopfAlgebra k n)
    ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)
  rw [geometricallyReducedCommHopfAlgProperty_iff] at hGL
  let _ := hGL K
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (conjugationMap n k).hom.toAlgHom (AlgHom.id k K)).toRingHom
    (Module.Flat.rTensor_preserves_injective_linearMap _ (conjugationMap_injective n k))

/-- The coordinate Hopf algebra of `PGLₙ` is geometrically connected over every field. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra n k) :=
  geometricallyConnectedCommHopfAlgProperty.of_injective
    (conjugationMap n k).hom.toAlgHom (conjugationMap_injective n k)
    (GeneralLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n)

/-- The structural morphism of the projective general linear group scheme is smooth
over every field. -/
instance smooth_groupScheme : Smooth (groupScheme n k).X.hom := by
  simp only [ConstantMultiplication.groupScheme_def]
  simpa only [smoothAffineGroupSchemeProperty_iff] using
    (algebraSmooth_iff_smooth_hopfSpec k (coordinateHopfAlgebra n k)).mp
    ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)

/-- The structural morphism of the projective general linear group scheme is geometrically
connected over every field. -/
instance geometricallyConnected_groupScheme :
    GeometricallyConnected (groupScheme n k).X.hom := by
  simp only [ConstantMultiplication.groupScheme_def]
  exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k
    (coordinateHopfAlgebra n k)).mp
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra n k)

end

end TauCeti.ProjectiveGeneralLinear
