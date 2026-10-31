/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.StabilizerDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Dimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Smooth projective orbit schemes

The locally closed projective orbit scheme of a line in a finite-dimensional representation of
a reduced affine group over an algebraically closed field is smooth over that field. No
connectedness assumption on the group is needed. Its structural morphism is smooth of relative
dimension `n` exactly when the orbit has dimension `n`.

These results concern the existing scheme-theoretic orbit image, not only its rational points.
They apply to vector orbits using the line through `(v, 1)` in the projective completion, and in
particular to adjoint orbits. They do not assert smoothness of the projection from the group to
the orbit: in positive characteristic its stabilizer can be nonreduced.

The smooth-locus argument uses `Scheme.Hom.smooth_of_transitive_on_closedPoints` and the existing
projective orbit translations. The relative-dimension characterization uses the equality of the
local dimensions at closed orbit points with the global orbit dimension.

## Main results

* `TauCeti.Comodule.smooth_projectiveOrbitToSpec`: projective orbit schemes are smooth.
* `TauCeti.Comodule.smoothOfRelativeDimension_projectiveOrbitToSpec_iff`: their relative dimension
  is their orbit dimension, also for disconnected groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [_root_.IsReduced H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The locally closed orbit scheme of a line under a reduced finite-type affine group is
smooth over the algebraically closed base field, even if the group is disconnected. -/
instance smooth_projectiveOrbitToSpec (m : M) (hm : Module.IsUnimodular k m) :
    Smooth (projectiveOrbitToSpec (H := H) m hm) := by
  apply Scheme.Hom.smooth_of_transitive_on_closedPoints
  intro y hy z hz
  obtain ⟨g, hg⟩ := exists_projectiveOrbitTranslation_eq_of_mem_closedPoints m hm hy hz
  exact ⟨projectiveOrbitTranslation m hm g, projectiveOrbitTranslation_hom_toSpec m hm g, hg⟩

/-- The orbit of a line is smooth of relative dimension `n` precisely when its topological
image in projective space has dimension `n`. Connectedness of the acting group is not required. -/
theorem smoothOfRelativeDimension_projectiveOrbitToSpec_iff
    (m : M) (hm : Module.IsUnimodular k m) (n : ℕ) :
    SmoothOfRelativeDimension n (projectiveOrbitToSpec (H := H) m hm) ↔
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) = n := by
  rw [← topologicalKrullDim_projectiveOrbitScheme]
  constructor
  · intro hn
    have := hn
    have : Nonempty (projectiveOrbitScheme (H := H) m hm) :=
      ⟨toProjectiveOrbit (H := H) m hm (Bialgebra.augmentationPoint k H)⟩
    exact TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension
      (projectiveOrbitToSpec (H := H) m hm)
  · intro hn
    apply (TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (projectiveOrbitToSpec (H := H) m hm) n).mpr
    refine ⟨inferInstance, fun y hy ↦ ?_⟩
    rw [ringKrullDim_stalk_eq_coheight,
      coheight_eq_topologicalKrullDim_of_mem_closedPoints m hm hy, hn]

end TauCeti.Comodule
