/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.RingTheory.Node.Basic
import Mathlib.AlgebraicGeometry.Fiber
import TauCeti.RingTheory.Node.BaseChange
import TauCeti.RingTheory.Node.Flat

/-!
# The local model of a node as a relative curve

For a ring `R` and `a ∈ R`, the morphism `Spec R[x, y] ⧸ (xy - a) ⟶ Spec R` is the local model
of a node in a family of curves: over a discrete valuation ring with uniformizer `π` and
`a = πⁿ`, its generic fibre is smooth and its special fibre is the union of two lines crossing
transversally at the origin.

This file shows that this morphism is flat, locally of finite presentation, and of pure relative
dimension one. These are the conditions, beside nodality of the geometric fibres, in the fibrewise
characterization of families of curves with at worst nodal singularities. The fibre over a prime
`p` of `R` is the spectrum of `κ(p) ⊗[R] R[x, y] ⧸ (xy - a)`, that is, of the node algebra of the
image of `a` in the residue field `κ(p)` (`TauCeti.NodeAlgebra.baseChange`), and over a field
the node algebra is pure of dimension one (`TauCeti.NodeAlgebra.isPureDimensional_primeSpectrum`).

## Main results

* `TauCeti.NodeAlgebra.flat_spec`: the local model of a node is flat.
* `TauCeti.NodeAlgebra.locallyOfFinitePresentation_spec`: it is locally of finite presentation.
* `TauCeti.NodeAlgebra.pureRelativeDimension_spec`: it has pure relative dimension one.

## References

* [Stacks Project, Example 55.14.1, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC), the
  local model `xy = πⁿ` of a node over a discrete valuation ring.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti

namespace NodeAlgebra

universe u

variable {R : Type u} [CommRing R] (a : R)

/-- The local model of a node is flat. -/
instance flat_spec : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The local model of a node is locally of finite presentation. -/
instance locallyOfFinitePresentation_spec :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr <|
    RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- The fibre of the local model of a node over a prime `p` of `R` is homeomorphic to the
spectrum of the node algebra of the image of `a` in the residue field `κ(p)`. -/
private def fiberHomeomorph (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))).fiber p ≃ₜ
      PrimeSpectrum (NodeAlgebra p.asIdeal.ResidueField (algebraMap R _ a)) :=
  (Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R (NodeAlgebra R a) p)).hom.homeomorph
    |>.trans (PrimeSpectrum.homeomorphOfRingEquiv (baseChange a).toRingEquiv)

/-- The local model of a node has pure relative dimension one: every fibre is a curve all of
whose irreducible components are one-dimensional. -/
instance pureRelativeDimension_spec :
    PureRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))) := by
  rw [pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber]
  refine ⟨⟨fun p ↦ ?_⟩, fun p ↦ ?_⟩
  · rw [(fiberHomeomorph a p).isHomeomorph.topologicalKrullDim_eq,
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_one]
    rfl
  · exact (isPureDimensional_primeSpectrum _).homeomorph (fiberHomeomorph a p).symm

end NodeAlgebra

end TauCeti
