/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import TauCeti.AlgebraicGeometry.Curves.SingularLocus
public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.RingTheory.Node.Basic
import Mathlib.AlgebraicGeometry.Fiber
import TauCeti.RingTheory.Node.BaseChange
import TauCeti.RingTheory.Node.Differential
import TauCeti.RingTheory.Node.Flat

/-!
# The local model of a node as a relative curve

For a ring `R` and `a ∈ R`, the morphism `Spec R[x, y] ⧸ (xy - a) ⟶ Spec R` is the local model
of a node in a family of curves: over a discrete valuation ring with uniformizer `π` and
`a = πⁿ` with `n > 0`, its generic fibre is smooth and its special fibre is the union of two
lines crossing transversally at the origin.

This file shows that this morphism is flat, locally of finite presentation, and of pure relative
dimension one. These are the conditions, beside nodality of the geometric fibres, in the fibrewise
characterization of families of curves with at worst nodal singularities. The fibre over a prime
`p` of `R` is the spectrum of `κ(p) ⊗[R] R[x, y] ⧸ (xy - a)`, that is, of the node algebra of the
image of `a` in the residue field `κ(p)` (`TauCeti.NodeAlgebra.baseChange`), and over a field
the node algebra is pure of dimension one (`TauCeti.NodeAlgebra.isPureDimensional_primeSpectrum`).

Its relative singular locus, the closed subscheme cut out by the first Fitting ideal sheaf of the
relative differentials, is cut out by the two coordinates `x` and `y`.

## Main results

* `TauCeti.NodeAlgebra.flat_spec`: the local model of a node is flat.
* `TauCeti.NodeAlgebra.locallyOfFinitePresentation_spec`: it is locally of finite presentation.
* `TauCeti.NodeAlgebra.fiberIso`: its fibres are spectra of node algebras over residue fields.
* `TauCeti.NodeAlgebra.pureRelativeDimension_spec`: it has pure relative dimension one.
* `TauCeti.NodeAlgebra.singularLocus_ideal_top`: its singular locus is cut out by `(x, y)`.

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

/-- The fibre of the local model of a node over a prime `p` of `R` is the spectrum of the node
algebra of the image of `a` in the residue field `κ(p)`. -/
def fiberIso (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))).fiber p ≅
      Spec (.of (NodeAlgebra p.asIdeal.ResidueField (algebraMap R _ a))) :=
  Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R (NodeAlgebra R a) p) ≪≫
    Scheme.Spec.mapIso (baseChange a).toRingEquiv.toCommRingCatIso.symm.op

/-- The underlying homeomorphism of `fiberIso`. -/
private def fiberHomeomorph (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))).fiber p ≃ₜ
      PrimeSpectrum (NodeAlgebra p.asIdeal.ResidueField (algebraMap R _ a)) :=
  (fiberIso a p).hom.homeomorph

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

/-- The direct structure morphism on the node chart, used to avoid the `Spec`-over-`Spec`
instance diamond when applying the singular-locus API. -/
local instance (priority := high) nodeSpecOverSpec :
    (Spec (.of (NodeAlgebra R a))).Over (Spec (.of R)) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))

local instance : Flat (Spec (.of (NodeAlgebra R a)) ↘ Spec (.of R)) :=
  flat_spec a

local instance :
    LocallyOfFinitePresentation (Spec (.of (NodeAlgebra R a)) ↘ Spec (.of R)) :=
  locallyOfFinitePresentation_spec a

local instance :
    PureRelativeDimension 1 (Spec (.of (NodeAlgebra R a)) ↘ Spec (.of R)) :=
  pureRelativeDimension_spec a

/-- The relative singular locus of the local model of a node `Spec R[x, y] ⧸ (xy - a)` over `R`
is cut out by the ideal `(x, y)` of the two coordinates. -/
theorem singularLocus_ideal_top :
    ((Spec (.of (NodeAlgebra R a))).singularLocus R).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {coord a 0, coord a 1}).map
        (Scheme.ΓSpecIso (.of (NodeAlgebra R a))).inv.hom := by
  rw [Scheme.singularLocus_ideal_top_Spec, fittingIdeal_differential_one]

end NodeAlgebra

end TauCeti
