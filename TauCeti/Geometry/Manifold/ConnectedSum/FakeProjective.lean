/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Geometry.Manifold.ConnectedSum.Basic
public import TauCeti.Geometry.Manifold.Smoothable
public import TauCeti.Topology.ComplexProjectiveSpace.Basic
public import TauCeti.Topology.Homotopy.Fake

/-!
# The smoothable fake `ℝℙ⁴ # ℂℙ²`

Teichner asked (Kirby's problem list, Problem 4.82) whether the connected sum `∗ℝℙ⁴ # ∗ℂℙ²` of
the fake real projective space `∗ℝℙ⁴` and the fake complex projective plane `∗ℂℙ²` has a smooth
structure. Neither summand has one: `∗ℂℙ²` has nonzero Kirby–Siebenmann invariant, and `∗ℝℙ⁴` is
not smoothable either (Ruberman). The invariants add up to zero in the connected sum, so the
Kirby–Siebenmann obstruction vanishes. Ruberman and Stern proved that `∗ℝℙ⁴ # ∗ℂℙ²` is smoothable,
and that it is homotopy equivalent but not homeomorphic to `ℝℙ⁴ # ℂℙ²`: it is a fake smooth
`ℝℙ⁴ # ℂℙ²`. This file states their theorem (`TauCeti.RubermanSternTheorem`); it is not proved
here.

## The statement

A closed topological `4`-manifold is a compact Hausdorff space with charts to `ℝ⁴`, with no
condition on the transition maps, as in `TauCeti.TriangulationConjecture`. A fake `ℝℙ⁴` is such a
manifold homotopy equivalent but not homeomorphic to `ℝℙ⁴` (`TauCeti.IsFake`), with `ℝℙ⁴` the
quotient `TauCeti.RealProjectiveSpace 4` of the round `4`-sphere by the antipodal map, and
likewise a fake `ℂℙ²` is homotopy equivalent but not homeomorphic to
`TauCeti.ComplexProjectiveSpace 2`. Up to homeomorphism there is exactly one of each: for `ℂℙ²` by
Freedman's classification of simply connected closed `4`-manifolds, and for `ℝℙ⁴` because its
topological structure set has two elements (Hillman, Chapter 12). The statement quantifies over all
of them, so it is the statement about `∗ℝℙ⁴` and `∗ℂℙ²`; the standard `ℝℙ⁴` and `ℂℙ²` are not
fake copies of themselves (`TauCeti.not_isFake_self`), so they are excluded.

The connected sum is `TauCeti.ConnectedSum e₁ e₂` along coordinate balls `e₁ : ℝ⁴ → X` and
`e₂ : ℝ⁴ → Y`, open embeddings of `ℝ⁴`. Its topology is given, and the theorem asks for a smooth
atlas compatible with it (`TauCeti.IsSmoothable` for the model `𝓡 4`). The connected sum of
topological manifolds does not depend on the balls up to homeomorphism (by the topological
annulus theorem, and since `ℝℙ⁴` is non-orientable the orientations of the balls do not matter),
which is not formalized here; the statement asks for every choice of balls, on both sides.

## Main definitions

* `TauCeti.RubermanSternTheorem`: for every fake `ℝℙ⁴` `X`, fake `ℂℙ²` `Y` and coordinate balls,
  `X # Y` is smoothable and is a fake `ℝℙ⁴ # ℂℙ²`.

## Main results

* `TauCeti.RubermanSternTheorem.isSmoothable`: the smoothability part, the positive answer to
  Kirby's Problem 4.82.
* `TauCeti.RubermanSternTheorem.isFake`: the fake part.

## References

* R. Kirby, *Problems in low-dimensional topology*, in *Geometric Topology*, AMS/IP Stud. Adv.
  Math. 2.2 (1997), Problem 4.82 (Teichner).
* D. Ruberman, R. Stern, *A fake smooth `CP² # RP⁴`*, Math. Res. Lett. 4 (1997), 375–379,
  arXiv:dg-ga/9702003.
* D. Ruberman, *Invariant knots of free involutions of `S⁴`*, Topology Appl. 18 (1984), 217–224.
* M. Freedman, F. Quinn, *Topology of 4-Manifolds*, Princeton University Press (1990),
  Section 10.4.
* J. Hillman, *Four-Manifolds, Geometries and Knots*, Geometry & Topology Monographs 5 (2002),
  Chapter 12, arXiv:math/0212142.
-/

public section

open scoped Manifold

namespace TauCeti

universe u

/-- **Ruberman and Stern's theorem**, recorded as its statement. Let `X` be a fake `ℝℙ⁴` and `Y` a
fake `ℂℙ²`, closed topological `4`-manifolds homotopy equivalent but not homeomorphic to `ℝℙ⁴` and
`ℂℙ²`. Then for all coordinate balls `e₁` of `X` and `e₂` of `Y` the connected sum `X # Y` admits
a smooth structure, and it is a fake `ℝℙ⁴ # ℂℙ²`: homotopy equivalent but not homeomorphic to the
connected sum of `ℝℙ⁴` and `ℂℙ²` along any coordinate balls. The smoothability is the positive
answer to Teichner's question, Problem 4.82 of Kirby's list. -/
def RubermanSternTheorem : Prop :=
  ∀ (X Y : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) X] [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) Y],
    IsFake (RealProjectiveSpace 4) X → IsFake (ComplexProjectiveSpace 2) Y →
    ∀ (e₁ : EuclideanSpace ℝ (Fin 4) → X) (e₂ : EuclideanSpace ℝ (Fin 4) → Y),
      Topology.IsOpenEmbedding e₁ → Topology.IsOpenEmbedding e₂ →
      IsSmoothable (𝓡 4) (ConnectedSum e₁ e₂) ∧
        ∀ (f₁ : EuclideanSpace ℝ (Fin 4) → RealProjectiveSpace 4)
          (f₂ : EuclideanSpace ℝ (Fin 4) → ComplexProjectiveSpace 2),
          Topology.IsOpenEmbedding f₁ → Topology.IsOpenEmbedding f₂ →
          IsFake (ConnectedSum f₁ f₂) (ConnectedSum e₁ e₂)

namespace RubermanSternTheorem

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) X] [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) Y]
  {e₁ : EuclideanSpace ℝ (Fin 4) → X} {e₂ : EuclideanSpace ℝ (Fin 4) → Y}

/-- Under Ruberman and Stern's theorem, the connected sum of a fake `ℝℙ⁴` and a fake `ℂℙ²` along
any coordinate balls is smoothable: the answer to Kirby's Problem 4.82 is yes. -/
theorem isSmoothable (h : RubermanSternTheorem.{u}) (hX : IsFake (RealProjectiveSpace 4) X)
    (hY : IsFake (ComplexProjectiveSpace 2) Y) (he₁ : Topology.IsOpenEmbedding e₁)
    (he₂ : Topology.IsOpenEmbedding e₂) : IsSmoothable (𝓡 4) (ConnectedSum e₁ e₂) :=
  (h X Y hX hY e₁ e₂ he₁ he₂).1

/-- Under Ruberman and Stern's theorem, the connected sum of a fake `ℝℙ⁴` and a fake `ℂℙ²` is a
fake `ℝℙ⁴ # ℂℙ²`. -/
theorem isFake (h : RubermanSternTheorem.{u}) (hX : IsFake (RealProjectiveSpace 4) X)
    (hY : IsFake (ComplexProjectiveSpace 2) Y) (he₁ : Topology.IsOpenEmbedding e₁)
    (he₂ : Topology.IsOpenEmbedding e₂) {f₁ : EuclideanSpace ℝ (Fin 4) → RealProjectiveSpace 4}
    {f₂ : EuclideanSpace ℝ (Fin 4) → ComplexProjectiveSpace 2}
    (hf₁ : Topology.IsOpenEmbedding f₁) (hf₂ : Topology.IsOpenEmbedding f₂) :
    IsFake (ConnectedSum f₁ f₂) (ConnectedSum e₁ e₂) :=
  (h X Y hX hY e₁ e₂ he₁ he₂).2 f₁ f₂ hf₁ hf₂

end RubermanSternTheorem

end TauCeti
