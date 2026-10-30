/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer

/-!
# Adjoint orbits as homogeneous spaces

Let `G = Spec H` be an affine group of finite type over a field `k`, with Lie algebra `𝔤`. The
adjoint orbit `Oₓ` of `x ∈ 𝔤` is the orbit of `x` under the adjoint representation. It is realized
as the orbit of the line through `(x, 1)` in the projective completion `P(𝔤 × k)` of `𝔤`, and it
lies in the affine chart `𝔤` (`TauCeti.Comodule.range_projectiveOrbitMap_subset_basicOpen_snd`).
Its stabilizer is the centralizer `C_G(x)`.

For a reduced group over an algebraically closed field:

* the orbit scheme of `x` represents the fppf homogeneous quotient `G / C_G(x)`;
* `dim Oₓ + dim C_G(x) = dim G`;
* in characteristic zero, where every group of finite type is reduced, `dim Oₓ = dim [𝔤, x]`,
  the rank of `ad x`. Here `[𝔤, x]` is the image of `x` under the differentiated adjoint action,
  the expected tangent space of the orbit at `x`.

These are the orbit and dimension statements behind the classification of nilpotent orbits, where
`x` is a nilpotent element of a semisimple Lie algebra. Smoothness of the orbit scheme and the
identification of its tangent spaces are not proved here.

## Main declarations

* `TauCeti.fppfHomogeneousQuotientIsoAdjointOrbitPoints`: `G / C_G(x)` is represented by the
  adjoint orbit scheme of `x`.
* `TauCeti.topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_centralizerHopfIdeal`:
  `dim Oₓ + dim C_G(x) = dim G`.
* `TauCeti.topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad`: in
  characteristic zero, `dim Oₓ = dim [𝔤, x]`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Chapter 1, for adjoint orbits and centralizers.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3, for orbit dimensions.
* J. S. Milne, *Algebraic Groups* (2017), §7.c and Chapter 10.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

section Quotient

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [_root_.IsReduced H]

/-- **The adjoint orbit is the homogeneous space of the centralizer.** For a reduced affine group
`G` of finite type over an algebraically closed field, the fppf homogeneous quotient `G / C_G(x)`
is isomorphic to the sheaf of points of the adjoint orbit scheme of `x`, the projective orbit
scheme of the line through `(x, 1)` in `P(𝔤 × k)`. -/
noncomputable def fppfHomogeneousQuotientIsoAdjointOrbitPoints
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    CommHopfAlgCat.fppfHomogeneousQuotient H (centralizerHopfIdeal H x) ≅
      Comodule.projectiveOrbitPointsSheaf (H := H)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one x) :=
  Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints _ _ _ fun A g h ↦ by
    rw [centralizerHopfIdeal_def]
    exact Comodule.coset_stabilizerHopfIdeal_eq_iff_exists_units_matrixCoefficient x A g h

/-- The isomorphism `G / C_G(x) ≅ Oₓ` restricts to the orbit map `g ↦ Ad(g) x` along the
projection `G ⟶ G / C_G(x)`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_fppfHomogeneousQuotientIsoAdjointOrbitPoints_hom
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    CommHopfAlgCat.fppfHomogeneousQuotientProjection H (centralizerHopfIdeal H x) ≫
        (fppfHomogeneousQuotientIsoAdjointOrbitPoints x).hom.hom =
      Comodule.toProjectiveOrbitPoints
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one x) := by
  rw [fppfHomogeneousQuotientIsoAdjointOrbitPoints,
    Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom,
    Comodule.fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints]

end Quotient

section Dimension

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

/-- **The dimension of an adjoint orbit.** For a reduced affine group `G` of finite type over an
algebraically closed field, the adjoint orbit `Oₓ` of `x` satisfies
`dim Oₓ + dim C_G(x) = dim G`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_centralizerHopfIdeal
    [_root_.IsReduced H] (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap (H := H)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one x))) +
      ringKrullDim (H ⧸ (centralizerHopfIdeal H x).toIdeal) = ringKrullDim H := by
  rw [centralizerHopfIdeal_def]
  exact Comodule.topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_stabilizerHopfIdeal x

/-- **The dimension of an adjoint orbit in characteristic zero.** For an affine group `G` of finite
type over an algebraically closed field of characteristic zero, the adjoint orbit of `x` has the
dimension of `[𝔤, x]`, the rank of `ad x`. No reducedness hypothesis is needed: such a group is
reduced by Cartier's theorem. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad [CharZero k]
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap (H := H)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one x))) =
      Module.finrank k (LinearMap.range
        (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)) := by
  rw [Comodule.topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range]
  -- Both ranks complement the dimension of the same centralizer in `dim G`.
  have hstab := Comodule.ringKrullDim_quotient_stabilizerHopfIdeal_add_finrank_range
    (k := k) (H := H) x
  have had := ringKrullDim_quotient_centralizerHopfIdeal_add_finrank_range_ad (k := k) (H := H) x
  rw [centralizerHopfIdeal_def, ← hstab,
    Comodule.ringKrullDim_quotient_stabilizerHopfIdeal (k := k) (H := H) x] at had
  norm_cast at had ⊢
  omega

end Dimension

end TauCeti
