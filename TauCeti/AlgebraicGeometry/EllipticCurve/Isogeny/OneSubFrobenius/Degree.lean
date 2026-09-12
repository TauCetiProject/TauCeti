/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Separable
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.TautologicalPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount

/-!
# The degree of `1 − π_q` is the number of rational points

Over a finite field the isogeny `1 − π_q` has degree the number of rational points of the curve.
One inequality is `pointCount_le_degree_oneSubFrobeniusIsogeny`: the kernel is every rational point
and the kernel is at most the degree. This file supplies the other.

An isogeny here has no map on points, so the count is made on embeddings of the function field.
Write `L` for the pulled-back field. Two embeddings of `K(W)` over `L` agree on `L`, so they move
the tautological point of `1 − π_q` to the same place; that image is the difference of the generic
point's image and its `q`-power image, so the two images of the generic point differ by a point
fixed by the `q`-power map, which therefore comes from the base field. An embedding is determined
by where it sends the generic point, so the resulting assignment of a rational point to an
embedding is injective. The separable degree is the number of such embeddings, and `1 − π_q` is
separable, so the degree is at most the point count.

## Main results

* `TauCeti.Isogeny.card_emb_oneSubFrobeniusIsogeny_le_pointCount`: the embeddings of `K(W)` over
  the pulled-back field are at most as many as the rational points.
* `TauCeti.Isogeny.degree_oneSubFrobeniusIsogeny_le_pointCount`: hence `deg (1 − π_q)` is at most
  the point count.
* `TauCeti.Isogeny.degree_oneSubFrobeniusIsogeny_eq_pointCount`: with the reverse bound,
  `deg (1 − π_q) = #E(𝔽_q)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10 and V.1.1.

## Provenance

The route is that of the AINTLIB `HasseWeil` project (Chris Birkbeck, Apache-2.0) at commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`, `HasseWeil/Isogeny/VerschiebungFactorization.lean`,
declaration `emb_le_card_kernel`, which assembles the same count at the point level. The proof
differs in what it rests on: there an isogeny carries its own map on points and the argument is
placed over `AlgebraicClosure K(E)` explicitly, while here the kernel is the translation-fixing
subgroup of the pulled-back field and the embeddings are Mathlib's `Field.Emb`, so the descent is
`WeierstrassCurve.Affine.Point.map_frobeniusAlgHom_eq_self_iff_mem_range_baseChange` and the
injectivity is `WeierstrassCurve.Affine.map_genericPoint_injective`.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **There are at most as many embeddings of the function field over the pulled-back field as
there are rational points.** Each embedding is sent to the rational point by which it moves the
generic point away from a fixed base embedding. -/
theorem card_emb_oneSubFrobeniusIsogeny_le_pointCount :
    Nat.card (Field.Emb (oneSubFrobeniusIsogeny W).fieldPullback.fieldRange W.FunctionField) ≤
      W.pointCount := by
  classical
  rw [WeierstrassCurve.pointCount_eq_card_point]
  set L := (oneSubFrobeniusIsogeny W).fieldPullback.fieldRange
  have hagree : ∀ σ τ : Field.Emb L W.FunctionField, ∀ z ∈ L,
      (σ.restrictScalars F) z = (τ.restrictScalars F) z := by
    intro σ τ z hz
    simpa using (σ.commutes ⟨z, hz⟩).trans (τ.commutes ⟨z, hz⟩).symm
  obtain ⟨σ₀⟩ : Nonempty (Field.Emb L W.FunctionField) := inferInstance
  choose f hf using fun σ : Field.Emb L W.FunctionField ↦
    exists_baseChange_eq_sub_map_genericPoint W (σ.restrictScalars F) (σ₀.restrictScalars F)
      (hagree σ σ₀)
  refine Nat.card_le_card_of_injective f ?_
  intro σ τ h
  have hQ : Point.map (σ.restrictScalars F) (genericPoint W) =
      Point.map (τ.restrictScalars F) (genericPoint W) := by
    have h2 : Point.map (σ.restrictScalars F) (genericPoint W) -
          Point.map (σ₀.restrictScalars F) (genericPoint W) =
        Point.map (τ.restrictScalars F) (genericPoint W) -
          Point.map (σ₀.restrictScalars F) (genericPoint W) := by
      rw [← hf σ, ← hf τ, h]
    exact sub_left_inj.1 h2
  exact AlgHom.restrictScalars_injective F (map_genericPoint_injective W hQ)

/-- **The degree of `1 − π_q` is at most the number of rational points**, the isogeny being
separable, so that its degree is the number of embeddings counted above. -/
theorem degree_oneSubFrobeniusIsogeny_le_pointCount :
    (oneSubFrobeniusIsogeny W).degree ≤ W.pointCount := by
  have := isSeparable_oneSubFrobeniusIsogeny W
  rw [← separableDegree_eq_degree_of_isSeparable, separableDegree_def]
  exact card_emb_oneSubFrobeniusIsogeny_le_pointCount W

/-- **`deg (1 − π_q) = #E(𝔽_q)`**, the first input of the Hasse bound. -/
@[simp]
theorem degree_oneSubFrobeniusIsogeny_eq_pointCount :
    (oneSubFrobeniusIsogeny W).degree = W.pointCount :=
  le_antisymm (degree_oneSubFrobeniusIsogeny_le_pointCount W)
    (pointCount_le_degree_oneSubFrobeniusIsogeny W)

end TauCeti.Isogeny

end
