/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic

/-!
# Rational points of closed subgroups on adelic points

Let `H` be a commutative Hopf algebra over the fraction field `K` of a Dedekind domain `R`, and let
`I` be a Hopf ideal of `H`, cutting out the closed subgroup scheme `Spec (H ⧸ I)` of `G = Spec H`.
Its rational points are the adelic points meeting `G(K)` along the rational diagonal: a rational
point kills `I` after extending its coefficients to `𝔸_K` exactly when it kills `I` over `K`,
since `K → 𝔸_K` is injective. This needs `𝔸_K` nontrivial, which holds for number fields; for
`R = K = 𝔽_p` there are no places and `𝔸_K` is the zero ring.

## Main declarations

* `TauCeti.AdelicPoints.diagonal_mem_quotientPointsSubgroup_iff`: a rational point lies in the
  adelic points cut out by `I` exactly when it lies in the rational points cut out by `I`.
* `TauCeti.AdelicPoints.comap_diagonal_quotientPointsSubgroup`,
  `TauCeti.AdelicPoints.map_diagonal_quotientPointsSubgroup`: the same statement as a preimage and
  as an image under the rational diagonal.
-/

public section

open IsDedekindDomain NumberField TauCeti.CommHopfAlgCat

universe u

namespace TauCeti

namespace AdelicPoints

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {H : _root_.CommHopfAlgCat.{u} K} [Nontrivial (AdeleRing R K)]

/-- A rational point lies in the adelic points of the closed subgroup scheme cut out by a Hopf
ideal `I` exactly when it lies in its rational points. -/
@[simp]
theorem diagonal_mem_quotientPointsSubgroup_iff (I : HopfIdeal K H) (g : WithConv (H →ₐ[K] K)) :
    diagonal R K H g ∈ quotientPointsSubgroup H I (CommAlgCat.of K (AdeleRing R K)) ↔
      g ∈ quotientPointsSubgroup H I (CommAlgCat.of K K) := by
  rw [diagonal_eq_mapValue]
  exact mapValue_mem_quotientPointsSubgroup_iff H I (algebraMap K (AdeleRing R K)).injective g

variable (R K H)

/-- The rational points of the closed subgroup scheme cut out by `I` are the preimage of its
adelic points under the rational diagonal. -/
theorem comap_diagonal_quotientPointsSubgroup (I : HopfIdeal K H) :
    (quotientPointsSubgroup H I (CommAlgCat.of K (AdeleRing R K))).comap (diagonal R K H) =
      quotientPointsSubgroup H I (CommAlgCat.of K K) := by
  rw [diagonal_eq_mapValue]
  exact comap_mapValue_quotientPointsSubgroup H I (algebraMap K (AdeleRing R K)).injective

/-- The image under the rational diagonal of the rational points of the closed subgroup scheme
cut out by `I` is the intersection of its adelic points with the image of `G(K)`. -/
theorem map_diagonal_quotientPointsSubgroup (I : HopfIdeal K H) :
    (quotientPointsSubgroup H I (CommAlgCat.of K K)).map (diagonal R K H) =
      quotientPointsSubgroup H I (CommAlgCat.of K (AdeleRing R K)) ⊓ (diagonal R K H).range := by
  rw [← comap_diagonal_quotientPointsSubgroup R K H I, Subgroup.map_comap_eq, inf_comm]

end AdelicPoints

end TauCeti
