/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Center
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.Topology.Algebra.PointTopology.HopfIdeal
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.HopfIdeal

/-!
# The centre on adelic points

Let `H` be a commutative Hopf algebra over the fraction field `K` of a Dedekind domain `R`, and
let `Z ⊆ G = Spec H` be the centre, the closed subgroup scheme cut out by the Hopf ideal
`TauCeti.CommHopfAlgCat.centerDefiningIdeal H`. This file defines its adelic points
`Z(𝔸_K) = TauCeti.AdelicPoints.centerPoints R K H` as the subgroup of `G(𝔸_K)` of points vanishing
on that ideal, and proves that

* `Z(𝔸_K)` is closed in `G(𝔸_K)`, because `𝔸_K` is Hausdorff and the point topology makes every
  evaluation continuous;
* `Z(𝔸_K)` lies in the centre of the group `G(𝔸_K)`, because its points are universally central;
* `Z(K) = Z(𝔸_K) ∩ G(K)` along the rational diagonal, the case of the centre of the statement for
  any Hopf ideal in `TauCeti.NumberTheory.NumberField.Global.AdelicPoints.HopfIdeal`. This needs
  `𝔸_K` nontrivial, which holds for number fields; for `R = K = 𝔽_p` there are no places and
  `𝔸_K` is the zero ring.

## Main declarations

* `TauCeti.AdelicPoints.centerPoints`: the adelic points `Z(𝔸_K)` of the centre.
* `TauCeti.AdelicPoints.isClosed_centerPoints`, `TauCeti.AdelicPoints.centerPoints_le_center`.
* `TauCeti.AdelicPoints.comap_diagonal_centerPoints`,
  `TauCeti.AdelicPoints.centerPoints_inf_range_diagonal`: `Z(K) = Z(𝔸_K) ∩ G(K)`.
* `TauCeti.AdelicPoints.centerPoints_eq_top`: for a commutative group, such as `𝔾ₘ`, every adelic
  point lies in the centre.
* For `GLₙ`, `Z(𝔸_K)` is the centre of `GLₙ(𝔸_K)`, the invertible scalar matrices: an `example`
  applying `TauCeti.GeneralLinear.map_centerPointsSubgroup_pointsMulEquiv_eq_center`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2.
-/

public section

open IsDedekindDomain NumberField WithConv TauCeti.CommHopfAlgCat

universe u

namespace TauCeti

namespace AdelicPoints

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (H : _root_.CommHopfAlgCat.{u} K)

/-- The adelic points `Z(𝔸_K)` of the centre `Z` of `G = Spec H`: the subgroup of `G(𝔸_K)` of
points vanishing on the Hopf ideal `TauCeti.CommHopfAlgCat.centerDefiningIdeal H` cutting out
`Z`. This is `TauCeti.CommHopfAlgCat.centerPointsSubgroup H` with coefficients in `𝔸_K`, which
that declaration cannot express unless `𝔸_K` lies in the universe of `H`. -/
noncomputable abbrev centerPoints : Subgroup (AdelicPoints R K H) :=
  quotientPointsSubgroup H (centerDefiningIdeal H) (CommAlgCat.of K (AdeleRing R K))

/-- `Z(𝔸_K)` is a closed subgroup of `G(𝔸_K)`. -/
theorem isClosed_centerPoints : IsClosed (centerPoints R K H : Set (AdelicPoints R K H)) :=
  PointTopology.isClosed_quotientPointsSubgroup (AdeleRing R K) H (centerDefiningIdeal H)

/-- `Z(𝔸_K)` is contained in the centre of the group `G(𝔸_K)`. -/
theorem centerPoints_le_center : centerPoints R K H ≤ Subgroup.center (AdelicPoints R K H) :=
  fun _ hx ↦ HopfAlgebra.center_le_center <| HopfAlgebra.mem_center.mpr <|
    isCentralPoint_of_mem_quotientPointsSubgroup H _ (isCentral_centerDefiningIdeal H)
      (CommAlgCat.of K (AdeleRing R K)) hx

/-- For a commutative affine group, such as `𝔾ₘ`, every adelic point lies in the centre:
`Z(𝔸_K) = G(𝔸_K)`. -/
theorem centerPoints_eq_top [Coalgebra.IsCocomm K H] : centerPoints R K H = ⊤ := by
  rw [centerPoints, (centerDefiningIdeal_eq_bot_iff_isCocomm H).2 inferInstance,
    quotientPointsSubgroup_bot]

/-! ### Rational points of the centre -/

variable {R K H} [Nontrivial (AdeleRing R K)]

/-- A rational point lies in `Z(𝔸_K)` exactly when it lies in `Z(K)`. -/
@[simp]
theorem diagonal_mem_centerPoints_iff (g : WithConv (H →ₐ[K] K)) :
    diagonal R K H g ∈ centerPoints R K H ↔
      g ∈ quotientPointsSubgroup H (centerDefiningIdeal H) (CommAlgCat.of K K) := by
  rw [centerPoints, diagonal_mem_quotientPointsSubgroup_iff]

variable (R K H)

/-- `Z(K) = Z(𝔸_K) ∩ G(K)`, as the preimage of `Z(𝔸_K)` under the rational diagonal. -/
theorem comap_diagonal_centerPoints :
    (centerPoints R K H).comap (diagonal R K H) =
      quotientPointsSubgroup H (centerDefiningIdeal H) (CommAlgCat.of K K) := by
  rw [centerPoints, comap_diagonal_quotientPointsSubgroup]

/-- `Z(K) = Z(𝔸_K) ∩ G(K)`: the intersection of `Z(𝔸_K)` with the image of `G(K)` is the image of
`Z(K)` under the rational diagonal. -/
theorem centerPoints_inf_range_diagonal :
    centerPoints R K H ⊓ (diagonal R K H).range =
      (quotientPointsSubgroup H (centerDefiningIdeal H) (CommAlgCat.of K K)).map
        (diagonal R K H) := by
  rw [centerPoints, map_diagonal_quotientPointsSubgroup]

/-! ### The general linear group -/

section GeneralLinear

variable (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (n : ℕ)

open GeneralLinear in
/-- For `GLₙ`, the adelic points of the centre are the centre of the group `GLₙ(𝔸_K)` of
invertible adelic matrices, which consists of the invertible scalar matrices; this is
`TauCeti.GeneralLinear.map_centerPointsSubgroup_pointsMulEquiv_eq_center` with coefficients in
`𝔸_K`. -/
example :
    (centerPoints R K (coordinateHopfAlgebra K n)).map (pointsMulEquiv n).toMonoidHom =
      Subgroup.center (Matrix.GeneralLinearGroup (Fin n) (AdeleRing R K)) :=
  map_centerPointsSubgroup_pointsMulEquiv_eq_center n (CommAlgCat.of K (AdeleRing R K))

end GeneralLinear

end AdelicPoints

end TauCeti
