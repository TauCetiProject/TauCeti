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
* `Z(K) = Z(𝔸_K) ∩ G(K)` along the rational diagonal: a rational point kills the defining ideal
  after extending its coefficients to `𝔸_K` exactly when it kills it over `K`, since `K → 𝔸_K` is
  injective. This needs `𝔸_K` nontrivial, which holds for number fields; for `R = K = 𝔽_p` there
  are no places and `𝔸_K` is the zero ring.

## Main declarations

* `TauCeti.AdelicPoints.centerPoints`: the adelic points `Z(𝔸_K)` of the centre.
* `TauCeti.AdelicPoints.isClosed_centerPoints`, `TauCeti.AdelicPoints.centerPoints_le_center`.
* `TauCeti.AdelicPoints.comap_diagonal_centerPoints`,
  `TauCeti.AdelicPoints.map_diagonal_centerPoints`: `Z(K) = Z(𝔸_K) ∩ G(K)`.
* `TauCeti.AdelicPoints.centerPoints_eq_top`: for a commutative group, such as `𝔾ₘ`, every adelic
  point lies in the centre.
* `TauCeti.AdelicPoints.map_centerPoints_pointsMulEquiv`: for `GLₙ`, `Z(𝔸_K)` is the centre of
  `GLₙ(𝔸_K)`, the invertible scalar matrices.

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
`Z`. -/
noncomputable def centerPoints : Subgroup (AdelicPoints R K H) :=
  quotientPointsSubgroup H (centerDefiningIdeal H) (CommAlgCat.of K (AdeleRing R K))

variable {R K H}

theorem mem_centerPoints_iff (x : AdelicPoints R K H) :
    x ∈ centerPoints R K H ↔ ∀ h : H, h ∈ centerDefiningIdeal H → x h = 0 :=
  mem_quotientPointsSubgroup_iff H _ (CommAlgCat.of K (AdeleRing R K)) x

variable (R K H)

/-- `Z(𝔸_K)` is a closed subgroup of `G(𝔸_K)`. -/
theorem isClosed_centerPoints : IsClosed (centerPoints R K H : Set (AdelicPoints R K H)) :=
  PointTopology.isClosed_quotientPointsSubgroup (AdeleRing R K) H (centerDefiningIdeal H)

variable {R K H}

/-- A point of `Z(𝔸_K)` is universally central: it commutes with every point of `G` after any
change of coefficients. -/
theorem isCentralPoint_of_mem_centerPoints {x : AdelicPoints R K H}
    (hx : x ∈ centerPoints R K H) : HopfAlgebra.IsCentralPoint x :=
  isCentralPoint_of_mem_quotientPointsSubgroup H _ (isCentral_centerDefiningIdeal H)
    (CommAlgCat.of K (AdeleRing R K)) hx

variable (R K H)

/-- `Z(𝔸_K)` is contained in the centre of the group `G(𝔸_K)`. -/
theorem centerPoints_le_center : centerPoints R K H ≤ Subgroup.center (AdelicPoints R K H) :=
  fun _ hx ↦ Subgroup.mem_center_iff.2 fun y ↦
    ((isCentralPoint_of_mem_centerPoints hx).commute y).symm.eq

/-- For a commutative affine group, such as `𝔾ₘ`, every adelic point lies in the centre:
`Z(𝔸_K) = G(𝔸_K)`. -/
theorem centerPoints_eq_top [Coalgebra.IsCocomm K H] : centerPoints R K H = ⊤ :=
  eq_top_iff.2 fun x _ ↦ (mem_centerPoints_iff x).2 fun h hh ↦ by
    rw [(centerDefiningIdeal_eq_bot_iff_isCocomm H).2 inferInstance] at hh
    rw [HopfIdeal.mem_bot.1 hh, map_zero]

/-! ### Rational points of the centre -/

variable {R K H} [Nontrivial (AdeleRing R K)]

/-- A rational point lies in `Z(𝔸_K)` exactly when it lies in `Z(K)`. -/
@[simp]
theorem diagonal_mem_centerPoints_iff (g : WithConv (H →ₐ[K] K)) :
    diagonal R K H g ∈ centerPoints R K H ↔
      g ∈ quotientPointsSubgroup H (centerDefiningIdeal H) (CommAlgCat.of K K) := by
  rw [mem_centerPoints_iff, mem_quotientPointsSubgroup_iff]
  refine forall₂_congr fun h _ ↦ ?_
  rw [diagonal_apply_apply, map_eq_zero_iff _ (algebraMap K (AdeleRing R K)).injective]

variable (R K H)

/-- `Z(K) = Z(𝔸_K) ∩ G(K)`, as the preimage of `Z(𝔸_K)` under the rational diagonal. -/
theorem comap_diagonal_centerPoints :
    (centerPoints R K H).comap (diagonal R K H) =
      quotientPointsSubgroup H (centerDefiningIdeal H) (CommAlgCat.of K K) :=
  Subgroup.ext diagonal_mem_centerPoints_iff

/-- `Z(K) = Z(𝔸_K) ∩ G(K)`: the image of `Z(K)` under the rational diagonal is the intersection of
`Z(𝔸_K)` with the image of `G(K)`. -/
theorem map_diagonal_centerPoints :
    (quotientPointsSubgroup H (centerDefiningIdeal H) (CommAlgCat.of K K)).map
        (diagonal R K H) =
      centerPoints R K H ⊓ (diagonal R K H).range := by
  rw [← comap_diagonal_centerPoints R K H, Subgroup.map_comap_eq, inf_comm]

/-! ### The general linear group -/

section GeneralLinear

variable (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (n : ℕ)

open GeneralLinear in
/-- For `GLₙ`, the adelic points of the centre are the centre of the group `GLₙ(𝔸_K)` of
invertible adelic matrices, which consists of the invertible scalar matrices. -/
theorem map_centerPoints_pointsMulEquiv :
    (centerPoints R K (coordinateHopfAlgebra K n)).map (pointsMulEquiv n).toMonoidHom =
      Subgroup.center (Matrix.GeneralLinearGroup (Fin n) (AdeleRing R K)) :=
  map_centerPointsSubgroup_pointsMulEquiv_eq_center n (CommAlgCat.of K (AdeleRing R K))

end GeneralLinear

end AdelicPoints

end TauCeti
