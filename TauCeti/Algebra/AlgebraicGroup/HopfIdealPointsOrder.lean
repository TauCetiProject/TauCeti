/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdealPointsNaturality

/-!
# Order of Hopf-ideal quotient point subgroups

A Hopf ideal `I` cuts out, on every value algebra `A`, the subgroup of ambient points
`H(A)` which vanish on `I`. This file records the elementary order behavior of this
construction: if `I ≤ J`, then every point which kills `J` also kills `I`, so the subgroup
cut out by `J` is contained in the subgroup cut out by `I`.

This is the point-level order bookkeeping for the Layer 3 ReductiveGroups roadmap item
"Hopf ideals ↔ closed subgroup schemes". Larger Hopf ideals correspond contravariantly to
smaller closed subgroup functors, and the inclusion is compatible with functoriality in the
value algebra.

## Main declarations

* `CommHopfAlgCat.quotientPointsSubgroup_antitone`: the cut-out point subgroup is antitone in
  the Hopf ideal.
* `CommHopfAlgCat.quotientPointsSubgroupInclusion`: the inclusion hom
  `G_J(A) →* G_I(A)` for `I ≤ J`.
* `CommHopfAlgCat.mapQuotientPointsSubgroup_inclusion`: these inclusions commute with
  post-composition in the value algebra.

## References

This uses the vanishing characterization of quotient points from
`TauCeti.Algebra.AlgebraicGroup.HopfIdealPoints` and the naturality API from
`TauCeti.Algebra.AlgebraicGroup.HopfIdealPointsNaturality`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The point subgroup cut out by a Hopf ideal is antitone in the Hopf ideal:
larger ideals impose more vanishing equations. -/
theorem quotientPointsSubgroup_antitone (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    Antitone fun I : HopfIdeal R H => quotientPointsSubgroup H I A := by
  intro I J hIJ g hg
  rw [mem_quotientPointsSubgroup_iff] at hg ⊢
  intro h hh
  exact hg h (hIJ hh)

/-- If `I ≤ J`, then the point subgroup cut out by `J` is contained in the point subgroup
cut out by `I`. -/
theorem quotientPointsSubgroup_le_of_le (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H J A ≤ quotientPointsSubgroup H I A :=
  quotientPointsSubgroup_antitone H A hIJ

/-- Rewriting form of `quotientPointsSubgroup_le_of_le` as a membership implication. -/
theorem mem_quotientPointsSubgroup_of_le (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) (A : CommAlgCat.{w} R)
    {g : HopfAlgebra.points (R := R) (H := H) A}
    (hg : g ∈ quotientPointsSubgroup H J A) :
    g ∈ quotientPointsSubgroup H I A :=
  quotientPointsSubgroup_le_of_le H hIJ A hg

/-- If `I = J`, then the point subgroups cut out by `I` and `J` are equal. -/
@[simp]
theorem quotientPointsSubgroup_eq_of_eq (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I = J) (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H I A = quotientPointsSubgroup H J A := by
  subst hIJ
  rfl

/-- The point subgroup cut out by the zero Hopf ideal is the full ambient point group. -/
@[simp]
theorem quotientPointsSubgroup_bot (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H (⊥ : HopfIdeal R H) A = ⊤ := by
  ext g
  constructor
  · intro _
    exact Subgroup.mem_top g
  · intro _
    rw [mem_quotientPointsSubgroup_iff]
    intro h hh
    rw [HopfIdeal.mem_bot.mp hh, map_zero]

/-- For `I ≤ J`, the inclusion of point subgroups cut out by Hopf ideals,
`G_J(A) →* G_I(A)`. -/
@[expose] noncomputable def quotientPointsSubgroupInclusion
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H J A →* quotientPointsSubgroup H I A :=
  Subgroup.inclusion (quotientPointsSubgroup_le_of_le H hIJ A)

/-- The inclusion between cut-out point subgroups is the identity on ambient points. -/
@[simp]
theorem quotientPointsSubgroupInclusion_apply
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R) (g : quotientPointsSubgroup H J A) :
    quotientPointsSubgroupInclusion H hIJ A g =
      ⟨g, mem_quotientPointsSubgroup_of_le H hIJ A g.property⟩ :=
  rfl

/-- Coercing the inclusion between cut-out point subgroups gives the same ambient point. -/
@[simp]
theorem coe_quotientPointsSubgroupInclusion_apply
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R) (g : quotientPointsSubgroup H J A) :
    (quotientPointsSubgroupInclusion H hIJ A g :
      HopfAlgebra.points (R := R) (H := H) A) = g :=
  rfl

/-- Pointwise form of the inclusion between cut-out point subgroups. -/
@[simp]
theorem quotientPointsSubgroupInclusion_apply_apply
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R) (g : quotientPointsSubgroup H J A) (h : H) :
    ((quotientPointsSubgroupInclusion H hIJ A g :
      HopfAlgebra.points (R := R) (H := H) A).ofConv) h = g.val.ofConv h :=
  rfl

/-- Inclusions of cut-out point subgroups compose along chains of Hopf ideals. -/
@[simp]
theorem quotientPointsSubgroupInclusion_comp
    (H : _root_.CommHopfAlgCat.{v} R) {I J K : HopfIdeal R H}
    (hIJ : I ≤ J) (hJK : J ≤ K) (A : CommAlgCat.{w} R) :
    (quotientPointsSubgroupInclusion H hIJ A).comp
        (quotientPointsSubgroupInclusion H hJK A) =
      quotientPointsSubgroupInclusion H (hIJ.trans hJK) A := by
  ext g
  rfl

/-- The inclusion for `I ≤ I` is the identity homomorphism. -/
@[simp]
theorem quotientPointsSubgroupInclusion_refl
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    quotientPointsSubgroupInclusion H (le_refl I) A =
      MonoidHom.id (quotientPointsSubgroup H I A) := by
  ext g
  rfl

/-- The subgroup inclusions associated to `I ≤ J` commute with maps of value algebras. -/
theorem mapQuotientPointsSubgroup_inclusion
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    {A B : CommAlgCat.{w} R} (χ : A ⟶ B) (g : quotientPointsSubgroup H J A) :
    mapQuotientPointsSubgroup H I χ
        (quotientPointsSubgroupInclusion H hIJ A g) =
      quotientPointsSubgroupInclusion H hIJ B
        (mapQuotientPointsSubgroup H J χ g) := by
  apply Subtype.ext
  rw [coe_mapQuotientPointsSubgroup_apply, coe_quotientPointsSubgroupInclusion_apply,
    coe_quotientPointsSubgroupInclusion_apply, coe_mapQuotientPointsSubgroup_apply]

end CommHopfAlgCat

end TauCeti
