/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdealPointsOrder

/-!
# Order maps between Hopf-ideal quotients

If `I ≤ J` are Hopf ideals in a commutative Hopf algebra `H`, then the quotient map
`H ⟶ H ⧸ J` kills `I`, so it factors through a coordinate morphism
`H ⧸ I ⟶ H ⧸ J`. Contravariantly, this is the map on closed-subgroup functors induced by
the inclusion of the subgroup cut out by `J` into the subgroup cut out by `I`.

This file records that quotient-to-quotient morphism in `CommHopfAlgCat` and in the
finite-type wrapper, together with its compatibility with the already-defined point subgroup
inclusions.

## Main declarations

* `CommHopfAlgCat.quotientMapOfLe`: the coordinate morphism `H ⧸ I ⟶ H ⧸ J` induced by
  `I ≤ J`.
* `CommHopfAlgCat.quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app`: on points,
  precomposition with `quotientMapOfLe` is compatible with the ambient quotient-points
  inclusions.
* `FiniteTypeCommHopfAlgCat.quotientMapOfLe`: the same morphism for finite-type
  commutative Hopf algebras.

## References

This is point-level and coordinate-ring bookkeeping for the ReductiveGroups roadmap,
Layer 3, "Hopf ideals ↔ closed subgroup schemes". It uses the quotient universal property
from `TauCeti.Algebra.AlgebraicGroup.HopfIdealQuotient` and the cut-out subgroup order API
from `TauCeti.Algebra.AlgebraicGroup.HopfIdealPointsOrder`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- If `I ≤ J`, then the quotient map by `J` kills every element of `I`. -/
lemma toIdeal_le_ker_mkQuotient_of_le
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    I.toIdeal ≤ RingHom.ker (mkQuotient H J).hom.toAlgHom.toRingHom := by
  intro h hh
  rw [RingHom.mem_ker]
  change (mkQuotient H J).hom h = 0
  rw [mkQuotient_eq_zero_iff]
  exact (HopfIdeal.mem_toIdeal (I := J)).mpr
    (hIJ ((HopfIdeal.mem_toIdeal (I := I)).mp hh))

/-- The coordinate morphism `H ⧸ I ⟶ H ⧸ J` induced by an inclusion `I ≤ J` of Hopf
ideals.

It is the unique morphism out of `H ⧸ I` whose composite with `H ⟶ H ⧸ I` is the quotient
map `H ⟶ H ⧸ J`. -/
noncomputable abbrev quotientMapOfLe (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) : quotient H I ⟶ quotient H J :=
  liftQuotient I (mkQuotient H J) (toIdeal_le_ker_mkQuotient_of_le H hIJ)

/-- The quotient-to-quotient morphism sends the class of `h` modulo `I` to its class
modulo `J`. -/
lemma quotientMapOfLe_mk (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H}
    (hIJ : I ≤ J) (h : H) :
    (quotientMapOfLe H hIJ).hom (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R J.toIdeal h := by
  rw [quotientMapOfLe, liftQuotient_mk, mkQuotient_apply]

/-- Composing the quotient map `H ⟶ H ⧸ I` with the quotient-to-quotient morphism for
`I ≤ J` gives the quotient map `H ⟶ H ⧸ J`. -/
lemma mkQuotient_comp_quotientMapOfLe (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    mkQuotient H I ≫ quotientMapOfLe H hIJ = mkQuotient H J :=
  mkQuotient_comp_liftQuotient I (mkQuotient H J)
    (toIdeal_le_ker_mkQuotient_of_le H hIJ)

/-- The quotient-to-quotient morphism for `I ≤ I` is the identity morphism. -/
@[simp]
lemma quotientMapOfLe_refl (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    quotientMapOfLe H (le_refl I) = 𝟙 (quotient H I) := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  rw [quotientMapOfLe_mk]
  rfl

/-- Quotient-to-quotient morphisms compose along inclusions of Hopf ideals. -/
@[simp]
lemma quotientMapOfLe_comp (H : _root_.CommHopfAlgCat.{v} R)
    {I J K : HopfIdeal R H} (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientMapOfLe H hIJ ≫ quotientMapOfLe H hJK =
      quotientMapOfLe H (hIJ.trans hJK) := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  rw [_root_.CommHopfAlgCat.comp_apply, quotientMapOfLe_mk, quotientMapOfLe_mk,
    quotientMapOfLe_mk]

/-- On points, precomposition with `quotientMapOfLe` is compatible with the ambient
quotient-points inclusions.

Starting with a point of `H ⧸ J`, mapping it to a point of `H ⧸ I` and then including into
ambient `H`-points gives the same ambient point as the direct inclusion from `H ⧸ J`. -/
@[simp]
lemma quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H J) A) :
    quotientPointsHom H I A ((mapPointsFunctor (quotientMapOfLe H hIJ)).app A f) =
      quotientPointsHom H J A f := by
  apply WithConv.ofConv_injective
  ext h
  rw [quotientPointsHom_apply_apply, mapPointsFunctor_app_apply_apply,
    quotientMapOfLe_mk, quotientPointsHom_apply_apply]

/-- The pointwise form of
`CommHopfAlgCat.quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app`. -/
@[simp]
lemma quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app_apply
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H J) A) (h : H) :
    (quotientPointsHom H I A ((mapPointsFunctor (quotientMapOfLe H hIJ)).app A f)).ofConv h =
      f.ofConv (Ideal.Quotient.mkₐ R J.toIdeal h) := by
  rw [quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app, quotientPointsHom_apply_apply]

/-- Under the quotient-point subgroup isomorphisms, the points map induced by
`quotientMapOfLe` is exactly the subgroup inclusion attached to `I ≤ J`. -/
lemma quotientPointsSubgroupIso_hom_mapPointsFunctor_quotientMapOfLe_app
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H J) A) :
    (quotientPointsSubgroupIso H I A).hom
        ((mapPointsFunctor (quotientMapOfLe H hIJ)).app A f) =
      Subgroup.inclusion (quotientPointsSubgroup_le_of_le H hIJ A)
        ((quotientPointsSubgroupIso H J A).hom f) := by
  apply Subtype.ext
  exact quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app H hIJ A f

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The finite-type coordinate morphism `H ⧸ I ⟶ H ⧸ J` induced by an inclusion `I ≤ J` of
Hopf ideals. -/
noncomputable abbrev quotientMapOfLe (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) : quotient H I ⟶ quotient H J :=
  ObjectProperty.homMk (CommHopfAlgCat.quotientMapOfLe H.obj hIJ)

/-- The finite-type quotient-to-quotient morphism forgets to the `CommHopfAlgCat`
quotient-to-quotient morphism. -/
lemma forget₂_commHopfAlgCat_map_quotientMapOfLe
    (H : FiniteTypeCommHopfAlgCat.{u, v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map
        (quotientMapOfLe H hIJ) =
      CommHopfAlgCat.quotientMapOfLe H.obj hIJ :=
  rfl

/-- The finite-type quotient-to-quotient morphism sends the class of `h` modulo `I` to its
class modulo `J`. -/
lemma quotientMapOfLe_mk (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) (h : H) :
    (toBialgHom (quotientMapOfLe H hIJ)) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R J.toIdeal h :=
  CommHopfAlgCat.quotientMapOfLe_mk H.obj hIJ h

/-- Composing the finite-type quotient map `H ⟶ H ⧸ I` with the quotient-to-quotient
morphism for `I ≤ J` gives the quotient map `H ⟶ H ⧸ J`. -/
@[simp]
lemma mkQuotient_comp_quotientMapOfLe (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    mkQuotient H I ≫ quotientMapOfLe H hIJ = mkQuotient H J := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe H.obj hIJ

/-- The finite-type quotient-to-quotient morphism for `I ≤ I` is the identity morphism. -/
@[simp]
lemma quotientMapOfLe_refl (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    quotientMapOfLe H (le_refl I) = 𝟙 (quotient H I) := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.quotientMapOfLe_refl H.obj I

/-- Finite-type quotient-to-quotient morphisms compose along inclusions of Hopf ideals. -/
@[simp]
lemma quotientMapOfLe_comp (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J K : HopfIdeal R H} (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientMapOfLe H hIJ ≫ quotientMapOfLe H hJK =
      quotientMapOfLe H (hIJ.trans hJK) := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.quotientMapOfLe_comp H.obj hIJ hJK

end FiniteTypeCommHopfAlgCat

end TauCeti
