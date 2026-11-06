/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Closed subgroup schemes from Hopf ideals

A Hopf ideal `I` in a commutative Hopf algebra `H` determines a quotient commutative Hopf
algebra `H ⧸ I`. Applying relative spectrum contravariantly to the quotient morphism gives a
morphism of group objects

`Spec(H ⧸ I) ⟶ Spec(H)`

over `Spec R`. Its underlying morphism of schemes is a closed immersion because the coordinate
map is surjective. Thus the construction retains the scheme structure cut out by `I`, rather
than only the induced inclusion on ordinary points.

If `I ≤ J`, the quotient-to-quotient coordinate map `H ⧸ I ⟶ H ⧸ J` gives a closed immersion
`Spec(H ⧸ J) ⟶ Spec(H ⧸ I)`. The ambient triangle, identity, and composition laws below record
that these closed subgroup schemes depend contravariantly on the Hopf ideal. For a finite-type
coordinate Hopf algebra, the quotient group scheme remains locally of finite type over the base.

The pinned affine-group-scheme bridge requires the base ring and the Hopf-algebra carrier to lie
in the same universe, which is reflected in all scheme-level declarations in this file.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotientSpec`: the group scheme represented by `H ⧸ I`.
* `TauCeti.CommHopfAlgCat.isAffine_quotientSpec`: its underlying scheme is affine.
* `TauCeti.CommHopfAlgCat.quotientSpecι`: its group-object morphism to the group scheme
  represented by `H`.
* `TauCeti.CommHopfAlgCat.isClosedImmersion_quotientSpecι`: the underlying scheme morphism of
  `quotientSpecι` is a closed immersion.
* `TauCeti.CommHopfAlgCat.quotientSpecMapOfLe`: the closed subgroup morphism induced by
  `I ≤ J`.
* `TauCeti.CommHopfAlgCat.quotientIsoQuotientQuotient` and
  `TauCeti.CommHopfAlgCat.quotientSpecQuotientIsoQuotientSpec`: for `I ≤ J`, the quotient of
  `H ⧸ I` by the image of `J` is `H ⧸ J`, and the subgroup scheme it cuts out is that of `J`.
* `CommHopfAlgCat.locallyOfFiniteType_quotientSpec`: a finite-type commutative Hopf algebra has
  quotient group schemes locally of finite type over `Spec R`.

## References

Milne, *Algebraic Groups*, Definition 3.10 and Propositions 3.12 and 3.15, describes Hopf-ideal
quotients and their relation to closed subgroup schemes over a field. The forward construction
used here works over an arbitrary commutative ring and is supplied by Tau Ceti's quotient Hopf
algebra API together with Mathlib's affine `Spec` and closed-immersion APIs.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory

namespace TauCeti

universe u

namespace CommHopfAlgCat

open AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- The affine group scheme represented by the quotient Hopf algebra `H ⧸ I`.

The same-universe restriction on `H` is imposed by Mathlib's current `hopfSpec` construction. -/
noncomputable abbrev quotientSpec (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) : Grp (Over (Spec (CommRingCat.of R))) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op (quotient H I))

/-- The scheme underlying a Hopf-ideal quotient group scheme is affine: it is the spectrum of
the quotient Hopf algebra. -/
instance isAffine_quotientSpec (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    IsAffine (quotientSpec H I).X.left := by
  rw [hopfSpec_obj_X_left]
  exact isAffine_Spec _

/-- The group-object morphism `Spec(H ⧸ I) ⟶ Spec(H)` induced contravariantly by the quotient
Hopf-algebra morphism `H ⟶ H ⧸ I`. -/
noncomputable def quotientSpecι (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) :
    quotientSpec H I ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (mkQuotient H I).op

/-- `quotientSpecι` is the image under `hopfSpec` of the opposite quotient morphism. -/
lemma quotientSpecι_def (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    quotientSpecι H I =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (mkQuotient H I).op :=
  (rfl)

/-- A morphism into a quotient Hopf spectrum, followed by its inclusion, is represented by
precomposing the coordinate morphism with the quotient map. -/
lemma hopfSpec_map_comp_quotientSpecι {H K : _root_.CommHopfAlgCat.{u} R}
    (I : HopfIdeal R H) (f : quotient H I ⟶ K) :
    (hopfSpec (CommRingCat.of R)).map f.op ≫ quotientSpecι H I =
      (hopfSpec (CommRingCat.of R)).map (mkQuotient H I ≫ f).op := by
  rw [quotientSpecι_def, op_comp, Functor.map_comp]

/-- Transporting a quotient spectrum along an equality of Hopf ideals and then including it into
the ambient Hopf spectrum gives the original quotient-spectrum inclusion. -/
theorem eqToHom_comp_quotientSpecι (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (h : I = J) :
    eqToHom (congrArg (quotientSpec H) h) ≫ quotientSpecι H J = quotientSpecι H I := by
  subst J
  simp

/-- The underlying scheme morphism of `quotientSpecι` is a closed immersion. Thus the quotient
Hopf algebra defines a closed subgroup scheme of the affine group scheme represented by `H`. -/
instance isClosedImmersion_quotientSpecι (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) : IsClosedImmersion (quotientSpecι H I).hom.hom.left := by
  rw [quotientSpecι_def, isClosedImmersion_hopfSpec_map_iff]
  intro q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  exact ⟨h, mkQuotient_apply H I h⟩

/-- If `I ≤ J`, the quotient coordinate map `H ⧸ I ⟶ H ⧸ J` induces the group-object morphism
`Spec(H ⧸ J) ⟶ Spec(H ⧸ I)`. -/
noncomputable def quotientSpecMapOfLe (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) : quotientSpec H J ⟶ quotientSpec H I :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (quotientMapOfLe H hIJ).op

/-- `quotientSpecMapOfLe` is the image under `hopfSpec` of the opposite quotient-to-quotient
morphism. -/
lemma quotientSpecMapOfLe_def (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    quotientSpecMapOfLe H hIJ =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (quotientMapOfLe H hIJ).op :=
  (rfl)

/-- The scheme morphism underlying `quotientSpecMapOfLe` is a closed immersion. In particular,
a larger Hopf ideal defines a closed subgroup scheme of the subgroup defined by a smaller one. -/
instance isClosedImmersion_quotientSpecMapOfLe (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    IsClosedImmersion (quotientSpecMapOfLe H hIJ).hom.hom.left := by
  rw [quotientSpecMapOfLe_def, isClosedImmersion_hopfSpec_map_iff]
  intro q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J.toIdeal q
  exact ⟨Ideal.Quotient.mkₐ R I.toIdeal h, quotientMapOfLe_mk H hIJ h⟩

/-- The inclusion associated to `I ≤ J`, followed by the inclusion into the ambient group scheme,
is the inclusion associated to `J`. -/
@[simp]
lemma quotientSpecMapOfLe_comp_quotientSpecι (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    quotientSpecMapOfLe H hIJ ≫ quotientSpecι H I = quotientSpecι H J := by
  rw [quotientSpecMapOfLe_def, quotientSpecι_def, quotientSpecι_def,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp,
    ← op_comp, mkQuotient_comp_quotientMapOfLe]

/-- The group-scheme inclusion induced by the reflexive inclusion `I ≤ I` is the identity. -/
@[simp]
lemma quotientSpecMapOfLe_refl (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    quotientSpecMapOfLe H (le_refl I) = 𝟙 (quotientSpec H I) := by
  rw [quotientSpecMapOfLe_def, quotientMapOfLe_refl]
  exact (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_id _

/-- Closed subgroup morphisms compose contravariantly along inclusions `I ≤ J ≤ K`. -/
@[simp]
lemma quotientSpecMapOfLe_comp (H : _root_.CommHopfAlgCat.{u} R)
    {I J K : HopfIdeal R H} (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientSpecMapOfLe H hJK ≫ quotientSpecMapOfLe H hIJ =
      quotientSpecMapOfLe H (hIJ.trans hJK) := by
  rw [quotientSpecMapOfLe_def, quotientSpecMapOfLe_def, quotientSpecMapOfLe_def,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp,
    ← op_comp, quotientMapOfLe_comp]

section RelativeQuotient

/-! ### Quotients of quotients

For Hopf ideals `I ≤ J` of `H`, the quotient of `H ⧸ I` by the image of `J` is the quotient of `H`
by `J`, and contravariantly the closed subgroup scheme cut out by the image of `J` in `Spec (H ⧸ I)`
is the one cut out by `J` in `Spec H`. The statements take the quotient morphism `q : H ⟶ H ⧸ I`
together with the hypothesis `hq : q = mkQuotient H I`, so that they apply verbatim to a coordinate
map that is only propositionally the quotient map. -/

variable {H : _root_.CommHopfAlgCat.{u} R} {I J : HopfIdeal R H}
  (q : H ⟶ CommHopfAlgCat.quotient H I) (hq : q = CommHopfAlgCat.mkQuotient H I)

include hq in
/-- Pulling the image of `J` in `H ⧸ I` back along the quotient morphism recovers `J`. -/
theorem comapOfSurjective_map_of_eq_mkQuotient (hqs : Function.Surjective q.hom) (hIJ : I ≤ J) :
    (J.map q.hom).comapOfSurjective q.hom hqs = J := by
  subst hq
  exact HopfIdeal.comapOfSurjective_map_mkBialgHom hIJ

/-- For `I ≤ J`, the quotient of `H` by `J` is the quotient of `H ⧸ I` by the image of `J`. -/
noncomputable def quotientIsoQuotientQuotient (hqs : Function.Surjective q.hom) (hIJ : I ≤ J) :
    CommHopfAlgCat.quotient H J ≅
      CommHopfAlgCat.quotient (CommHopfAlgCat.quotient H I) (J.map q.hom) :=
  eqToIso (congrArg (CommHopfAlgCat.quotient H)
      (comapOfSurjective_map_of_eq_mkQuotient q hq hqs hIJ).symm) ≪≫
    CommHopfAlgCat.Hom.quotientIsoOfSurjective q hqs _

/-- The identification `H ⧸ J ≅ (H ⧸ I) ⧸ J` commutes with the quotient maps from `H`. -/
theorem mkQuotient_comp_quotientIsoQuotientQuotient_hom (hqs : Function.Surjective q.hom)
    (hIJ : I ≤ J) :
    CommHopfAlgCat.mkQuotient H J ≫ (quotientIsoQuotientQuotient q hq hqs hIJ).hom =
      q ≫ CommHopfAlgCat.mkQuotient _ (J.map q.hom) := by
  rw [quotientIsoQuotientQuotient, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_eqToHom (comapOfSurjective_map_of_eq_mkQuotient q hq hqs hIJ),
    CommHopfAlgCat.Hom.mkQuotient_comp_quotientIsoOfSurjective_hom]

/-- The closed subgroup scheme of `Spec (H ⧸ I)` cut out by the image of `J` is the one cut out by
`J` in `Spec H`. -/
noncomputable def quotientSpecQuotientIsoQuotientSpec (hqs : Function.Surjective q.hom)
    (hIJ : I ≤ J) :
    quotientSpec (CommHopfAlgCat.quotient H I) (J.map q.hom) ≅ quotientSpec H J :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
    (quotientIsoQuotientQuotient q hq hqs hIJ).op

/-- Under `quotientSpecQuotientIsoQuotientSpec`, the inclusion of the subgroup scheme of `J` into
that of `I` is the inclusion of the subgroup scheme of the image of `J` into `Spec (H ⧸ I)`. -/
theorem quotientSpecQuotientIsoQuotientSpec_hom_comp_quotientSpecMapOfLe
    (hqs : Function.Surjective q.hom) (hIJ : I ≤ J) :
    (quotientSpecQuotientIsoQuotientSpec q hq hqs hIJ).hom ≫ quotientSpecMapOfLe H hIJ =
      quotientSpecι (CommHopfAlgCat.quotient H I) (J.map q.hom) := by
  rw [quotientSpecQuotientIsoQuotientSpec, quotientSpecMapOfLe_def, quotientSpecι_def,
    Functor.mapIso_hom, Iso.op_hom, ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp,
    ← op_comp]
  congr 2
  rw [← cancel_epi (CommHopfAlgCat.mkQuotient H I),
    CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe_assoc,
    mkQuotient_comp_quotientIsoQuotientQuotient_hom, hq]

end RelativeQuotient

end CommHopfAlgCat

end TauCeti

namespace CommHopfAlgCat

open AlgebraicGeometry TauCeti TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- If the commutative Hopf algebra `H` is of finite type, then the group scheme represented by
`H ⧸ I` is locally of finite type over `Spec R`. No finite-generation hypothesis on `I` is
needed. -/
instance locallyOfFiniteType_quotientSpec (H : _root_.CommHopfAlgCat.{u} R)
    [Algebra.FiniteType R H] (I : HopfIdeal R H) :
    LocallyOfFiniteType (quotientSpec H I).X.hom := by
  -- Mathlib's `specOverSpec` has a documented `OverClass` instance diamond. A standalone
  -- rewrite lemma for this structural morphism selects the other instance path, after which
  -- typeclass search cannot use the finite-type instance of `H ⧸ I`; `change` keeps it usable.
  change LocallyOfFiniteType
    (Spec (CommRingCat.of (H ⧸ I.toIdeal)) ↘ Spec (CommRingCat.of R))
  infer_instance

end CommHopfAlgCat
