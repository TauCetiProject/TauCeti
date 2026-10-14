/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.IdealSheaf.WeilRestriction

/-!
# Incidence and equality loci of closed subschemes

Let `f : X ⟶ S` be a morphism of schemes and let `I`, `J` be ideal sheaves on `X` whose closed
subscheme `V(J)` is finite locally free over `S` (finite, flat and locally of finite presentation).
For a base change `X' = X ×_S S'` along `t : S' ⟶ S`, the inverse image of `V(J)` may or may not
be contained in the inverse image of `V(I)`. This file shows that the condition is closed on the
base: there is an ideal sheaf `incidenceLocus f I J` on `S` such that `V(J)_{S'} ⊆ V(I)_{S'}`,
that is `I.comap g ≤ J.comap g`, exactly when `t` factors through its closed subscheme
(`AlgebraicGeometry.Scheme.IdealSheafData.incidenceLocus_le_ker_iff_of_isPullback`). It is the
Weil restriction along `V(J) ⟶ S` of the inverse image of `V(I)` in `V(J)`.

When both `V(I)` and `V(J)` are finite locally free over `S`, the **equality locus**
`equalityLocus f I J`, the supremum of the two incidence loci, is the closed subscheme of `S` over
which the two closed subschemes agree (`equalityLocus_le_ker_iff_of_isPullback`). Both loci are
compatible with arbitrary base change (`comap_incidenceLocus`, `comap_equalityLocus`).

The main application is to relative effective Cartier divisors `D`, `D'` on a proper relative
curve `C ⟶ S`, which are finite locally free over `S`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier.isFinite` together with
flatness and finite presentation). Then `incidenceLocus` is the universal incidence locus
`D' ≤ D` and `equalityLocus` the universal equality locus `D' = D`: the closed subschemes of the
base over which one divisor is contained in, respectively equal to, the other. No hypothesis
is placed on `S`, which may be nonreduced: equality is tested scheme-theoretically, not on
geometric fibres.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.incidenceLocus f I J`: the ideal sheaf on `S` of the
  locus over which `V(J)` is contained in `V(I)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.equalityLocus f I J`: the ideal sheaf on `S` of the
  locus over which `V(I)` and `V(J)` agree.

## Main results

* `incidenceLocus_le_ker_iff_of_isPullback`, `incidenceLocus_le_ker_iff`: the universal property
  of the incidence locus; `incidenceLocus_eq_bot_iff` is its value over `S` itself.
* `comap_le_comap_pullback_snd_subschemeι_incidenceLocus`: the universal family of the incidence
  locus.
* `comap_incidenceLocus`: the incidence locus commutes with arbitrary base change.
* `equalityLocus_le_ker_iff_of_isPullback`, `equalityLocus_le_ker_iff`, `equalityLocus_eq_bot_iff`,
  `comap_eq_comap_pullback_snd_subschemeι_equalityLocus` and `comap_equalityLocus`: the
  corresponding statements for the equality locus.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Chapter 1, for relative effective Cartier divisors on
  relative curves and the closed loci where they are contained in, or equal to, one another.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S X : Scheme.{u}} (f : X ⟶ S)

section Incidence

variable (I J : X.IdealSheafData) [IsFinite (J.subschemeι ≫ f)] [Flat (J.subschemeι ≫ f)]
  [LocallyOfFinitePresentation (J.subschemeι ≫ f)]

/-- The ideal sheaf on `S` of the **incidence locus** of the closed subschemes `V(J) ⊆ X` and
`V(I) ⊆ X`, where `V(J)` is finite locally free over `S` along `f : X ⟶ S`. A morphism `S' ⟶ S`
factors through its closed subscheme exactly when the inverse image of `V(J)` in the base change
`X ×_S S'` is contained in that of `V(I)`
(`AlgebraicGeometry.Scheme.IdealSheafData.incidenceLocus_le_ker_iff_of_isPullback`). It is the
Weil restriction along `V(J) ⟶ S` of the inverse image of `V(I)` in `V(J)`. -/
noncomputable def incidenceLocus : S.IdealSheafData :=
  (I.comap J.subschemeι).weilRestriction (J.subschemeι ≫ f)

/-- The incidence locus is the Weil restriction along `V(J) ⟶ S` of the inverse image of `V(I)` in
`V(J)`. -/
theorem incidenceLocus_eq_weilRestriction :
    incidenceLocus f I J = (I.comap J.subschemeι).weilRestriction (J.subschemeι ≫ f) :=
  (rfl)

variable {f} in
/-- **The universal property of the incidence locus.** For a pullback square with `g : X' ⟶ X`
over `t : S' ⟶ S`, the morphism `t` factors through the closed subscheme of
`incidenceLocus f I J` exactly when the inverse image of `V(J)` in `X'` is contained in that of
`V(I)`. -/
theorem incidenceLocus_le_ker_iff_of_isPullback {X' S' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ S'}
    {t : S' ⟶ S} (H : IsPullback g f' f t) :
    incidenceLocus f I J ≤ t.ker ↔ I.comap g ≤ J.comap g := by
  rw [incidenceLocus_eq_weilRestriction, weilRestriction_comap_le_ker_iff I J.subschemeι
    (J.isPullback_subschemeMap_comap f H).flip (subschemeMap_subschemeι _ _ _ _).symm,
    ker_subschemeι]

/-- The universal property of the incidence locus, for the base change `T ×_S X` along
`t : T ⟶ S`. -/
theorem incidenceLocus_le_ker_iff {T : Scheme.{u}} (t : T ⟶ S) :
    incidenceLocus f I J ≤ t.ker ↔
      I.comap (pullback.snd t f) ≤ J.comap (pullback.snd t f) :=
  incidenceLocus_le_ker_iff_of_isPullback I J (IsPullback.of_hasPullback t f).flip

/-- The incidence locus is all of `S` exactly when `V(J)` is contained in `V(I)`. -/
@[simp]
theorem incidenceLocus_eq_bot_iff : incidenceLocus f I J = ⊥ ↔ I ≤ J := by
  rw [← le_bot_iff, ← Scheme.Hom.ker_eq_bot_of_isIso (𝟙 S),
    incidenceLocus_le_ker_iff_of_isPullback I J (.id_horiz f), comap_id, comap_id]

/-- The incidence locus of `V(J)` in itself is all of `S`. -/
@[simp]
theorem incidenceLocus_self : incidenceLocus f J J = ⊥ :=
  (incidenceLocus_eq_bot_iff f J J).2 le_rfl

/-- The incidence locus of `V(J)` in `X` is all of `S`. -/
@[simp]
theorem incidenceLocus_bot : incidenceLocus f ⊥ J = ⊥ :=
  (incidenceLocus_eq_bot_iff f ⊥ J).2 bot_le

/-- **The universal family of the incidence locus.** Over the closed subscheme `Z` of
`incidenceLocus f I J`, the inverse image of `V(J)` in `Z ×_S X` is contained in that of
`V(I)`. -/
theorem comap_le_comap_pullback_snd_subschemeι_incidenceLocus :
    I.comap (pullback.snd (incidenceLocus f I J).subschemeι f) ≤
      J.comap (pullback.snd (incidenceLocus f I J).subschemeι f) :=
  (incidenceLocus_le_ker_iff f I J _).1 (ker_subschemeι _).ge

variable {f} in
/-- **The incidence locus commutes with base change.** For a pullback square with `g : X' ⟶ X`
over `t : S' ⟶ S`, the inverse image along `t` of the incidence locus of `V(J)` in `V(I)` is the
incidence locus of their inverse images in `X'`.

The closed subscheme of `J.comap g` is the base change of that of `J`
(`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeMap_comap`), so the instance
arguments follow from those for `J` by `MorphismProperty.of_isPullback`. -/
theorem comap_incidenceLocus {X' S' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ S'} {t : S' ⟶ S}
    (H : IsPullback g f' f t) :
    letI : IsFinite ((J.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
    letI : Flat ((J.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
    letI : LocallyOfFinitePresentation ((J.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
    (incidenceLocus f I J).comap t = incidenceLocus f' (I.comap g) (J.comap g) := by
  let _ : IsFinite ((J.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
  let _ : Flat ((J.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
  let _ : LocallyOfFinitePresentation ((J.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
  -- both sides have the same morphisms factoring through their closed subschemes
  have key {T : Scheme.{u}} (s : T ⟶ S') : (incidenceLocus f I J).comap t ≤ s.ker ↔
      incidenceLocus f' (I.comap g) (J.comap g) ≤ s.ker := by
    rw [← le_map_iff_comap_le, map_ker, incidenceLocus_le_ker_iff_of_isPullback I J
      ((IsPullback.of_hasPullback s f').flip.paste_horiz H), incidenceLocus_le_ker_iff,
      comap_comp, comap_comp]
  exact le_antisymm (((key _).2 (ker_subschemeι _).ge).trans (ker_subschemeι _).le)
    (((key _).1 (ker_subschemeι _).ge).trans (ker_subschemeι _).le)

end Incidence

section Equality

variable (I J : X.IdealSheafData) [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
  [LocallyOfFinitePresentation (I.subschemeι ≫ f)] [IsFinite (J.subschemeι ≫ f)]
  [Flat (J.subschemeι ≫ f)] [LocallyOfFinitePresentation (J.subschemeι ≫ f)]

/-- The ideal sheaf on `S` of the **equality locus** of the closed subschemes `V(I)` and `V(J)` of
`X`, both finite locally free over `S` along `f : X ⟶ S`. A morphism `S' ⟶ S` factors through
its closed subscheme exactly when the inverse images of `V(I)` and `V(J)` in the base change
`X ×_S S'` agree
(`AlgebraicGeometry.Scheme.IdealSheafData.equalityLocus_le_ker_iff_of_isPullback`). It is the
supremum of the two incidence loci, so its closed subscheme is their intersection. -/
noncomputable def equalityLocus : S.IdealSheafData :=
  incidenceLocus f I J ⊔ incidenceLocus f J I

/-- The equality locus is the supremum of the two incidence loci. -/
theorem equalityLocus_eq_sup : equalityLocus f I J = incidenceLocus f I J ⊔ incidenceLocus f J I :=
  (rfl)

/-- The equality locus is symmetric. -/
theorem equalityLocus_comm : equalityLocus f I J = equalityLocus f J I := by
  rw [equalityLocus_eq_sup, equalityLocus_eq_sup, sup_comm]

variable {f} in
/-- **The universal property of the equality locus.** For a pullback square with `g : X' ⟶ X`
over `t : S' ⟶ S`, the morphism `t` factors through the closed subscheme of
`equalityLocus f I J` exactly when the inverse images of `V(I)` and `V(J)` in `X'` agree. -/
theorem equalityLocus_le_ker_iff_of_isPullback {X' S' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ S'}
    {t : S' ⟶ S} (H : IsPullback g f' f t) :
    equalityLocus f I J ≤ t.ker ↔ I.comap g = J.comap g := by
  rw [equalityLocus_eq_sup, sup_le_iff, incidenceLocus_le_ker_iff_of_isPullback I J H,
    incidenceLocus_le_ker_iff_of_isPullback J I H, le_antisymm_iff]

/-- The universal property of the equality locus, for the base change `T ×_S X` along
`t : T ⟶ S`. -/
theorem equalityLocus_le_ker_iff {T : Scheme.{u}} (t : T ⟶ S) :
    equalityLocus f I J ≤ t.ker ↔
      I.comap (pullback.snd t f) = J.comap (pullback.snd t f) :=
  equalityLocus_le_ker_iff_of_isPullback I J (IsPullback.of_hasPullback t f).flip

/-- The equality locus is all of `S` exactly when `V(I)` and `V(J)` agree. -/
@[simp]
theorem equalityLocus_eq_bot_iff : equalityLocus f I J = ⊥ ↔ I = J := by
  rw [equalityLocus_eq_sup, sup_eq_bot_iff, incidenceLocus_eq_bot_iff, incidenceLocus_eq_bot_iff,
    le_antisymm_iff]

/-- The equality locus of `V(I)` with itself is all of `S`. -/
@[simp]
theorem equalityLocus_self : equalityLocus f I I = ⊥ :=
  (equalityLocus_eq_bot_iff f I I).2 rfl

/-- **The universal family of the equality locus.** Over the closed subscheme `Z` of
`equalityLocus f I J`, the inverse images of `V(I)` and `V(J)` in `Z ×_S X` agree. -/
theorem comap_eq_comap_pullback_snd_subschemeι_equalityLocus :
    I.comap (pullback.snd (equalityLocus f I J).subschemeι f) =
      J.comap (pullback.snd (equalityLocus f I J).subschemeι f) :=
  (equalityLocus_le_ker_iff f I J _).1 (ker_subschemeι _).ge

variable {f} in
/-- **The equality locus commutes with base change.** For a pullback square with `g : X' ⟶ X`
over `t : S' ⟶ S`, the inverse image along `t` of the equality locus of `V(I)` and `V(J)` is the
equality locus of their inverse images in `X'`. -/
theorem comap_equalityLocus {X' S' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ S'} {t : S' ⟶ S}
    (H : IsPullback g f' f t) :
    letI : IsFinite ((I.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (I.isPullback_subschemeMap_comap f H) inferInstance
    letI : Flat ((I.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (I.isPullback_subschemeMap_comap f H) inferInstance
    letI : LocallyOfFinitePresentation ((I.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (I.isPullback_subschemeMap_comap f H) inferInstance
    letI : IsFinite ((J.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
    letI : Flat ((J.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
    letI : LocallyOfFinitePresentation ((J.comap g).subschemeι ≫ f') :=
      MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
    (equalityLocus f I J).comap t = equalityLocus f' (I.comap g) (J.comap g) := by
  let _ : IsFinite ((I.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (I.isPullback_subschemeMap_comap f H) inferInstance
  let _ : Flat ((I.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (I.isPullback_subschemeMap_comap f H) inferInstance
  let _ : LocallyOfFinitePresentation ((I.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (I.isPullback_subschemeMap_comap f H) inferInstance
  let _ : IsFinite ((J.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
  let _ : Flat ((J.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
  let _ : LocallyOfFinitePresentation ((J.comap g).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback (J.isPullback_subschemeMap_comap f H) inferInstance
  rw [equalityLocus_eq_sup, equalityLocus_eq_sup, comap_sup, comap_incidenceLocus I J H,
    comap_incidenceLocus J I H]

end Equality

end AlgebraicGeometry.Scheme.IdealSheafData
