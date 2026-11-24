/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# When is the quotient square of a ring map cartesian?

Let `f : A →+* B` be a ring map, and let `I` and `J` be two-sided ideals of `A` and `B` with
`I ≤ J.comap f`, for instance `J = I.map f` when the rings are commutative. The square

```
  A  ──f──▶  B
  │          │
  ▼          ▼
 A/I ─────▶ B/J
```

commutes, so `a ↦ (f a, [a])` is a ring map `RingHom.toQuotientPullback f J hIJ` from `A` to the
fibre product `B ×_{B/J} A/I`, realised as Mathlib's `RingHom.pullback`, the carrier of
`CommRingCat.pullbackCone`. No finiteness, injectivity or Noetherian hypothesis is needed to
define it. This file computes its kernel and characterises when it is surjective.

* Its kernel is `ker f ⊓ I`.
* It is surjective exactly when `J ⊆ f '' I`. Since `f '' I ⊆ I.map f ⊆ J` always holds, this
  says that `J = I.map f` and that the image of `I` is already an ideal of `B`.

Hence, for commutative rings, the square is cartesian in `CommRingCat` exactly when both
conditions hold (`RingHom.isPullback_quotient_iff`). The two conditions are independent. For
`ℤ →+* ZMod 2` with `I = 2ℤ` and `J = 0`, the image of `I` is the ideal `J`, but `2` and `0` have
the same image. For the diagonal `ZMod 2 →+* ZMod 2 × ZMod 2` with `I = ⊤` and `J = ⊤`, the map
is injective, but `J` is not the diagonal `f '' I`.

The main instance is a subring `S` of `B` together with an ideal `C` of `B` contained in `S`,
such as the conductor of `S` in `B`. Then `S` is the fibre product of `B` and `S/(C ∩ S)` over
`B/C` (`Subring.isPullback_quotient_comap_subtype`). These are the squares along which
`Spec B` is pinched to `Spec S`.

## Main definitions

* `RingHom.toQuotientPullback f J hIJ`: the comparison map `A →+* B ×_{B/J} A/I`.
* `RingHom.quotientPullbackEquiv`: the comparison as a ring isomorphism, when `ker f ⊓ I = ⊥`
  and `J ⊆ f '' I`.

## Main results

* `RingHom.ker_toQuotientPullback`: the kernel of the comparison is `ker f ⊓ I`.
* `RingHom.toQuotientPullback_surjective_iff`: the comparison is surjective exactly when
  `J ⊆ f '' I`.
* `RingHom.toQuotientPullback_bijective_iff`: the comparison is bijective exactly when
  `ker f ⊓ I = ⊥` and `J ⊆ f '' I`.
* `RingHom.isPullback_quotient_iff`: the quotient square is a pullback square in `CommRingCat`
  exactly when `ker f ⊓ I = ⊥` and `J ⊆ f '' I`.
* `Subring.isPullback_quotient_comap_subtype`: for an ideal `C` of `B` contained in a subring
  `S`, the square `S → B`, `S/(C ∩ S) → B/C` is a pullback square.

## References

* D. Ferrand, *Conducteur, descente et pincement*, Bull. Soc. Math. France 131 (2003),
  553–585, §1.1 and Lemme 1.3.
-/

public section

open CategoryTheory Limits

namespace RingHom

variable {A B : Type*} [Ring A] [Ring B] (f : A →+* B) {I : Ideal A} (J : Ideal B)
  [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J.comap f)

/-- The comparison map `a ↦ (f a, [a])` from `A` to the fibre product `B ×_{B/J} A/I` of the
quotient square of `f` along ideals `I` and `J` with `I ≤ J.comap f`. -/
def toQuotientPullback :
    A →+* (Ideal.Quotient.mk J).pullback (Ideal.quotientMap J f hIJ) :=
  (f.prod (Ideal.Quotient.mk I)).codRestrict _ fun a ↦ by simp

@[simp]
theorem coe_toQuotientPullback_apply (a : A) :
    (f.toQuotientPullback J hIJ a : B × A ⧸ I) = (f a, Ideal.Quotient.mk I a) :=
  (rfl)

/-- The `B`-coordinate of the comparison map is `f`. -/
@[simp]
theorem pullbackFst_comp_toQuotientPullback :
    (pullbackFst _ _).comp (f.toQuotientPullback J hIJ) = f :=
  (rfl)

/-- The `A/I`-coordinate of the comparison map is the quotient map. -/
@[simp]
theorem pullbackSnd_comp_toQuotientPullback :
    (pullbackSnd _ _).comp (f.toQuotientPullback J hIJ) = Ideal.Quotient.mk I :=
  (rfl)

/-- The comparison map is the only ring map to the fibre product whose coordinates are `f` and
the quotient map. -/
theorem eq_toQuotientPullback
    {g : A →+* (Ideal.Quotient.mk J).pullback (Ideal.quotientMap J f hIJ)}
    (h₁ : (pullbackFst _ _).comp g = f) (h₂ : (pullbackSnd _ _).comp g = Ideal.Quotient.mk I) :
    g = f.toQuotientPullback J hIJ := by
  ext a
  · exact congr($h₁ a)
  · exact congr($h₂ a)

/-- The kernel of the comparison map is `ker f ⊓ I`. -/
@[simp]
theorem ker_toQuotientPullback : ker (f.toQuotientPullback J hIJ) = ker f ⊓ I := by
  ext a
  simp [mem_ker, Subtype.ext_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The comparison map is injective exactly when `ker f ⊓ I = ⊥`. -/
theorem toQuotientPullback_injective_iff :
    Function.Injective (f.toQuotientPullback J hIJ) ↔ ker f ⊓ I = ⊥ := by
  rw [injective_iff_ker_eq_bot, ker_toQuotientPullback]

/-- The comparison map is surjective exactly when every element of `J` is the image of an
element of `I`. -/
theorem toQuotientPullback_surjective_iff :
    Function.Surjective (f.toQuotientPullback J hIJ) ↔ (J : Set B) ⊆ f '' I := by
  refine ⟨fun h b hb ↦ ?_, fun h ⟨⟨b, x⟩, hx⟩ ↦ ?_⟩
  · obtain ⟨a, ha⟩ := h ⟨(b, 0), by simpa [Ideal.Quotient.eq_zero_iff_mem] using hb⟩
    simp only [Subtype.ext_iff, coe_toQuotientPullback_apply, Prod.ext_iff,
      Ideal.Quotient.eq_zero_iff_mem] at ha
    exact ⟨a, ha.2, ha.1⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨i, hi, hfi⟩ := h <| Ideal.Quotient.eq.mp <| by simpa using hx
    refine ⟨a + i, Subtype.ext <| Prod.ext ?_ ?_⟩
    · simp [hfi]
    · simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hi

/-- The comparison map is bijective exactly when `ker f ⊓ I = ⊥` and every element of `J` is
the image of an element of `I`. -/
theorem toQuotientPullback_bijective_iff :
    Function.Bijective (f.toQuotientPullback J hIJ) ↔ ker f ⊓ I = ⊥ ∧ (J : Set B) ⊆ f '' I := by
  rw [Function.Bijective, toQuotientPullback_injective_iff, toQuotientPullback_surjective_iff]

/-- When `ker f ⊓ I = ⊥` and every element of `J` is the image of an element of `I`, the
comparison map identifies `A` with the fibre product `B ×_{B/J} A/I`. -/
noncomputable def quotientPullbackEquiv (hker : ker f ⊓ I = ⊥) (him : (J : Set B) ⊆ f '' I) :
    A ≃+* (Ideal.Quotient.mk J).pullback (Ideal.quotientMap J f hIJ) :=
  .ofBijective (f.toQuotientPullback J hIJ) <|
    (toQuotientPullback_bijective_iff f J hIJ).mpr ⟨hker, him⟩

variable {f J hIJ}

@[simp]
theorem coe_quotientPullbackEquiv (hker : ker f ⊓ I = ⊥) (him : (J : Set B) ⊆ f '' I) :
    ⇑(f.quotientPullbackEquiv J hIJ hker him) = f.toQuotientPullback J hIJ :=
  (rfl)

/-- The image under `f` of the preimage of a point of the fibre product is its
`B`-coordinate. -/
@[simp]
theorem apply_quotientPullbackEquiv_symm (hker : ker f ⊓ I = ⊥) (him : (J : Set B) ⊆ f '' I)
    (x : (Ideal.Quotient.mk J).pullback (Ideal.quotientMap J f hIJ)) :
    f ((f.quotientPullbackEquiv J hIJ hker him).symm x) = (x : B × A ⧸ I).1 := by
  obtain ⟨a, rfl⟩ := (f.quotientPullbackEquiv J hIJ hker him).surjective x
  rw [RingEquiv.symm_apply_apply]
  simp

/-- The class modulo `I` of the preimage of a point of the fibre product is its
`A/I`-coordinate. -/
@[simp]
theorem mk_quotientPullbackEquiv_symm (hker : ker f ⊓ I = ⊥) (him : (J : Set B) ⊆ f '' I)
    (x : (Ideal.Quotient.mk J).pullback (Ideal.quotientMap J f hIJ)) :
    Ideal.Quotient.mk I ((f.quotientPullbackEquiv J hIJ hker him).symm x) = (x : B × A ⧸ I).2 := by
  obtain ⟨a, rfl⟩ := (f.quotientPullbackEquiv J hIJ hker him).surjective x
  rw [RingEquiv.symm_apply_apply]
  simp

end RingHom

universe u

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) {I : Ideal A} (J : Ideal B)
  (hIJ : I ≤ J.comap f)

/-- The quotient square of `f` along ideals `I` and `J` with `I ≤ J.comap f` is a pullback square
in `CommRingCat` exactly when `ker f ⊓ I = ⊥` and every element of `J` is the image of an
element of `I`. -/
theorem isPullback_quotient_iff :
    IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk I))
        (CommRingCat.ofHom (Ideal.Quotient.mk J)) (CommRingCat.ofHom (Ideal.quotientMap J f hIJ)) ↔
      ker f ⊓ I = ⊥ ∧ (J : Set B) ⊆ f '' I := by
  have hsq : CommSq (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) (CommRingCat.ofHom (Ideal.quotientMap J f hIJ)) :=
    ⟨by ext; simp⟩
  have hlift : (CommRingCat.pullbackConeIsLimit _ _).lift hsq.cone =
      CommRingCat.ofHom (f.toQuotientPullback J hIJ) :=
    PullbackCone.IsLimit.hom_ext (CommRingCat.pullbackConeIsLimit _ _)
      (by simpa using CommRingCat.hom_ext (pullbackFst_comp_toQuotientPullback f J hIJ).symm)
      (by simpa using CommRingCat.hom_ext (pullbackSnd_comp_toQuotientPullback f J hIJ).symm)
  refine (⟨fun h ↦ h.isLimit', fun h ↦ ⟨hsq, h⟩⟩ : _ ↔ Nonempty (IsLimit hsq.cone)).trans ?_
  rw [(CommRingCat.pullbackConeIsLimit _ _).nonempty_isLimit_iff_isIso_lift, hlift]
  exact (ConcreteCategory.isIso_iff_bijective _).trans (toQuotientPullback_bijective_iff f J hIJ)

end RingHom

namespace Subring

variable {B : Type u} [CommRing B] {S : Subring B} {C : Ideal B}

/-- For an ideal `C` of `B` contained in a subring `S`, the square formed by the inclusion
`S → B` and the quotient maps `S → S/(C ∩ S)` and `B → B/C` is a pullback square of commutative
rings: `S` is the fibre product `B ×_{B/C} S/(C ∩ S)`. -/
theorem isPullback_quotient_comap_subtype (hC : (C : Set B) ⊆ S) :
    IsPullback (CommRingCat.ofHom S.subtype)
      (CommRingCat.ofHom (Ideal.Quotient.mk (C.comap S.subtype)))
      (CommRingCat.ofHom (Ideal.Quotient.mk C))
      (CommRingCat.ofHom (Ideal.quotientMap C S.subtype le_rfl)) := by
  refine (RingHom.isPullback_quotient_iff _ _ _).mpr ⟨?_, fun c hc ↦ ⟨⟨c, hC hc⟩, hc, rfl⟩⟩
  rw [(RingHom.injective_iff_ker_eq_bot _).mp S.subtype_injective, bot_inf_eq]

end Subring
