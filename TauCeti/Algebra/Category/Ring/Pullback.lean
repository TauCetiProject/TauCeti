/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import TauCeti.RingTheory.Pullback

/-!
# Pullbacks in the category of rings

The fibre product `RingHom.pullback f g` of ring homomorphisms `f : A →+* C` and `g : B →+* C`,
the subring of pairs of `A × B` that agree in `C`, is the pullback of `f` and `g` in `RingCat`.
The rings need not be commutative. This compares the explicit fibre product, on which Milnor
squares are built, with the categorical pullback, so that limit arguments in `RingCat` apply
to it. Mathlib's `CommRingCat.pullbackConeIsLimit` is the commutative counterpart.

For commutative rings, a pullback square

```
  A  ──f──▶  B
  │          │
  g          p
  ▼          ▼
  A' ──q──▶  C
```

with `p` surjective is also a pushout square: the natural map `B ⊗_A A' → C` is an
isomorphism. Such squares are Ferrand's affine pinchings and the Milnor squares of algebraic
K-theory. For the fibre product `RingHom.pullback p q` itself this is `RingHom.isPushout_pullback`
in `TauCeti.RingTheory.FiberProduct.Basic`; here it is proved for an arbitrary pullback square,
such as a conductor square.

## Main definitions

* `RingCat.pullbackCone f g`: the pullback cone on `RingHom.pullback f.hom g.hom`, with the two
  projections.
* `RingCat.pullbackConeIsLimit f g`: this cone is a limit cone.

## Main results

* `RingHom.isPullback_pullback`: the fibre product `B ×_C A'` with its projections is a pullback
  square in `CommRingCat`.
* `CommRingCat.isPushout_of_isPullback`: a pullback square of commutative rings with a
  surjective leg is a pushout square.

## References

* D. Ferrand, *Conducteur, descente et pincement*, Bull. Soc. Math. France 131 (2003),
  553–585, §1.1.
* J. Milnor, *Introduction to algebraic K-theory*, Annals of Mathematics Studies 72 (1971),
  §2.
-/

public section

universe u

open CategoryTheory Limits

namespace RingCat

variable {A B C : RingCat.{u}} (f : A ⟶ C) (g : B ⟶ C)

/-- The pullback cone in `RingCat` on the fibre product `RingHom.pullback f.hom g.hom`, with the
projections `RingHom.pullbackFst` and `RingHom.pullbackSnd`.

The body is exposed because the statements of `pullbackCone_fst` and `pullbackCone_snd` compare
morphisms out of `(pullbackCone f g).pt` with morphisms out of `of (f.hom.pullback g.hom)`, and
these sources agree only after unfolding the cone. -/
@[expose]
def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (ofHom (f.hom.pullbackFst g.hom)) (ofHom (f.hom.pullbackSnd g.hom))
    (hom_ext (f.hom.pullback_comm_sq g.hom))

@[simp]
theorem pullbackCone_pt : (pullbackCone f g).pt = of (f.hom.pullback g.hom) :=
  (rfl)

@[simp]
theorem pullbackCone_fst : (pullbackCone f g).fst = ofHom (f.hom.pullbackFst g.hom) :=
  (rfl)

@[simp]
theorem pullbackCone_snd : (pullbackCone f g).snd = ofHom (f.hom.pullbackSnd g.hom) :=
  (rfl)

/-- The fibre product of rings is the pullback in `RingCat`: the cone `RingCat.pullbackCone f g`
is a limit cone, with lift given by `RingHom.pullbackLift`. -/
def pullbackConeIsLimit : IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk _
    (fun s ↦ ofHom (f.hom.pullbackLift g.hom s.fst.hom s.snd.hom congr(($s.condition).hom)))
    (fun _ ↦ hom_ext (RingHom.pullbackFst_comp_pullbackLift ..))
    (fun _ ↦ hom_ext (RingHom.pullbackSnd_comp_pullbackLift ..))
    (fun _ _ h₁ h₂ ↦ hom_ext (RingHom.eq_pullbackLift _ congr(($h₁).hom) congr(($h₂).hom)))

end RingCat

namespace RingHom

variable {B C A' : Type u} [CommRing B] [CommRing C] [CommRing A'] (p : B →+* C) (q : A' →+* C)

/-- The fibre product `B ×_C A'` of commutative rings, with its two projections, is a pullback
square in `CommRingCat`. -/
theorem isPullback_pullback :
    IsPullback (CommRingCat.ofHom (p.pullbackFst q)) (CommRingCat.ofHom (p.pullbackSnd q))
      (CommRingCat.ofHom p) (CommRingCat.ofHom q) :=
  .of_isLimit (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom p) (CommRingCat.ofHom q))

end RingHom

namespace CommRingCat

/-- **A pullback square of commutative rings along a surjection is a pushout square.** If
`A` is the fibre product of `B` and `A'` over `C` and `p : B ⟶ C` is surjective, then the
natural map `B ⊗_A A' → C` is an isomorphism. -/
theorem isPushout_of_isPullback {A B A' C : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ A'}
    {p : B ⟶ C} {q : A' ⟶ C} (h : IsPullback f g p q) (hp : Function.Surjective p) :
    IsPushout f g p q := by
  have hT := h.map (forget CommRingCat)
  -- a pair `(b, a')` with `p b = q a'` comes from an element of `A`
  have hlift (b : B) (a' : A') (hba : p b = q a') : ∃ a, f a = b ∧ g a = a' :=
    Types.exists_of_isPullback hT b a' hba
  refine IsPushout.of_isColimit' ⟨h.w⟩ <| PushoutCocone.IsColimit.mk _
    (fun s ↦ ofHom (p.hom.liftOfSurjective hp ⟨s.inl.hom, fun b hb ↦ ?_⟩))
    (fun s ↦ hom_ext (p.hom.liftOfSurjective_comp hp _))
    (fun s ↦ hom_ext <| RingHom.ext fun a' ↦ ?_)
    (fun s m hm _ ↦ hom_ext <| p.hom.eq_liftOfSurjective hp _ _ m.hom congr(($hm).hom))
  · obtain ⟨a, rfl, ha⟩ := hlift b 0 (by simpa using hb)
    simpa [ha] using congr($(s.condition) a)
  · obtain ⟨b, hb⟩ := hp (q a')
    obtain ⟨a, rfl, rfl⟩ := hlift b a' hb
    simpa [← hb, RingHom.liftOfSurjective_comp_apply] using congr($(s.condition) a)

end CommRingCat
