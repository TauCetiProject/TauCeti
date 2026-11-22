/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Pullback squares of commutative rings along a surjection

A commutative square of commutative rings

```
  A  ──f──▶  B
  │          │
  g          p
  ▼          ▼
  A' ──q──▶  C
```

which is a pullback square, with `p` surjective, is also a pushout square: the natural map
`B ⊗_A A' → C` is an isomorphism, and dually `Spec C = Spec B ×_{Spec A} Spec A'`. Such
squares are the affine pinchings of Ferrand and the Milnor squares of algebraic K-theory. The
standard example is the fibre product `B ×_C A'`, Mathlib's `RingHom.pullback p q`, with its two
projections.

## Main results

* `CommRingCat.isPushout_of_isPullback`: a pullback square of commutative rings with a
  surjective leg is a pushout square.
* `RingHom.isPullback_pullback`: the fibre product `B ×_C A'` with its projections is a
  pullback square in `CommRingCat`.
* `RingHom.isPushout_pullback`: if `p` is surjective, it is also a pushout square.

## References

* D. Ferrand, *Conducteur, descente et pincement*, Bull. Soc. Math. France 131 (2003),
  553–585, §1.1.
* J. Milnor, *Introduction to algebraic K-theory*, Annals of Mathematics Studies 72 (1971),
  §2.
-/

public section

open CategoryTheory Limits

namespace CommRingCat

universe u

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

namespace RingHom

universe u

variable {B C A' : Type u} [CommRing B] [CommRing C] [CommRing A'] (p : B →+* C) (q : A' →+* C)

/-- The fibre product `B ×_C A'` of commutative rings, with its two projections, is a pullback
square in `CommRingCat`. -/
theorem isPullback_pullback :
    IsPullback (CommRingCat.ofHom (p.pullbackFst q)) (CommRingCat.ofHom (p.pullbackSnd q))
      (CommRingCat.ofHom p) (CommRingCat.ofHom q) :=
  -- `CommRingCat.pullbackCone` is built from the subring `RingHom.pullback` and its projections
  IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom p)
    (CommRingCat.ofHom q))

/-- If `p : B →+* C` is surjective, the fibre product square of `B ×_C A'` is also a pushout
square in `CommRingCat`: `B ⊗_{B ×_C A'} A' ≅ C`. -/
theorem isPushout_pullback (hp : Function.Surjective p) :
    IsPushout (CommRingCat.ofHom (p.pullbackFst q)) (CommRingCat.ofHom (p.pullbackSnd q))
      (CommRingCat.ofHom p) (CommRingCat.ofHom q) :=
  CommRingCat.isPushout_of_isPullback (isPullback_pullback p q) hp

end RingHom
