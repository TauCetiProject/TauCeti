/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Twist

/-!
# Relative q-power Frobenius over finite fields

Let `k` have cardinality `q = p ^ a`. The `a`-th Frobenius twist of a `k`-scheme is
canonically the original scheme, since the `a`-th absolute Frobenius of `Spec k` is
identity. Under this identification, iterated relative Frobenius is q-power Frobenius.

After arbitrary base change `T → Spec k`, the corresponding twist over `T` is again
canonically the base-changed scheme. Its relative Frobenius is the base change of the
original q-power map. It need not be the absolute q-power map: the base-changed map
fixes `T`, whereas absolute Frobenius also acts on its scalars.

The comparisons below specify both projections, so the base-change formula can be
used without unfolding the isomorphisms.

## References

* Stacks Project, Section 33.36 (Tag 0CC6), especially Remark 33.36.11 (Tag 0CCG).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X T : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
  (a : ℕ) (ha : Nat.card k = p ^ a)

/-- Over a field with `p ^ a` elements, the `a`-th Frobenius twist is the original
scheme. The identification is its first projection. -/
noncomputable def qPowerFrobeniusTwistIso :
    pullback f ((Spec (CommRingCat.of k)).iterateFrobenius p
      (natCast_spec_eq_zero (CommRingCat.of k)) a) ≅ X :=
  pullback.congrHom rfl
    ((iterateFrobenius_spec_eq_id k a ha).trans (iterateFrobenius_zero _).symm) ≪≫
      f.iterateFrobeniusTwistZeroIso p (natCast_spec_eq_zero (CommRingCat.of k))

/-- The finite-field twist identification is the first projection. -/
@[simp]
theorem qPowerFrobeniusTwistIso_hom :
    (f.qPowerFrobeniusTwistIso p a ha).hom = pullback.fst _ _ := by
  simp [qPowerFrobeniusTwistIso]

/-- The twist identification respects the given structure map to the finite field. -/
@[reassoc]
theorem qPowerFrobeniusTwistIso_hom_comp :
    (f.qPowerFrobeniusTwistIso p a ha).hom ≫ f = pullback.snd _ _ := by
  rw [qPowerFrobeniusTwistIso_hom, pullback.condition,
    iterateFrobenius_spec_eq_id k a ha, Category.comp_id]

/-- The inverse finite-field twist identification cancels the first projection. -/
@[reassoc (attr := simp)]
theorem qPowerFrobeniusTwistIso_inv_fst :
    (f.qPowerFrobeniusTwistIso p a ha).inv ≫ pullback.fst _ _ = 𝟙 X := by
  simpa only [qPowerFrobeniusTwistIso_hom] using
    (f.qPowerFrobeniusTwistIso p a ha).inv_hom_id

/-- The inverse finite-field twist identification respects the structure map. -/
@[reassoc (attr := simp)]
theorem qPowerFrobeniusTwistIso_inv_snd :
    (f.qPowerFrobeniusTwistIso p a ha).inv ≫ pullback.snd _ _ = f := by
  rw [← qPowerFrobeniusTwistIso_hom_comp f p a ha, Iso.inv_hom_id_assoc]

/-- The first projection cancels the inverse finite-field twist identification. -/
@[reassoc (attr := simp)]
theorem fst_qPowerFrobeniusTwistIso_inv :
    pullback.fst _ _ ≫ (f.qPowerFrobeniusTwistIso p a ha).inv = 𝟙 _ := by
  simpa only [qPowerFrobeniusTwistIso_hom] using
    (f.qPowerFrobeniusTwistIso p a ha).hom_inv_id

/-- Relative Frobenius over a finite field becomes the absolute q-power map after
identifying its twist with the original scheme. -/
@[reassoc]
theorem iterateRelativeFrobenius_qPowerFrobeniusTwistIso_hom :
    f.iterateRelativeFrobenius p (natCast_spec_eq_zero (CommRingCat.of k)) a ≫
        (f.qPowerFrobeniusTwistIso p a ha).hom = qPowerFrobenius k f a ha := by
  simp [qPowerFrobenius_eq_iterated]

/-- After any base change from a finite field, the `a`-th relative Frobenius twist
is canonically the base-changed scheme. No perfectness of the new base is required. -/
noncomputable def qPowerFrobeniusTwistBaseChangeIso (g : T ⟶ Spec (CommRingCat.of k)) :
    pullback (pullback.snd f g)
      (T.iterateFrobenius p (natCast_eq_zero_of_hom g
        (natCast_spec_eq_zero (CommRingCat.of k))) a) ≅ pullback f g :=
  pullbackLeftPullbackSndIso f g _ ≪≫ pullback.congrHom rfl (by
    simpa [qPowerFrobenius_eq_iterated] using qPowerFrobenius_over k g a ha)

/-- The first projection of the base-changed finite-field twist comparison. -/
@[reassoc (attr := simp)]
theorem qPowerFrobeniusTwistBaseChangeIso_hom_fst (g : T ⟶ Spec (CommRingCat.of k)) :
    (f.qPowerFrobeniusTwistBaseChangeIso p a ha g).hom ≫ pullback.fst f g =
      pullback.fst _ _ ≫ pullback.fst f g := by
  simp [qPowerFrobeniusTwistBaseChangeIso]

/-- The base-changed twist comparison is a morphism over the new base. -/
@[reassoc (attr := simp)]
theorem qPowerFrobeniusTwistBaseChangeIso_hom_snd (g : T ⟶ Spec (CommRingCat.of k)) :
    (f.qPowerFrobeniusTwistBaseChangeIso p a ha g).hom ≫ pullback.snd f g =
      pullback.snd _ _ := by
  simp [qPowerFrobeniusTwistBaseChangeIso]

/-- The inverse comparison has the prescribed projection to the original scheme. -/
@[reassoc (attr := simp)]
theorem qPowerFrobeniusTwistBaseChangeIso_inv_fst_fst (g : T ⟶ Spec (CommRingCat.of k)) :
    (f.qPowerFrobeniusTwistBaseChangeIso p a ha g).inv ≫
        pullback.fst (pullback.snd f g)
          (T.iterateFrobenius p (natCast_eq_zero_of_hom g
            (natCast_spec_eq_zero (CommRingCat.of k))) a) ≫
          pullback.fst f g = pullback.fst f g := by
  rw [Iso.inv_comp_eq]
  simp

/-- The inverse twist comparison also respects the new base. -/
@[reassoc (attr := simp)]
theorem qPowerFrobeniusTwistBaseChangeIso_inv_snd (g : T ⟶ Spec (CommRingCat.of k)) :
    (f.qPowerFrobeniusTwistBaseChangeIso p a ha g).inv ≫ pullback.snd _ _ =
      pullback.snd f g := by
  rw [Iso.inv_comp_eq]
  simp

/-- The base change of q-power Frobenius is relative Frobenius over the new base,
under the canonical twist identification. In particular it fixes the new scalars. -/
theorem qPowerFrobenius_baseChange (g : T ⟶ Spec (CommRingCat.of k)) :
    ((Over.pullback g).map
      (Over.homMk (U := Over.mk f) (V := Over.mk f)
        (qPowerFrobenius k f a ha) (qPowerFrobenius_over k f a ha))).left =
      (pullback.snd f g).iterateRelativeFrobenius p
          (natCast_eq_zero_of_hom g (natCast_spec_eq_zero (CommRingCat.of k))) a ≫
        (f.qPowerFrobeniusTwistBaseChangeIso p a ha g).hom := by
  apply pullback.hom_ext
  · have h := qPowerFrobenius_naturality k (pullback.snd f g ≫ g) f
      (pullback.fst f g) a ha
    simpa [qPowerFrobenius_eq_iterated] using h.symm
  · simp

end AlgebraicGeometry.Scheme.Hom
