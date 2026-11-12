/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Retract

/-!
# Retracts of pushout and pullback squares

Let the span `Q ← P → P'` be a retract of a span `B ← A → X`, compatibly with both maps. Then:

* `CategoryTheory.IsPushout.nonempty_retractArrow_of_retract`: the second leg of any pushout of
  the small span is a retract, in the arrow category, of the second leg of any pushout of the big
  span;
* `CategoryTheory.IsPushout.hasPushout_of_retract`: in an idempotent complete category, if the
  big span has a pushout then so does the small one; it is the image of the idempotent induced on
  the big pushout.

`CategoryTheory.IsPullback.nonempty_retractArrow_of_retract` and
`CategoryTheory.IsPullback.hasPullback_of_retract` are the dual statements for cospans.
-/

public section

namespace CategoryTheory

open Limits

variable {D : Type*} [Category D] {P Q P' A B X W : D} {iP : P ⟶ A} {rP : A ⟶ P} {iQ : Q ⟶ B}
  {rQ : B ⟶ Q} {iP' : P' ⟶ X} {rP' : X ⟶ P'}

namespace IsPushout

variable {i : P ⟶ Q} {h : P ⟶ P'} {a : A ⟶ B} {k : A ⟶ X} {k' : B ⟶ W} {a' : X ⟶ W}

/-- Let the span `Q ← P → P'` be a retract of the span `B ← A → X`. Then the second leg of any
pushout of the small span is a retract of the second leg of any pushout of the big span. -/
theorem nonempty_retractArrow_of_retract {Z : D} {h'' : Q ⟶ Z} {i'' : P' ⟶ Z}
    (sq : IsPushout i h h'' i'') (big : IsPushout a k k' a') (hQ : iQ ≫ rQ = 𝟙 Q)
    (hP' : iP' ≫ rP' = 𝟙 P') (wi : i ≫ iQ = iP ≫ a) (wr : a ≫ rQ = rP ≫ i)
    (wk : h ≫ iP' = iP ≫ k) (wk' : k ≫ rP' = rP ≫ h) :
    Nonempty (RetractArrow i'' a') := by
  let φ : Z ⟶ W := sq.desc (iQ ≫ k') (iP' ≫ a') (by rw [reassoc_of% wi, big.w, reassoc_of% wk])
  let ψ : W ⟶ Z := big.desc (rQ ≫ h'') (rP' ≫ i'') (by rw [reassoc_of% wr, sq.w, reassoc_of% wk'])
  refine ⟨⟨Arrow.homMk iP' φ (by simp [φ]), Arrow.homMk rP' ψ (by simp [ψ]), ?_⟩⟩
  refine Arrow.hom_ext _ _ (by simpa using hP') ?_
  simp only [Arrow.comp_right, Arrow.homMk_right, Arrow.id_right]
  exact sq.hom_ext (by simp [φ, ψ, reassoc_of% hQ]) (by simp [φ, ψ, reassoc_of% hP'])

/-- Let the span `Q ← P → P'` be a retract of the span `B ← A → X`, in an idempotent complete
category. If the big span has a pushout, so does the small one: it is the image of the idempotent
induced on the big pushout. -/
theorem hasPushout_of_retract [IsIdempotentComplete D] (big : IsPushout a k k' a')
    (hQ : iQ ≫ rQ = 𝟙 Q) (hP' : iP' ≫ rP' = 𝟙 P') (wi : i ≫ iQ = iP ≫ a)
    (wr : a ≫ rQ = rP ≫ i) (wk : h ≫ iP' = iP ≫ k) (wk' : k ≫ rP' = rP ≫ h) :
    HasPushout i h := by
  let e : W ⟶ W := big.desc (rQ ≫ iQ ≫ k') (rP' ≫ iP' ≫ a')
    (by rw [reassoc_of% wr, reassoc_of% wi, big.w, reassoc_of% wk', reassoc_of% wk])
  have he₁ : k' ≫ e = rQ ≫ iQ ≫ k' := big.inl_desc _ _ _
  have he₂ : a' ≫ e = rP' ≫ iP' ≫ a' := big.inr_desc _ _ _
  have he : e ≫ e = e :=
    big.hom_ext (by rw [reassoc_of% he₁, he₁, reassoc_of% hQ]) (by rw [reassoc_of% he₂, he₂,
      reassoc_of% hP'])
  obtain ⟨Z, iZ, rZ, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split W e he
  have hk : k' ≫ rZ = rQ ≫ iQ ≫ k' ≫ rZ := by
    rw [← reassoc_of% he₁, ← h₂, Category.assoc, h₁, Category.comp_id]
  have ha : a' ≫ rZ = rP' ≫ iP' ≫ a' ≫ rZ := by
    rw [← reassoc_of% he₂, ← h₂, Category.assoc, h₁, Category.comp_id]
  have w : i ≫ iQ ≫ k' ≫ rZ = h ≫ iP' ≫ a' ≫ rZ := by
    rw [reassoc_of% wi, reassoc_of% wk, reassoc_of% big.w]
  have hs (s : PushoutCocone i h) : a ≫ rQ ≫ s.inl = k ≫ rP' ≫ s.inr := by
    rw [reassoc_of% wr, s.condition, reassoc_of% wk']
  refine (IsPushout.of_isColimit (PushoutCocone.IsColimit.mk w
    (fun s ↦ iZ ≫ big.desc (rQ ≫ s.inl) (rP' ≫ s.inr) (hs s)) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m h₁' h₂' ↦ ?_))).hasPushout
  · simp only [Category.assoc]
    rw [← Category.assoc rZ, h₂, reassoc_of% he₁, big.inl_desc]
    simp [reassoc_of% hQ]
  · simp only [Category.assoc]
    rw [← Category.assoc rZ, h₂, reassoc_of% he₂, big.inr_desc]
    simp [reassoc_of% hP']
  · rw [← Category.id_comp m, ← h₁, Category.assoc]
    congr 1
    refine big.hom_ext ?_ ?_
    · rw [big.inl_desc, reassoc_of% hk, ← h₁']
      simp only [Category.assoc]
    · rw [big.inr_desc, reassoc_of% ha, ← h₂']
      simp only [Category.assoc]

end IsPushout

namespace IsPullback

/-- Let the cospan `Q → P ← P'` be a retract of the cospan `B → A ← X`. Then the second leg of any
pullback of the small cospan is a retract of the second leg of any pullback of the big cospan. -/
theorem nonempty_retractArrow_of_retract {Z : D} {i : Q ⟶ P} {h : P' ⟶ P} {h'' : Z ⟶ Q}
    {i'' : Z ⟶ P'} {a : B ⟶ A} {k : X ⟶ A} {k' : W ⟶ B} {a' : W ⟶ X}
    (sq : IsPullback h'' i'' i h) (big : IsPullback k' a' a k) (hQ : iQ ≫ rQ = 𝟙 Q)
    (hP' : iP' ≫ rP' = 𝟙 P') (wi : iQ ≫ a = i ≫ iP) (wr : rQ ≫ i = a ≫ rP)
    (wk : iP' ≫ k = h ≫ iP) (wk' : rP' ≫ h = k ≫ rP) :
    Nonempty (RetractArrow i'' a') := by
  let φ : Z ⟶ W := big.lift (h'' ≫ iQ) (i'' ≫ iP') (by rw [Category.assoc, Category.assoc, wi,
    wk, reassoc_of% sq.w])
  let ψ : W ⟶ Z := sq.lift (k' ≫ rQ) (a' ≫ rP') (by rw [Category.assoc, Category.assoc, wr, wk',
    reassoc_of% big.w])
  refine ⟨⟨Arrow.homMk φ iP' (by simp [φ]), Arrow.homMk ψ rP' (by simp [ψ]), ?_⟩⟩
  refine Arrow.hom_ext _ _ ?_ (by simpa using hP')
  simp only [Arrow.comp_left, Arrow.homMk_left, Arrow.id_left]
  exact sq.hom_ext (by simp [φ, ψ, hQ]) (by simp [φ, ψ, hP'])

/-- Let the cospan `Q → P ← P'` be a retract of the cospan `B → A ← X`, in an idempotent complete
category. If the big cospan has a pullback, so does the small one. -/
theorem hasPullback_of_retract [IsIdempotentComplete D] {i : Q ⟶ P} {h : P' ⟶ P}
    {a : B ⟶ A} {k : X ⟶ A} {k' : W ⟶ B} {a' : W ⟶ X} (big : IsPullback k' a' a k)
    (hQ : iQ ≫ rQ = 𝟙 Q) (hP' : iP' ≫ rP' = 𝟙 P') (wi : iQ ≫ a = i ≫ iP)
    (wr : rQ ≫ i = a ≫ rP) (wk : iP' ≫ k = h ≫ iP) (wk' : rP' ≫ h = k ≫ rP) :
    HasPullback i h := by
  let e : W ⟶ W := big.lift (k' ≫ rQ ≫ iQ) (a' ≫ rP' ≫ iP')
    (by simp only [Category.assoc]
        rw [wi, reassoc_of% wr, wk, reassoc_of% wk', reassoc_of% big.w])
  have he₁ : e ≫ k' = k' ≫ rQ ≫ iQ := big.lift_fst _ _ _
  have he₂ : e ≫ a' = a' ≫ rP' ≫ iP' := big.lift_snd _ _ _
  have he : e ≫ e = e :=
    big.hom_ext (by rw [Category.assoc, he₁, reassoc_of% he₁, reassoc_of% hQ])
      (by rw [Category.assoc, he₂, reassoc_of% he₂, reassoc_of% hP'])
  obtain ⟨Z, iZ, rZ, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split W e he
  have hk : iZ ≫ k' = iZ ≫ k' ≫ rQ ≫ iQ := by
    rw [← he₁, ← h₂]
    simp [reassoc_of% h₁]
  have ha : iZ ≫ a' = iZ ≫ a' ≫ rP' ≫ iP' := by
    rw [← he₂, ← h₂]
    simp [reassoc_of% h₁]
  have w : (iZ ≫ k' ≫ rQ) ≫ i = (iZ ≫ a' ≫ rP') ≫ h := by
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, wr, wk',
      reassoc_of% big.w]
  have hs (s : PullbackCone i h) : (s.fst ≫ iQ) ≫ a = (s.snd ≫ iP') ≫ k := by
    rw [Category.assoc, Category.assoc, wi, wk, reassoc_of% s.condition]
  refine (IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s ↦ big.lift (s.fst ≫ iQ) (s.snd ≫ iP') (hs s) ≫ rZ) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m h₁' h₂' ↦ ?_))).hasPullback
  · rw [Category.assoc, reassoc_of% h₂, reassoc_of% he₁, big.lift_fst_assoc]
    simp [hQ]
  · rw [Category.assoc, reassoc_of% h₂, reassoc_of% he₂, big.lift_snd_assoc]
    simp [hP']
  · rw [← Category.comp_id m, ← h₁, ← Category.assoc]
    congr 1
    refine big.hom_ext ?_ ?_
    · rw [big.lift_fst, Category.assoc, hk, ← h₁']
      simp only [Category.assoc]
    · rw [big.lift_snd, Category.assoc, ha, ← h₂']
      simp only [Category.assoc]

end IsPullback

end CategoryTheory
