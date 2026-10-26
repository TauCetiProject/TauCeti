/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import TauCeti.CategoryTheory.Exact.Biproduct
public import TauCeti.CategoryTheory.Exact.Functor

/-!
# The idempotent completion of an exact category

Let `E` be an exact structure on an additive category `C`. Its idempotent completion
`Karoubi C` carries an exact structure whose conflations are the retracts, in the category of
short complexes, of the images of conflations of `E` under `toKaroubi`.

## Main definitions

* `TauCeti.ExactStructure.karoubi`: the exact structure on `Karoubi C` induced by `E`.

## Main results

* `TauCeti.ExactStructure.karoubi_isInflation_iff`,
  `TauCeti.ExactStructure.karoubi_isDeflation_iff`: the inflations (deflations) of `E.karoubi`
  are the retracts, in the arrow category, of images of inflations (deflations) of `E`.
* `TauCeti.ExactStructure.isConflationExact_toKaroubi`: the embedding `toKaroubi` is exact.
* `TauCeti.IsKernelCokernelPair.map_toKaroubi`: `toKaroubi` preserves kernel–cokernel pairs.
* `TauCeti.isPushout_map_toKaroubi`, `TauCeti.isPullback_map_toKaroubi`: `toKaroubi` preserves
  pushout and pullback squares.

## Implementation notes

A retract of the image of an inflation `a` is an inflation: its cokernel is the image of the
idempotent induced on the cokernel of `a`. Composition uses the involution of `B ⊞ B'` exchanging
two copies of a common retract, and (co)base change uses that a retract of a pushout square is a
pushout square after splitting one idempotent. No complements of short complexes are formed.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Section 6,
  Proposition 6.13, for the exact structure on the idempotent completion.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe v u

variable {C : Type u} [Category.{v} C]

/-- The functor `toKaroubi` preserves pushout squares: a morphism out of a formal direct factor is a
morphism of `C` compatible with the idempotent, and the induced morphism inherits that
compatibility by uniqueness. -/
theorem isPushout_map_toKaroubi {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z}
    (sq : IsPushout f g h k) :
    IsPushout ((toKaroubi C).map f) ((toKaroubi C).map g) ((toKaroubi C).map h)
      ((toKaroubi C).map k) := by
  have w : (toKaroubi C).map f ≫ (toKaroubi C).map h =
      (toKaroubi C).map g ≫ (toKaroubi C).map k := by
    rw [← Functor.map_comp, sq.w, Functor.map_comp]
  have hs (s : PushoutCocone ((toKaroubi C).map f) ((toKaroubi C).map g)) :
      f ≫ s.inl.f = g ≫ s.inr.f := by
    simpa using congrArg Karoubi.Hom.f s.condition
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk w
    (fun s ↦ ⟨sq.desc s.inl.f s.inr.f (hs s), ?_⟩) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · simp only [toKaroubi_obj_p]
    exact sq.hom_ext (by simp) (by simp)
  · ext
    simp
  · ext
    simp
  · ext
    refine sq.hom_ext ?_ ?_
    · simpa using congrArg Karoubi.Hom.f h₁
    · simpa using congrArg Karoubi.Hom.f h₂

/-- The functor `toKaroubi` preserves pullback squares. -/
theorem isPullback_map_toKaroubi {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z}
    (sq : IsPullback f g h k) :
    IsPullback ((toKaroubi C).map f) ((toKaroubi C).map g) ((toKaroubi C).map h)
      ((toKaroubi C).map k) := by
  have w : (toKaroubi C).map f ≫ (toKaroubi C).map h =
      (toKaroubi C).map g ≫ (toKaroubi C).map k := by
    rw [← Functor.map_comp, sq.w, Functor.map_comp]
  have hs (s : PullbackCone ((toKaroubi C).map h) ((toKaroubi C).map k)) :
      s.fst.f ≫ h = s.snd.f ≫ k := by
    simpa using congrArg Karoubi.Hom.f s.condition
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s ↦ ⟨sq.lift s.fst.f s.snd.f (hs s), ?_⟩) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · simp only [toKaroubi_obj_p]
    exact sq.hom_ext (by simp) (by simp)
  · ext
    simp
  · ext
    simp
  · ext
    refine sq.hom_ext ?_ ?_
    · simpa using congrArg Karoubi.Hom.f h₁
    · simpa using congrArg Karoubi.Hom.f h₂

section RetractSquares

variable {D : Type*} [Category D] {P Q P' A B X W : D} {i : P ⟶ Q} {h : P ⟶ P'} {a : A ⟶ B}
  {k : A ⟶ X} {k' : B ⟶ W} {a' : X ⟶ W} (iP : P ⟶ A) (rP : A ⟶ P) (iQ : Q ⟶ B) (rQ : B ⟶ Q)
  (iP' : P' ⟶ X) (rP' : X ⟶ P')

/-- Let the span `Q ← P → P'` be a retract of the span `B ← A → X`. Then the second leg of any
pushout of the small span is a retract of the second leg of any pushout of the big span. -/
private theorem retractArrow_of_isPushout {Z : D} {h'' : Q ⟶ Z} {i'' : P' ⟶ Z}
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
private theorem hasPushout_of_retract [IsIdempotentComplete D] (big : IsPushout a k k' a')
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

/-- Let the cospan `Q → P ← P'` be a retract of the cospan `B → A ← X`. Then the second leg of any
pullback of the small cospan is a retract of the second leg of any pullback of the big cospan. -/
private theorem retractArrow_of_isPullback {Z : D} {i : Q ⟶ P} {h : P' ⟶ P} {h'' : Z ⟶ Q}
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
private theorem hasPullback_of_retract [IsIdempotentComplete D] {i : Q ⟶ P} {h : P' ⟶ P}
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

end RetractSquares

variable [Preadditive C]

namespace IsKernelCokernelPair

/-- The functor `toKaroubi` sends kernel–cokernel pairs to kernel–cokernel pairs. A morphism from
a formal direct factor `(X, p)` into the middle term is a morphism out of `X`; its lift through the
kernel is compatible with `p` because the kernel is a monomorphism, and dually for the cokernel. -/
theorem map_toKaroubi {S : ShortComplex C} (h : IsKernelCokernelPair S) :
    IsKernelCokernelPair (S.map (toKaroubi C)) where
  nonempty_fIsKernel := by
    have := h.mono_f
    refine ⟨KernelFork.IsLimit.ofι _ _
      (fun {P} k hk ↦ ⟨h.lift k.f (by simpa using congrArg Karoubi.Hom.f hk), ?_⟩)
      (fun k hk ↦ ?_) (fun k hk l hl ↦ ?_)⟩
    · rw [← cancel_mono S.f]
      simp
    · ext
      simp
    · ext
      rw [← cancel_mono S.f]
      simpa using congrArg Karoubi.Hom.f hl
  nonempty_gIsCokernel := by
    have := h.epi_g
    refine ⟨CokernelCofork.IsColimit.ofπ _ _
      (fun {P} k hk ↦ ⟨h.desc k.f (by simpa using congrArg Karoubi.Hom.f hk), ?_⟩)
      (fun k hk ↦ ?_) (fun k hk l hl ↦ ?_)⟩
    · rw [← cancel_epi S.g]
      simp
    · ext
      simp
    · ext
      rw [← cancel_epi S.g]
      simpa using congrArg Karoubi.Hom.f hl

end IsKernelCokernelPair

variable [HasBinaryBiproducts C] in
/-- The composition step, with the two retractions spelled out. The middle object `Q` is a retract
of both `B` and `B'`; the involution `θ` of `B ⊞ B'` exchanges these two copies of `Q` and is the
identity on their complements, so `i ≫ j` is a retract of the image of `(a ⊞ 𝟙) ≫ θ ≫ (𝟙 ⊞ b)`. -/
private theorem exists_retractArrow_comp_of_retracts {P Q R : Karoubi C} (i : P ⟶ Q)
    (j : Q ⟶ R) {A B B' C' : C} {a : A ⟶ B} {b : B' ⟶ C'} (iP : P ⟶ (toKaroubi C).obj A)
    (rP : (toKaroubi C).obj A ⟶ P)
    (iQ : Q ⟶ (toKaroubi C).obj B) (rQ : (toKaroubi C).obj B ⟶ Q)
    (jQ : Q ⟶ (toKaroubi C).obj B') (sQ : (toKaroubi C).obj B' ⟶ Q)
    (jR : R ⟶ (toKaroubi C).obj C') (sR : (toKaroubi C).obj C' ⟶ R)
    (hP : iP ≫ rP = 𝟙 P) (hQ : iQ ≫ rQ = 𝟙 Q) (hQ' : jQ ≫ sQ = 𝟙 Q) (hR : jR ≫ sR = 𝟙 R)
    (wi : iP ≫ (toKaroubi C).map a = i ≫ iQ) (wr : rP ≫ i = (toKaroubi C).map a ≫ rQ)
    (wj : jQ ≫ (toKaroubi C).map b = j ≫ jR) (wj' : sQ ≫ j = (toKaroubi C).map b ≫ sR) :
    ∃ θ : B ⊞ B' ⟶ B ⊞ B', IsIso θ ∧
      Nonempty (RetractArrow (i ≫ j) ((toKaroubi C).map (biprod.map a (𝟙 B') ≫ θ ≫
        biprod.map (𝟙 B) b))) := by
  have hPf : iP.f ≫ rP.f = P.p := by simpa using congrArg Karoubi.Hom.f hP
  have hQf : iQ.f ≫ rQ.f = Q.p := by simpa using congrArg Karoubi.Hom.f hQ
  have hRf : jR.f ≫ sR.f = R.p := by simpa using congrArg Karoubi.Hom.f hR
  have hQf' : jQ.f ≫ sQ.f = Q.p := by simpa using congrArg Karoubi.Hom.f hQ'
  have wif : iP.f ≫ a = i.f ≫ iQ.f := by simpa using congrArg Karoubi.Hom.f wi
  have wrf : rP.f ≫ i.f = a ≫ rQ.f := by simpa using congrArg Karoubi.Hom.f wr
  have wjf : jQ.f ≫ b = j.f ≫ jR.f := by simpa using congrArg Karoubi.Hom.f wj
  have wjf' : sQ.f ≫ j.f = b ≫ sR.f := by simpa using congrArg Karoubi.Hom.f wj'
  let θ : B ⊞ B' ⟶ B ⊞ B' :=
    biprod.desc (biprod.lift (𝟙 B - (rQ.f ≫ iQ.f : B ⟶ B)) (rQ.f ≫ jQ.f : B ⟶ B'))
      (biprod.lift (sQ.f ≫ iQ.f : B' ⟶ B) (𝟙 B' - (sQ.f ≫ jQ.f : B' ⟶ B')))
  have hθ : θ ≫ θ = 𝟙 _ := by
    ext <;> simp [θ, Preadditive.comp_sub, Preadditive.sub_comp, reassoc_of% hQf,
      reassoc_of% hQf']
  refine ⟨θ, ⟨θ, hθ, hθ⟩, ⟨
    Arrow.homMk (iP ≫ (toKaroubi C).map biprod.inl) (jR ≫ (toKaroubi C).map biprod.inr) ?_,
    Arrow.homMk ((toKaroubi C).map biprod.fst ≫ rP) ((toKaroubi C).map biprod.snd ≫ sR) ?_, ?_⟩⟩
  · refine Karoubi.hom_ext _ _ ?_
    simp only [Karoubi.comp_f, toKaroubi_map_f, Arrow.mk_hom]
    refine biprod.hom_ext _ _ ?_ ?_
    · simp [θ, reassoc_of% wif, Preadditive.comp_sub, reassoc_of% hQf]
    · simp [θ, reassoc_of% wif, reassoc_of% hQf, wjf]
  · refine Karoubi.hom_ext _ _ ?_
    simp only [Karoubi.comp_f, toKaroubi_map_f, Arrow.mk_hom]
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp [θ, ← wjf', reassoc_of% hQf', reassoc_of% wrf]
    · simp [θ, Preadditive.sub_comp, ← wjf', reassoc_of% hQf']
  · ext <;> simp [hPf, hRf]

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- The idempotent completion of an additive category has finite biproducts. -/
instance : HasFiniteBiproducts (Karoubi C) :=
  have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  Karoubi.karoubi_hasFiniteBiproducts

instance : HasBinaryBiproducts (Karoubi C) := hasBinaryBiproducts_of_finite_biproducts _

variable (E : ExactStructure C)

/-- The conflation class on the idempotent completion: the retracts, in the category of short
complexes, of the images of conflations of `E` under `toKaroubi`. -/
private def karoubiConflations : ConflationClass (Karoubi C) where
  Conflation S := ∃ T : ShortComplex C, E.Conflation T ∧ Nonempty (Retract S (T.map (toKaroubi C)))
  isKernelCokernelPair _ := fun ⟨_, hT, ⟨e⟩⟩ ↦
    ((E.isKernelCokernelPair _ hT).map_toKaroubi).of_retract e
  isClosedUnderIsomorphisms := ⟨fun e ⟨T, hT, ⟨r⟩⟩ ↦
    ⟨T, hT, ⟨⟨e.inv ≫ r.i, r.r ≫ e.hom, by simp⟩⟩⟩⟩

/-- The image of a conflation of `E` is a conflation of the idempotent completion. -/
private theorem karoubiConflations_map_toKaroubi {T : ShortComplex C} (hT : E.Conflation T) :
    E.karoubiConflations.Conflation (T.map (toKaroubi C)) :=
  ⟨T, hT, ⟨⟨𝟙 _, 𝟙 _, by simp⟩⟩⟩

/-- A retract of the image of an inflation of `E` is an inflation of the idempotent completion.
The cokernel is the image of the idempotent induced on the cokernel of the inflation of `E`. -/
private theorem karoubiConflations_isInflation_of_retract {P Q : Karoubi C} {f : P ⟶ Q} {A B : C}
    {a : A ⟶ B} (ha : E.IsInflation a) (h : RetractArrow f ((toKaroubi C).map a)) :
    E.karoubiConflations.IsInflation f := by
  obtain ⟨D, d, zero, hT⟩ := (ConflationClass.isInflation_iff _ a).mp ha
  have hK := (E.isKernelCokernelPair _ hT).map_toKaroubi
  have : Epi ((toKaroubi C).map d) := hK.epi_g
  have wi : f ≫ h.i.right = h.i.left ≫ (toKaroubi C).map a := h.i_w.symm
  have wr : (toKaroubi C).map a ≫ h.r.right = h.r.left ≫ f := h.r_w.symm
  have hd : (toKaroubi C).map a ≫ h.r.right ≫ h.i.right ≫ (toKaroubi C).map d = 0 := by
    rw [reassoc_of% wr, reassoc_of% wi, ← Functor.map_comp, zero, Functor.map_zero, comp_zero,
      comp_zero]
  let eD : (toKaroubi C).obj D ⟶ (toKaroubi C).obj D := hK.desc _ hd
  have heD : (toKaroubi C).map d ≫ eD = h.r.right ≫ h.i.right ≫ (toKaroubi C).map d :=
    hK.g_desc _ hd
  have hidem : eD ≫ eD = eD := by
    rw [← cancel_epi ((toKaroubi C).map d), reassoc_of% heD, heD]
    simp
  obtain ⟨R, iR, rR, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split _ eD hidem
  have zero' : f ≫ h.i.right ≫ (toKaroubi C).map d ≫ rR = 0 := by
    rw [reassoc_of% wi, ← Functor.map_comp_assoc, zero, Functor.map_zero, zero_comp, comp_zero]
  refine (ConflationClass.isInflation_iff _ f).mpr
    ⟨R, _, zero', ShortComplex.mk a d zero, hT, ⟨⟨?_, ?_, ?_⟩⟩⟩
  · exact
      { τ₁ := h.i.left
        τ₂ := h.i.right
        τ₃ := iR
        comm₁₂ := wi.symm
        comm₂₃ := by
          simp only [ShortComplex.map_g, Category.assoc, h₂]
          rw [heD]
          simp }
  · exact
      { τ₁ := h.r.left
        τ₂ := h.r.right
        τ₃ := rR
        comm₁₂ := wr.symm
        comm₂₃ := by
          simp only [ShortComplex.map_g]
          rw [show h.r.right ≫ h.i.right ≫ (toKaroubi C).map d ≫ rR =
              ((toKaroubi C).map d ≫ eD) ≫ rR by rw [heD]; simp only [Category.assoc],
            ← h₂, Category.assoc, Category.assoc, h₁, Category.comp_id] }
  · ext <;> simp [h₁]

/-- An inflation of the idempotent completion is a retract of the image of an inflation of `E`. -/
private theorem karoubiConflations_isInflation_iff {P Q : Karoubi C} (f : P ⟶ Q) :
    E.karoubiConflations.IsInflation f ↔ ∃ (A B : C) (a : A ⟶ B),
      E.IsInflation a ∧ Nonempty (RetractArrow f ((toKaroubi C).map a)) := by
  constructor
  · intro hf
    obtain ⟨_, _, _, T, hT, ⟨e⟩⟩ := (ConflationClass.isInflation_iff _ f).mp hf
    refine ⟨_, _, T.f, E.isInflation_f hT,
      ⟨⟨Arrow.homMk e.i.τ₁ e.i.τ₂ e.i.comm₁₂, Arrow.homMk e.r.τ₁ e.r.τ₂ e.r.comm₁₂, ?_⟩⟩⟩
    refine Arrow.hom_ext _ _ ?_ ?_
    · have := congrArg ShortComplex.Hom.τ₁ e.retract
      simp only [ShortComplex.comp_τ₁, ShortComplex.id_τ₁] at this
      simpa using this
    · have := congrArg ShortComplex.Hom.τ₂ e.retract
      simp only [ShortComplex.comp_τ₂, ShortComplex.id_τ₂] at this
      simpa using this
  · rintro ⟨_, _, _, ha, ⟨h⟩⟩
    exact E.karoubiConflations_isInflation_of_retract ha h

/-- A retract of the image of a deflation of `E` is a deflation of the idempotent completion.
The kernel is the image of the idempotent induced on the kernel of the deflation of `E`. -/
private theorem karoubiConflations_isDeflation_of_retract {Q R : Karoubi C} {g : Q ⟶ R} {B D : C}
    {d : B ⟶ D} (hd : E.IsDeflation d) (h : RetractArrow g ((toKaroubi C).map d)) :
    E.karoubiConflations.IsDeflation g := by
  obtain ⟨A, a, zero, hT⟩ := (ConflationClass.isDeflation_iff _ d).mp hd
  have hK := (E.isKernelCokernelPair _ hT).map_toKaroubi
  have : Mono ((toKaroubi C).map a) := hK.mono_f
  have wi : g ≫ h.i.right = h.i.left ≫ (toKaroubi C).map d := h.i_w.symm
  have wr : (toKaroubi C).map d ≫ h.r.right = h.r.left ≫ g := h.r_w.symm
  have ha : ((toKaroubi C).map a ≫ h.r.left ≫ h.i.left) ≫ (toKaroubi C).map d = 0 := by
    rw [Category.assoc, Category.assoc, ← wi, ← reassoc_of% wr, ← Functor.map_comp_assoc, zero,
      Functor.map_zero, zero_comp]
  let eA : (toKaroubi C).obj A ⟶ (toKaroubi C).obj A := hK.lift _ ha
  have heA : eA ≫ (toKaroubi C).map a = (toKaroubi C).map a ≫ h.r.left ≫ h.i.left :=
    hK.lift_f _ ha
  have hidem : eA ≫ eA = eA := by
    rw [← cancel_mono ((toKaroubi C).map a), Category.assoc, heA, reassoc_of% heA]
    simp
  obtain ⟨K, iK, rK, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split _ eA hidem
  have zero' : (iK ≫ (toKaroubi C).map a ≫ h.r.left) ≫ g = 0 := by
    rw [Category.assoc, Category.assoc, ← wr, ← Functor.map_comp_assoc, zero, Functor.map_zero,
      zero_comp, comp_zero]
  refine (ConflationClass.isDeflation_iff _ g).mpr
    ⟨K, _, zero', ShortComplex.mk a d zero, hT, ⟨⟨?_, ?_, ?_⟩⟩⟩
  · exact
      { τ₁ := iK
        τ₂ := h.i.left
        τ₃ := h.i.right
        comm₁₂ := by
          simp only [ShortComplex.map_f, Category.assoc]
          rw [← heA, ← h₂]
          simp [reassoc_of% h₁]
        comm₂₃ := wi.symm }
  · exact
      { τ₁ := rK
        τ₂ := h.r.left
        τ₃ := h.r.right
        comm₁₂ := by
          simp only [ShortComplex.map_f]
          rw [reassoc_of% h₂, reassoc_of% heA]
          simp
        comm₂₃ := wr.symm }
  · ext <;> simp [h₁]

/-- A deflation of the idempotent completion is a retract of the image of a deflation of `E`. -/
private theorem karoubiConflations_isDeflation_iff {Q R : Karoubi C} (g : Q ⟶ R) :
    E.karoubiConflations.IsDeflation g ↔ ∃ (B D : C) (d : B ⟶ D),
      E.IsDeflation d ∧ Nonempty (RetractArrow g ((toKaroubi C).map d)) := by
  constructor
  · intro hg
    obtain ⟨_, _, _, T, hT, ⟨e⟩⟩ := (ConflationClass.isDeflation_iff _ g).mp hg
    refine ⟨_, _, T.g, E.isDeflation_g hT,
      ⟨⟨Arrow.homMk e.i.τ₂ e.i.τ₃ e.i.comm₂₃, Arrow.homMk e.r.τ₂ e.r.τ₃ e.r.comm₂₃, ?_⟩⟩⟩
    refine Arrow.hom_ext _ _ ?_ ?_
    · have := congrArg ShortComplex.Hom.τ₂ e.retract
      simp only [ShortComplex.comp_τ₂, ShortComplex.id_τ₂] at this
      simpa using this
    · have := congrArg ShortComplex.Hom.τ₃ e.retract
      simp only [ShortComplex.comp_τ₃, ShortComplex.id_τ₃] at this
      simpa using this
  · rintro ⟨_, _, _, hd, ⟨h⟩⟩
    exact E.karoubiConflations_isDeflation_of_retract hd h

/-- Identities are inflations of the idempotent completion: `𝟙 P` is a retract of `𝟙 P.X`. -/
private theorem karoubiConflations_isInflation_id (P : Karoubi C) :
    E.karoubiConflations.IsInflation (𝟙 P) :=
  E.karoubiConflations_isInflation_of_retract (E.isInflation_id P.X)
    ⟨Arrow.homMk (Karoubi.decompId_i P) (Karoubi.decompId_i P),
      Arrow.homMk (Karoubi.decompId_p P) (Karoubi.decompId_p P),
      by ext <;> simp⟩

/-- Identities are deflations of the idempotent completion: `𝟙 P` is a retract of `𝟙 P.X`. -/
private theorem karoubiConflations_isDeflation_id (P : Karoubi C) :
    E.karoubiConflations.IsDeflation (𝟙 P) :=
  E.karoubiConflations_isDeflation_of_retract (E.isDeflation_id P.X)
    ⟨Arrow.homMk (Karoubi.decompId_i P) (Karoubi.decompId_i P),
      Arrow.homMk (Karoubi.decompId_p P) (Karoubi.decompId_p P),
      by ext <;> simp⟩

/-- Inflations of the idempotent completion are closed under composition. -/
private theorem karoubiConflations_isInflation_comp {P Q R : Karoubi C} {i : P ⟶ Q} {j : Q ⟶ R}
    (hi : E.karoubiConflations.IsInflation i) (hj : E.karoubiConflations.IsInflation j) :
    E.karoubiConflations.IsInflation (i ≫ j) := by
  obtain ⟨_, B, _, ha, ⟨hi⟩⟩ := (E.karoubiConflations_isInflation_iff i).mp hi
  obtain ⟨_, _, _, hb, ⟨hj⟩⟩ := (E.karoubiConflations_isInflation_iff j).mp hj
  obtain ⟨θ, _, ⟨h⟩⟩ := exists_retractArrow_comp_of_retracts i j _ _ _ _ _ _ _ _
    hi.retract_left hi.retract_right hj.retract_left hj.retract_right hi.i_w hi.r_w hj.i_w hj.r_w
  exact E.karoubiConflations_isInflation_of_retract
    (E.isInflation_comp _ _ (E.isInflation_biprod_id ha _)
      (E.isInflation_comp _ _ (E.isInflation_of_isIso θ) (E.isInflation_id_biprod hb B))) h

/-- Deflations of the idempotent completion are closed under composition. -/
private theorem karoubiConflations_isDeflation_comp {P Q R : Karoubi C} {p : P ⟶ Q} {q : Q ⟶ R}
    (hp : E.karoubiConflations.IsDeflation p) (hq : E.karoubiConflations.IsDeflation q) :
    E.karoubiConflations.IsDeflation (p ≫ q) := by
  obtain ⟨_, B, _, hd, ⟨hp⟩⟩ := (E.karoubiConflations_isDeflation_iff p).mp hp
  obtain ⟨_, _, _, hd', ⟨hq⟩⟩ := (E.karoubiConflations_isDeflation_iff q).mp hq
  obtain ⟨θ, _, ⟨h⟩⟩ := exists_retractArrow_comp_of_retracts p q _ _ _ _ _ _ _ _
    hp.retract_left hp.retract_right hq.retract_left hq.retract_right hp.i_w hp.r_w hq.i_w hq.r_w
  exact E.karoubiConflations_isDeflation_of_retract
    (E.isDeflation_comp _ _ (E.isDeflation_biprod_id hd _)
      (E.isDeflation_comp _ _ (E.isDeflation_of_isIso θ) (E.isDeflation_id_biprod hd' B))) h

/-- Pushouts of inflations of the idempotent completion exist. If `i` is a retract of the image of
an inflation `a : A ⟶ B` of `E`, the span `(i, h)` is a retract of the image of the span `(a, k)`,
where `k` is `h` read through the retractions; the pushout of `(a, k)` in `C` exists by `E`. -/
private theorem karoubiConflations_hasPushout {P Q P' : Karoubi C} {i : P ⟶ Q}
    (hi : E.karoubiConflations.IsInflation i) (h : P ⟶ P') : HasPushout i h := by
  obtain ⟨A, B, a, ha, ⟨r⟩⟩ := (E.karoubiConflations_isInflation_iff i).mp hi
  let k : A ⟶ P'.X := (r.r.left ≫ h ≫ Karoubi.decompId_i P').f
  have hk : (toKaroubi C).map k = r.r.left ≫ h ≫ Karoubi.decompId_i P' := by
    ext
    simp [k]
  have : HasPushout a k := E.hasPushouts_inflations.hasPushout k ha
  exact hasPushout_of_retract r.i.left r.r.left r.i.right r.r.right (Karoubi.decompId_i P')
    (Karoubi.decompId_p P') (isPushout_map_toKaroubi (IsPushout.of_hasPushout a k))
    r.retract_right (Karoubi.decompId P').symm r.i_w.symm r.r_w.symm (by rw [hk]; simp)
    (by rw [hk, Category.assoc, Category.assoc, ← Karoubi.decompId, Category.comp_id])

/-- Inflations of the idempotent completion are stable under cobase change. The cobase change of
`i` along `h` is a retract of the image of the cobase change in `C` of the corresponding
inflation of `E`. -/
private theorem karoubiConflations_isInflation_of_isPushout {P Q P' Z : Karoubi C} {i : P ⟶ Q}
    {h : P ⟶ P'} {h' : Q ⟶ Z} {i' : P' ⟶ Z} (sq : IsPushout h i i' h')
    (hi : E.karoubiConflations.IsInflation i) : E.karoubiConflations.IsInflation i' := by
  obtain ⟨A, B, a, ha, ⟨r⟩⟩ := (E.karoubiConflations_isInflation_iff i).mp hi
  let k : A ⟶ P'.X := (r.r.left ≫ h ≫ Karoubi.decompId_i P').f
  have hk : (toKaroubi C).map k = r.r.left ≫ h ≫ Karoubi.decompId_i P' := by
    ext
    simp [k]
  have : HasPushout a k := E.hasPushouts_inflations.hasPushout k ha
  have hpo := IsPushout.of_hasPushout a k
  obtain ⟨r'⟩ := retractArrow_of_isPushout r.i.left r.r.left r.i.right r.r.right
    (Karoubi.decompId_i P') (Karoubi.decompId_p P') sq.flip (isPushout_map_toKaroubi hpo)
    r.retract_right (Karoubi.decompId P').symm r.i_w.symm r.r_w.symm (by rw [hk]; simp)
    (by rw [hk, Category.assoc, Category.assoc, ← Karoubi.decompId, Category.comp_id])
  exact E.karoubiConflations_isInflation_of_retract
    (E.isStableUnderCobaseChange_inflations.of_isPushout hpo.flip ha) r'

/-- Pullbacks of deflations of the idempotent completion exist; dual to
`karoubiConflations_hasPushout`. -/
private theorem karoubiConflations_hasPullback {Q P P' : Karoubi C} {p : Q ⟶ P}
    (hp : E.karoubiConflations.IsDeflation p) (h : P' ⟶ P) : HasPullback p h := by
  obtain ⟨B, D, d, hd, ⟨r⟩⟩ := (E.karoubiConflations_isDeflation_iff p).mp hp
  let k : P'.X ⟶ D := (Karoubi.decompId_p P' ≫ h ≫ r.i.right).f
  have hk : (toKaroubi C).map k = Karoubi.decompId_p P' ≫ h ≫ r.i.right := by
    ext
    simp [k]
  have : HasPullback d k := E.hasPullbacks_deflations.hasPullback k hd
  exact hasPullback_of_retract r.i.right r.r.right r.i.left r.r.left (Karoubi.decompId_i P')
    (Karoubi.decompId_p P') (isPullback_map_toKaroubi (IsPullback.of_hasPullback d k))
    r.retract_left (Karoubi.decompId P').symm r.i_w r.r_w
    (by rw [hk, ← Category.assoc, ← Karoubi.decompId, Category.id_comp]) (by rw [hk]; simp)

/-- Deflations of the idempotent completion are stable under base change; dual to
`karoubiConflations_isInflation_of_isPushout`. -/
private theorem karoubiConflations_isDeflation_of_isPullback {Q P P' Z : Karoubi C} {p : Q ⟶ P}
    {h : P' ⟶ P} {h' : Z ⟶ Q} {p' : Z ⟶ P'} (sq : IsPullback h' p' p h)
    (hp : E.karoubiConflations.IsDeflation p) : E.karoubiConflations.IsDeflation p' := by
  obtain ⟨B, D, d, hd, ⟨r⟩⟩ := (E.karoubiConflations_isDeflation_iff p).mp hp
  let k : P'.X ⟶ D := (Karoubi.decompId_p P' ≫ h ≫ r.i.right).f
  have hk : (toKaroubi C).map k = Karoubi.decompId_p P' ≫ h ≫ r.i.right := by
    ext
    simp [k]
  have : HasPullback d k := E.hasPullbacks_deflations.hasPullback k hd
  have hpb := IsPullback.of_hasPullback d k
  obtain ⟨r'⟩ := retractArrow_of_isPullback r.i.right r.r.right r.i.left r.r.left
    (Karoubi.decompId_i P') (Karoubi.decompId_p P') sq (isPullback_map_toKaroubi hpb)
    r.retract_left (Karoubi.decompId P').symm r.i_w r.r_w
    (by rw [hk, ← Category.assoc, ← Karoubi.decompId, Category.id_comp]) (by rw [hk]; simp)
  exact E.karoubiConflations_isDeflation_of_retract
    (E.isStableUnderBaseChange_deflations.of_isPullback hpb hd) r'

/-- The exact structure on the idempotent completion (Bühler, Proposition 6.13). Its conflations
are the retracts, in the category of short complexes, of images of conflations of `E`. -/
def karoubi : ExactStructure (Karoubi C) where
  toConflationClass := E.karoubiConflations
  isInflation_id := E.karoubiConflations_isInflation_id
  isDeflation_id := E.karoubiConflations_isDeflation_id
  isInflation_comp _ _ := E.karoubiConflations_isInflation_comp
  isDeflation_comp _ _ := E.karoubiConflations_isDeflation_comp
  hasPushouts_inflations := ⟨fun g hf ↦ E.karoubiConflations_hasPushout hf g⟩
  isStableUnderCobaseChange_inflations :=
    ⟨fun sq hf ↦ E.karoubiConflations_isInflation_of_isPushout sq hf⟩
  hasPullbacks_deflations := ⟨fun g hf ↦ E.karoubiConflations_hasPullback hf g⟩
  isStableUnderBaseChange_deflations :=
    ⟨fun sq hg ↦ E.karoubiConflations_isDeflation_of_isPullback sq hg⟩

/-- The conflations of `E.karoubi` are the retracts of images of conflations of `E`. -/
theorem karoubi_conflation_iff (S : ShortComplex (Karoubi C)) :
    E.karoubi.Conflation S ↔
      ∃ T : ShortComplex C, E.Conflation T ∧ Nonempty (Retract S (T.map (toKaroubi C))) :=
  Iff.rfl

/-- The inflations of `E.karoubi` are the retracts of images of inflations of `E`. -/
theorem karoubi_isInflation_iff {P Q : Karoubi C} (f : P ⟶ Q) :
    E.karoubi.IsInflation f ↔ ∃ (A B : C) (a : A ⟶ B),
      E.IsInflation a ∧ Nonempty (RetractArrow f ((toKaroubi C).map a)) :=
  E.karoubiConflations_isInflation_iff f

/-- The deflations of `E.karoubi` are the retracts of images of deflations of `E`. -/
theorem karoubi_isDeflation_iff {Q R : Karoubi C} (g : Q ⟶ R) :
    E.karoubi.IsDeflation g ↔ ∃ (B D : C) (d : B ⟶ D),
      E.IsDeflation d ∧ Nonempty (RetractArrow g ((toKaroubi C).map d)) :=
  E.karoubiConflations_isDeflation_iff g

/-- The embedding of `C` into its idempotent completion is exact. -/
theorem isConflationExact_toKaroubi : E.IsConflationExact E.karoubi (toKaroubi C) where
  map_conflation hT := E.karoubiConflations_map_toKaroubi hT

end ExactStructure

end TauCeti
