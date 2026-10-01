/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Functor
public import TauCeti.CategoryTheory.Products.Preadditive

/-!
# Products of exact categories

The product of two exact categories carries the componentwise exact structure: a short complex
in the product is a conflation precisely when both of its projections are conflations. This file
constructs that exact structure directly from Quillen's axioms and records its characteristic
lemmas.

The projection functors preserve conflations and jointly detect them. Inserting a zero object in
either coordinate is also conflation-exact. These functors are the input for the product formula
for exact Grothendieck groups.

## Main definitions

* `TauCeti.ExactStructure.prod`: the componentwise exact structure on a product category.

## Main results

* `TauCeti.ExactStructure.prod_conflation_iff`: a short complex in the product is a conflation
  exactly when both projected short complexes are conflations.
* `TauCeti.ExactStructure.isConflationExact_fst_prod` and
  `TauCeti.ExactStructure.isConflationExact_snd_prod`: the two projections preserve conflations.
* `TauCeti.ExactStructure.isConflationExact_sectL_prod` and
  `TauCeti.ExactStructure.isConflationExact_sectR_prod`: the zero-section functors preserve
  conflations.
* `TauCeti.ExactStructure.IsConflationExact.prod`: the product of two conflation-exact functors
  is conflation-exact for the product structures.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Definition 2.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [HasBinaryBiproducts D] in
private theorem isPushout_fst {A A' B B' : C × D} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPushout g f f' g') :
    IsPushout g.1 f.1 f'.1 g'.1 := by
  refine IsPushout.mk' (congrArg Prod.fst sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    let k : B' ⟶ (T, (0 : D)) := (φ, 0)
    let l : B' ⟶ (T, (0 : D)) := (φ', 0)
    have h := sq.hom_ext (k := k) (l := l)
      (Prod.hom_ext (by simpa using h₁) (by dsimp [k, l]))
      (Prod.hom_ext (by simpa using h₂) (by dsimp [k, l]))
    exact congrArg Prod.fst h
  · intro T a b h
    let a' : B ⟶ (T, (0 : D)) := (a, 0)
    let b' : A' ⟶ (T, (0 : D)) := (b, 0)
    have hab : g ≫ a' = f ≫ b' :=
      Prod.hom_ext (by simpa using h) (by dsimp [a', b']; simp)
    let l := sq.desc a' b' hab
    exact ⟨l.1, congrArg Prod.fst (sq.inl_desc a' b' hab),
      congrArg Prod.fst (sq.inr_desc a' b' hab)⟩

omit [HasBinaryBiproducts C] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem isPushout_snd {A A' B B' : C × D} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPushout g f f' g') :
    IsPushout g.2 f.2 f'.2 g'.2 := by
  refine IsPushout.mk' (congrArg Prod.snd sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    let k : B' ⟶ ((0 : C), T) := (0, φ)
    let l : B' ⟶ ((0 : C), T) := (0, φ')
    have h := sq.hom_ext (k := k) (l := l)
      (Prod.hom_ext (by dsimp [k, l]) (by simpa using h₁))
      (Prod.hom_ext (by dsimp [k, l]) (by simpa using h₂))
    exact congrArg Prod.snd h
  · intro T a b h
    let a' : B ⟶ ((0 : C), T) := (0, a)
    let b' : A' ⟶ ((0 : C), T) := (0, b)
    have hab : g ≫ a' = f ≫ b' :=
      Prod.hom_ext (by dsimp [a', b']; simp) (by simpa using h)
    let l := sq.desc a' b' hab
    exact ⟨l.2, congrArg Prod.snd (sq.inl_desc a' b' hab),
      congrArg Prod.snd (sq.inr_desc a' b' hab)⟩

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [HasBinaryBiproducts D] in
private theorem isPullback_fst {A A' B B' : C × D} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPullback f g g' f') :
    IsPullback f.1 g.1 g'.1 f'.1 := by
  refine IsPullback.mk' (congrArg Prod.fst sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    let k : (T, (0 : D)) ⟶ A := (φ, 0)
    let l : (T, (0 : D)) ⟶ A := (φ', 0)
    have h := sq.hom_ext (k := k) (l := l)
      (Prod.hom_ext (by simpa using h₁) (by dsimp [k, l]))
      (Prod.hom_ext (by simpa using h₂) (by dsimp [k, l]))
    exact congrArg Prod.fst h
  · intro T a b h
    let a' : (T, (0 : D)) ⟶ A' := (a, 0)
    let b' : (T, (0 : D)) ⟶ B := (b, 0)
    have hab : a' ≫ g' = b' ≫ f' :=
      Prod.hom_ext (by simpa using h) (by dsimp [a', b']; simp)
    let l := sq.lift a' b' hab
    exact ⟨l.1, congrArg Prod.fst (sq.lift_fst a' b' hab),
      congrArg Prod.fst (sq.lift_snd a' b' hab)⟩

omit [HasBinaryBiproducts C] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem isPullback_snd {A A' B B' : C × D} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPullback f g g' f') :
    IsPullback f.2 g.2 g'.2 f'.2 := by
  refine IsPullback.mk' (congrArg Prod.snd sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    let k : ((0 : C), T) ⟶ A := (0, φ)
    let l : ((0 : C), T) ⟶ A := (0, φ')
    have h := sq.hom_ext (k := k) (l := l)
      (Prod.hom_ext (by dsimp [k, l]) (by simpa using h₁))
      (Prod.hom_ext (by dsimp [k, l]) (by simpa using h₂))
    exact congrArg Prod.snd h
  · intro T a b h
    let a' : ((0 : C), T) ⟶ A' := (0, a)
    let b' : ((0 : C), T) ⟶ B := (0, b)
    have hab : a' ≫ g' = b' ≫ f' :=
      Prod.hom_ext (by dsimp [a', b']; simp) (by simpa using h)
    let l := sq.lift a' b' hab
    exact ⟨l.2, congrArg Prod.snd (sq.lift_fst a' b' hab),
      congrArg Prod.snd (sq.lift_snd a' b' hab)⟩

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem isPushout_prod {A A' B B' : C × D} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (h₁ : IsPushout g.1 f.1 f'.1 g'.1)
    (h₂ : IsPushout g.2 f.2 f'.2 g'.2) : IsPushout g f f' g' := by
  refine IsPushout.mk' (Prod.hom_ext h₁.w h₂.w) ?_ ?_
  · intro T φ φ' h₁' h₂'
    exact Prod.hom_ext
      (h₁.hom_ext (congrArg Prod.fst h₁') (congrArg Prod.fst h₂'))
      (h₂.hom_ext (congrArg Prod.snd h₁') (congrArg Prod.snd h₂'))
  · intro T a b h
    exact ⟨(h₁.desc a.1 b.1 (congrArg Prod.fst h),
        h₂.desc a.2 b.2 (congrArg Prod.snd h)),
      Prod.hom_ext (h₁.inl_desc _ _ _) (h₂.inl_desc _ _ _),
      Prod.hom_ext (h₁.inr_desc _ _ _) (h₂.inr_desc _ _ _)⟩

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem isPullback_prod {A A' B B' : C × D} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (h₁ : IsPullback f.1 g.1 g'.1 f'.1)
    (h₂ : IsPullback f.2 g.2 g'.2 f'.2) : IsPullback f g g' f' := by
  refine IsPullback.mk' (Prod.hom_ext h₁.w h₂.w) ?_ ?_
  · intro T φ φ' h₁' h₂'
    exact Prod.hom_ext
      (h₁.hom_ext (congrArg Prod.fst h₁') (congrArg Prod.fst h₂'))
      (h₂.hom_ext (congrArg Prod.snd h₁') (congrArg Prod.snd h₂'))
  · intro T a b h
    exact ⟨(h₁.lift a.1 b.1 (congrArg Prod.fst h),
        h₂.lift a.2 b.2 (congrArg Prod.snd h)),
      Prod.hom_ext (h₁.lift_fst _ _ _) (h₂.lift_fst _ _ _),
      Prod.hom_ext (h₁.lift_snd _ _ _) (h₂.lift_snd _ _ _)⟩

omit [HasZeroObject C] [HasBinaryBiproducts C]
    [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem isKernelCokernelPair_prod (S : ShortComplex (C × D))
    (h₁ : IsKernelCokernelPair (S.map (CategoryTheory.Prod.fst C D)))
    (h₂ : IsKernelCokernelPair (S.map (CategoryTheory.Prod.snd C D))) :
    IsKernelCokernelPair S := by
  have := h₁.mono_f
  have := h₂.mono_f
  let : Mono S.f :=
    ⟨fun {T} a b h => Prod.hom_ext
      ((cancel_mono (S.map (CategoryTheory.Prod.fst C D)).f).1 (congrArg Prod.fst h))
      ((cancel_mono (S.map (CategoryTheory.Prod.snd C D)).f).1 (congrArg Prod.snd h))⟩
  have := h₁.epi_g
  have := h₂.epi_g
  let : Epi S.g :=
    ⟨fun {T} a b h => Prod.hom_ext
      ((cancel_epi (S.map (CategoryTheory.Prod.fst C D)).g).1 (congrArg Prod.fst h))
      ((cancel_epi (S.map (CategoryTheory.Prod.snd C D)).g).1 (congrArg Prod.snd h))⟩
  exact
    { nonempty_fIsKernel := ⟨KernelFork.IsLimit.ofι' S.f S.zero fun {T} k hk =>
        ⟨(h₁.lift k.1 (congrArg Prod.fst hk), h₂.lift k.2 (congrArg Prod.snd hk)),
          Prod.hom_ext (h₁.lift_f _ _) (h₂.lift_f _ _)⟩⟩
      nonempty_gIsCokernel := ⟨CokernelCofork.IsColimit.ofπ' S.g S.zero fun {T} k hk =>
        ⟨(h₁.desc k.1 (congrArg Prod.fst hk), h₂.desc k.2 (congrArg Prod.snd hk)),
          Prod.hom_ext (h₁.g_desc _ _) (h₂.g_desc _ _)⟩⟩ }

namespace ExactStructure

variable (E : ExactStructure C) (E' : ExactStructure D)

private noncomputable def prodConflationClass : ConflationClass (C × D) where
  Conflation S := E.Conflation (S.map (CategoryTheory.Prod.fst C D)) ∧
    E'.Conflation (S.map (CategoryTheory.Prod.snd C D))
  isKernelCokernelPair S hS := isKernelCokernelPair_prod S
    (E.isKernelCokernelPair _ hS.1) (E'.isKernelCokernelPair _ hS.2)
  isClosedUnderIsomorphisms :=
    { of_iso := fun i hS => ⟨E.conflation_of_iso
          ((CategoryTheory.Prod.fst C D).mapShortComplex.mapIso i) hS.1,
        E'.conflation_of_iso ((CategoryTheory.Prod.snd C D).mapShortComplex.mapIso i) hS.2⟩ }

private theorem prodConflationClass_isInflation_iff {X Y : C × D} (i : X ⟶ Y) :
    (prodConflationClass E E').IsInflation i ↔ E.IsInflation i.1 ∧ E'.IsInflation i.2 := by
  constructor
  · intro hi
    obtain ⟨Z, p, zero, hS⟩ :=
      (ConflationClass.isInflation_iff (prodConflationClass E E') i).mp hi
    exact ⟨(ConflationClass.isInflation_iff E.toConflationClass i.1).mpr
        ⟨Z.1, p.1, congrArg Prod.fst zero, hS.1⟩,
      (ConflationClass.isInflation_iff E'.toConflationClass i.2).mpr
        ⟨Z.2, p.2, congrArg Prod.snd zero, hS.2⟩⟩
  · rintro ⟨hi₁, hi₂⟩
    obtain ⟨Z₁, p₁, zero₁, h₁⟩ :=
      (ConflationClass.isInflation_iff E.toConflationClass i.1).mp hi₁
    obtain ⟨Z₂, p₂, zero₂, h₂⟩ :=
      (ConflationClass.isInflation_iff E'.toConflationClass i.2).mp hi₂
    exact (ConflationClass.isInflation_iff (prodConflationClass E E') i).mpr
      ⟨(Z₁, Z₂), (p₁, p₂), Prod.hom_ext zero₁ zero₂, ⟨h₁, h₂⟩⟩

private theorem prodConflationClass_isDeflation_iff {Y Z : C × D} (p : Y ⟶ Z) :
    (prodConflationClass E E').IsDeflation p ↔ E.IsDeflation p.1 ∧ E'.IsDeflation p.2 := by
  constructor
  · intro hp
    obtain ⟨X, i, zero, hS⟩ :=
      (ConflationClass.isDeflation_iff (prodConflationClass E E') p).mp hp
    exact ⟨(ConflationClass.isDeflation_iff E.toConflationClass p.1).mpr
        ⟨X.1, i.1, congrArg Prod.fst zero, hS.1⟩,
      (ConflationClass.isDeflation_iff E'.toConflationClass p.2).mpr
        ⟨X.2, i.2, congrArg Prod.snd zero, hS.2⟩⟩
  · rintro ⟨hp₁, hp₂⟩
    obtain ⟨X₁, i₁, zero₁, h₁⟩ :=
      (ConflationClass.isDeflation_iff E.toConflationClass p.1).mp hp₁
    obtain ⟨X₂, i₂, zero₂, h₂⟩ :=
      (ConflationClass.isDeflation_iff E'.toConflationClass p.2).mp hp₂
    exact (ConflationClass.isDeflation_iff (prodConflationClass E E') p).mpr
      ⟨(X₁, X₂), (i₁, i₂), Prod.hom_ext zero₁ zero₂, ⟨h₁, h₂⟩⟩

private theorem prod_hasPushouts : (prodConflationClass E E').inflations.HasPushouts where
  hasPushout {X Y Z} {f} g hf := by
    have hfi := (prodConflationClass_isInflation_iff E E' f).1 hf
    let _ : HasPushout f.1 g.1 := E.hasPushouts_inflations.hasPushout g.1 hfi.1
    let _ : HasPushout f.2 g.2 := E'.hasPushouts_inflations.hasPushout g.2 hfi.2
    let P : C × D := (pushout f.1 g.1, pushout f.2 g.2)
    let inl : X ⟶ P := (pushout.inl f.1 g.1, pushout.inl f.2 g.2)
    let inr : Y ⟶ P := (pushout.inr f.1 g.1, pushout.inr f.2 g.2)
    apply IsPushout.hasPushout
    apply isPushout_prod (f' := inl) (g' := inr)
    · simpa [inl] using IsPushout.of_hasPushout f.1 g.1
    · simpa [inr] using IsPushout.of_hasPushout f.2 g.2

private theorem prod_hasPullbacks : (prodConflationClass E E').deflations.HasPullbacks where
  hasPullback {X Y Z} {f} g hf := by
    have hfi := (prodConflationClass_isDeflation_iff E E' f).1 hf
    let _ : HasPullback f.1 g.1 := E.hasPullbacks_deflations.hasPullback g.1 hfi.1
    let _ : HasPullback f.2 g.2 := E'.hasPullbacks_deflations.hasPullback g.2 hfi.2
    let P : C × D := (pullback f.1 g.1, pullback f.2 g.2)
    let fst : P ⟶ X := (pullback.fst f.1 g.1, pullback.fst f.2 g.2)
    let snd : P ⟶ Y := (pullback.snd f.1 g.1, pullback.snd f.2 g.2)
    apply IsPullback.hasPullback
    apply isPullback_prod (f := fst) (g := snd)
    · simpa [fst] using IsPullback.of_hasPullback f.1 g.1
    · simpa [snd] using IsPullback.of_hasPullback f.2 g.2

/-- **The componentwise exact structure on a product category.** A short complex is a
conflation when each of its two projections is a conflation. -/
noncomputable def prod : ExactStructure (C × D) where
  toConflationClass := prodConflationClass E E'
  isInflation_id X := (prodConflationClass_isInflation_iff E E' _).2
    ⟨E.isInflation_id X.1, E'.isInflation_id X.2⟩
  isDeflation_id X := (prodConflationClass_isDeflation_iff E E' _).2
    ⟨E.isDeflation_id X.1, E'.isDeflation_id X.2⟩
  isInflation_comp i j hi hj := (prodConflationClass_isInflation_iff E E' _).2
    ⟨E.isInflation_comp i.1 j.1
        ((prodConflationClass_isInflation_iff E E' i).1 hi).1
        ((prodConflationClass_isInflation_iff E E' j).1 hj).1,
      E'.isInflation_comp i.2 j.2
        ((prodConflationClass_isInflation_iff E E' i).1 hi).2
        ((prodConflationClass_isInflation_iff E E' j).1 hj).2⟩
  isDeflation_comp p q hp hq := (prodConflationClass_isDeflation_iff E E' _).2
    ⟨E.isDeflation_comp p.1 q.1
        ((prodConflationClass_isDeflation_iff E E' p).1 hp).1
        ((prodConflationClass_isDeflation_iff E E' q).1 hq).1,
      E'.isDeflation_comp p.2 q.2
        ((prodConflationClass_isDeflation_iff E E' p).1 hp).2
        ((prodConflationClass_isDeflation_iff E E' q).1 hq).2⟩
  hasPushouts_inflations := prod_hasPushouts E E'
  isStableUnderCobaseChange_inflations :=
    { of_isPushout := fun sq hf => (prodConflationClass_isInflation_iff E E' _).2
        ⟨E.isStableUnderCobaseChange_inflations.of_isPushout (isPushout_fst sq)
            ((prodConflationClass_isInflation_iff E E' _).1 hf).1,
          E'.isStableUnderCobaseChange_inflations.of_isPushout (isPushout_snd sq)
            ((prodConflationClass_isInflation_iff E E' _).1 hf).2⟩ }
  hasPullbacks_deflations := prod_hasPullbacks E E'
  isStableUnderBaseChange_deflations :=
    { of_isPullback := fun sq hp => (prodConflationClass_isDeflation_iff E E' _).2
        ⟨E.isStableUnderBaseChange_deflations.of_isPullback (isPullback_fst sq)
            ((prodConflationClass_isDeflation_iff E E' _).1 hp).1,
          E'.isStableUnderBaseChange_deflations.of_isPullback (isPullback_snd sq)
            ((prodConflationClass_isDeflation_iff E E' _).1 hp).2⟩ }

/-- A short complex is a conflation for the product exact structure exactly when both projected
short complexes are conflations. -/
@[simp]
theorem prod_conflation_iff (S : ShortComplex (C × D)) :
    (E.prod E').Conflation S ↔
      E.Conflation (S.map (CategoryTheory.Prod.fst C D)) ∧
        E'.Conflation (S.map (CategoryTheory.Prod.snd C D)) :=
  Iff.rfl

/-- The first projection from a product exact category preserves conflations. -/
theorem isConflationExact_fst_prod :
    IsConflationExact (E.prod E') E (CategoryTheory.Prod.fst C D) :=
  ⟨fun hS => (prod_conflation_iff E E' _).1 hS |>.1⟩

/-- The second projection from a product exact category preserves conflations. -/
theorem isConflationExact_snd_prod :
    IsConflationExact (E.prod E') E' (CategoryTheory.Prod.snd C D) :=
  ⟨fun hS => (prod_conflation_iff E E' _).1 hS |>.2⟩

/-- Inserting a zero object in the second coordinate preserves conflations. -/
theorem isConflationExact_sectL_prod :
    IsConflationExact E (E.prod E') (CategoryTheory.Prod.sectL C (0 : D)) := by
  refine ⟨fun {S} hS => (prod_conflation_iff E E' _).2 ⟨?_, ?_⟩⟩
  · simpa [ShortComplex.map, CategoryTheory.Prod.sectL, CategoryTheory.Prod.fst] using hS
  · apply E'.conflation_of_splitting
    apply ShortComplex.Splitting.ofIsZero
    all_goals exact isZero_zero D

/-- Inserting a zero object in the first coordinate preserves conflations. -/
theorem isConflationExact_sectR_prod :
    IsConflationExact E' (E.prod E') (CategoryTheory.Prod.sectR (0 : C) D) := by
  refine ⟨fun {S} hS => (prod_conflation_iff E E' _).2 ⟨?_, ?_⟩⟩
  · apply E.conflation_of_splitting
    apply ShortComplex.Splitting.ofIsZero
    all_goals exact isZero_zero C
  · simpa [ShortComplex.map, CategoryTheory.Prod.sectR, CategoryTheory.Prod.snd] using hS

section Functor

variable {C₁ : Type u} [Category.{v} C₁] [Preadditive C₁] [HasZeroObject C₁]
  [HasBinaryBiproducts C₁]
  {C₂ : Type*} [Category C₂] [Preadditive C₂] [HasZeroObject C₂]
  [HasBinaryBiproducts C₂]
  {D₁ : Type u'} [Category.{v'} D₁] [Preadditive D₁] [HasZeroObject D₁]
  [HasBinaryBiproducts D₁]
  {D₂ : Type*} [Category D₂] [Preadditive D₂] [HasZeroObject D₂]
  [HasBinaryBiproducts D₂]
  {E₁ : ExactStructure C₁} {E₂ : ExactStructure C₂}
  {E₁' : ExactStructure D₁} {E₂' : ExactStructure D₂}
  {F : C₁ ⥤ C₂} {G : D₁ ⥤ D₂} [F.Additive] [G.Additive]

namespace IsConflationExact

/-- The product of two conflation-exact functors is conflation-exact for the componentwise exact
structures. -/
theorem prod (hF : E₁.IsConflationExact E₂ F) (hG : E₁'.IsConflationExact E₂' G) :
    (E₁.prod E₁').IsConflationExact (E₂.prod E₂') (F.prod G) := by
  refine ⟨fun {S} hS => (prod_conflation_iff E₂ E₂' _).2 ⟨?_, ?_⟩⟩
  · have h := hF.map_conflation ((prod_conflation_iff E₁ E₁' S).1 hS |>.1)
    simpa [ShortComplex.map, CategoryTheory.Functor.prod, CategoryTheory.Prod.fst] using h
  · have h := hG.map_conflation ((prod_conflation_iff E₁ E₁' S).1 hS |>.2)
    simpa [ShortComplex.map, CategoryTheory.Functor.prod, CategoryTheory.Prod.snd] using h

end IsConflationExact

end Functor

end ExactStructure

end TauCeti
