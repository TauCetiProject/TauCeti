/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Retract

/-!
# Limits, biproducts and retracts in the idempotent completion

* The embedding `toKaroubi` preserves all limits and colimits.
* `HasFiniteBiproducts (Karoubi C)` and `HasBinaryBiproducts (Karoubi C)` for a preadditive
  category `C` with a zero object and binary biproducts.
* `CategoryTheory.Idempotents.Karoubi.exists_span_retract`: if `i` is a retract of the image of
  `a : A ⟶ B` under `toKaroubi`, then for every `h` out of the source of `i` the span `(i, h)` is a
  retract of the image of a span `(a, k)`; `exists_cospan_retract` is the dual.
* `CategoryTheory.Idempotents.Karoubi.exists_retractArrow_comp_of_retracts`: if `i` and `j` are
  retracts of the images of `a` and `b` under `toKaroubi`, then `i ≫ j` is a retract of the image
  of `(a ⊞ 𝟙) ≫ θ ≫ (𝟙 ⊞ b)` for some isomorphism `θ`.
-/

public section

namespace CategoryTheory

open Limits Idempotents

universe w w' v u

variable {C : Type u} [Category.{v} C]

namespace Idempotents

/-- The embedding `toKaroubi` preserves all limits. -/
instance {J : Type*} [Category J] (K : J ⥤ C) : PreservesLimit K (toKaroubi C) where
  preserves {c} hc := ⟨{
    lift s := ⟨hc.lift ⟨s.pt.X,
        { app j := (s.π.app j).f
          naturality j j' f := by simpa using (congrArg Karoubi.Hom.f (s.w f)).symm }⟩,
      -- The lift is compatible with the idempotent of `s.pt` by uniqueness.
      by simpa using hc.hom_ext fun j ↦ by simp⟩
    fac s j := by
      ext
      simp
    uniq s m hm := by
      ext
      exact hc.hom_ext fun j ↦ by simpa using congrArg Karoubi.Hom.f (hm j) }⟩

/-- The embedding `toKaroubi` preserves all colimits. -/
instance {J : Type*} [Category J] (K : J ⥤ C) : PreservesColimit K (toKaroubi C) where
  preserves {c} hc := ⟨{
    desc s := ⟨hc.desc ⟨s.pt.X,
        { app j := (s.ι.app j).f
          naturality j j' f := by simpa using congrArg Karoubi.Hom.f (s.w f) }⟩,
      -- The descent is compatible with the idempotent of `s.pt` by uniqueness.
      by simpa using hc.hom_ext fun j ↦ by simp⟩
    fac s j := by
      ext
      simp
    uniq s m hm := by
      ext
      exact hc.hom_ext fun j ↦ by simpa using congrArg Karoubi.Hom.f (hm j) }⟩

instance {J : Type*} [Category J] : PreservesLimitsOfShape J (toKaroubi C) where

instance {J : Type*} [Category J] : PreservesColimitsOfShape J (toKaroubi C) where

instance : PreservesLimitsOfSize.{w, w'} (toKaroubi C) where

instance : PreservesColimitsOfSize.{w, w'} (toKaroubi C) where

end Idempotents

/-- If `i` is a retract of the image of `a : A ⟶ B` under `toKaroubi`, then for every
`h : P ⟶ P'` there is `k : A ⟶ P'.X` such that the span `(i, h)` is a retract of the image of the
span `(a, k)`, with `P'` a retract of `P'.X` by `Karoubi.decompId`. -/
theorem Idempotents.Karoubi.exists_span_retract {P Q P' : Karoubi C} {i : P ⟶ Q} {A B : C}
    {a : A ⟶ B} (r : RetractArrow i ((toKaroubi C).map a)) (h : P ⟶ P') :
    ∃ k : A ⟶ P'.X, h ≫ Karoubi.decompId_i P' = r.i.left ≫ (toKaroubi C).map k ∧
      (toKaroubi C).map k ≫ Karoubi.decompId_p P' = r.r.left ≫ h := by
  have hk : (toKaroubi C).map (r.r.left ≫ h ≫ Karoubi.decompId_i P').f =
      r.r.left ≫ h ≫ Karoubi.decompId_i P' := by
    ext
    simp
  refine ⟨_, by rw [hk]; simp, ?_⟩
  rw [hk, Category.assoc, Category.assoc, ← Karoubi.decompId, Category.comp_id]

/-- If `p` is a retract of the image of `d : B ⟶ D` under `toKaroubi`, then for every
`h : P' ⟶ P` there is `k : P'.X ⟶ D` such that the cospan `(p, h)` is a retract of the image of
the cospan `(d, k)`. This is dual to `Karoubi.exists_span_retract`. -/
theorem Idempotents.Karoubi.exists_cospan_retract {Q P P' : Karoubi C} {p : Q ⟶ P} {B D : C}
    {d : B ⟶ D} (r : RetractArrow p ((toKaroubi C).map d)) (h : P' ⟶ P) :
    ∃ k : P'.X ⟶ D, Karoubi.decompId_i P' ≫ (toKaroubi C).map k = h ≫ r.i.right ∧
      Karoubi.decompId_p P' ≫ h = (toKaroubi C).map k ≫ r.r.right := by
  have hk : (toKaroubi C).map (Karoubi.decompId_p P' ≫ h ≫ r.i.right).f =
      Karoubi.decompId_p P' ≫ h ≫ r.i.right := by
    ext
    simp
  refine ⟨_, ?_, by rw [hk]; simp⟩
  rw [hk, ← Category.assoc, ← Karoubi.decompId, Category.id_comp]

variable [Preadditive C]

section Biproducts

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- The idempotent completion of an additive category has finite biproducts. -/
instance : HasFiniteBiproducts (Karoubi C) :=
  have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  Idempotents.Karoubi.karoubi_hasFiniteBiproducts

instance : HasBinaryBiproducts (Karoubi C) := hasBinaryBiproducts_of_finite_biproducts _

end Biproducts

variable [HasBinaryBiproducts C]

/-- Let `i : P ⟶ Q` and `j : Q ⟶ R` be retracts of the images under `toKaroubi` of `a : A ⟶ B`
and `b : B' ⟶ C'`, with the retractions given explicitly. Then for some isomorphism `θ` of
`B ⊞ B'`, the composite `i ≫ j` is a retract of the image of `(a ⊞ 𝟙) ≫ θ ≫ (𝟙 ⊞ b)`. -/
theorem Idempotents.Karoubi.exists_retractArrow_comp_of_retracts {P Q R : Karoubi C} (i : P ⟶ Q)
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
  -- `θ` is the involution exchanging the copy of `Q` in `B` with the copy in `B'`.
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

end CategoryTheory
