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
# Squares, biproducts and retracts in the idempotent completion

* `CategoryTheory.IsPushout.map_toKaroubi`, `CategoryTheory.IsPullback.map_toKaroubi`: the
  embedding `toKaroubi` preserves pushout and pullback squares.
* `HasFiniteBiproducts (Karoubi C)` and `HasBinaryBiproducts (Karoubi C)` for a preadditive
  category `C` with a zero object and binary biproducts.
* `CategoryTheory.Idempotents.Karoubi.exists_retractArrow_comp_of_retracts`: if `i` and `j` are
  retracts of the images of `a` and `b` under `toKaroubi`, then `i ≫ j` is a retract of the image
  of `(a ⊞ 𝟙) ≫ θ ≫ (𝟙 ⊞ b)` for an isomorphism `θ`, the involution exchanging the two copies of
  the middle object.
-/

public section

namespace CategoryTheory

open Limits Idempotents

universe v u

variable {C : Type u} [Category.{v} C]

/-- The functor `toKaroubi` preserves pushout squares: a morphism out of a formal direct factor is a
morphism of `C` compatible with the idempotent, and the induced morphism inherits that
compatibility by uniqueness. -/
theorem IsPushout.map_toKaroubi {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z}
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
theorem IsPullback.map_toKaroubi {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z}
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

/-- The composition step, with the two retractions spelled out. The middle object `Q` is a retract
of both `B` and `B'`; the involution `θ` of `B ⊞ B'` exchanges these two copies of `Q` and is the
identity on their complements, so `i ≫ j` is a retract of the image of `(a ⊞ 𝟙) ≫ θ ≫ (𝟙 ⊞ b)`. -/
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
