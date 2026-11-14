/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Zero
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Category homology of a single-object category

For a monoid `G`, the category `SingleObj G` has a single object `SingleObj.star G` and
endomorphism monoid `G` with categorical composition `f ≫ g = g * f`
(`CategoryTheory.SingleObj.comp_as_mul`). This file records the low-degree differentials and
degree-`0` universal property of `categoryChainComplex M` and `categoryHomology M` for a functor
`M : SingleObj G ⥤ A`, and computes the degree-`2` homology of `SingleObj (Multiplicative (ZMod 2))`
with constant coefficients:

* Whenever `(2 : ℤ) • 𝟙 X : X ⟶ X` is a monomorphism in `A`,
  `categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2` vanishes
  (`isZero_categoryHomology_two_singleObj_zmod_two`). In particular, for trivial integral
  coefficients `ModuleCat.of ℤ ℤ`,
  `H₂(SingleObj (Multiplicative (ZMod 2)), ℤ) = 0`
  (`isZero_categoryHomology_two_singleObj_zmod_two_int`), in contrast with the even-degree group
  cohomology `H²(ℤ/2ℤ; ℤ) ≅ ℤ/2ℤ` (`TauCeti.groupCohomologyEvenEquivQuotSMulTop`).
* Conversely, whenever `(2 : ℤ) • 𝟙 X = 0` (for instance `X = ModuleCat.of ℤ (ZMod 2)`),
  `categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2` is canonically
  isomorphic to `X` (`categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero`,
  `categoryHomologyTwoSingleObjZModTwoModTwoIso`), matching `H₂(ℝP^∞; ℤ/2ℤ) ≅ ℤ/2ℤ`.

## Main results

* `TauCeti.ιCategoryChainComplex₁_d_singleObj`, `TauCeti.ιCategoryChainComplex₂_d_singleObj`,
  `TauCeti.ιCategoryChainComplex_mk₃_d_singleObj`: low-degree differentials on `SingleObj G`.
* `TauCeti.categoryChainComplex_const_d_one_zero_singleObj`: for constant coefficients on
  `SingleObj G`, the differential `d 1 0` vanishes.
* `TauCeti.epi_ιCategoryHomology₀_singleObj`, `TauCeti.descCategoryHomology₀SingleObj`: coinvariant
  universal property of `categoryHomology M 0` on `SingleObj G`.
* `TauCeti.isZero_categoryHomology_two_singleObj_zmod_two`,
  `TauCeti.isZero_categoryHomology_two_singleObj_zmod_two_moduleCat`,
  `TauCeti.isZero_categoryHomology_two_singleObj_zmod_two_int`: vanishing of degree-`2` homology of
  `SingleObj (Multiplicative (ZMod 2))` with `2`-torsion-free constant coefficients.
* `TauCeti.categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero`,
  `TauCeti.categoryHomologyTwoSingleObjZModTwoModTwoIso`: identification of degree-`2` homology of
  `SingleObj (Multiplicative (ZMod 2))` with `X` when `2 • 𝟙 X = 0`.
-/

public section

noncomputable section

open CategoryTheory Category Limits

universe u w u' v'

namespace TauCeti

section Monoid

variable {G : Type u} [Monoid G] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{u} A] [Preadditive A]

/-- On `SingleObj G`, the degree-`1` differential on `g : G` acts by `M(g) - 𝟙`. -/
@[reassoc]
lemma ιCategoryChainComplex₁_d_singleObj (M : SingleObj G ⥤ A) (g : G) :
    ιCategoryChainComplex₁ M (Quiver.SingleObj.toHom g) ≫ (categoryChainComplex M).d 1 0 =
      (M.map (Quiver.SingleObj.toHom g) - 𝟙 (M.obj (SingleObj.star G))) ≫
        ιCategoryChainComplex₀ M (SingleObj.star G) := by
  rw [ιCategoryChainComplex₁_d, Preadditive.sub_comp, id_comp]

/-- On `SingleObj G`, the degree-`2` differential sends `(f, g)` to
`M(f)` on `g`, minus `g * f`, plus `f`. -/
@[reassoc]
lemma ιCategoryChainComplex₂_d_singleObj (M : SingleObj G ⥤ A) (f g : G) :
    ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom g) ≫
        (categoryChainComplex M).d 2 1 =
      M.map (Quiver.SingleObj.toHom f) ≫ ιCategoryChainComplex₁ M (Quiver.SingleObj.toHom g) -
        ιCategoryChainComplex₁ M (Quiver.SingleObj.toHom (g * f)) +
        ιCategoryChainComplex₁ M (Quiver.SingleObj.toHom f) :=
  ιCategoryChainComplex₂_d M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom g)

/-- On `SingleObj G`, the degree-`3` differential sends `(f, g, h)` to
`M(f)` on `(g, h)`, minus `(g * f, h)`, plus `(f, h * g)`, minus `(f, g)`. -/
@[reassoc]
lemma ιCategoryChainComplex_mk₃_d_singleObj (M : SingleObj G ⥤ A) (f g h : G) :
    ιCategoryChainComplex M
        (ComposableArrows.mk₃ (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom g)
          (Quiver.SingleObj.toHom h)) ≫
        (categoryChainComplex M).d 3 2 =
      M.map (Quiver.SingleObj.toHom f) ≫
          ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom g) (Quiver.SingleObj.toHom h) -
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom (g * f)) (Quiver.SingleObj.toHom h) +
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom (h * g)) -
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom g) := by
  let f' := Quiver.SingleObj.toHom f
  let g' := Quiver.SingleObj.toHom g
  let h' := Quiver.SingleObj.toHom h
  have h0 : ιCategoryChainComplex M ((nerve (SingleObj G)).δ 0 (ComposableArrows.mk₃ f' g' h')) =
      ιCategoryChainComplex₂ M g' h' :=
    (ιCategoryChainComplex_congr M (nerve.δ₀_mk₃_eq f' g' h') rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (id_comp _))
  have h1 : (ιCategoryChainComplex M ((nerve (SingleObj G)).δ 1 (ComposableArrows.mk₃ f' g' h')) :
        M.obj (SingleObj.star G) ⟶ (categoryChainComplex M).X 2) =
      ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom (g * f)) h' :=
    (ιCategoryChainComplex_congr M (nerve.δ₁_mk₃_eq f' g' h') rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (id_comp _))
  have h2 : (ιCategoryChainComplex M ((nerve (SingleObj G)).δ 2 (ComposableArrows.mk₃ f' g' h')) :
        M.obj (SingleObj.star G) ⟶ (categoryChainComplex M).X 2) =
      ιCategoryChainComplex₂ M f' (Quiver.SingleObj.toHom (h * g)) :=
    (ιCategoryChainComplex_congr M (nerve.δ₂_mk₃_eq f' g' h') rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (id_comp _))
  have h3 : (ιCategoryChainComplex M ((nerve (SingleObj G)).δ 3 (ComposableArrows.mk₃ f' g' h')) :
        M.obj (SingleObj.star G) ⟶ (categoryChainComplex M).X 2) =
      ιCategoryChainComplex₂ M f' g' :=
    (ιCategoryChainComplex_congr M (nerve.δ₃_mk₃_eq f' g' h') rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (id_comp _))
  let s : Fin 3 → (M.obj (SingleObj.star G) ⟶ (categoryChainComplex M).X 2) := fun j ↦
    (-1 : ℤ) ^ (j.val + 1) •
      ιCategoryChainComplex M ((nerve (SingleObj G)).δ j.succ (ComposableArrows.mk₃ f' g' h'))
  refine (ιCategoryChainComplex_d M (ComposableArrows.mk₃ f' g' h')).trans
    ((congrArg₂ Add.add (congrArg (M.map f' ≫ ·) h0)
      ((Fin.sum_univ_three s).trans
        (congrArg₂ Add.add
          (congrArg₂ Add.add
            (congrArg ((-1 : ℤ) ^ (1 : ℕ) • ·) h1)
            (congrArg ((-1 : ℤ) ^ (2 : ℕ) • ·) h2))
          (congrArg ((-1 : ℤ) ^ (3 : ℕ) • ·) h3)))).trans ?_)
  change (M.map f' ≫ ιCategoryChainComplex₂ M g' h') +
    (((-1 : ℤ) • ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom (g * f)) h' +
      (1 : ℤ) • ιCategoryChainComplex₂ M f' (Quiver.SingleObj.toHom (h * g))) +
      (-1 : ℤ) • ιCategoryChainComplex₂ M f' g') = _
  dsimp only [f', g', h']
  simp [sub_eq_add_neg, add_assoc]

/-- For constant coefficients `X` on `SingleObj G`, the degree-`1` differential vanishes. -/
@[simp]
lemma categoryChainComplex_const_d_one_zero_singleObj (G : Type u) [Monoid G] (X : A) :
    (categoryChainComplex ((Functor.const (SingleObj G)).obj X)).d 1 0 = 0 := by
  ext σ
  obtain ⟨x, y, g, rfl⟩ := ComposableArrows.mk₁_surjective σ
  cases x; cases y
  simp

section DegreeZero

variable [CategoryWithHomology A]

/-- On `SingleObj G`, the canonical map `M.obj (SingleObj.star G) ⟶ categoryHomology M 0` is an
epimorphism. -/
instance epi_ιCategoryHomology₀_singleObj (M : SingleObj G ⥤ A) :
    Epi (ιCategoryHomology₀ M (SingleObj.star G)) where
  left_cancellation _ _ h := categoryHomology₀_hom_ext fun X ↦ by cases X; exact h

/-- Universal coinvariant morphism `categoryHomology M 0 ⟶ T` induced by a `G`-invariant morphism
`u : M.obj (SingleObj.star G) ⟶ T`. -/
def descCategoryHomology₀SingleObj (M : SingleObj G ⥤ A) {T : A}
    (u : M.obj (SingleObj.star G) ⟶ T)
    (hu : ∀ g : SingleObj.star G ⟶ SingleObj.star G, M.map g ≫ u = u) :
    categoryHomology M 0 ⟶ T :=
  (isColimitCategoryHomology₀Cocone M).desc
    { pt := T
      ι := { app := fun _ ↦ u
             naturality := fun _ _ g ↦
               (hu g).trans ((comp_id u).symm.trans (by simp)) } }

@[reassoc (attr := simp)]
lemma ιCategoryHomology₀_descSingleObj (M : SingleObj G ⥤ A) {T : A}
    (u : M.obj (SingleObj.star G) ⟶ T)
    (hu : ∀ g : SingleObj.star G ⟶ SingleObj.star G, M.map g ≫ u = u) :
    ιCategoryHomology₀ M (SingleObj.star G) ≫ descCategoryHomology₀SingleObj M u hu = u :=
  (isColimitCategoryHomology₀Cocone M).fac _ (SingleObj.star G)

end DegreeZero

end Monoid

/-! ### Degree-`2` category homology of `SingleObj (Multiplicative (ZMod 2))` -/

section ZModTwo

private abbrev ZModTwoGrp : Type := Multiplicative (ZMod 2)

private abbrev zmodTwoStar : SingleObj ZModTwoGrp := SingleObj.star ZModTwoGrp

private abbrev zmodTwoHom (a : ZModTwoGrp) : zmodTwoStar ⟶ zmodTwoStar :=
  Quiver.SingleObj.toHom a

private def zmodTwoGen : ZModTwoGrp := Multiplicative.ofAdd (1 : ZMod 2)

private lemma zmodTwo_cases (a : ZModTwoGrp) : a = 1 ∨ a = zmodTwoGen := by
  let x : ZMod 2 := Multiplicative.toAdd a
  have hlt : x.val < 2 := ZMod.val_lt x
  have hval : (x.val : ZMod 2) = x := ZMod.natCast_zmod_val x
  have ha : a = Multiplicative.ofAdd x := rfl
  rw [ha, ← hval]
  rcases h : x.val with _ | _ | n
  · exact .inl rfl
  · exact .inr rfl
  · rw [h] at hlt; omega

private lemma zmodTwoGen_ne_one : zmodTwoGen ≠ 1 := by decide

private lemma zmodTwoGen_mul_self : zmodTwoGen * zmodTwoGen = 1 := by
  change Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1
  rw [← ofAdd_add]
  decide

section Chains

variable {A : Type u'} [Category.{v'} A] [HasCoproducts.{0} A] [Preadditive A]

private abbrev zmodTwoConst (X : A) : SingleObj ZModTwoGrp ⥤ A :=
  (Functor.const (SingleObj ZModTwoGrp)).obj X

private def ι₁ZModTwo (X : A) (a : ZModTwoGrp) :
    X ⟶ (categoryChainComplex (zmodTwoConst X)).X 1 :=
  ιCategoryChainComplex₁ (zmodTwoConst X) (zmodTwoHom a)

private def ι₂ZModTwo (X : A) (a b : ZModTwoGrp) :
    X ⟶ (categoryChainComplex (zmodTwoConst X)).X 2 :=
  ιCategoryChainComplex₂ (zmodTwoConst X) (zmodTwoHom a) (zmodTwoHom b)

private def ι₃ZModTwo (X : A) (a b c : ZModTwoGrp) :
    X ⟶ (categoryChainComplex (zmodTwoConst X)).X 3 :=
  ιCategoryChainComplex (zmodTwoConst X)
    (ComposableArrows.mk₃ (zmodTwoHom a) (zmodTwoHom b) (zmodTwoHom c))

private def π₁ZModTwo (X : A) (a : ZModTwoGrp) :
    (categoryChainComplex (zmodTwoConst X)).X 1 ⟶ X :=
  descCategoryChainComplex (zmodTwoConst X) fun τ ↦
    if Quiver.SingleObj.toHom.symm (τ.map' 0 1) = a then 𝟙 X else 0

@[reassoc]
private lemma ι₁_π₁ZModTwo (X : A) (a b : ZModTwoGrp) :
    ι₁ZModTwo X a ≫ π₁ZModTwo X b = if a = b then 𝟙 X else 0 :=
  ιCategoryChainComplex_desc (zmodTwoConst X) _ (ComposableArrows.mk₁ (zmodTwoHom a))

private def π₂ZModTwo (X : A) (a b : ZModTwoGrp) :
    (categoryChainComplex (zmodTwoConst X)).X 2 ⟶ X :=
  descCategoryChainComplex (zmodTwoConst X) fun σ ↦
    if Quiver.SingleObj.toHom.symm (σ.map' 0 1) = a ∧
        Quiver.SingleObj.toHom.symm (σ.map' 1 2) = b then 𝟙 X else 0

@[reassoc]
private lemma ι₂_π₂ZModTwo (X : A) (a b c d : ZModTwoGrp) :
    ι₂ZModTwo X a b ≫ π₂ZModTwo X c d = if a = c ∧ b = d then 𝟙 X else 0 :=
  ιCategoryChainComplex_desc (zmodTwoConst X) _
    (ComposableArrows.mk₂ (zmodTwoHom a) (zmodTwoHom b))

private lemma zmodTwo_X₂_decomp (X : A) :
    𝟙 ((categoryChainComplex (zmodTwoConst X)).X 2) =
      π₂ZModTwo X 1 1 ≫ ι₂ZModTwo X 1 1 +
        π₂ZModTwo X 1 zmodTwoGen ≫ ι₂ZModTwo X 1 zmodTwoGen +
        π₂ZModTwo X zmodTwoGen 1 ≫ ι₂ZModTwo X zmodTwoGen 1 +
        π₂ZModTwo X zmodTwoGen zmodTwoGen ≫ ι₂ZModTwo X zmodTwoGen zmodTwoGen := by
  have hne : zmodTwoGen ≠ 1 := zmodTwoGen_ne_one
  have hne' : (1 : ZModTwoGrp) ≠ zmodTwoGen := hne.symm
  ext σ
  obtain ⟨x₀, x₁, x₂, f, g, rfl⟩ := ComposableArrows.mk₂_surjective σ
  cases x₀; cases x₁; cases x₂
  obtain ⟨a, rfl⟩ := Quiver.SingleObj.toHom.surjective f
  obtain ⟨b, rfl⟩ := Quiver.SingleObj.toHom.surjective g
  change ι₂ZModTwo X a b ≫ 𝟙 _ =
    ι₂ZModTwo X a b ≫
      (π₂ZModTwo X 1 1 ≫ ι₂ZModTwo X 1 1 +
        π₂ZModTwo X 1 zmodTwoGen ≫ ι₂ZModTwo X 1 zmodTwoGen +
        π₂ZModTwo X zmodTwoGen 1 ≫ ι₂ZModTwo X zmodTwoGen 1 +
        π₂ZModTwo X zmodTwoGen zmodTwoGen ≫ ι₂ZModTwo X zmodTwoGen zmodTwoGen)
  rw [comp_id, Preadditive.comp_add, Preadditive.comp_add, Preadditive.comp_add,
    ι₂_π₂ZModTwo_assoc, ι₂_π₂ZModTwo_assoc, ι₂_π₂ZModTwo_assoc, ι₂_π₂ZModTwo_assoc]
  rcases zmodTwo_cases a with rfl | rfl <;> rcases zmodTwo_cases b with rfl | rfl <;>
    simp [hne, hne']

private lemma ι₂ZModTwo_d (X : A) (a b : ZModTwoGrp) :
    ι₂ZModTwo X a b ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 =
      ι₁ZModTwo X b - ι₁ZModTwo X (b * a) + ι₁ZModTwo X a := by
  dsimp only [ι₂ZModTwo, ι₁ZModTwo]
  rw [ιCategoryChainComplex₂_d_singleObj]
  simp

private lemma ι₃ZModTwo_d (X : A) (a b c : ZModTwoGrp) :
    ι₃ZModTwo X a b c ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 =
      ι₂ZModTwo X b c - ι₂ZModTwo X (b * a) c + ι₂ZModTwo X a (c * b) - ι₂ZModTwo X a b := by
  dsimp only [ι₃ZModTwo, ι₂ZModTwo]
  rw [ιCategoryChainComplex_mk₃_d_singleObj]
  simp

@[reassoc]
private lemma ι₂_d_two_one_one_one (X : A) :
    ι₂ZModTwo X 1 1 ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 = ι₁ZModTwo X 1 := by
  rw [ι₂ZModTwo_d, mul_one, sub_self, zero_add]

@[reassoc]
private lemma ι₂_d_two_one_one_gen (X : A) :
    ι₂ZModTwo X 1 zmodTwoGen ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 = ι₁ZModTwo X 1 := by
  rw [ι₂ZModTwo_d, mul_one, sub_self, zero_add]

@[reassoc]
private lemma ι₂_d_two_one_gen_one (X : A) :
    ι₂ZModTwo X zmodTwoGen 1 ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 = ι₁ZModTwo X 1 := by
  rw [ι₂ZModTwo_d, one_mul, sub_add_cancel]

@[reassoc]
private lemma ι₂_d_two_one_gen_gen (X : A) :
    ι₂ZModTwo X zmodTwoGen zmodTwoGen ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 =
      ((2 : ℤ) • 𝟙 X) ≫ ι₁ZModTwo X zmodTwoGen - ι₁ZModTwo X 1 := by
  rw [ι₂ZModTwo_d, zmodTwoGen_mul_self, two_zsmul, Preadditive.add_comp, id_comp]
  abel

private lemma d_two_one_π₁_gen (X : A) :
    (categoryChainComplex (zmodTwoConst X)).d 2 1 ≫ π₁ZModTwo X zmodTwoGen =
      π₂ZModTwo X zmodTwoGen zmodTwoGen ≫ ((2 : ℤ) • 𝟙 X) := by
  have hne : (1 : ZModTwoGrp) ≠ zmodTwoGen := zmodTwoGen_ne_one.symm
  rw [← id_comp ((categoryChainComplex (zmodTwoConst X)).d 2 1), zmodTwo_X₂_decomp X]
  simp [Preadditive.add_comp, assoc, ι₂_d_two_one_one_one_assoc, ι₂_d_two_one_one_gen_assoc,
    ι₂_d_two_one_gen_one_assoc, ι₂_d_two_one_gen_gen_assoc, Preadditive.sub_comp,
    ι₁_π₁ZModTwo, hne]

private lemma d_two_one_π₁_one (X : A) :
    (categoryChainComplex (zmodTwoConst X)).d 2 1 ≫ π₁ZModTwo X 1 =
      π₂ZModTwo X 1 1 + π₂ZModTwo X 1 zmodTwoGen +
        π₂ZModTwo X zmodTwoGen 1 - π₂ZModTwo X zmodTwoGen zmodTwoGen := by
  have hne : zmodTwoGen ≠ 1 := zmodTwoGen_ne_one
  rw [← id_comp ((categoryChainComplex (zmodTwoConst X)).d 2 1), zmodTwo_X₂_decomp X]
  simp only [Preadditive.add_comp, assoc, ι₂_d_two_one_one_one_assoc, ι₂_d_two_one_one_gen_assoc,
    ι₂_d_two_one_gen_one_assoc, ι₂_d_two_one_gen_gen_assoc, Preadditive.sub_comp,
    ι₁_π₁ZModTwo, hne, ↓reduceIte, Preadditive.comp_neg, comp_id, comp_zero, zero_sub]
  abel

private lemma ι₃_d_three_two_one_one_gen (X : A) :
    ι₃ZModTwo X 1 1 zmodTwoGen ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 =
      ι₂ZModTwo X 1 zmodTwoGen - ι₂ZModTwo X 1 1 := by
  rw [ι₃ZModTwo_d, one_mul, mul_one, sub_self, zero_add]

private lemma ι₃_d_three_two_gen_one_one (X : A) :
    ι₃ZModTwo X zmodTwoGen 1 1 ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 =
      ι₂ZModTwo X 1 1 - ι₂ZModTwo X zmodTwoGen 1 := by
  rw [ι₃ZModTwo_d, one_mul, one_mul, sub_add_cancel]

private lemma d_three_two_π₂_gen_gen (X : A) :
    (categoryChainComplex (zmodTwoConst X)).d 3 2 ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen = 0 := by
  have hne' : (1 : ZModTwoGrp) ≠ zmodTwoGen := zmodTwoGen_ne_one.symm
  ext σ
  obtain ⟨x₀, x₁, x₂, x₃, f, g, h, rfl⟩ := ComposableArrows.mk₃_surjective σ
  cases x₀; cases x₁; cases x₂; cases x₃
  obtain ⟨a, rfl⟩ := Quiver.SingleObj.toHom.surjective f
  obtain ⟨b, rfl⟩ := Quiver.SingleObj.toHom.surjective g
  obtain ⟨c, rfl⟩ := Quiver.SingleObj.toHom.surjective h
  rw [comp_zero, ← assoc]
  change (ι₃ZModTwo X a b c ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2) ≫
    π₂ZModTwo X zmodTwoGen zmodTwoGen = 0
  rw [ι₃ZModTwo_d, Preadditive.sub_comp, Preadditive.add_comp, Preadditive.sub_comp]
  simp only [ι₂_π₂ZModTwo]
  rcases zmodTwo_cases a with rfl | rfl <;>
    rcases zmodTwo_cases b with rfl | rfl <;>
    rcases zmodTwo_cases c with rfl | rfl <;>
    simp [zmodTwoGen_mul_self, hne']

private def zmodTwoHomotopy₂ (X : A) :
    (categoryChainComplex (zmodTwoConst X)).X 2 ⟶
      (categoryChainComplex (zmodTwoConst X)).X 3 :=
  π₂ZModTwo X 1 zmodTwoGen ≫ ι₃ZModTwo X 1 1 zmodTwoGen -
    π₂ZModTwo X zmodTwoGen 1 ≫ ι₃ZModTwo X zmodTwoGen 1 1

/-- Key `2`-cycle decomposition on `SingleObj (Multiplicative (ZMod 2))`: any `2`-cycle `z` differs
from its `(g, g)`-component along `ι₂(g, g) + ι₂(1, 1)` by the boundary of
`z ≫ zmodTwoHomotopy₂`. -/
private lemma zmodTwo_cycle_sub_boundary {X T : A}
    (z : T ⟶ (categoryChainComplex (zmodTwoConst X)).X 2)
    (hz : z ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 = 0) :
    z - (z ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen) ≫
        (ι₂ZModTwo X zmodTwoGen zmodTwoGen + ι₂ZModTwo X 1 1) =
      (z ≫ zmodTwoHomotopy₂ X) ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 := by
  let c00 : T ⟶ X := z ≫ π₂ZModTwo X 1 1
  let c01 : T ⟶ X := z ≫ π₂ZModTwo X 1 zmodTwoGen
  let c10 : T ⟶ X := z ≫ π₂ZModTwo X zmodTwoGen 1
  let c11 : T ⟶ X := z ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen
  have h1 : c00 + c01 + c10 - c11 = 0 := by
    have h := congrArg (· ≫ π₁ZModTwo X 1) hz
    rw [zero_comp, assoc, d_two_one_π₁_one, Preadditive.comp_sub, Preadditive.comp_add,
      Preadditive.comp_add] at h
    exact h
  have hc00 : c00 = c11 - c01 - c10 := by
    rw [sub_eq_zero] at h1
    rw [← h1]
    abel
  have hz_decomp : z =
      c00 ≫ ι₂ZModTwo X 1 1 + c01 ≫ ι₂ZModTwo X 1 zmodTwoGen +
        c10 ≫ ι₂ZModTwo X zmodTwoGen 1 + c11 ≫ ι₂ZModTwo X zmodTwoGen zmodTwoGen := by
    simpa only [comp_id, Preadditive.comp_add, ← assoc] using
      congrArg (z ≫ ·) (zmodTwo_X₂_decomp X)
  have rhs_eq : (z ≫ zmodTwoHomotopy₂ X) ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 =
      c01 ≫ (ι₂ZModTwo X 1 zmodTwoGen - ι₂ZModTwo X 1 1) -
        c10 ≫ (ι₂ZModTwo X 1 1 - ι₂ZModTwo X zmodTwoGen 1) := by
    dsimp only [zmodTwoHomotopy₂]
    rw [Preadditive.comp_sub, Preadditive.sub_comp, ← assoc z (π₂ZModTwo X 1 zmodTwoGen),
      ← assoc z (π₂ZModTwo X zmodTwoGen 1), assoc c01, assoc c10,
      ι₃_d_three_two_one_one_gen, ι₃_d_three_two_gen_one_one]
  change z - c11 ≫ (ι₂ZModTwo X zmodTwoGen zmodTwoGen + ι₂ZModTwo X 1 1) = _
  rw [rhs_eq, hz_decomp, hc00]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_add]
  abel

section Homology

variable [CategoryWithHomology A]

/-- Whenever `(2 : ℤ) • 𝟙 X : X ⟶ X` is a monomorphism in `A`, the degree-`2` category homology of
`SingleObj (Multiplicative (ZMod 2))` with constant coefficients `X` vanishes. -/
lemma isZero_categoryHomology_two_singleObj_zmod_two (X : A) [Mono ((2 : ℤ) • 𝟙 X)] :
    IsZero (categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2) := by
  let K : ChainComplex A ℕ := categoryChainComplex (zmodTwoConst X)
  have hc11 : K.iCycles 2 ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen = 0 := by
    rw [← cancel_mono ((2 : ℤ) • 𝟙 X), zero_comp, assoc, ← d_two_one_π₁_gen X, ← assoc,
      K.iCycles_d 2 1, zero_comp]
  have hbd : (K.iCycles 2 ≫ zmodTwoHomotopy₂ X) ≫ K.d 3 2 = K.iCycles 2 := by
    have h := zmodTwo_cycle_sub_boundary (K.iCycles 2) (K.iCycles_d 2 1)
    rw [hc11, zero_comp, sub_zero] at h
    exact h.symm
  have hsec : (K.iCycles 2 ≫ zmodTwoHomotopy₂ X) ≫ K.toCycles 3 2 = 𝟙 (K.cycles 2) := by
    rw [← cancel_mono (K.iCycles 2), id_comp, assoc, K.toCycles_i 3 2]
    exact hbd
  refine (IsZero.iff_id_eq_zero (K.homology 2)).mpr ?_
  rw [← cancel_epi (K.homologyπ 2), comp_id, comp_zero, ← id_comp (K.homologyπ 2), ← hsec,
    assoc, K.toCycles_comp_homologyπ 3 2, comp_zero]

/-- Whenever `(2 : ℤ) • 𝟙 X = 0` in `A`, the degree-`2` category homology of
`SingleObj (Multiplicative (ZMod 2))` with constant coefficients `X` is isomorphic to `X`, generated
by the fundamental `2`-cycle `[g | g] + [1 | 1]`. -/
def categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero (X : A)
    (hX : (2 : ℤ) • 𝟙 X = 0) :
    categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2 ≅ X := by
  let K : ChainComplex A ℕ := categoryChainComplex (zmodTwoConst X)
  let ζ : X ⟶ K.X 2 := ι₂ZModTwo X zmodTwoGen zmodTwoGen + ι₂ZModTwo X 1 1
  have hζ : ζ ≫ K.d 2 1 = 0 := by
    dsimp only [ζ]
    rw [Preadditive.add_comp, ι₂_d_two_one_gen_gen, ι₂_d_two_one_one_one, hX, zero_comp,
      zero_sub, neg_add_cancel]
  have hprev : (ComplexShape.down ℕ).prev 2 = 3 :=
    (ComplexShape.down ℕ).prev_eq' (rfl : (ComplexShape.down ℕ).Rel 3 2)
  have hnext : (ComplexShape.down ℕ).next 2 = 1 :=
    (ComplexShape.down ℕ).next_eq' (rfl : (ComplexShape.down ℕ).Rel 2 1)
  let hom : K.homology 2 ⟶ X :=
    K.homologyι 2 ≫ K.descOpcycles (π₂ZModTwo X zmodTwoGen zmodTwoGen) 3 hprev
      (d_three_two_π₂_gen_gen X)
  have hπ_hom : K.homologyπ 2 ≫ hom = K.iCycles 2 ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen := by
    dsimp only [hom]
    rw [← assoc, K.homology_π_ι 2, assoc, K.p_descOpcycles]
  let liftζ : X ⟶ K.cycles 2 := K.liftCycles ζ 1 hnext hζ
  let inv : X ⟶ K.homology 2 := liftζ ≫ K.homologyπ 2
  refine
    { hom := hom
      inv := inv
      hom_inv_id := by
        rw [← cancel_epi (K.homologyπ 2), comp_id]
        have hπ_inv : K.homologyπ 2 ≫ hom ≫ inv =
            ((K.iCycles 2 ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen) ≫ liftζ) ≫ K.homologyπ 2 := by
          dsimp only [inv]
          rw [← assoc (K.homologyπ 2) hom, hπ_hom]
          simp only [assoc]
        rw [hπ_inv]
        have hcyc : 𝟙 (K.cycles 2) -
            (K.iCycles 2 ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen) ≫ liftζ =
            K.iCycles 2 ≫ zmodTwoHomotopy₂ X ≫ K.toCycles 3 2 := by
          rw [← cancel_mono (K.iCycles 2), Preadditive.sub_comp, id_comp]
          dsimp only [liftζ, ζ, K]
          simp only [assoc, HomologicalComplex.liftCycles_i, HomologicalComplex.toCycles_i]
          simpa only [assoc] using zmodTwo_cycle_sub_boundary
            ((categoryChainComplex (zmodTwoConst X)).iCycles 2)
            ((categoryChainComplex (zmodTwoConst X)).iCycles_d 2 1)
        have hcomp := congrArg (· ≫ K.homologyπ 2) hcyc
        simp only [Preadditive.sub_comp, id_comp, assoc, K.toCycles_comp_homologyπ 3 2,
          comp_zero, sub_eq_zero] at hcomp
        simpa only [assoc] using hcomp.symm
      inv_hom_id := by
        have hne : (1 : ZModTwoGrp) ≠ zmodTwoGen := zmodTwoGen_ne_one.symm
        dsimp only [inv]
        rw [assoc, hπ_hom, ← assoc, K.liftCycles_i ζ 1 hnext hζ]
        dsimp only [ζ]
        simp [Preadditive.add_comp, ι₂_π₂ZModTwo, hne] }

end Homology

end Chains

/-- For any ring `R` and `R`-module `V` without nontrivial `2`-torsion
(`∀ v : V, v + v = 0 → v = 0`), the degree-`2` category homology of
`SingleObj (Multiplicative (ZMod 2))` with constant coefficients `ModuleCat.of R V` vanishes. -/
lemma isZero_categoryHomology_two_singleObj_zmod_two_moduleCat {R : Type u} [Ring R]
    {V : Type w} [AddCommGroup V] [Module R V] (hV : ∀ v : V, v + v = 0 → v = 0) :
    IsZero (categoryHomology
      ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of R V)) 2) := by
  have : Mono ((2 : ℤ) • 𝟙 (ModuleCat.of R V)) := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have h0 : ((2 : ℤ) • 𝟙 (ModuleCat.of R V)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [two_zsmul] at h0
    exact sub_eq_zero.mp (hV (x - y) h0)
  exact isZero_categoryHomology_two_singleObj_zmod_two (ModuleCat.of R V)

/-- With trivial integral coefficients `ℤ`, the degree-`2` category homology of
`SingleObj (Multiplicative (ZMod 2))` vanishes:
`H₂(SingleObj (Multiplicative (ZMod 2)), ℤ) = 0`, in contrast with the group cohomology
`H²(ℤ/2ℤ; ℤ) ≅ ℤ/2ℤ`. -/
lemma isZero_categoryHomology_two_singleObj_zmod_two_int :
    IsZero (categoryHomology
      ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of ℤ ℤ)) 2) :=
  isZero_categoryHomology_two_singleObj_zmod_two_moduleCat fun _ hv ↦ by omega

/-- With constant `ℤ/2ℤ`-coefficients `ModuleCat.of ℤ (ZMod 2)`, the degree-`2` category homology of
`SingleObj (Multiplicative (ZMod 2))` is canonically isomorphic to `ℤ/2ℤ`. -/
def categoryHomologyTwoSingleObjZModTwoModTwoIso :
    categoryHomology
      ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of ℤ (ZMod 2))) 2 ≅
      ModuleCat.of ℤ (ZMod 2) :=
  categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero (ModuleCat.of ℤ (ZMod 2)) (by
    ext x
    change (2 : ℤ) • x = 0
    rw [two_zsmul, ← two_mul]
    exact zero_mul x)

/-- The degree-`2` category homology of `SingleObj (Multiplicative (ZMod 2))` with constant
`ℤ/2ℤ`-coefficients is nontrivial. -/
lemma not_isZero_categoryHomology_two_singleObj_zmod_two_mod_two :
    ¬ IsZero (categoryHomology
      ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of ℤ (ZMod 2))) 2) := by
  intro h
  have h' : IsZero (ModuleCat.of ℤ (ZMod 2)) :=
    h.of_iso categoryHomologyTwoSingleObjZModTwoModTwoIso.symm
  have h10 : (1 : ZMod 2) = 0 :=
    ConcreteCategory.congr_hom (h'.eq_of_tgt (𝟙 (ModuleCat.of ℤ (ZMod 2))) 0) (1 : ZMod 2)
  exact absurd h10 (by decide)

end ZModTwo

end TauCeti
