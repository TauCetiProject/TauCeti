/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.Grp.FunctorTensor
public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.Algebra.Homology.Ext.Map.NatTrans
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Comparison

/-!
# External products of Ext groups of functors

For functors `M, N : C ⥤ AddCommGrpCat`, write `M ⊗ N` for their objectwise tensor product
`CategoryTheory.objectwiseTensor`, and recall that tensoring with a functor of flat values
(`CategoryTheory.Functor.HasFlatValues`) is exact (both are in
`TauCeti.Algebra.Category.Grp.FunctorTensor`).

For `x ∈ Extᵃ(M, F)` and `y ∈ Extᵇ(N, G)`, with `M` and `G` of flat values, and a pairing
`μ : F ⊗ G ⟶ K`, the *external product*
`CategoryTheory.Abelian.Ext.externalProduct μ x y : Extᵃ⁺ᵇ(M ⊗ N, K)` is the push-forward by `μ`
of the Yoneda product of `M ⊗ y ∈ Extᵇ(M ⊗ N, M ⊗ G)` and `x ⊗ G ∈ Extᵃ(M ⊗ G, F ⊗ G)`. It is
biadditive (`CategoryTheory.Abelian.Ext.add_externalProduct`,
`CategoryTheory.Abelian.Ext.externalProduct_add` and the `zero`, `neg` and `sub` variants; bundled
as `CategoryTheory.Abelian.Ext.externalProductAddHom`), natural
in both arguments (`CategoryTheory.Abelian.Ext.mk₀_comp_externalProduct`) and in the coefficients
(`CategoryTheory.Abelian.Ext.externalProduct_comp_mk₀_left_right`), commutes with
restriction along a functor, and comparison maps (`CategoryTheory.Functor.extComparison`) carry
external products to external products when they carry the pairing to the pairing
(`CategoryTheory.Functor.extComparison_externalProduct`).

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Hodge/CupProduct.lean` (declarations `New.Variety.cup`,
  `New.Variety.cup_map`, `New.Variety.Comparison.pull_cup`); Apache 2.0, Copyright 2026
  Anthropic, PBC. The definitions and results are adapted from these declarations.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Section 3.4 (Yoneda Ext and its products).
-/

public section

open CategoryTheory Limits Abelian

universe t t' w v u v' u' v'' u''

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-! ### The external product -/

namespace Abelian.Ext

variable [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] {M N F G K : C ⥤ AddCommGrpCat.{w}} {a b n : ℕ}

local notation "T" => objectwiseTensor C

/-- The *external product* of `x ∈ Extᵃ(M, F)` and `y ∈ Extᵇ(N, G)` along a pairing
`μ : F ⊗ G ⟶ K`, for `M` and `G` of flat values: the class in `Extᵃ⁺ᵇ(M ⊗ N, K)` obtained by
pushing forward along `μ` the Yoneda product of `M ⊗ y ∈ Extᵇ(M ⊗ N, M ⊗ G)` and
`x ⊗ G ∈ Extᵃ(M ⊗ G, F ⊗ G)`. -/
noncomputable def externalProduct [M.HasFlatValues] [G.HasFlatValues]
    (μ : ((T).obj F).obj G ⟶ K) (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    Ext.{t} (((T).obj M).obj N) K n :=
  ((y.mapExactFunctor ((T).obj M)).comp (x.mapExactFunctor ((T).flip.obj G))
    (by lia)).comp (mk₀ μ) (add_zero n)

/-- The external product is additive in the first argument. -/
lemma add_externalProduct [M.HasFlatValues] [G.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x x' : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ (x + x') y h = externalProduct μ x y h + externalProduct μ x' y h := by
  simp only [externalProduct, mapExactFunctor_add, comp_add, add_comp]

/-- The external product is additive in the second argument. -/
lemma externalProduct_add [M.HasFlatValues] [G.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x : Ext.{t} M F a) (y y' : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ x (y + y') h = externalProduct μ x y h + externalProduct μ x y' h := by
  simp only [externalProduct, mapExactFunctor_add, add_comp]

@[simp]
lemma zero_externalProduct [M.HasFlatValues] [G.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (y : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ (0 : Ext.{t} M F a) y h = 0 := by
  simp only [externalProduct, mapExactFunctor_zero, comp_zero, zero_comp]

@[simp]
lemma externalProduct_zero [M.HasFlatValues] [G.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x : Ext.{t} M F a) (h : a + b = n) :
    externalProduct μ x (0 : Ext.{t} N G b) h = 0 := by
  simp only [externalProduct, mapExactFunctor_zero, zero_comp]

/-- The external product, as a biadditive map. -/
noncomputable def externalProductAddHom [M.HasFlatValues] [G.HasFlatValues]
    (μ : ((T).obj F).obj G ⟶ K)
    (h : a + b = n) : Ext.{t} M F a →+ Ext.{t} N G b →+ Ext.{t} (((T).obj M).obj N) K n :=
  AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ externalProduct μ x y h)
    fun y y' ↦ externalProduct_add μ x y y' h)
    fun x x' ↦ AddMonoidHom.ext fun y ↦ add_externalProduct μ x x' y h

@[simp]
lemma externalProductAddHom_apply_apply [M.HasFlatValues] [G.HasFlatValues]
    (μ : ((T).obj F).obj G ⟶ K)
    (h : a + b = n) (x : Ext.{t} M F a) (y : Ext.{t} N G b) :
    externalProductAddHom μ h x y = externalProduct μ x y h :=
  (rfl)

@[simp]
lemma neg_externalProduct [M.HasFlatValues] [G.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ (-x) y h = -externalProduct μ x y h := by
  have := DFunLike.congr_fun ((externalProductAddHom μ h).map_neg x) y
  rwa [AddMonoidHom.neg_apply, externalProductAddHom_apply_apply,
    externalProductAddHom_apply_apply] at this

@[simp]
lemma externalProduct_neg [M.HasFlatValues] [G.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ x (-y) h = -externalProduct μ x y h :=
  (externalProductAddHom μ h x).map_neg y

lemma sub_externalProduct [M.HasFlatValues] [G.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x x' : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ (x - x') y h = externalProduct μ x y h - externalProduct μ x' y h := by
  have := DFunLike.congr_fun ((externalProductAddHom μ h).map_sub x x') y
  rwa [AddMonoidHom.sub_apply, externalProductAddHom_apply_apply,
    externalProductAddHom_apply_apply, externalProductAddHom_apply_apply] at this

lemma externalProduct_sub [M.HasFlatValues] [G.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x : Ext.{t} M F a) (y y' : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ x (y - y') h = externalProduct μ x y h - externalProduct μ x y' h :=
  (externalProductAddHom μ h x).map_sub y y'

/-- Pushing an external product forward along `κ : K ⟶ K'` changes the pairing to `μ ≫ κ`. -/
lemma externalProduct_comp_mk₀ [M.HasFlatValues] [G.HasFlatValues] {K' : C ⥤ AddCommGrpCat.{w}}
    (μ : ((T).obj F).obj G ⟶ K) (κ : K ⟶ K') (x : Ext.{t} M F a) (y : Ext.{t} N G b)
    (h : a + b = n) :
    (externalProduct μ x y h).comp (mk₀ κ) (add_zero n) = externalProduct (μ ≫ κ) x y h := by
  unfold externalProduct
  rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]

/-- The external product is natural in the coefficients: pushing `x` forward along `β₁ : F ⟶ F'`
and `y` along `β₂ : G ⟶ G'` and pairing by `μ'` is pairing `x` and `y` by `(β₁ ⊗ β₂) ≫ μ'`. -/
lemma externalProduct_comp_mk₀_left_right [M.HasFlatValues] [G.HasFlatValues]
    {F' G' : C ⥤ AddCommGrpCat.{w}} [G'.HasFlatValues] (β₁ : F ⟶ F') (β₂ : G ⟶ G')
    (μ' : ((T).obj F').obj G' ⟶ K) (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ' (x.comp (mk₀ β₁) (add_zero a)) (y.comp (mk₀ β₂) (add_zero b)) h =
      externalProduct (((T).map β₁).app G ≫ ((T).obj F').map β₂ ≫ μ') x y h := by
  have hτ := mapExactFunctor_comp_mk₀_comp ((T).flip.map β₂) x
    (mk₀ (((T).flip.obj G').map β₁ ≫ μ')) (add_zero a)
  unfold externalProduct
  simp only [mapExactFunctor_comp, mapExactFunctor_mk₀, comp_assoc_of_third_deg_zero,
    comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
  rw [← Functor.flip_map_app, ← hτ, mk₀_comp_mk₀,
    ← Category.assoc, ← Category.assoc]
  congr 4
  exact (objectwiseTensor.map_app_comp_map β₁ β₂).symm

/-- **Naturality of the external product in both arguments.** For `α : M' ⟶ M`, `β : N' ⟶ N`
and `γ : L ⟶ M ⊗ N` equal to `γ' : L ⟶ M' ⊗ N'` followed by `α ⊗ β`, pulling back the external
product of `x` and `y` along `γ` is pulling back the external product of `α* x` and `β* y` along
`γ'`. -/
lemma mk₀_comp_externalProduct [M.HasFlatValues] [G.HasFlatValues]
    {M' N' L : C ⥤ AddCommGrpCat.{w}} [M'.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) (α : M' ⟶ M) (β : N' ⟶ N)
    {γ : L ⟶ ((T).obj M).obj N} {γ' : L ⟶ ((T).obj M').obj N'}
    (hγ : γ' ≫ ((T).map α).app N' ≫ ((T).obj M).map β = γ) :
    (mk₀ γ).comp (externalProduct μ x y h) (zero_add n) =
      (mk₀ γ').comp (externalProduct μ ((mk₀ α).comp x (zero_add a))
        ((mk₀ β).comp y (zero_add b)) h) (zero_add n) := by
  have hτ := mapExactFunctor_comp_mk₀_comp ((T).map α) y
    ((x.mapExactFunctor ((T).flip.obj G)).comp (mk₀ μ) (add_zero a)) (by lia : b + a = n)
  unfold externalProduct
  simp only [mapExactFunctor_comp, mapExactFunctor_mk₀, comp_assoc_of_third_deg_zero,
    mk₀_comp_mk₀_assoc, comp_assoc_of_first_deg_zero]
  rw [Functor.flip_obj_map, hτ, mk₀_comp_mk₀_assoc,
    ← hγ, Category.assoc, objectwiseTensor.map_app_comp_map]

/-- Restriction along a functor `φ : C' ⥤ C` commutes with external products: the restriction of
the external product of `x` and `y` along `μ` is the external product of the restrictions along the
restricted pairing `φ.whiskerLeft μ`. -/
lemma mapExactFunctor_whiskeringLeft_externalProduct {C' : Type u'} [Category.{v'} C']
    [HasExt.{t'} (C' ⥤ AddCommGrpCat.{w})] (φ : C' ⥤ C) [M.HasFlatValues] [G.HasFlatValues]
    (μ : ((T).obj F).obj G ⟶ K) (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    (externalProduct μ x y h).mapExactFunctor
        ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ) =
      externalProduct (Functor.whiskerLeft φ μ)
        (x.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ))
        (y.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)) h := by
  unfold externalProduct
  rw [mapExactFunctor_comp, mapExactFunctor_comp, mapExactFunctor_mk₀, ← comp_mapExactFunctor,
    ← comp_mapExactFunctor, ← comp_mapExactFunctor, ← comp_mapExactFunctor]
  -- The two sides differ only in the exact functors `(T).obj M ⋙ restrict` against
  -- `restrict ⋙ (T').obj (φ ⋙ M)`, and `(T).flip.obj G ⋙ restrict` against
  -- `restrict ⋙ (T').flip.obj (φ ⋙ G)`, which are equal by
  -- `objectwiseTensor.obj_comp_whiskeringLeft` and `objectwiseTensor.flip_obj_comp_whiskeringLeft`.
  -- The type of `Ext.mapExactFunctor` depends on the functor, so these equalities cannot be
  -- rewritten under it; both hold by `rfl`, and so does the goal.
  rfl

end Abelian.Ext

open Abelian.Ext in
/-- **Comparison maps respect external products.** Let `(φ, β_F)`, `(φ, β_G)` and `(φ, β_K)` be
comparisons from `F`, `G`, `K` on `C` to `F'`, `G'`, `K'` on `C'` along the same functor `φ`,
carrying the pairing `μ : F ⊗ G ⟶ K` to `μ' : F' ⊗ G' ⟶ K'`, in the sense that
`(β_F ⊗ β_G) ≫ μ' = φ.whiskerLeft μ ≫ β_K`. For `x ∈ Extᵃ(M, F)`, `y ∈ Extᵇ(M', G)` and maps
`α₁ : N₁ ⟶ φ ⋙ M`, `α₂ : N₂ ⟶ φ ⋙ M'`, the comparison map for `β_K` along `α₁ ⊗ α₂` sends the
external product of `x` and `y` to the external product of the comparison images of `x` and `y`.
The case `F = G = K` with `β_F = β_G = β_K`, and of functors `M = Θ ⋙ N`, `M' = Θ ⋙ N'`
restricted from a third category along `Θ : C ⥤ A`, with `α₁` and `α₂` induced by a natural
transformation `η : Θ' ⟶ φ ⋙ Θ`, is the compatibility of comparisons with products of the
cohomology of functors on `A`. -/
theorem Functor.extComparison_externalProduct {C' : Type u'} [Category.{v'} C']
    [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C' ⥤ AddCommGrpCat.{w})]
    {F G K M M' : C ⥤ AddCommGrpCat.{w}} {F' G' K' N₁ N₂ : C' ⥤ AddCommGrpCat.{w}}
    [G.HasFlatValues] [G'.HasFlatValues] [M.HasFlatValues] [N₁.HasFlatValues] (φ : C' ⥤ C)
    (βF : φ ⋙ F ⟶ F') (βG : φ ⋙ G ⟶ G') (βK : φ ⋙ K ⟶ K')
    {μ : ((objectwiseTensor C).obj F).obj G ⟶ K}
    {μ' : ((objectwiseTensor C').obj F').obj G' ⟶ K'}
    (hμ : ((objectwiseTensor C').map βF).app (φ ⋙ G) ≫ ((objectwiseTensor C').obj F').map βG ≫
      μ' = φ.whiskerLeft μ ≫ βK)
    {a b n : ℕ} (x : Ext.{t} M F a) (y : Ext.{t} M' G b) (α₁ : N₁ ⟶ φ ⋙ M) (α₂ : N₂ ⟶ φ ⋙ M')
    (h : a + b = n) :
    extComparison φ βK (((objectwiseTensor C').map α₁).app N₂ ≫
        ((objectwiseTensor C').obj (φ ⋙ M)).map α₂ :
          _ ⟶ φ ⋙ ((objectwiseTensor C).obj M).obj M') n (externalProduct μ x y h) =
      externalProduct μ' (extComparison φ βF α₁ a x) (extComparison φ βG α₂ b y) h := by
  -- Restriction along `φ` commutes with the product (`h₁`); pushing forward along `β_K` turns the
  -- pairing into `φ.whiskerLeft μ ≫ β_K` (`h₂`), which `hμ` rewrites as `β_F` and `β_G` pushed
  -- onto the two factors (`h₄`); naturality in the source moves `α₁ ⊗ α₂` onto them (`h₃`).
  set x' := x.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)
  set y' := y.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)
  have h₁ := mapExactFunctor_whiskeringLeft_externalProduct φ μ x y h
  have h₂ := externalProduct_comp_mk₀ (φ.whiskerLeft μ) βK x' y' h
  have h₄ := (congrArg (fun m ↦ externalProduct m x' y' h) hμ.symm).trans
    (externalProduct_comp_mk₀_left_right βF βG μ' x' y' h).symm
  have h₃ := mk₀_comp_externalProduct μ' (x'.comp (mk₀ βF) (add_zero a))
    (y'.comp (mk₀ βG) (add_zero b)) h α₁ α₂ (γ' := 𝟙 _) (Category.id_comp _)
  rw [mk₀_id_comp] at h₃
  rw [extComparison_apply, h₁, extComparison_apply, extComparison_apply]
  -- The pull-back map `α₁ ⊗ α₂` has target `φ ⋙ (M ⊗ M')` only up to unfolding
  -- `objectwiseTensor`, so `h₂` and `h₄` are applied under it by `congrArg` rather than `rw`.
  exact (congrArg (fun z ↦ (mk₀ _).comp z (zero_add n)) (h₂.trans h₄)).trans h₃

end CategoryTheory
