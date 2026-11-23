/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Data.ZMod.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.SingleObj
import TauCeti.Data.ZMod.Two

/-!
# Degree-`2` category homology of `SingleObj (Multiplicative (ZMod 2))`

Using the `(g, g)`-coordinate `TauCeti.categoryChainComplexπ₂SingleObjZModTwo`
(`g = Multiplicative.ofAdd 1`) and `2`-chain `TauCeti.categoryChainComplexSingleObjZModTwoFundChain`
(`[g | g] + [1 | 1]`), `TauCeti.categoryHomologyTwoSingleObjZModTwoIsoKernel` gives
`H₂(SingleObj (Multiplicative (ZMod 2)), X) ≅ kernel ((2 : ℤ) • 𝟙 X)`, yielding
`TauCeti.isZero_categoryHomology_two_singleObj_zmod_two_of_mono` /
`TauCeti.isZero_categoryHomology_two_singleObj_zmod_two_int` (`H₂ = 0` on `ℤ`, vs. `H² ≅ ℤ/2ℤ`) and
`TauCeti.categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero` /
`TauCeti.categoryHomologyTwoSingleObjZModTwoModTwoIso` (`H₂ ≅ ℤ/2ℤ` on `ℤ/2ℤ`).
-/

public section

noncomputable section

open CategoryTheory Category Limits

universe u w u' v'

namespace TauCeti

variable {A : Type u'} [Category.{v'} A] [HasCoproducts.{0} A] [Preadditive A]

private abbrev zmodTwoConst (X : A) : SingleObj (Multiplicative (ZMod 2)) ⥤ A :=
  (Functor.const _).obj X

private abbrev ι₁ZModTwo (X : A) (a : Multiplicative (ZMod 2)) :
    X ⟶ (categoryChainComplex (zmodTwoConst X)).X 1 :=
  ιCategoryChainComplex₁ (zmodTwoConst X) (Quiver.SingleObj.toHom a)

private abbrev ι₂ZModTwo (X : A) (a b : Multiplicative (ZMod 2)) :
    X ⟶ (categoryChainComplex (zmodTwoConst X)).X 2 :=
  ιCategoryChainComplex₂ (zmodTwoConst X) (Quiver.SingleObj.toHom a) (Quiver.SingleObj.toHom b)

private abbrev ι₃ZModTwo (X : A) (a b c : Multiplicative (ZMod 2)) :
    X ⟶ (categoryChainComplex (zmodTwoConst X)).X 3 :=
  ιCategoryChainComplex₃ (zmodTwoConst X) (Quiver.SingleObj.toHom a) (Quiver.SingleObj.toHom b)
    (Quiver.SingleObj.toHom c)

private lemma zmodTwo_X₂_hom_ext {X Y : A} {φ ψ : (categoryChainComplex (zmodTwoConst X)).X 2 ⟶ Y}
    (h : ∀ a b : Multiplicative (ZMod 2), ι₂ZModTwo X a b ≫ φ = ι₂ZModTwo X a b ≫ ψ) : φ = ψ := by
  ext σ; obtain ⟨⟨⟩, ⟨⟩, ⟨⟩, f, g, rfl⟩ := ComposableArrows.mk₂_surjective σ
  exact h (Quiver.SingleObj.toHom.symm f) (Quiver.SingleObj.toHom.symm g)

private lemma zmodTwo_X₃_hom_ext {X Y : A} {φ ψ : (categoryChainComplex (zmodTwoConst X)).X 3 ⟶ Y}
    (h : ∀ a b c : Multiplicative (ZMod 2), ι₃ZModTwo X a b c ≫ φ = ι₃ZModTwo X a b c ≫ ψ) :
    φ = ψ := by
  ext σ; obtain ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, f, g, k, rfl⟩ := ComposableArrows.mk₃_surjective σ
  exact h (Quiver.SingleObj.toHom.symm f) (Quiver.SingleObj.toHom.symm g)
    (Quiver.SingleObj.toHom.symm k)

private def π₁ZModTwo (X : A) (a : Multiplicative (ZMod 2)) :
    (categoryChainComplex (zmodTwoConst X)).X 1 ⟶ X :=
  descCategoryChainComplex (zmodTwoConst X) fun τ ↦
    if Quiver.SingleObj.toHom.symm (τ.map' 0 1) = a then 𝟙 X else 0

@[reassoc] private lemma ι₁_π₁ZModTwo (X : A) (a b : Multiplicative (ZMod 2)) :
    ι₁ZModTwo X a ≫ π₁ZModTwo X b = if a = b then 𝟙 X else 0 := by
  simp [π₁ZModTwo]

/-- Coordinate projection onto the `(a, b)`-summand of `2`-chains on
`SingleObj (Multiplicative (ZMod 2))` with constant coefficients `X`. -/
def categoryChainComplexπ₂SingleObjZModTwo (X : A) (a b : Multiplicative (ZMod 2)) :
    (categoryChainComplex ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X)).X 2 ⟶ X :=
  descCategoryChainComplex (zmodTwoConst X) fun σ ↦
    if Quiver.SingleObj.toHom.symm (σ.map' 0 1) = a ∧
        Quiver.SingleObj.toHom.symm (σ.map' 1 2) = b then 𝟙 X else 0

@[reassoc (attr := simp)]
lemma ιCategoryChainComplex₂_π₂SingleObjZModTwo (X : A) (a b c d : Multiplicative (ZMod 2)) :
    ιCategoryChainComplex₂ (X := SingleObj.star _) (Y := SingleObj.star _) (Z := SingleObj.star _)
        ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) a b ≫
      categoryChainComplexπ₂SingleObjZModTwo X c d = if a = c ∧ b = d then 𝟙 X else 0 := by
  simp [categoryChainComplexπ₂SingleObjZModTwo, ιCategoryChainComplex₂]

@[reassoc] private lemma ι₂_π₂ZModTwo (X : A) (a b c d : Multiplicative (ZMod 2)) :
    ι₂ZModTwo X a b ≫ categoryChainComplexπ₂SingleObjZModTwo X c d =
      if a = c ∧ b = d then 𝟙 X else 0 := by simp

@[reassoc] private lemma categoryChainComplexMap_const_π₂SingleObjZModTwo {X Y : A} (f : X ⟶ Y)
    (a b : Multiplicative (ZMod 2)) :
    (categoryChainComplexMap ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).map f)).f 2 ≫
        categoryChainComplexπ₂SingleObjZModTwo Y a b =
      categoryChainComplexπ₂SingleObjZModTwo X a b ≫ f :=
  zmodTwo_X₂_hom_ext fun _ _ ↦ by simp; split_ifs <;> simp

@[reassoc] private lemma ι₂ZModTwo_d (X : A) (a b : Multiplicative (ZMod 2)) :
    ι₂ZModTwo X a b ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 =
      ι₁ZModTwo X b - ι₁ZModTwo X (b * a) + ι₁ZModTwo X a :=
  (ιCategoryChainComplex₂_d_singleObj (zmodTwoConst X) a b).trans (by simp [ι₁ZModTwo])

@[reassoc] private lemma ι₃ZModTwo_d (X : A) (a b c : Multiplicative (ZMod 2)) :
    ι₃ZModTwo X a b c ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 =
      ι₂ZModTwo X b c - ι₂ZModTwo X (b * a) c + ι₂ZModTwo X a (c * b) - ι₂ZModTwo X a b :=
  (ιCategoryChainComplex₃_d_singleObj (zmodTwoConst X) a b c).trans (by simp [ι₂ZModTwo])

/-- Fundamental `2`-chain `[g | g] + [1 | 1]` (`g = Multiplicative.ofAdd 1`) at `X : A`. -/
def categoryChainComplexSingleObjZModTwoFundChain (X : A) :
    X ⟶ (categoryChainComplex ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X)).X 2 :=
  ι₂ZModTwo X (.ofAdd 1) (.ofAdd 1) + ι₂ZModTwo X 1 1

/-- The boundary of `categoryChainComplexSingleObjZModTwoFundChain X` is `2 • [g]`. -/
@[reassoc] lemma categoryChainComplexSingleObjZModTwoFundChain_d (X : A) :
    categoryChainComplexSingleObjZModTwoFundChain X ≫
      (categoryChainComplex ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X)).d 2 1 =
      ((2 : ℤ) • 𝟙 X) ≫ ιCategoryChainComplex₁
        ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X)
        (Quiver.SingleObj.toHom (Multiplicative.ofAdd (1 : ZMod 2))) := by
  dsimp [categoryChainComplexSingleObjZModTwoFundChain]
  rw [Preadditive.add_comp, ι₂ZModTwo_d, ι₂ZModTwo_d,
    (by decide : Multiplicative.ofAdd (1 : ZMod 2) * .ofAdd 1 = 1), mul_one, two_zsmul,
    Preadditive.add_comp, id_comp]; abel

private lemma d_two_one_π₁_gen (X : A) :
    (categoryChainComplex (zmodTwoConst X)).d 2 1 ≫ π₁ZModTwo X (.ofAdd 1) =
      categoryChainComplexπ₂SingleObjZModTwo X (.ofAdd 1) (.ofAdd 1) ≫ ((2 : ℤ) • 𝟙 X) := by
  refine zmodTwo_X₂_hom_ext fun a b ↦ ?_; rw [ι₂ZModTwo_d_assoc]
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    simp [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.comp_add, ι₁_π₁ZModTwo,
      (by decide : Multiplicative.ofAdd (1 : ZMod 2) * .ofAdd 1 = 1),
      (by decide : (1 : Multiplicative (ZMod 2)) ≠ .ofAdd 1), two_zsmul]

private lemma d_three_two_π₂_gen_gen (X : A) : (categoryChainComplex (zmodTwoConst X)).d 3 2 ≫
    categoryChainComplexπ₂SingleObjZModTwo X (.ofAdd 1) (.ofAdd 1) = 0 := by
  refine zmodTwo_X₃_hom_ext fun a b c ↦ ?_; rw [comp_zero, ι₃ZModTwo_d_assoc]
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases c.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    simp [Preadditive.sub_comp, Preadditive.add_comp,
      (by decide : Multiplicative.ofAdd (1 : ZMod 2) * .ofAdd 1 = 1),
      (by decide : (1 : Multiplicative (ZMod 2)) ≠ .ofAdd 1)]

private def zmodTwoHomotopy₂ (X : A) :
    (categoryChainComplex (zmodTwoConst X)).X 2 ⟶ (categoryChainComplex (zmodTwoConst X)).X 3 :=
  categoryChainComplexπ₂SingleObjZModTwo X 1 (.ofAdd 1) ≫ ι₃ZModTwo X 1 1 (.ofAdd 1) -
    categoryChainComplexπ₂SingleObjZModTwo X (.ofAdd 1) 1 ≫ ι₃ZModTwo X (.ofAdd 1) 1 1

private lemma zmodTwo_id_X₂_eq (X : A) : 𝟙 ((categoryChainComplex (zmodTwoConst X)).X 2) =
    categoryChainComplexπ₂SingleObjZModTwo X (.ofAdd 1) (.ofAdd 1) ≫
        categoryChainComplexSingleObjZModTwoFundChain X +
      zmodTwoHomotopy₂ X ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 +
      (categoryChainComplex (zmodTwoConst X)).d 2 1 ≫ π₁ZModTwo X 1 ≫ ι₂ZModTwo X 1 1 := by
  refine zmodTwo_X₂_hom_ext fun a b ↦ ?_
  dsimp only [categoryChainComplexSingleObjZModTwoFundChain, zmodTwoHomotopy₂]
  rcases a.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    rcases b.eq_one_or_eq_ofAdd_one with rfl | rfl <;>
    simp only [comp_id, Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sub,
      Preadditive.sub_comp, assoc, ι₂_π₂ZModTwo_assoc, ι₃ZModTwo_d, ι₂ZModTwo_d_assoc,
      ι₁_π₁ZModTwo_assoc, mul_one, one_mul,
      (by decide : Multiplicative.ofAdd (1 : ZMod 2) * .ofAdd 1 = 1),
      (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1),
      (by decide : (1 : Multiplicative (ZMod 2)) ≠ .ofAdd 1),
      and_self, and_false, false_and, ↓reduceIte, id_comp, zero_comp] <;> abel

private lemma zmodTwo_cycle_sub_boundary {X T : A}
    (z : T ⟶ (categoryChainComplex (zmodTwoConst X)).X 2)
    (hz : z ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 = 0) :
    z - (z ≫ categoryChainComplexπ₂SingleObjZModTwo X (.ofAdd 1) (.ofAdd 1)) ≫
        categoryChainComplexSingleObjZModTwoFundChain X =
      (z ≫ zmodTwoHomotopy₂ X) ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 := by
  have h := congrArg (z ≫ ·) (zmodTwo_id_X₂_eq X)
  rw [comp_id, Preadditive.comp_add, Preadditive.comp_add, ← assoc, ← assoc, ← assoc, hz,
    zero_comp, add_zero] at h; exact sub_eq_of_eq_add' h

section Homology

variable [CategoryWithHomology A]

/-- Morphism `H₂(SingleObj (Multiplicative (ZMod 2)), X) ⟶ X` from the `(g, g)`-coordinate. -/
def categoryHomologyTwoSingleObjZModTwoToCoeff (X : A) :
    categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2 ⟶ X :=
  (categoryChainComplex (zmodTwoConst X)).homologyι 2 ≫
    (categoryChainComplex (zmodTwoConst X)).descOpcycles
      (categoryChainComplexπ₂SingleObjZModTwo X (.ofAdd 1) (.ofAdd 1)) 3 (by simp)
      (d_three_two_π₂_gen_gen X)

@[reassoc (attr := simp)] lemma homologyπ_categoryHomologyTwoSingleObjZModTwoToCoeff (X : A) :
    (categoryChainComplex ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X)).homologyπ 2
        ≫ categoryHomologyTwoSingleObjZModTwoToCoeff X = (categoryChainComplex _).iCycles 2 ≫
      categoryChainComplexπ₂SingleObjZModTwo X (.ofAdd 1) (.ofAdd 1) := by
  dsimp only [categoryHomologyTwoSingleObjZModTwoToCoeff]
  rw [← assoc, HomologicalComplex.homology_π_ι, assoc, HomologicalComplex.p_descOpcycles]

@[reassoc]
lemma categoryHomologyMap_const_categoryHomologyTwoSingleObjZModTwoToCoeff {X Y : A} (f : X ⟶ Y) :
    categoryHomologyMap ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).map f) 2 ≫
        categoryHomologyTwoSingleObjZModTwoToCoeff Y =
      categoryHomologyTwoSingleObjZModTwoToCoeff X ≫ f := by
  rw [← cancel_epi ((categoryChainComplex (zmodTwoConst X)).homologyπ 2)]
  simp [categoryHomologyMap, categoryChainComplexMap_const_π₂SingleObjZModTwo]

private def zmodTwoHomologyTwoToKernel (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    categoryHomology (zmodTwoConst X) 2 ⟶ kernel ((2 : ℤ) • 𝟙 X) :=
  kernel.lift ((2 : ℤ) • 𝟙 X) (categoryHomologyTwoSingleObjZModTwoToCoeff X) (by
    rw [← cancel_epi ((categoryChainComplex (zmodTwoConst X)).homologyπ 2),
      homologyπ_categoryHomologyTwoSingleObjZModTwoToCoeff_assoc, ← d_two_one_π₁_gen, ← assoc,
      HomologicalComplex.iCycles_d, zero_comp, comp_zero])

private def zmodTwoKernelToCycles (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    kernel ((2 : ℤ) • 𝟙 X) ⟶ (categoryChainComplex (zmodTwoConst X)).cycles 2 :=
  (categoryChainComplex (zmodTwoConst X)).liftCycles
    (kernel.ι ((2 : ℤ) • 𝟙 X) ≫ categoryChainComplexSingleObjZModTwoFundChain X) 1 (by simp)
    (by rw [assoc, categoryChainComplexSingleObjZModTwoFundChain_d, kernel.condition_assoc,
      zero_comp])

private lemma zmodTwo_cycles_id_sub_eq (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    𝟙 ((categoryChainComplex (zmodTwoConst X)).cycles 2) -
        ((categoryChainComplex (zmodTwoConst X)).homologyπ 2 ≫ zmodTwoHomologyTwoToKernel X) ≫
          zmodTwoKernelToCycles X =
      (categoryChainComplex (zmodTwoConst X)).iCycles 2 ≫ zmodTwoHomotopy₂ X ≫
        (categoryChainComplex (zmodTwoConst X)).toCycles 3 2 := by
  rw [← cancel_mono ((categoryChainComplex (zmodTwoConst X)).iCycles 2)]
  simpa [zmodTwoKernelToCycles, zmodTwoHomologyTwoToKernel] using
    zmodTwo_cycle_sub_boundary _ ((categoryChainComplex (zmodTwoConst X)).iCycles_d 2 1)

/-- Canonical isomorphism `H₂(SingleObj (Multiplicative (ZMod 2)), X) ≅ kernel ((2 : ℤ) • 𝟙 X)`. -/
def categoryHomologyTwoSingleObjZModTwoIsoKernel (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2 ≅
      kernel ((2 : ℤ) • 𝟙 X) where
  hom := zmodTwoHomologyTwoToKernel X
  inv := zmodTwoKernelToCycles X ≫ (categoryChainComplex (zmodTwoConst X)).homologyπ 2
  hom_inv_id := by
    rw [← cancel_epi ((categoryChainComplex (zmodTwoConst X)).homologyπ 2), comp_id]
    exact (sub_eq_zero.mp <| by
      simpa only [Preadditive.sub_comp, id_comp, assoc, HomologicalComplex.toCycles_comp_homologyπ,
        comp_zero] using congrArg (· ≫ (categoryChainComplex (zmodTwoConst X)).homologyπ 2)
        (zmodTwo_cycles_id_sub_eq X)).symm
  inv_hom_id := by
    rw [← cancel_mono (kernel.ι ((2 : ℤ) • 𝟙 X))]
    simp [zmodTwoHomologyTwoToKernel, zmodTwoKernelToCycles,
      categoryChainComplexSingleObjZModTwoFundChain,
      (by decide : (1 : Multiplicative (ZMod 2)) ≠ .ofAdd 1)]

@[reassoc (attr := simp)] lemma categoryHomologyTwoSingleObjZModTwoIsoKernel_hom_ι (X : A)
    [HasKernel ((2 : ℤ) • 𝟙 X)] :
    (categoryHomologyTwoSingleObjZModTwoIsoKernel X).hom ≫ kernel.ι ((2 : ℤ) • 𝟙 X) =
      categoryHomologyTwoSingleObjZModTwoToCoeff X := kernel.lift_ι _ _ _

@[reassoc (attr := simp)] lemma categoryHomologyTwoSingleObjZModTwoIsoKernel_inv_toCoeff (X : A)
    [HasKernel ((2 : ℤ) • 𝟙 X)] : (categoryHomologyTwoSingleObjZModTwoIsoKernel X).inv ≫
      categoryHomologyTwoSingleObjZModTwoToCoeff X = kernel.ι ((2 : ℤ) • 𝟙 X) := by
  rw [← categoryHomologyTwoSingleObjZModTwoIsoKernel_hom_ι, Iso.inv_hom_id_assoc]

lemma categoryHomologyTwoSingleObjZModTwoIsoKernel_inv (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    (categoryHomologyTwoSingleObjZModTwoIsoKernel X).inv =
      (categoryChainComplex _).liftCycles
        (kernel.ι ((2 : ℤ) • 𝟙 X) ≫ categoryChainComplexSingleObjZModTwoFundChain X) 1 (by simp)
        (by rw [assoc, categoryChainComplexSingleObjZModTwoFundChain_d, kernel.condition_assoc,
          zero_comp]) ≫ (categoryChainComplex _).homologyπ 2 := (rfl)

@[reassoc] lemma categoryHomologyMap_const_categoryHomologyTwoSingleObjZModTwoIsoKernel_hom
    {X Y : A} (f : X ⟶ Y) [HasKernel ((2 : ℤ) • 𝟙 X)] [HasKernel ((2 : ℤ) • 𝟙 Y)] :
    categoryHomologyMap ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).map f) 2 ≫
        (categoryHomologyTwoSingleObjZModTwoIsoKernel Y).hom =
      (categoryHomologyTwoSingleObjZModTwoIsoKernel X).hom ≫
        kernel.map ((2 : ℤ) • 𝟙 X) ((2 : ℤ) • 𝟙 Y) f f (by simp) := by
  rw [← cancel_mono (kernel.ι ((2 : ℤ) • 𝟙 Y))]
  simp [categoryHomologyMap_const_categoryHomologyTwoSingleObjZModTwoToCoeff]

/-- Whenever `(2 : ℤ) • 𝟙 X` is monic in `A`, `H₂(SingleObj (Multiplicative (ZMod 2)), X) = 0`. -/
lemma isZero_categoryHomology_two_singleObj_zmod_two_of_mono (X : A) [Mono ((2 : ℤ) • 𝟙 X)] :
    IsZero (categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2) := by
  have : HasZeroObject A := Preadditive.hasZeroObject_of_hasCoproduct.{0} A
  have : HasKernel ((2 : ℤ) • 𝟙 X) := HasLimit.mk ⟨_, kernel.isLimitConeZeroCone _⟩
  exact (isZero_kernel_of_mono ((2 : ℤ) • 𝟙 X)).of_iso
    (categoryHomologyTwoSingleObjZModTwoIsoKernel X)

/-- When `(2 : ℤ) • 𝟙 X = 0`, `H₂(SingleObj (Multiplicative (ZMod 2)), X) ≅ X` via `[g|g]+[1|1]`. -/
def categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero (X : A) (hX : (2 : ℤ) • 𝟙 X = 0) :
    categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2 ≅ X :=
  have : HasKernel ((2 : ℤ) • 𝟙 X) := hX ▸ inferInstance
  categoryHomologyTwoSingleObjZModTwoIsoKernel X ≪≫ kernelIsoOfEq hX ≪≫ kernelZeroIsoSource

@[simp] lemma categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero_hom (X : A)
    (hX : (2 : ℤ) • 𝟙 X = 0) : (categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero X hX).hom =
      categoryHomologyTwoSingleObjZModTwoToCoeff X := by
  have : HasKernel ((2 : ℤ) • 𝟙 X) := hX ▸ inferInstance
  simp [categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero]

lemma categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero_inv (X : A) (hX : (2 : ℤ) • 𝟙 X = 0) :
    (categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero X hX).inv =
      (categoryChainComplex _).liftCycles (categoryChainComplexSingleObjZModTwoFundChain X) 1
        (by simp) (by rw [categoryChainComplexSingleObjZModTwoFundChain_d, hX, zero_comp]) ≫
          (categoryChainComplex _).homologyπ 2 := by
  rw [← cancel_mono (categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero X hX).hom,
    Iso.inv_hom_id]
  simp [categoryChainComplexSingleObjZModTwoFundChain,
    (by decide : (1 : Multiplicative (ZMod 2)) ≠ .ofAdd 1)]

@[reassoc]
lemma categoryHomologyMap_const_categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero_hom
    {X Y : A} (f : X ⟶ Y) (hX : (2 : ℤ) • 𝟙 X = 0) (hY : (2 : ℤ) • 𝟙 Y = 0) :
    categoryHomologyMap ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).map f) 2 ≫
        (categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero Y hY).hom =
      (categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero X hX).hom ≫ f := by
  simp [categoryHomologyMap_const_categoryHomologyTwoSingleObjZModTwoToCoeff]

end Homology

/-- For an `R`-module `V` with `∀ v : V, v + v = 0 → v = 0`,
`H₂(SingleObj (Multiplicative (ZMod 2)), ModuleCat.of R V) = 0`. -/
lemma isZero_categoryHomology_two_singleObj_zmod_two_moduleCat_of_add_self_eq_zero {R : Type u}
    [Ring R] {V : Type w} [AddCommGroup V] [Module R V] (hV : ∀ v : V, v + v = 0 → v = 0) :
    IsZero (categoryHomology
      ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of R V)) 2) := by
  have : Mono ((2 : ℤ) • 𝟙 (ModuleCat.of R V)) := by
    rw [ModuleCat.mono_iff_injective]; intro x y hxy
    have h0 : ((2 : ℤ) • 𝟙 (ModuleCat.of R V)) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    rw [two_zsmul] at h0; exact sub_eq_zero.mp (hV (x - y) h0)
  exact isZero_categoryHomology_two_singleObj_zmod_two_of_mono (ModuleCat.of R V)

/-- With integral coefficients `ℤ`, `H₂(SingleObj (Multiplicative (ZMod 2)), ℤ) = 0`, in contrast
with group cohomology `H²(ℤ/2ℤ; ℤ) ≅ ℤ/2ℤ`. -/
lemma isZero_categoryHomology_two_singleObj_zmod_two_int : IsZero (categoryHomology
    ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of ℤ ℤ)) 2) :=
  isZero_categoryHomology_two_singleObj_zmod_two_moduleCat_of_add_self_eq_zero fun _ hv ↦ by omega

private lemma two_zsmul_id_modTwo : (2 : ℤ) • 𝟙 (ModuleCat.of ℤ (ZMod 2)) = 0 := by
  rw [two_zsmul]; ext x; simpa using (by decide : ∀ y : ZMod 2, y + y = 0) x

/-- Canonical isomorphism `H₂(SingleObj (Multiplicative (ZMod 2)), ℤ/2ℤ) ≅ ℤ/2ℤ`. -/
def categoryHomologyTwoSingleObjZModTwoModTwoIso : categoryHomology
    ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of ℤ (ZMod 2))) 2 ≅
      ModuleCat.of ℤ (ZMod 2) :=
  categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero _ two_zsmul_id_modTwo

@[simp] lemma categoryHomologyTwoSingleObjZModTwoModTwoIso_hom :
    categoryHomologyTwoSingleObjZModTwoModTwoIso.hom =
      categoryHomologyTwoSingleObjZModTwoToCoeff (ModuleCat.of ℤ (ZMod 2)) := by
  simp [categoryHomologyTwoSingleObjZModTwoModTwoIso]

lemma categoryHomologyTwoSingleObjZModTwoModTwoIso_inv :
    categoryHomologyTwoSingleObjZModTwoModTwoIso.inv = (categoryChainComplex _).liftCycles
      (categoryChainComplexSingleObjZModTwoFundChain (ModuleCat.of ℤ (ZMod 2))) 1 (by simp)
      (by rw [categoryChainComplexSingleObjZModTwoFundChain_d, two_zsmul_id_modTwo, zero_comp]) ≫
        (categoryChainComplex _).homologyπ 2 :=
  categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero_inv _ two_zsmul_id_modTwo

/-- `H₂(SingleObj (Multiplicative (ZMod 2)), ℤ/2ℤ)` is nontrivial. -/
lemma not_isZero_categoryHomology_two_singleObj_zmod_two_mod_two : ¬ IsZero (categoryHomology
    ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of ℤ (ZMod 2))) 2) :=
  fun h ↦ absurd (ConcreteCategory.congr_hom
    ((h.of_iso categoryHomologyTwoSingleObjZModTwoModTwoIso.symm).eq_of_tgt (𝟙 _) 0) (1 : ZMod 2))
    (by decide)

end TauCeti
