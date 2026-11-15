/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Zero
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Category homology of a single-object category

For a monoid `G`, `SingleObj G` has unique object `SingleObj.star G` and endomorphisms `G` with
`f ≫ g = g * f` (`CategoryTheory.SingleObj.comp_as_mul`). This file records the low-degree
differentials (`TauCeti.ιCategoryChainComplex₁_d_singleObj`,
`TauCeti.ιCategoryChainComplex₂_d_singleObj`, `TauCeti.ιCategoryChainComplex_mk₃_d_singleObj`,
`TauCeti.categoryChainComplex_const_d_one_zero_singleObj`) and coinvariant `H₀` property
(`TauCeti.epi_ιCategoryHomology₀_singleObj`, `TauCeti.descCategoryHomology₀SingleObj`) for
`M : SingleObj G ⥤ A`, and computes `H₂` of `SingleObj (Multiplicative (ZMod 2))` at `X : A`:
* `TauCeti.categoryHomologyTwoSingleObjZModTwoIsoKernel`:
  `H₂(SingleObj (Multiplicative (ZMod 2)), X) ≅ kernel ((2 : ℤ) • 𝟙 X)`;
* mono `(2 : ℤ) • 𝟙 X`: `H₂ = 0` (`TauCeti.isZero_categoryHomology_two_singleObj_zmod_two`,
  `TauCeti.isZero_categoryHomology_two_singleObj_zmod_two_moduleCat`,
  `TauCeti.isZero_categoryHomology_two_singleObj_zmod_two_int`), vs. `H²(ℤ/2ℤ; ℤ) ≅ ℤ/2ℤ`;
* `(2 : ℤ) • 𝟙 X = 0`: `H₂ ≅ X` (`TauCeti.categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero`,
  `TauCeti.categoryHomologyTwoSingleObjZModTwoModTwoIso`).
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
          (Quiver.SingleObj.toHom h)) ≫ (categoryChainComplex M).d 3 2 =
      M.map (Quiver.SingleObj.toHom f) ≫
          ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom g) (Quiver.SingleObj.toHom h) -
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom (g * f)) (Quiver.SingleObj.toHom h) +
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom (h * g)) -
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom g) := by
  let f' := Quiver.SingleObj.toHom f; let g' := Quiver.SingleObj.toHom g
  let h' := Quiver.SingleObj.toHom h
  have h0 : ιCategoryChainComplex M ((nerve (SingleObj G)).δ 0 (.mk₃ f' g' h')) =
      ιCategoryChainComplex₂ M g' h' :=
    (ιCategoryChainComplex_congr M (nerve.δ₀_mk₃_eq f' g' h') rfl).trans (id_comp _)
  have h1 : (ιCategoryChainComplex M ((nerve (SingleObj G)).δ 1 (.mk₃ f' g' h')) :
      M.obj (SingleObj.star G) ⟶ (categoryChainComplex M).X 2) =
      ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom (g * f)) h' :=
    (ιCategoryChainComplex_congr M (nerve.δ₁_mk₃_eq f' g' h') rfl).trans (id_comp _)
  have h2 : (ιCategoryChainComplex M ((nerve (SingleObj G)).δ 2 (.mk₃ f' g' h')) :
      M.obj (SingleObj.star G) ⟶ (categoryChainComplex M).X 2) =
      ιCategoryChainComplex₂ M f' (Quiver.SingleObj.toHom (h * g)) :=
    (ιCategoryChainComplex_congr M (nerve.δ₂_mk₃_eq f' g' h') rfl).trans (id_comp _)
  have h3 : (ιCategoryChainComplex M ((nerve (SingleObj G)).δ 3 (.mk₃ f' g' h')) :
      M.obj (SingleObj.star G) ⟶ (categoryChainComplex M).X 2) =
      ιCategoryChainComplex₂ M f' g' :=
    (ιCategoryChainComplex_congr M (nerve.δ₃_mk₃_eq f' g' h') rfl).trans (id_comp _)
  calc ιCategoryChainComplex M (.mk₃ f' g' h') ≫ (categoryChainComplex M).d 3 2
    _ = _ := ιCategoryChainComplex_d M (.mk₃ f' g' h')
    _ = M.map f' ≫ ιCategoryChainComplex₂ M g' h' +
          ((-ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom (g * f)) h' +
            ιCategoryChainComplex₂ M f' (Quiver.SingleObj.toHom (h * g))) +
            -ιCategoryChainComplex₂ M f' g') :=
        congrArg₂ (· + ·) (congrArg (M.map f' ≫ ·) h0) ((Fin.sum_univ_three _).trans
          (congrArg₂ (· + ·)
            (congrArg₂ (· + ·) ((neg_one_zsmul _).trans (congrArg Neg.neg h1))
              ((one_zsmul _).trans h2))
            ((neg_one_zsmul _).trans (congrArg Neg.neg h3))))
    _ = _ := by dsimp only [f', g', h']; abel

/-- For constant coefficients `X` on `SingleObj G`, the degree-`1` differential vanishes. -/
@[simp]
lemma categoryChainComplex_const_d_one_zero_singleObj (G : Type u) [Monoid G] (X : A) :
    (categoryChainComplex ((Functor.const (SingleObj G)).obj X)).d 1 0 = 0 := by
  ext σ; obtain ⟨⟨⟩, ⟨⟩, g, rfl⟩ := ComposableArrows.mk₁_surjective σ; simp

section DegreeZero

variable [CategoryWithHomology A]

/-- On `SingleObj G`, the canonical map `M.obj (SingleObj.star G) ⟶ categoryHomology M 0` is an
epimorphism. -/
instance epi_ιCategoryHomology₀_singleObj (M : SingleObj G ⥤ A) :
    Epi (ιCategoryHomology₀ M (SingleObj.star G)) where
  left_cancellation _ _ h := categoryHomology₀_hom_ext fun ⟨⟩ ↦ h

/-- Universal coinvariant morphism `categoryHomology M 0 ⟶ T` induced by a `G`-invariant morphism
`u : M.obj (SingleObj.star G) ⟶ T`. -/
def descCategoryHomology₀SingleObj (M : SingleObj G ⥤ A) {T : A}
    (u : M.obj (SingleObj.star G) ⟶ T)
    (hu : ∀ g : SingleObj.star G ⟶ SingleObj.star G, M.map g ≫ u = u) :
    categoryHomology M 0 ⟶ T :=
  (isColimitCategoryHomology₀Cocone M).desc
    { pt := T
      ι := { app := fun _ ↦ u
             naturality := fun _ _ g ↦ (hu g).trans ((comp_id u).symm.trans (by simp)) } }

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

private abbrev zmodTwoHom (a : ZModTwoGrp) :
    SingleObj.star ZModTwoGrp ⟶ SingleObj.star ZModTwoGrp := Quiver.SingleObj.toHom a

private def zmodTwoGen : ZModTwoGrp := Multiplicative.ofAdd (1 : ZMod 2)

private lemma zmodTwo_cases (a : ZModTwoGrp) : a = 1 ∨ a = zmodTwoGen := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (Multiplicative.toAdd a) with h | h
  · exact .inl (Multiplicative.toAdd.injective h)
  · exact .inr (Multiplicative.toAdd.injective h)

private lemma zmodTwoGen_ne_one : zmodTwoGen ≠ 1 := by decide

private lemma zmodTwoGen_mul_self : zmodTwoGen * zmodTwoGen = 1 := by
  dsimp only [zmodTwoGen]; rw [← ofAdd_add]; decide

section Chains

variable {A : Type u'} [Category.{v'} A] [HasCoproducts.{0} A] [Preadditive A]

private abbrev zmodTwoConst (X : A) : SingleObj ZModTwoGrp ⥤ A := (Functor.const _).obj X

private def ι₁ZModTwo (X : A) (a : ZModTwoGrp) : X ⟶ (categoryChainComplex (zmodTwoConst X)).X 1 :=
  ιCategoryChainComplex₁ (zmodTwoConst X) (zmodTwoHom a)

private def ι₂ZModTwo (X : A) (a b : ZModTwoGrp) :
    X ⟶ (categoryChainComplex (zmodTwoConst X)).X 2 :=
  ιCategoryChainComplex₂ (zmodTwoConst X) (zmodTwoHom a) (zmodTwoHom b)

private def ι₃ZModTwo (X : A) (a b c : ZModTwoGrp) :
    X ⟶ (categoryChainComplex (zmodTwoConst X)).X 3 :=
  ιCategoryChainComplex (zmodTwoConst X) (.mk₃ (zmodTwoHom a) (zmodTwoHom b) (zmodTwoHom c))

private lemma zmodTwo_X₂_hom_ext {X Y : A}
    {φ ψ : (categoryChainComplex (zmodTwoConst X)).X 2 ⟶ Y}
    (h : ∀ a b : ZModTwoGrp, ι₂ZModTwo X a b ≫ φ = ι₂ZModTwo X a b ≫ ψ) : φ = ψ := by
  ext σ; obtain ⟨⟨⟩, ⟨⟩, ⟨⟩, f, g, rfl⟩ := ComposableArrows.mk₂_surjective σ
  exact h (Quiver.SingleObj.toHom.symm f) (Quiver.SingleObj.toHom.symm g)

private lemma zmodTwo_X₃_hom_ext {X Y : A}
    {φ ψ : (categoryChainComplex (zmodTwoConst X)).X 3 ⟶ Y}
    (h : ∀ a b c : ZModTwoGrp, ι₃ZModTwo X a b c ≫ φ = ι₃ZModTwo X a b c ≫ ψ) : φ = ψ := by
  ext σ; obtain ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, f, g, k, rfl⟩ := ComposableArrows.mk₃_surjective σ
  exact h (Quiver.SingleObj.toHom.symm f) (Quiver.SingleObj.toHom.symm g)
    (Quiver.SingleObj.toHom.symm k)

private def π₁ZModTwo (X : A) (a : ZModTwoGrp) :
    (categoryChainComplex (zmodTwoConst X)).X 1 ⟶ X :=
  descCategoryChainComplex (zmodTwoConst X) fun τ ↦
    if Quiver.SingleObj.toHom.symm (τ.map' 0 1) = a then 𝟙 X else 0

@[reassoc]
private lemma ι₁_π₁ZModTwo (X : A) (a b : ZModTwoGrp) :
    ι₁ZModTwo X a ≫ π₁ZModTwo X b = if a = b then 𝟙 X else 0 :=
  ιCategoryChainComplex_desc (zmodTwoConst X) _ (.mk₁ (zmodTwoHom a))

private def π₂ZModTwo (X : A) (a b : ZModTwoGrp) :
    (categoryChainComplex (zmodTwoConst X)).X 2 ⟶ X :=
  descCategoryChainComplex (zmodTwoConst X) fun σ ↦
    if Quiver.SingleObj.toHom.symm (σ.map' 0 1) = a ∧
        Quiver.SingleObj.toHom.symm (σ.map' 1 2) = b then 𝟙 X else 0

@[reassoc]
private lemma ι₂_π₂ZModTwo (X : A) (a b c d : ZModTwoGrp) :
    ι₂ZModTwo X a b ≫ π₂ZModTwo X c d = if a = c ∧ b = d then 𝟙 X else 0 :=
  ιCategoryChainComplex_desc _ _ (.mk₂ (zmodTwoHom a) (zmodTwoHom b))

@[reassoc]
private lemma ι₂ZModTwo_d (X : A) (a b : ZModTwoGrp) :
    ι₂ZModTwo X a b ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 =
      ι₁ZModTwo X b - ι₁ZModTwo X (b * a) + ι₁ZModTwo X a := by
  rw [ι₂ZModTwo, ιCategoryChainComplex₂_d_singleObj]; simp [ι₁ZModTwo]

@[reassoc]
private lemma ι₃ZModTwo_d (X : A) (a b c : ZModTwoGrp) :
    ι₃ZModTwo X a b c ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 =
      ι₂ZModTwo X b c - ι₂ZModTwo X (b * a) c + ι₂ZModTwo X a (c * b) - ι₂ZModTwo X a b := by
  simp [ι₃ZModTwo, ι₂ZModTwo, ιCategoryChainComplex_mk₃_d_singleObj]

private def zmodTwoFundChain (X : A) : X ⟶ (categoryChainComplex (zmodTwoConst X)).X 2 :=
  ι₂ZModTwo X zmodTwoGen zmodTwoGen + ι₂ZModTwo X 1 1

private lemma zmodTwoFundChain_d (X : A) :
    zmodTwoFundChain X ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 =
      ((2 : ℤ) • 𝟙 X) ≫ ι₁ZModTwo X zmodTwoGen := by
  rw [zmodTwoFundChain, Preadditive.add_comp, ι₂ZModTwo_d, ι₂ZModTwo_d, zmodTwoGen_mul_self,
    mul_one, two_zsmul, Preadditive.add_comp, id_comp]; abel

private lemma d_two_one_π₁_gen (X : A) :
    (categoryChainComplex (zmodTwoConst X)).d 2 1 ≫ π₁ZModTwo X zmodTwoGen =
      π₂ZModTwo X zmodTwoGen zmodTwoGen ≫ ((2 : ℤ) • 𝟙 X) := by
  refine zmodTwo_X₂_hom_ext fun a b ↦ ?_
  rw [ι₂ZModTwo_d_assoc]
  rcases zmodTwo_cases a with rfl | rfl <;> rcases zmodTwo_cases b with rfl | rfl <;>
    simp [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.comp_add, ι₁_π₁ZModTwo,
      ι₂_π₂ZModTwo, zmodTwoGen_mul_self, zmodTwoGen_ne_one.symm, two_zsmul]

private lemma d_three_two_π₂_gen_gen (X : A) :
    (categoryChainComplex (zmodTwoConst X)).d 3 2 ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen = 0 := by
  refine zmodTwo_X₃_hom_ext fun a b c ↦ ?_
  rw [comp_zero, ι₃ZModTwo_d_assoc]
  rcases zmodTwo_cases a with rfl | rfl <;> rcases zmodTwo_cases b with rfl | rfl <;>
    rcases zmodTwo_cases c with rfl | rfl <;>
    simp [Preadditive.sub_comp, Preadditive.add_comp, ι₂_π₂ZModTwo, zmodTwoGen_mul_self,
      zmodTwoGen_ne_one.symm]

private def zmodTwoHomotopy₂ (X : A) :
    (categoryChainComplex (zmodTwoConst X)).X 2 ⟶ (categoryChainComplex (zmodTwoConst X)).X 3 :=
  π₂ZModTwo X 1 zmodTwoGen ≫ ι₃ZModTwo X 1 1 zmodTwoGen -
    π₂ZModTwo X zmodTwoGen 1 ≫ ι₃ZModTwo X zmodTwoGen 1 1

private lemma zmodTwo_id_X₂_eq (X : A) :
    𝟙 ((categoryChainComplex (zmodTwoConst X)).X 2) =
      π₂ZModTwo X zmodTwoGen zmodTwoGen ≫ zmodTwoFundChain X +
        zmodTwoHomotopy₂ X ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 +
        (categoryChainComplex (zmodTwoConst X)).d 2 1 ≫ π₁ZModTwo X 1 ≫ ι₂ZModTwo X 1 1 := by
  refine zmodTwo_X₂_hom_ext fun a b ↦ ?_
  dsimp only [zmodTwoHomotopy₂, zmodTwoFundChain]
  rcases zmodTwo_cases a with rfl | rfl <;> rcases zmodTwo_cases b with rfl | rfl <;>
    simp only [comp_id, Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sub,
      Preadditive.sub_comp, assoc, ι₂_π₂ZModTwo_assoc, ι₃ZModTwo_d, ι₂ZModTwo_d_assoc,
      ι₁_π₁ZModTwo_assoc, mul_one, one_mul, zmodTwoGen_mul_self, zmodTwoGen_ne_one,
      zmodTwoGen_ne_one.symm, and_self, and_false, false_and, ↓reduceIte, id_comp, zero_comp] <;>
    abel

/-- Any `2`-cycle `z` differs from its `(g, g)`-multiple of `zmodTwoFundChain X` by a boundary. -/
private lemma zmodTwo_cycle_sub_boundary {X T : A}
    (z : T ⟶ (categoryChainComplex (zmodTwoConst X)).X 2)
    (hz : z ≫ (categoryChainComplex (zmodTwoConst X)).d 2 1 = 0) :
    z - (z ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen) ≫ zmodTwoFundChain X =
      (z ≫ zmodTwoHomotopy₂ X) ≫ (categoryChainComplex (zmodTwoConst X)).d 3 2 := by
  have h := congrArg (z ≫ ·) (zmodTwo_id_X₂_eq X)
  rw [comp_id, Preadditive.comp_add, Preadditive.comp_add, ← assoc, ← assoc, ← assoc, hz,
    zero_comp, add_zero] at h
  exact sub_eq_of_eq_add' h

section Homology

variable [CategoryWithHomology A]

private def zmodTwoHomologyTwoToCoeff (X : A) : categoryHomology (zmodTwoConst X) 2 ⟶ X :=
  (categoryChainComplex (zmodTwoConst X)).homologyι 2 ≫
    (categoryChainComplex (zmodTwoConst X)).descOpcycles (π₂ZModTwo X zmodTwoGen zmodTwoGen) 3
      ((ComplexShape.down ℕ).prev_eq' (rfl : (ComplexShape.down ℕ).Rel 3 2))
      (d_three_two_π₂_gen_gen X)

@[reassoc]
private lemma homologyπ_zmodTwoHomologyTwoToCoeff (X : A) :
    (categoryChainComplex (zmodTwoConst X)).homologyπ 2 ≫ zmodTwoHomologyTwoToCoeff X =
      (categoryChainComplex (zmodTwoConst X)).iCycles 2 ≫ π₂ZModTwo X zmodTwoGen zmodTwoGen := by
  dsimp only [zmodTwoHomologyTwoToCoeff]
  rw [← assoc, HomologicalComplex.homology_π_ι, assoc, HomologicalComplex.p_descOpcycles]

private def zmodTwoHomologyTwoToKernel (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    categoryHomology (zmodTwoConst X) 2 ⟶ kernel ((2 : ℤ) • 𝟙 X) :=
  kernel.lift ((2 : ℤ) • 𝟙 X) (zmodTwoHomologyTwoToCoeff X) (by
    rw [← cancel_epi ((categoryChainComplex (zmodTwoConst X)).homologyπ 2),
      homologyπ_zmodTwoHomologyTwoToCoeff_assoc, ← d_two_one_π₁_gen, ← assoc,
      HomologicalComplex.iCycles_d, zero_comp, comp_zero])

private def zmodTwoKernelToCycles (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    kernel ((2 : ℤ) • 𝟙 X) ⟶ (categoryChainComplex (zmodTwoConst X)).cycles 2 :=
  (categoryChainComplex (zmodTwoConst X)).liftCycles
    (kernel.ι ((2 : ℤ) • 𝟙 X) ≫ zmodTwoFundChain X) 1
    ((ComplexShape.down ℕ).next_eq' (rfl : (ComplexShape.down ℕ).Rel 2 1))
    (by rw [assoc, zmodTwoFundChain_d, kernel.condition_assoc, zero_comp])

private def zmodTwoKernelToHomologyTwo (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    kernel ((2 : ℤ) • 𝟙 X) ⟶ categoryHomology (zmodTwoConst X) 2 :=
  zmodTwoKernelToCycles X ≫ (categoryChainComplex (zmodTwoConst X)).homologyπ 2

private lemma zmodTwo_cycles_id_sub_eq (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    𝟙 ((categoryChainComplex (zmodTwoConst X)).cycles 2) -
        ((categoryChainComplex (zmodTwoConst X)).homologyπ 2 ≫ zmodTwoHomologyTwoToKernel X) ≫
          zmodTwoKernelToCycles X =
      (categoryChainComplex (zmodTwoConst X)).iCycles 2 ≫ zmodTwoHomotopy₂ X ≫
        (categoryChainComplex (zmodTwoConst X)).toCycles 3 2 := by
  rw [← cancel_mono ((categoryChainComplex (zmodTwoConst X)).iCycles 2), Preadditive.sub_comp,
    id_comp, assoc, assoc, zmodTwoKernelToCycles, HomologicalComplex.liftCycles_i,
    ← assoc (zmodTwoHomologyTwoToKernel X), zmodTwoHomologyTwoToKernel, kernel.lift_ι,
    ← assoc, homologyπ_zmodTwoHomologyTwoToCoeff, assoc, assoc, assoc,
    HomologicalComplex.toCycles_i]
  simpa only [assoc] using
    zmodTwo_cycle_sub_boundary _ ((categoryChainComplex (zmodTwoConst X)).iCycles_d 2 1)

/-- The degree-`2` category homology of `SingleObj (Multiplicative (ZMod 2))` with constant
coefficients `X` is canonically isomorphic to the `2`-torsion `kernel ((2 : ℤ) • 𝟙 X)`, via the
`(g, g)`-coordinate on `2`-cycles and the fundamental `2`-cycle `[g | g] + [1 | 1]`. -/
def categoryHomologyTwoSingleObjZModTwoIsoKernel (X : A) [HasKernel ((2 : ℤ) • 𝟙 X)] :
    categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2 ≅
      kernel ((2 : ℤ) • 𝟙 X) where
  hom := zmodTwoHomologyTwoToKernel X
  inv := zmodTwoKernelToHomologyTwo X
  hom_inv_id := by
    rw [← cancel_epi ((categoryChainComplex (zmodTwoConst X)).homologyπ 2), comp_id,
      zmodTwoKernelToHomologyTwo]
    have h := congrArg (· ≫ (categoryChainComplex (zmodTwoConst X)).homologyπ 2)
      (zmodTwo_cycles_id_sub_eq X)
    simp only [Preadditive.sub_comp, id_comp, assoc, HomologicalComplex.toCycles_comp_homologyπ,
      comp_zero, sub_eq_zero] at h
    exact h.symm
  inv_hom_id := by
    rw [← cancel_mono (kernel.ι ((2 : ℤ) • 𝟙 X)), id_comp, assoc, zmodTwoHomologyTwoToKernel,
      kernel.lift_ι, zmodTwoKernelToHomologyTwo, assoc, homologyπ_zmodTwoHomologyTwoToCoeff,
      ← assoc, zmodTwoKernelToCycles, HomologicalComplex.liftCycles_i, assoc]
    simp [zmodTwoFundChain, Preadditive.add_comp, ι₂_π₂ZModTwo, zmodTwoGen_ne_one.symm]

/-- Whenever `(2 : ℤ) • 𝟙 X : X ⟶ X` is a monomorphism in `A`, the degree-`2` category homology of
`SingleObj (Multiplicative (ZMod 2))` with constant coefficients `X` vanishes. -/
lemma isZero_categoryHomology_two_singleObj_zmod_two (X : A) [Mono ((2 : ℤ) • 𝟙 X)] :
    IsZero (categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2) := by
  have : HasZeroObject A := Preadditive.hasZeroObject_of_hasCoproduct.{0} A
  have : HasKernel ((2 : ℤ) • 𝟙 X) := HasLimit.mk ⟨_, kernel.isLimitConeZeroCone _⟩
  exact (isZero_kernel_of_mono ((2 : ℤ) • 𝟙 X)).of_iso
    (categoryHomologyTwoSingleObjZModTwoIsoKernel X)

/-- Whenever `(2 : ℤ) • 𝟙 X = 0` in `A`, the degree-`2` category homology of
`SingleObj (Multiplicative (ZMod 2))` with constant coefficients `X` is isomorphic to `X`, generated
by the fundamental `2`-cycle `[g | g] + [1 | 1]`. -/
def categoryHomologyTwoSingleObjZModTwoIsoOfTwoSMulEqZero (X : A) (hX : (2 : ℤ) • 𝟙 X = 0) :
    categoryHomology ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj X) 2 ≅ X :=
  have : HasKernel ((2 : ℤ) • 𝟙 X) := hX ▸ inferInstance
  categoryHomologyTwoSingleObjZModTwoIsoKernel X ≪≫ kernelIsoOfEq hX ≪≫ kernelZeroIsoSource

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
    rw [ModuleCat.mono_iff_injective]; intro x y hxy
    have h0 : ((2 : ℤ) • 𝟙 (ModuleCat.of R V)) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    rw [two_zsmul] at h0; exact sub_eq_zero.mp (hV (x - y) h0)
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
    rw [two_zsmul]; ext x; simpa using (by decide : ∀ y : ZMod 2, y + y = 0) x)

/-- The degree-`2` category homology of `SingleObj (Multiplicative (ZMod 2))` with constant
`ℤ/2ℤ`-coefficients is nontrivial. -/
lemma not_isZero_categoryHomology_two_singleObj_zmod_two_mod_two :
    ¬ IsZero (categoryHomology
      ((Functor.const (SingleObj (Multiplicative (ZMod 2)))).obj (ModuleCat.of ℤ (ZMod 2))) 2) :=
  fun h ↦ absurd (ConcreteCategory.congr_hom
    ((h.of_iso categoryHomologyTwoSingleObjZModTwoModTwoIso.symm).eq_of_tgt (𝟙 _) 0) (1 : ZMod 2))
    (by decide)

end ZModTwo

end TauCeti
