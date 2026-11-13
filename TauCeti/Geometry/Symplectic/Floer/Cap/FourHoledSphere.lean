/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.PairOfPants
public import TauCeti.Geometry.Symplectic.Floer.Cap.Sewing

/-!
# Gluing caps along a four-holed sphere

Let `γ₁`, `γ₂`, `γ₃` and `γ₀` be loops in a space `X` based at `x`. Cutting a four-holed sphere
with inputs `γ₁`, `γ₂`, `γ₃` and output `γ₀` along three seams from the output to the inputs gives
a homotopy of loops from `γ₀` to the triple concatenation `(γ₁ ⬝ γ₂) ⬝ γ₃`, whose homotopy class
relative to the boundary is a morphism `W : γ₀ ⟶ (γ₁ ⬝ γ₂) ⬝ γ₃` in the fundamental groupoid of
the loop space `Ω X x`. Raw caps `D₁`, `D₂`, `D₃` of the inputs placed side by side on top of `W`
give a raw cap of `γ₀` (`TauCeti.Floer.RawCap.glue₃`), exactly as raw caps glue along a pair of
pants (`TauCeti.Floer.RawCap.pantsGlue`).

A four-holed sphere degenerates into two pairs of pants in two ways, and the glued cap is the
iterated gluing along the two pieces in either case.

* **Sewing into the first input.** A pair of pants `P : γ₀ ⟶ γ ⬝ γ₃` with a pair of pants
  `P' : γ ⟶ γ₁ ⬝ γ₂` sewn into its first input is the four-holed sphere `P ≫ (P' ⋀ 𝟙)`, and gluing
  along it is gluing along `P'` and then along `P`
  (`TauCeti.Floer.RawCap.pantsGlue_pantsGlue_left`). This is the functoriality of the product of
  path classes (`HSpace.pathHmul_comp`).
* **Sewing into the second input.** A pair of pants `Q : γ₀ ⟶ γ₁ ⬝ γ` with a pair of pants
  `Q' : γ ⟶ γ₂ ⬝ γ₃` sewn into its second input is a homotopy of loops ending at
  `γ₁ ⬝ (γ₂ ⬝ γ₃)`. If it is the four-holed sphere `W` followed by the associator
  `Path.transAssoc` of the loop space, then gluing along `W` is gluing along `Q'` and then along
  `Q` (`TauCeti.Floer.RawCap.glue₃_eq_pantsGlue_pantsGlue_right`). This is the naturality of the
  associator (`Path.pathHmul_pathHmul_comp_transAssoc`), together with the fact that it is constant
  at the constant loops (`Path.transAssoc_refl`).

So the two broken configurations at the ends of a one-parameter family of four-holed spheres glue
the same caps of the inputs to the same cap of the output, provided both represent the homotopy
class of the family. This is the identification of glued caps that
`TauCeti.Floer.productClass_add_eq_add_iff` asks for. On the cap classes of
`TauCeti.Floer.SphericalCapClass`, the class `D₀ -ᵥ glue₃ W D₁ D₂ D₃` of the four-holed sphere `W`
relative to caps of its four boundary loops is the sum of the classes of the two pairs of pants
of either decomposition, whatever cap is chosen at the intermediate loop
(`TauCeti.Floer.SphericalCapClass.vsub_glue₃_eq_productClass_add_productClass_left`,
`TauCeti.Floer.SphericalCapClass.vsub_glue₃_eq_productClass_add_productClass_right`). In
particular the sums of the classes of the two broken configurations agree
(`TauCeti.Floer.SphericalCapClass.productClass_add_productClass_eq_of_comp_transAssoc_eq`): cap
classes add under both degenerations of a four-holed sphere. These are the classes in which the
pairs of pants at the two ends of the associativity family are counted, and their agreement is what
lets the coefficients `e^(-A)` of the two broken products be compared class by class.

These are statements about homotopy classes of loops in a space; no Floer equation, moduli space or
count is involved.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  classes of pairs of pants relative to caps and the associativity of the pair-of-pants product.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. (2) **54**
  (1951), 425–505, on the homotopy associativity of the loop space.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy HSpaces

namespace TauCeti.Floer

section Raw

variable {X : Type*} [TopologicalSpace X] {x : X}

namespace RawCap

variable {γ γ₀ γ₁ γ₂ γ₃ : Ω X x}

/-- **Gluing caps along a four-holed sphere.** For a four-holed sphere `W : γ₀ ⟶ (γ₁ ⬝ γ₂) ⬝ γ₃`,
a homotopy class of homotopies of loops from the output `γ₀` to the triple concatenation of the
inputs, and raw caps `D₁`, `D₂`, `D₃` of the inputs, the raw cap of `γ₀` obtained by placing the
three caps side by side on top of `W`. -/
def glue₃ (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) : RawCap γ₀ :=
  W ≫ HSpace.pathHmul (HSpace.pathHmul D₁ D₂) D₃ ≫
    eqToHom (congrArg FundamentalGroupoid.mk
      ((congrArg (· ⋀ HSpace.e) HSpace.hmul_e_e).trans HSpace.hmul_e_e))

theorem glue₃_def (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂ D₃ =
      W ≫ HSpace.pathHmul (HSpace.pathHmul D₁ D₂) D₃ ≫
        eqToHom (congrArg FundamentalGroupoid.mk
          ((congrArg (· ⋀ HSpace.e) HSpace.hmul_e_e).trans HSpace.hmul_e_e)) :=
  (rfl)

/-- **Sewing a pair of pants into the first input.** Gluing caps along a pair of pants
`P : γ₀ ⟶ γ ⬝ γ₃` whose first input cap is glued along a pair of pants `P' : γ ⟶ γ₁ ⬝ γ₂` is gluing
along the four-holed sphere `P ≫ (P' ⋀ 𝟙)`. -/
theorem pantsGlue_pantsGlue_left (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂)
    (D₃ : RawCap γ₃) :
    pantsGlue P (pantsGlue P' D₁ D₂) D₃ = glue₃ (P ≫ HSpace.pathHmul P' (𝟙 _)) D₁ D₂ D₃ := by
  have h : HSpace.pathHmul (P' ≫ HSpace.pathHmul D₁ D₂ ≫
      eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) D₃ =
      HSpace.pathHmul P' (𝟙 _) ≫ HSpace.pathHmul (HSpace.pathHmul D₁ D₂) D₃ ≫
        HSpace.pathHmul (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) (𝟙 _) := by
    rw [← HSpace.pathHmul_comp, ← HSpace.pathHmul_comp, Category.id_comp, Category.comp_id]
  calc pantsGlue P (pantsGlue P' D₁ D₂) D₃
      = P ≫ (HSpace.pathHmul P' (𝟙 _) ≫ HSpace.pathHmul (HSpace.pathHmul D₁ D₂) D₃ ≫
          HSpace.pathHmul (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) (𝟙 _)) ≫
          eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e) := by
        rw [pantsGlue_def, pantsGlue_def, h]
    _ = P ≫ HSpace.pathHmul P' (𝟙 _) ≫ HSpace.pathHmul (HSpace.pathHmul D₁ D₂) D₃ ≫
          eqToHom (congrArg FundamentalGroupoid.mk
            ((congrArg (· ⋀ HSpace.e) HSpace.hmul_e_e).trans HSpace.hmul_e_e)) := by
        rw [HSpace.pathHmul_eqToHom_id (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)]
        simp only [Category.assoc, eqToHom_trans]
    -- The four-holed sphere `P ≫ (P' ⋀ 𝟙)` ends at `(γ₁ ⬝ γ₂) ⋀ γ₃` and the gluing map starts at
    -- `(γ₁ ⋀ γ₂) ⋀ γ₃`. These objects agree only after unfolding the product of the loop space,
    -- which rewriting does not do, so this reassociation is a term.
    _ = glue₃ (P ≫ HSpace.pathHmul P' (𝟙 _)) D₁ D₂ D₃ := (Category.assoc _ _ _).symm

/-- **Sewing a pair of pants into the second input.** If the four-holed sphere `W`, followed by
the associator of the loop space, is the pair of pants `Q : γ₀ ⟶ γ₁ ⬝ γ` with the pair of pants
`Q' : γ ⟶ γ₂ ⬝ γ₃` sewn into its second input, then gluing caps along `W` is gluing along `Q'` and
then along `Q`. -/
theorem glue₃_eq_pantsGlue_pantsGlue_right
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ⟩)
    (Q' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (hW : W ≫ Path.transAssoc γ₁ γ₂ γ₃ = Q ≫ HSpace.pathHmul (𝟙 _) Q') (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂ D₃ = pantsGlue Q D₁ (pantsGlue Q' D₂ D₃) := by
  have h : HSpace.pathHmul D₁ (Q' ≫ HSpace.pathHmul D₂ D₃ ≫
      eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) =
      HSpace.pathHmul (𝟙 _) Q' ≫ HSpace.pathHmul D₁ (HSpace.pathHmul D₂ D₃) ≫
        HSpace.pathHmul (𝟙 _) (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) := by
    rw [← HSpace.pathHmul_comp, ← HSpace.pathHmul_comp, Category.id_comp, Category.comp_id]
  have ht : Path.transAssoc (Path.refl x) (Path.refl x) (Path.refl x) ≫
      HSpace.pathHmul (𝟙 (⟨Path.refl x⟩ : FundamentalGroupoid (Ω X x)))
        (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) ≫
      eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e) =
      eqToHom (congrArg FundamentalGroupoid.mk
        ((congrArg (· ⋀ HSpace.e) HSpace.hmul_e_e).trans HSpace.hmul_e_e)) := by
    rw [Path.transAssoc_refl]
    exact (congrArg (eqToHom _ ≫ · ≫ eqToHom _)
      (HSpace.pathHmul_id_eqToHom _ (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e))).trans
        ((congrArg (eqToHom _ ≫ ·) (eqToHom_trans _ _)).trans (eqToHom_trans _ _))
  -- As in `pantsGlue_pantsGlue_left`, the objects `(γ₁ ⬝ γ₂) ⬝ γ₃` and `(γ₁ ⋀ γ₂) ⋀ γ₃` only agree
  -- after unfolding the product of the loop space, so the reassociations are terms.
  calc glue₃ W D₁ D₂ D₃
      = W ≫ HSpace.pathHmul (HSpace.pathHmul D₁ D₂) D₃ ≫
          Path.transAssoc (Path.refl x) (Path.refl x) (Path.refl x) ≫
          HSpace.pathHmul (𝟙 _) (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) ≫
          eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e) :=
        congrArg (W ≫ HSpace.pathHmul (HSpace.pathHmul D₁ D₂) D₃ ≫ ·) ht.symm
    _ = W ≫ Path.transAssoc γ₁ γ₂ γ₃ ≫ HSpace.pathHmul D₁ (HSpace.pathHmul D₂ D₃) ≫
          HSpace.pathHmul (𝟙 _) (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) ≫
          eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e) :=
        congrArg (W ≫ ·)
          ((Path.pathHmul_pathHmul_comp_transAssoc_assoc _ _ _ _).trans (Category.assoc _ _ _))
    _ = (W ≫ Path.transAssoc γ₁ γ₂ γ₃) ≫ HSpace.pathHmul D₁ (HSpace.pathHmul D₂ D₃) ≫
          HSpace.pathHmul (𝟙 _) (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) ≫
          eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e) := (Category.assoc _ _ _).symm
    _ = Q ≫ (HSpace.pathHmul (𝟙 _) Q' ≫ HSpace.pathHmul D₁ (HSpace.pathHmul D₂ D₃) ≫
          HSpace.pathHmul (𝟙 _) (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e))) ≫
          eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e) := by
        rw [hW]
        simp only [Category.assoc]
        rfl
    _ = pantsGlue Q D₁ (pantsGlue Q' D₂ D₃) := by rw [pantsGlue_def, pantsGlue_def, h]

/-- Gluing caps along a four-holed sphere `W` is gluing them along `W`, read as a pair of pants
with inputs `γ₁ ⬝ γ₂` and `γ₃`, after gluing the first two caps along the trivial pair of
pants. -/
theorem glue₃_eq_pantsGlue_pantsGlue
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂ D₃ = pantsGlue W (pantsGlue (𝟙 _) D₁ D₂) D₃ := by
  rw [pantsGlue_pantsGlue_left]
  exact congrArg (glue₃ · D₁ D₂ D₃) ((congrArg (W ≫ ·) (HSpace.pathHmul_id _ _)).trans
    (Category.comp_id W)).symm

/-- Gluing a homotopy of loops `p` from `γ₀'` to the output `γ₀` to a cap glued along a
four-holed sphere is gluing caps along the composite four-holed sphere `p ≫ W`. -/
@[simp]
theorem comp_glue₃ {γ₀' : Ω X x} (p : (⟨γ₀'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₀⟩)
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) : p ≫ glue₃ W D₁ D₂ D₃ = glue₃ (p ≫ W) D₁ D₂ D₃ := by
  simp only [glue₃_def, Category.assoc]

/-- Gluing caps glued to homotopies of loops `p₁`, `p₂` and `p₃` at the inputs is gluing caps
along the four-holed sphere `W` followed by the product `(p₁ ⋀ p₂) ⋀ p₃` of the homotopies. -/
theorem glue₃_comp_comp_comp {γ₁' γ₂' γ₃' : Ω X x}
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (p₁ : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁'⟩)
    (p₂ : (⟨γ₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂'⟩)
    (p₃ : (⟨γ₃⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₃'⟩) (D₁ : RawCap γ₁') (D₂ : RawCap γ₂')
    (D₃ : RawCap γ₃') :
    glue₃ W (p₁ ≫ D₁) (p₂ ≫ D₂) (p₃ ≫ D₃) =
      glue₃ (W ≫ HSpace.pathHmul (HSpace.pathHmul p₁ p₂) p₃) D₁ D₂ D₃ := by
  rw [glue₃_def, glue₃_def, HSpace.pathHmul_comp p₁ D₁ p₂ D₂]
  -- As in `pantsGlue_pantsGlue_left`, the objects `γ₁ ⬝ γ₂` and `γ₁ ⋀ γ₂` only agree after
  -- unfolding the product of the loop space, so the outer functoriality and the reassociation
  -- are terms.
  exact (congrArg (W ≫ · ≫ eqToHom _)
    (HSpace.pathHmul_comp (HSpace.pathHmul p₁ p₂) (HSpace.pathHmul D₁ D₂) p₃ D₃)).trans
      ((congrArg (W ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm)

/-- **The two broken configurations of a four-holed sphere glue the same cap.** If the pair of
pants `P` with `P'` sewn into its first input and the pair of pants `Q` with `Q'` sewn into its
second input represent the same four-holed sphere, up to the associator of the loop space, then
gluing caps along the two configurations gives the same cap of the output. -/
theorem pantsGlue_pantsGlue_eq_of_comp_transAssoc_eq {γ' : Ω X x}
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ'⟩)
    (Q' : (⟨γ'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (h : (P ≫ HSpace.pathHmul P' (𝟙 _)) ≫ Path.transAssoc γ₁ γ₂ γ₃ =
      Q ≫ HSpace.pathHmul (𝟙 _) Q') (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    pantsGlue P (pantsGlue P' D₁ D₂) D₃ = pantsGlue Q D₁ (pantsGlue Q' D₂ D₃) :=
  (pantsGlue_pantsGlue_left P P' D₁ D₂ D₃).trans
    (glue₃_eq_pantsGlue_pantsGlue_right _ Q Q' h D₁ D₂ D₃)

/-- Gluing a sphere at the centre of the first input cap glues the same sphere at the centre of
the cap glued along a four-holed sphere. -/
@[simp]
theorem glue₃_vadd_left (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (a : Additive (π_ 2 X x)) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W (a +ᵥ D₁) D₂ D₃ = a +ᵥ glue₃ W D₁ D₂ D₃ := by
  simp only [glue₃_eq_pantsGlue_pantsGlue, pantsGlue_vadd_left]

/-- Gluing a sphere at the centre of the second input cap glues the same sphere at the centre of
the cap glued along a four-holed sphere. -/
@[simp]
theorem glue₃_vadd_middle (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (a : Additive (π_ 2 X x)) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁ (a +ᵥ D₂) D₃ = a +ᵥ glue₃ W D₁ D₂ D₃ := by
  simp only [glue₃_eq_pantsGlue_pantsGlue, pantsGlue_vadd_right, pantsGlue_vadd_left]

/-- Gluing a sphere at the centre of the third input cap glues the same sphere at the centre of
the cap glued along a four-holed sphere. -/
@[simp]
theorem glue₃_vadd_right (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (a : Additive (π_ 2 X x)) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂ (a +ᵥ D₃) = a +ᵥ glue₃ W D₁ D₂ D₃ := by
  simp only [glue₃_eq_pantsGlue_pantsGlue, pantsGlue_vadd_right]

/-- Changing the first input cap changes the cap glued along a four-holed sphere by the same
sphere. -/
@[simp]
theorem glue₃_vsub_glue₃_left
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩) (D₁' D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁' D₂ D₃ -ᵥ glue₃ W D₁ D₂ D₃ = D₁' -ᵥ D₁ := by
  simp only [glue₃_eq_pantsGlue_pantsGlue, pantsGlue_vsub_pantsGlue_left]

/-- Changing the second input cap changes the cap glued along a four-holed sphere by the same
sphere. -/
@[simp]
theorem glue₃_vsub_glue₃_middle
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩) (D₁ : RawCap γ₁)
    (D₂' D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂' D₃ -ᵥ glue₃ W D₁ D₂ D₃ = D₂' -ᵥ D₂ := by
  simp only [glue₃_eq_pantsGlue_pantsGlue, pantsGlue_vsub_pantsGlue_left,
    pantsGlue_vsub_pantsGlue_right]

/-- Changing the third input cap changes the cap glued along a four-holed sphere by the same
sphere. -/
@[simp]
theorem glue₃_vsub_glue₃_right
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) (D₃' D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂ D₃' -ᵥ glue₃ W D₁ D₂ D₃ = D₃' -ᵥ D₃ := by
  simp only [glue₃_eq_pantsGlue_pantsGlue, pantsGlue_vsub_pantsGlue_right]

end RawCap

end Raw

section Spherical

variable {X : Type} [TopologicalSpace X] {x : X}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

namespace SphericalCapClass

variable {γ γ' γ₀ γ₁ γ₂ γ₃ : Ω X x}

/-- **Gluing cap classes along a four-holed sphere** `W : γ₀ ⟶ (γ₁ ⬝ γ₂) ⬝ γ₃`, computed on
representatives by `TauCeti.Floer.RawCap.glue₃` (`TauCeti.Floer.SphericalCapClass.glue₃_mk`). -/
def glue₃ (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) : SphericalCapClass ω c γ₀ :=
  pantsGlue W (pantsGlue (𝟙 _) q₁ q₂) q₃

@[simp]
theorem glue₃_mk (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W (mk ω c D₁) (mk ω c D₂) (mk ω c D₃) = mk ω c (RawCap.glue₃ W D₁ D₂ D₃) := by
  rw [glue₃, pantsGlue_mk, pantsGlue_mk, RawCap.glue₃_eq_pantsGlue_pantsGlue]

theorem glue₃_eq_pantsGlue_pantsGlue
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁ q₂ q₃ = pantsGlue W (pantsGlue (𝟙 _) q₁ q₂) q₃ :=
  (rfl)

/-- Gluing a homotopy of loops at the output to a cap class glued along a four-holed sphere is
gluing along the composite four-holed sphere. -/
@[simp]
theorem glue_glue₃ {γ₀' : Ω X x} (p : (⟨γ₀'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₀⟩)
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) : glue p (glue₃ W q₁ q₂ q₃) = glue₃ (p ≫ W) q₁ q₂ q₃ := by
  rw [glue₃_eq_pantsGlue_pantsGlue, glue_pantsGlue, glue₃_eq_pantsGlue_pantsGlue]

/-- Gluing cap classes glued to homotopies of loops `p₁`, `p₂` and `p₃` at the inputs is gluing
along the four-holed sphere followed by the product `(p₁ ⋀ p₂) ⋀ p₃` of the homotopies. -/
theorem glue₃_glue_glue_glue {γ₁' γ₂' γ₃' : Ω X x}
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (p₁ : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁'⟩)
    (p₂ : (⟨γ₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂'⟩)
    (p₃ : (⟨γ₃⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₃'⟩) (q₁ : SphericalCapClass ω c γ₁')
    (q₂ : SphericalCapClass ω c γ₂') (q₃ : SphericalCapClass ω c γ₃') :
    glue₃ W (glue p₁ q₁) (glue p₂ q₂) (glue p₃ q₃) =
      glue₃ (W ≫ HSpace.pathHmul (HSpace.pathHmul p₁ p₂) p₃) q₁ q₂ q₃ := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃ using induction_on with
  | h D₃ => rw [glue_mk, glue_mk, glue_mk, glue₃_mk, glue₃_mk, RawCap.glue₃_comp_comp_comp]

/-- **Sewing a pair of pants into the first input**, on cap classes: gluing along `P` after
gluing along `P'` at its first input is gluing along the four-holed sphere `P ≫ (P' ⋀ 𝟙)`. -/
theorem pantsGlue_pantsGlue_left (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₃ : SphericalCapClass ω c γ₃) :
    pantsGlue P (pantsGlue P' q₁ q₂) q₃ = glue₃ (P ≫ HSpace.pathHmul P' (𝟙 _)) q₁ q₂ q₃ := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃ using induction_on with
  | h D₃ => rw [pantsGlue_mk, pantsGlue_mk, glue₃_mk, RawCap.pantsGlue_pantsGlue_left]

/-- **Sewing a pair of pants into the second input**, on cap classes: if `W` followed by the
associator of the loop space is `Q` with `Q'` sewn into its second input, then gluing along `W`
is gluing along `Q'` and then along `Q`. -/
theorem glue₃_eq_pantsGlue_pantsGlue_right
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ⟩)
    (Q' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (hW : W ≫ Path.transAssoc γ₁ γ₂ γ₃ = Q ≫ HSpace.pathHmul (𝟙 _) Q')
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁ q₂ q₃ = pantsGlue Q q₁ (pantsGlue Q' q₂ q₃) := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃ using induction_on with
  | h D₃ => rw [pantsGlue_mk, pantsGlue_mk, glue₃_mk,
      RawCap.glue₃_eq_pantsGlue_pantsGlue_right W Q Q' hW]

/-- **The two broken configurations of a four-holed sphere glue the same cap.** If the pair of
pants `P` with `P'` sewn into its first input and the pair of pants `Q` with `Q'` sewn into its
second input represent the same four-holed sphere, up to the associator of the loop space, then
gluing cap classes along the two configurations gives the same cap class of the output. -/
theorem pantsGlue_pantsGlue_eq_of_comp_transAssoc_eq
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ'⟩)
    (Q' : (⟨γ'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (h : (P ≫ HSpace.pathHmul P' (𝟙 _)) ≫ Path.transAssoc γ₁ γ₂ γ₃ =
      Q ≫ HSpace.pathHmul (𝟙 _) Q')
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) :
    pantsGlue P (pantsGlue P' q₁ q₂) q₃ = pantsGlue Q q₁ (pantsGlue Q' q₂ q₃) :=
  (pantsGlue_pantsGlue_left P P' q₁ q₂ q₃).trans
    (glue₃_eq_pantsGlue_pantsGlue_right _ Q Q' h q₁ q₂ q₃)

variable [PathConnectedSpace X]

/-- **Gluing cap classes along a four-holed sphere is equivariant in the first input**. -/
@[simp]
theorem glue₃_vadd_left (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (g : SphericalPeriodGroup ω c) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W (g +ᵥ q₁) q₂ q₃ = g +ᵥ glue₃ W q₁ q₂ q₃ := by
  simp only [glue₃, pantsGlue_vadd_left]

/-- **Gluing cap classes along a four-holed sphere is equivariant in the second input**. -/
@[simp]
theorem glue₃_vadd_middle (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (g : SphericalPeriodGroup ω c) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁ (g +ᵥ q₂) q₃ = g +ᵥ glue₃ W q₁ q₂ q₃ := by
  simp only [glue₃, pantsGlue_vadd_right, pantsGlue_vadd_left]

/-- **Gluing cap classes along a four-holed sphere is equivariant in the third input**. -/
@[simp]
theorem glue₃_vadd_right (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (g : SphericalPeriodGroup ω c) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁ q₂ (g +ᵥ q₃) = g +ᵥ glue₃ W q₁ q₂ q₃ := by
  simp only [glue₃, pantsGlue_vadd_right]

variable [Nonempty (RawCap γ₀)]

/-- **Cap classes add when a pair of pants is sewn into the first input.** The class
`q₀ -ᵥ glue₃ (P ≫ (P' ⋀ 𝟙)) q₁ q₂ q₃` of the four-holed sphere obtained by sewing `P'` into the
first input of `P`, relative to cap classes of its boundary loops, is the class of `P` plus the
class of `P'`, for any cap class `q` of the intermediate loop. -/
theorem vsub_glue₃_eq_productClass_add_productClass_left [Nonempty (RawCap γ)]
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₃ : SphericalCapClass ω c γ₃) (q : SphericalCapClass ω c γ)
    (q₀ : SphericalCapClass ω c γ₀) :
    q₀ -ᵥ glue₃ (P ≫ HSpace.pathHmul P' (𝟙 _)) q₁ q₂ q₃ =
      productClass (pantsGlue P) q q₃ q₀ + productClass (pantsGlue P') q₁ q₂ q := by
  rw [← productClass_comp_fst (pantsGlue P') (pantsGlue P)
    (fun g q q₃ => pantsGlue_vadd_left P g q q₃), productClass_def, pantsGlue_pantsGlue_left]

/-- **Cap classes add when a pair of pants is sewn into the second input.** If `W` followed by
the associator of the loop space is `Q ≫ (𝟙 ⋀ Q')`, the class `q₀ -ᵥ glue₃ W q₁ q₂ q₃` of the
four-holed sphere `W` is the class of `Q` plus the class of `Q'`, for any cap class `q` of the
intermediate loop. -/
theorem vsub_glue₃_eq_productClass_add_productClass_right [Nonempty (RawCap γ)]
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ⟩)
    (Q' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (hW : W ≫ Path.transAssoc γ₁ γ₂ γ₃ = Q ≫ HSpace.pathHmul (𝟙 _) Q')
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) (q : SphericalCapClass ω c γ)
    (q₀ : SphericalCapClass ω c γ₀) :
    q₀ -ᵥ glue₃ W q₁ q₂ q₃ =
      productClass (pantsGlue Q) q₁ q q₀ + productClass (pantsGlue Q') q₂ q₃ q := by
  rw [← productClass_comp_snd (pantsGlue Q') (pantsGlue Q)
    (fun g q₁ q => pantsGlue_vadd_right Q g q₁ q), productClass_def,
    glue₃_eq_pantsGlue_pantsGlue_right W Q Q' hW]

/-- **Cap classes add under both degenerations of a four-holed sphere.** If the pair of pants `P`
with `P'` sewn into its first input and the pair of pants `Q` with `Q'` sewn into its second input
represent the same four-holed sphere, up to the associator of the loop space, then the sums of the
classes of the two broken configurations agree, whatever cap classes `q` and `q'` are chosen at the
two intermediate loops. -/
theorem productClass_add_productClass_eq_of_comp_transAssoc_eq [Nonempty (RawCap γ)]
    [Nonempty (RawCap γ')]
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ'⟩)
    (Q' : (⟨γ'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (h : (P ≫ HSpace.pathHmul P' (𝟙 _)) ≫ Path.transAssoc γ₁ γ₂ γ₃ =
      Q ≫ HSpace.pathHmul (𝟙 _) Q')
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) (q : SphericalCapClass ω c γ)
    (q' : SphericalCapClass ω c γ') (q₀ : SphericalCapClass ω c γ₀) :
    productClass (pantsGlue P) q q₃ q₀ + productClass (pantsGlue P') q₁ q₂ q =
      productClass (pantsGlue Q) q₁ q' q₀ + productClass (pantsGlue Q') q₂ q₃ q' :=
  (vsub_glue₃_eq_productClass_add_productClass_left P P' q₁ q₂ q₃ q q₀).symm.trans
    (vsub_glue₃_eq_productClass_add_productClass_right _ Q Q' h q₁ q₂ q₃ q' q₀)

end SphericalCapClass

end Spherical

end TauCeti.Floer
