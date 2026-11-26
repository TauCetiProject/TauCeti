/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Associativity

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

* **Sewing into the first input.** If `W` is a pair of pants `P : γ₀ ⟶ γ ⬝ γ₃` with a pair of
  pants `P' : γ ⟶ γ₁ ⬝ γ₂` sewn into its first input, that is `W = P ≫ (P' ⋀ 𝟙)`, then gluing
  along `W` is gluing along `P'` and then along `P`
  (`TauCeti.Floer.RawCap.glue₃_eq_pantsGlue_pantsGlue_left`). This is the functoriality of the
  product of path classes (`TauCeti.Floer.RawCap.pantsGlue_pantsGlue_left`).
* **Sewing into the second input.** A pair of pants `Q : γ₀ ⟶ γ₁ ⬝ γ` with a pair of pants
  `Q' : γ ⟶ γ₂ ⬝ γ₃` sewn into its second input is a homotopy of loops ending at
  `γ₁ ⬝ (γ₂ ⬝ γ₃)`. If it is `W` after the associator `Path.loopTransAssoc` of the loop space,
  then gluing along `W` is gluing along `Q'` and then along `Q`
  (`TauCeti.Floer.RawCap.glue₃_eq_pantsGlue_pantsGlue_right`). This is the gluing law
  `TauCeti.Floer.RawCap.pantsGlue_assoc` for the two decompositions of a four-holed sphere.

Gluing along a four-holed sphere is equivariant for spheres added at any of the three inputs
(`TauCeti.Floer.RawCap.glue₃_vadd_left` and its variants). On the cap classes of
`TauCeti.Floer.SphericalCapClass`, the class `q₀ -ᵥ glue₃ W q₁ q₂ q₃` of the four-holed sphere `W`
relative to cap classes of its four boundary loops is the sum of the classes of the two pairs of
pants of either decomposition, whatever cap class is chosen at the intermediate loop
(`TauCeti.Floer.SphericalCapClass.vsub_glue₃_eq_productClass_add_productClass_left`,
`TauCeti.Floer.SphericalCapClass.vsub_glue₃_eq_productClass_add_productClass_right`): cap classes
add under both degenerations of a four-holed sphere, and the sum is the class of the unbroken
four-holed sphere. The agreement of the two sums alone is
`TauCeti.Floer.SphericalCapClass.productClass_pantsGlue_add_productClass_pantsGlue`.

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
three caps side by side on top of `W`: the first two caps glued along the trivial pair of pants,
then glued with the third along `W`. -/
def glue₃ (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) : RawCap γ₀ :=
  pantsGlue W (pantsGlue (𝟙 _) D₁ D₂) D₃

/-- Gluing caps along a four-holed sphere `W` is gluing them along `W`, read as a pair of pants
with inputs `γ₁ ⬝ γ₂` and `γ₃`, after gluing the first two caps along the trivial pair of
pants. -/
theorem glue₃_eq_pantsGlue_pantsGlue
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂ D₃ = pantsGlue W (pantsGlue (𝟙 _) D₁ D₂) D₃ :=
  (rfl)

/-- **Sewing a pair of pants into the first input.** If the four-holed sphere `W` is the pair of
pants `P : γ₀ ⟶ γ ⬝ γ₃` with the pair of pants `P' : γ ⟶ γ₁ ⬝ γ₂` sewn into its first input, then
gluing caps along `W` is gluing along `P'` and then along `P`. -/
theorem glue₃_eq_pantsGlue_pantsGlue_left
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (hW : P ≫ HSpace.pathHmul P' (𝟙 _) = W) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂)
    (D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂ D₃ = pantsGlue P (pantsGlue P' D₁ D₂) D₃ := by
  subst hW
  rw [glue₃_eq_pantsGlue_pantsGlue, pantsGlue_pantsGlue_left P P']

/-- **Sewing a pair of pants into the second input.** If the four-holed sphere `W` is the pair of
pants `Q : γ₀ ⟶ γ₁ ⬝ γ` with the pair of pants `Q' : γ ⟶ γ₂ ⬝ γ₃` sewn into its second input,
followed by the associator of the loop space, then gluing caps along `W` is gluing along `Q'` and
then along `Q`. -/
theorem glue₃_eq_pantsGlue_pantsGlue_right
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ⟩)
    (Q' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (hW : Q ≫ HSpace.pathHmul (𝟙 _) Q' ≫ Path.loopTransAssoc γ₁ γ₂ γ₃ = W) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    glue₃ W D₁ D₂ D₃ = pantsGlue Q D₁ (pantsGlue Q' D₂ D₃) := by
  rw [glue₃_eq_pantsGlue_pantsGlue]
  exact pantsGlue_assoc W (𝟙 _) Q Q'
    (by rw [hW, HSpace.pathHmul_id]; exact (Category.comp_id W).symm) D₁ D₂ D₃

/-- Gluing a homotopy of loops `p` from `γ₀'` to the output `γ₀` to a cap glued along a
four-holed sphere is gluing caps along the composite four-holed sphere `p ≫ W`. -/
@[simp]
theorem comp_glue₃ {γ₀' : Ω X x} (p : (⟨γ₀'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₀⟩)
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) : p ≫ glue₃ W D₁ D₂ D₃ = glue₃ (p ≫ W) D₁ D₂ D₃ := by
  simp only [glue₃_eq_pantsGlue_pantsGlue, comp_pantsGlue]

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
  have h : pantsGlue (𝟙 _) (p₁ ≫ D₁) (p₂ ≫ D₂) =
      HSpace.pathHmul p₁ p₂ ≫ pantsGlue (𝟙 _) D₁ D₂ := by
    rw [pantsGlue_comp_comp, comp_pantsGlue, Category.id_comp, Category.comp_id]
  rw [glue₃_eq_pantsGlue_pantsGlue, glue₃_eq_pantsGlue_pantsGlue, h, pantsGlue_comp_comp]
  -- The objects `γ₁' ⬝ γ₂'` and `γ₁' ⋀ γ₂'` of the two trivial pairs of pants only agree after
  -- unfolding the product of the loop space.
  rfl

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

variable {γ γ₀ γ₁ γ₂ γ₃ : Ω X x}

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
  simp only [glue₃, pantsGlue_mk, RawCap.glue₃_eq_pantsGlue_pantsGlue]

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
  simp only [glue₃_eq_pantsGlue_pantsGlue, glue_pantsGlue]

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
  | h D₃ => simp only [glue_mk, glue₃_mk, RawCap.glue₃_comp_comp_comp]

/-- **Sewing a pair of pants into the first input**, on cap classes: if `W` is `P ≫ (P' ⋀ 𝟙)`,
then gluing along `W` is gluing along `P'` and then along `P`. -/
theorem glue₃_eq_pantsGlue_pantsGlue_left
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (hW : P ≫ HSpace.pathHmul P' (𝟙 _) = W) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁ q₂ q₃ = pantsGlue P (pantsGlue P' q₁ q₂) q₃ := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃ using induction_on with
  | h D₃ => simp only [pantsGlue_mk, glue₃_mk, RawCap.glue₃_eq_pantsGlue_pantsGlue_left W P P' hW]

/-- **Sewing a pair of pants into the second input**, on cap classes: if `W` is
`Q ≫ (𝟙 ⋀ Q')` followed by the associator of the loop space, then gluing along `W` is gluing
along `Q'` and then along `Q`. -/
theorem glue₃_eq_pantsGlue_pantsGlue_right
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ⟩)
    (Q' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (hW : Q ≫ HSpace.pathHmul (𝟙 _) Q' ≫ Path.loopTransAssoc γ₁ γ₂ γ₃ = W)
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁ q₂ q₃ = pantsGlue Q q₁ (pantsGlue Q' q₂ q₃) := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃ using induction_on with
  | h D₃ => simp only [pantsGlue_mk, glue₃_mk, RawCap.glue₃_eq_pantsGlue_pantsGlue_right W Q Q' hW]

/-- Changing the first input cap class changes the cap class glued along a four-holed sphere by
the same class. -/
@[simp]
theorem glue₃_vsub_glue₃_left
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (q₁' q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁' q₂ q₃ -ᵥ glue₃ W q₁ q₂ q₃ = q₁' -ᵥ q₁ := by
  induction q₁' using induction_on with | h D₁' =>
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃ using induction_on with
  | h D₃ => simp only [glue₃_mk, mk_vsub_mk, RawCap.glue₃_vsub_glue₃_left]

/-- Changing the second input cap class changes the cap class glued along a four-holed sphere by
the same class. -/
@[simp]
theorem glue₃_vsub_glue₃_middle
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (q₁ : SphericalCapClass ω c γ₁) (q₂' q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁ q₂' q₃ -ᵥ glue₃ W q₁ q₂ q₃ = q₂' -ᵥ q₂ := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂' using induction_on with | h D₂' =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃ using induction_on with
  | h D₃ => simp only [glue₃_mk, mk_vsub_mk, RawCap.glue₃_vsub_glue₃_middle]

/-- Changing the third input cap class changes the cap class glued along a four-holed sphere by
the same class. -/
@[simp]
theorem glue₃_vsub_glue₃_right
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃' q₃ : SphericalCapClass ω c γ₃) :
    glue₃ W q₁ q₂ q₃' -ᵥ glue₃ W q₁ q₂ q₃ = q₃' -ᵥ q₃ := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃' using induction_on with | h D₃' =>
  induction q₃ using induction_on with
  | h D₃ => simp only [glue₃_mk, mk_vsub_mk, RawCap.glue₃_vsub_glue₃_right]

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

/-- **Cap classes add when a pair of pants is sewn into the first input.** If `W` is
`P ≫ (P' ⋀ 𝟙)`, the class `q₀ -ᵥ glue₃ W q₁ q₂ q₃` of the four-holed sphere `W`, relative to cap
classes of its boundary loops, is the class of `P` plus the class of `P'`, for any cap class `q`
of the intermediate loop. -/
theorem vsub_glue₃_eq_productClass_add_productClass_left [Nonempty (RawCap γ)]
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ.trans γ₃⟩)
    (P' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (hW : P ≫ HSpace.pathHmul P' (𝟙 _) = W) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₃ : SphericalCapClass ω c γ₃) (q : SphericalCapClass ω c γ)
    (q₀ : SphericalCapClass ω c γ₀) :
    q₀ -ᵥ glue₃ W q₁ q₂ q₃ =
      productClass (pantsGlue P) q q₃ q₀ + productClass (pantsGlue P') q₁ q₂ q := by
  rw [← productClass_comp_fst (pantsGlue P') (pantsGlue P)
    (fun g q q₃ => pantsGlue_vadd_left P g q q₃), productClass_def,
    glue₃_eq_pantsGlue_pantsGlue_left W P P' hW]

/-- **Cap classes add when a pair of pants is sewn into the second input.** If `W` is
`Q ≫ (𝟙 ⋀ Q')` followed by the associator of the loop space, the class `q₀ -ᵥ glue₃ W q₁ q₂ q₃`
of the four-holed sphere `W` is the class of `Q` plus the class of `Q'`, for any cap class `q` of
the intermediate loop. -/
theorem vsub_glue₃_eq_productClass_add_productClass_right [Nonempty (RawCap γ)]
    (W : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨(γ₁.trans γ₂).trans γ₃⟩)
    (Q : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ⟩)
    (Q' : (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (hW : Q ≫ HSpace.pathHmul (𝟙 _) Q' ≫ Path.loopTransAssoc γ₁ γ₂ γ₃ = W)
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) (q : SphericalCapClass ω c γ)
    (q₀ : SphericalCapClass ω c γ₀) :
    q₀ -ᵥ glue₃ W q₁ q₂ q₃ =
      productClass (pantsGlue Q) q₁ q q₀ + productClass (pantsGlue Q') q₂ q₃ q := by
  rw [← productClass_comp_snd (pantsGlue Q') (pantsGlue Q)
    (fun g q₁ q => pantsGlue_vadd_right Q g q₁ q), productClass_def,
    glue₃_eq_pantsGlue_pantsGlue_right W Q Q' hW]

end SphericalCapClass

end Spherical

end TauCeti.Floer
