/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.PairOfPants
public import TauCeti.Geometry.Symplectic.Floer.Cap.Sewing

/-!
# Gluing caps along the two decompositions of a four-holed sphere

Let `γ₁`, `γ₂`, `γ₃` and `γ₀` be loops in a space `X` based at `x`. A four-holed sphere with inputs
`γ₁`, `γ₂`, `γ₃` and output `γ₀`, with its seams at `x`, is a homotopy of loops from `γ₀` to a
concatenation of the inputs. Cutting it along a loop that separates two adjacent inputs from the
rest decomposes it into two pairs of pants, in the sense of
`TauCeti.Geometry.Symplectic.Floer.Cap.PairOfPants`, and there are two such cuts:

* along a loop `γ₁₂` around the first two inputs, into `P₁₂ : γ₀ ⟶ γ₁₂ ⬝ γ₃` and
  `Q₁₂ : γ₁₂ ⟶ γ₁ ⬝ γ₂`, whose composite `P₁₂ ≫ (Q₁₂ ⋀ 𝟙)` ends at `(γ₁ ⬝ γ₂) ⬝ γ₃`;
* along a loop `γ₂₃` around the last two inputs, into `P₂₃ : γ₀ ⟶ γ₁ ⬝ γ₂₃` and
  `Q₂₃ : γ₂₃ ⟶ γ₂ ⬝ γ₃`, whose composite `P₂₃ ≫ (𝟙 ⋀ Q₂₃)` ends at `γ₁ ⬝ (γ₂ ⬝ γ₃)`.

They are cuts of the same four-holed sphere when the two composites agree after the associator
`Path.loopTransAssoc γ₁ γ₂ γ₃ : γ₁ ⬝ (γ₂ ⬝ γ₃) ⟶ (γ₁ ⬝ γ₂) ⬝ γ₃` of the loop space. These are the
two broken configurations at the ends of the one-parameter family of four-punctured spheres that
gives the associativity of the pair-of-pants product.

This file proves that gluing caps of the inputs along the two decompositions gives the same cap of
the output:

`pantsGlue P₁₂ (pantsGlue Q₁₂ D₁ D₂) D₃ = pantsGlue P₂₃ D₁ (pantsGlue Q₂₃ D₂ D₃)`

(`TauCeti.Floer.RawCap.pantsGlue_assoc`, and `TauCeti.Floer.SphericalCapClass.pantsGlue_assoc` for
cap classes). The key step is the case of the trivial four-holed sphere: placing three discs side
by side does not depend on which two are placed together first, up to the associator
(`TauCeti.Floer.RawCap.loopTransAssoc_comp_pantsGlue_pantsGlue`). This is the naturality of the
associator (`Path.pathHmul_pathHmul_comp_loopTransAssoc`) together with its triviality at the
constant loops (`Path.loopTransAssoc_refl`).

Consequently the classes of the two broken configurations, measured against any caps of the
inputs, the output and the two separating loops, have the same sum
(`TauCeti.Floer.SphericalCapClass.productClass_pantsGlue_add_productClass_pantsGlue`). This is the
geometric identification of glued caps asked for by `TauCeti.Floer.productClass_add_eq_add_iff`:
the class of a configuration is additive under the breaking of a four-holed sphere into two pairs
of pants, and it is the same for both ways of breaking, so the Novikov exponents of the two broken
triple products in an associativity identity agree. No moduli space, gluing theorem or count is
constructed here.

## Main results

* `TauCeti.Floer.RawCap.loopTransAssoc_comp_pantsGlue_pantsGlue`: placing three caps side by side
  is associative up to the associator of the loop space.
* `TauCeti.Floer.RawCap.pantsGlue_assoc`, `TauCeti.Floer.SphericalCapClass.pantsGlue_assoc`: the
  two decompositions of a four-holed sphere glue the same output cap.
* `TauCeti.Floer.SphericalCapClass.productClass_pantsGlue_add_productClass_pantsGlue`: the classes
  of the two broken configurations have the same sum.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the classes of pairs of pants relative to caps and the associativity of the product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on
  Floer homology and the pair-of-pants product.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy HSpaces

namespace TauCeti.Floer

section Raw

variable {X : Type*} [TopologicalSpace X] {x : X}

namespace RawCap

variable {γ₀ γ₁ γ₂ γ₃ γ₁₂ γ₂₃ : Ω X x}

/-- **Placing three caps side by side is associative**: the caps `D₁ ⋀ D₂` glued beside `D₃`,
pulled back along the associator, are the caps `D₁` glued beside `D₂ ⋀ D₃`. -/
theorem loopTransAssoc_comp_pantsGlue_pantsGlue (D₁ : RawCap γ₁) (D₂ : RawCap γ₂)
    (D₃ : RawCap γ₃) :
    Path.loopTransAssoc γ₁ γ₂ γ₃ ≫ pantsGlue (𝟙 _) (pantsGlue (𝟙 _) D₁ D₂) D₃ =
      pantsGlue (𝟙 _) D₁ (pantsGlue (𝟙 _) D₂ D₃) := by
  have h₁ := HSpace.pathHmul_comp (HSpace.pathHmul D₁ D₂)
    (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)) D₃ (𝟙 _)
  have h₂ := HSpace.pathHmul_comp D₁ (𝟙 _) (HSpace.pathHmul D₂ D₃)
    (eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e))
  rw [Category.comp_id] at h₁
  rw [Category.comp_id] at h₂
  simp only [pantsGlue_def, Category.id_comp, h₁, h₂, Category.assoc]
  rw [← Category.assoc]
  -- naturality of the associator, applied with `congrArg` for the reason given in `pantsGlue_assoc`
  refine (congrArg (· ≫ _) (Path.pathHmul_pathHmul_comp_loopTransAssoc D₁ D₂ D₃).symm).trans ?_
  rw [Category.assoc, Path.loopTransAssoc_refl]
  simp

/-- **Gluing caps along the two decompositions of a four-holed sphere.** Let a four-holed sphere
with inputs `γ₁`, `γ₂`, `γ₃` and output `γ₀` be cut in two ways into two pairs of pants: into
`P₁₂ : γ₀ ⟶ γ₁₂ ⬝ γ₃` and `Q₁₂ : γ₁₂ ⟶ γ₁ ⬝ γ₂` along a loop `γ₁₂` separating the first two
inputs, and into `P₂₃ : γ₀ ⟶ γ₁ ⬝ γ₂₃` and `Q₂₃ : γ₂₃ ⟶ γ₂ ⬝ γ₃` along a loop `γ₂₃` separating
the last two. That both are cuts of the same surface means that the composites
`P₁₂ ≫ (Q₁₂ ⋀ 𝟙)` and `P₂₃ ≫ (𝟙 ⋀ Q₂₃)` agree after the associator
`γ₁ ⬝ (γ₂ ⬝ γ₃) ⟶ (γ₁ ⬝ γ₂) ⬝ γ₃`. Then gluing caps of the three inputs gives the same cap of the
output along both decompositions. -/
theorem pantsGlue_assoc (P₁₂ : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁₂.trans γ₃⟩)
    (Q₁₂ : (⟨γ₁₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (P₂₃ : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂₃⟩)
    (Q₂₃ : (⟨γ₂₃⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (h : P₂₃ ≫ HSpace.pathHmul (𝟙 _) Q₂₃ ≫ Path.loopTransAssoc γ₁ γ₂ γ₃ =
      P₁₂ ≫ HSpace.pathHmul Q₁₂ (𝟙 _))
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) (D₃ : RawCap γ₃) :
    pantsGlue P₁₂ (pantsGlue Q₁₂ D₁ D₂) D₃ = pantsGlue P₂₃ D₁ (pantsGlue Q₂₃ D₂ D₃) := by
  -- The groupoid objects here are written both as `γ ⬝ γ'` and as the H-space product `γ ⋀ γ'`,
  -- which is `γ ⬝ γ'` by definition of the H-space structure of the loop space; `rw` does not
  -- match across the two spellings, so the three-cap identity is applied with `congrArg`, and
  -- the trailing identity it leaves on the right is removed by `Category.comp_id` in a term.
  have key := congrArg (P₂₃ ≫ HSpace.pathHmul (𝟙 _) Q₂₃ ≫ ·)
    (loopTransAssoc_comp_pantsGlue_pantsGlue D₁ D₂ D₃)
  simp only [comp_pantsGlue, Category.comp_id] at key
  rw [pantsGlue_pantsGlue_left, pantsGlue_pantsGlue_right, ← h]
  exact key.trans (congrArg (pantsGlue · D₁ _) (congrArg (P₂₃ ≫ ·) (Category.comp_id _)))

end RawCap

end Raw

section Spherical

variable {X : Type} [TopologicalSpace X] {x : X}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

namespace SphericalCapClass

variable {γ₀ γ₁ γ₂ γ₃ γ₁₂ γ₂₃ : Ω X x}

/-- **Gluing cap classes along the two decompositions of a four-holed sphere** gives the same cap
class of the output (`TauCeti.Floer.RawCap.pantsGlue_assoc` on representatives). -/
theorem pantsGlue_assoc (P₁₂ : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁₂.trans γ₃⟩)
    (Q₁₂ : (⟨γ₁₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (P₂₃ : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂₃⟩)
    (Q₂₃ : (⟨γ₂₃⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (h : P₂₃ ≫ HSpace.pathHmul (𝟙 _) Q₂₃ ≫ Path.loopTransAssoc γ₁ γ₂ γ₃ =
      P₁₂ ≫ HSpace.pathHmul Q₁₂ (𝟙 _))
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) :
    pantsGlue P₁₂ (pantsGlue Q₁₂ q₁ q₂) q₃ = pantsGlue P₂₃ q₁ (pantsGlue Q₂₃ q₂ q₃) := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with | h D₂ =>
  induction q₃ using induction_on with
  | h D₃ => simp only [pantsGlue_mk, RawCap.pantsGlue_assoc P₁₂ Q₁₂ P₂₃ Q₂₃ h]

/-- **The classes of the two broken configurations of a four-holed sphere have the same sum.**
For the two decompositions of a four-holed sphere into pairs of pants, as in
`TauCeti.Floer.SphericalCapClass.pantsGlue_assoc`, and any cap classes of the three inputs, of
the output and of the two separating loops, the class of the outer pair of pants plus the class
of the inner one is the same for both decompositions: the intermediate caps cancel and the glued
output caps agree. -/
theorem productClass_pantsGlue_add_productClass_pantsGlue [PathConnectedSpace X]
    [Nonempty (RawCap γ₀)] [Nonempty (RawCap γ₁₂)] [Nonempty (RawCap γ₂₃)]
    (P₁₂ : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁₂.trans γ₃⟩)
    (Q₁₂ : (⟨γ₁₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (P₂₃ : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂₃⟩)
    (Q₂₃ : (⟨γ₂₃⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂.trans γ₃⟩)
    (h : P₂₃ ≫ HSpace.pathHmul (𝟙 _) Q₂₃ ≫ Path.loopTransAssoc γ₁ γ₂ γ₃ =
      P₁₂ ≫ HSpace.pathHmul Q₁₂ (𝟙 _))
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂)
    (q₃ : SphericalCapClass ω c γ₃) (q₁₂ : SphericalCapClass ω c γ₁₂)
    (q₂₃ : SphericalCapClass ω c γ₂₃) (q₀ : SphericalCapClass ω c γ₀) :
    productClass (ω := ω.comp (sphericalClasses X 1).subtype)
        (c := c.comp (sphericalClasses X 1).subtype) (pantsGlue P₁₂) q₁₂ q₃ q₀ +
      productClass (ω := ω.comp (sphericalClasses X 1).subtype)
        (c := c.comp (sphericalClasses X 1).subtype) (pantsGlue Q₁₂) q₁ q₂ q₁₂ =
    productClass (ω := ω.comp (sphericalClasses X 1).subtype)
        (c := c.comp (sphericalClasses X 1).subtype) (pantsGlue P₂₃) q₁ q₂₃ q₀ +
      productClass (ω := ω.comp (sphericalClasses X 1).subtype)
        (c := c.comp (sphericalClasses X 1).subtype) (pantsGlue Q₂₃) q₂ q₃ q₂₃ :=
  (productClass_add_eq_add_iff (pantsGlue Q₁₂) (pantsGlue P₁₂) (pantsGlue Q₂₃) (pantsGlue P₂₃)
    (fun g q₁₂ q₃ => pantsGlue_vadd_left P₁₂ g q₁₂ q₃)
    (fun g q₁ q₂₃ => pantsGlue_vadd_right P₂₃ g q₁ q₂₃) q₁ q₂ q₃ q₁₂ q₂₃ q₀).2
    (pantsGlue_assoc P₁₂ Q₁₂ P₂₃ Q₂₃ h q₁ q₂ q₃)

end SphericalCapClass

end Spherical

end TauCeti.Floer
