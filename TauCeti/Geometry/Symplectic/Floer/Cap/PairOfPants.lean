/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.HSpace
public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop

/-!
# Gluing caps along a pair of pants

Let `γ₁`, `γ₂` and `γ₀` be loops in a space `X` based at `x`. A *pair of pants* with inputs `γ₁`,
`γ₂` and output `γ₀`, with its two seams at `x`, is a homotopy of loops from `γ₀` to the
concatenation `γ₁ ⬝ γ₂`: cutting a pair of pants along two seams from the output boundary to the
input boundaries gives a square, whose bottom edge runs along `γ₀`, whose top edge runs along
`γ₁` and then `γ₂`, and whose sides are the seams. Its homotopy class relative to the boundary is a
morphism `P : γ₀ ⟶ γ₁ ⬝ γ₂` in the fundamental groupoid of the loop space `Ω X x`.

Caps of the inputs glue to the pair of pants and give a cap of the output. A raw cap `D` of `γ` is
a morphism `γ ⟶ c` to the constant loop `c` (`TauCeti.Floer.RawCap`). Placing caps `D₁` and `D₂`
of the inputs side by side is the product `D₁ ⋀ D₂ : γ₁ ⬝ γ₂ ⟶ c ⬝ c` of path classes in the
H-space `Ω X x` (`HSpace.pathHmul`), and the glued cap is

`RawCap.pantsGlue P D₁ D₂ = P ≫ (D₁ ⋀ D₂) ≫ (c ⬝ c = c)`.

Gluing a sphere at the centre of an input cap glues the same sphere at the centre of the output
cap (`TauCeti.Floer.RawCap.pantsGlue_vadd_left`, `TauCeti.Floer.RawCap.pantsGlue_vadd_right`).
This is the unit law of the H-space `Ω X x` on loops of loops at the constant loop
(`HSpace.pathHmul_id_right_comp_eqToHom`, `HSpace.pathHmul_id_left_comp_eqToHom`): placing the
constant disc beside a sphere does not change the sphere. Gluing is natural in the three boundary
loops: a homotopy of loops at the output composes with the pair of pants
(`TauCeti.Floer.RawCap.comp_pantsGlue`), and homotopies of loops at the inputs compose with it
through their product (`TauCeti.Floer.RawCap.pantsGlue_comp_comp`).

The equivariance descends to the cap classes of `TauCeti.Floer.SphericalCapClass`, the raw caps
modulo spheres of zero area and zero first Chern number. On a path-connected space,
`TauCeti.Floer.SphericalCapClass.pantsGlue P` is equivariant in each input under the spherical
period group `Γ`. So it is a gluing map of the kind that the cap-class API of
`TauCeti.Geometry.Symplectic.Floer.Cap.Basic` takes as input. In particular the class
`A = D₀ + u - D₁ - D₂ ∈ Γ` of the pair of pants `u = P` relative to caps `D₁`, `D₂`, `D₀`, which is
`TauCeti.Floer.productClass (SphericalCapClass.pantsGlue P) D₁ D₂ D₀`, obeys the change of
reference caps, and the topological energy `A₁(D₁) + A₂(D₂) - A₀(D₀) + ω(A)` of a pair of pants
does not depend on the caps. These are `TauCeti.Floer.productClass_eq_add_sub` and
`TauCeti.Floer.add_sub_add_map_productClass_eq` applied to the equivariance laws
`TauCeti.Floer.SphericalCapClass.pantsGlue_vadd_left P` and
`TauCeti.Floer.SphericalCapClass.pantsGlue_vadd_right P`.

The three loops share the base point `x`, which is where the two seams of the pair of pants
start and end. Orbits with different base points are brought to this form by conjugating the input
loops along paths to the base point of the output; the corresponding transport of caps is not
treated here.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on capped loops.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the classes of pairs of pants relative to caps of their boundary orbits.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy HSpaces

namespace TauCeti.Floer

section Raw

variable {X : Type*} [TopologicalSpace X] {x : X}

namespace RawCap

variable {γ₀ γ₁ γ₂ : Ω X x}

/-- **Gluing caps along a pair of pants.** For a pair of pants `P : γ₀ ⟶ γ₁ ⬝ γ₂`, a homotopy
class of homotopies of loops from the output `γ₀` to the concatenation of the inputs, and raw caps
`D₁` of `γ₁` and `D₂` of `γ₂`, the raw cap of `γ₀` obtained by placing `D₁` and `D₂` side by side
on top of `P`. -/
def pantsGlue (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) : RawCap γ₀ :=
  P ≫ HSpace.pathHmul D₁ D₂ ≫ eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e)

theorem pantsGlue_def (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    pantsGlue P D₁ D₂ =
      P ≫ HSpace.pathHmul D₁ D₂ ≫ eqToHom (congrArg FundamentalGroupoid.mk HSpace.hmul_e_e) :=
  (rfl)

/-- **Recapping the first input recaps the glued cap**: gluing a sphere at the centre of the first
input cap glues the same sphere at the centre of the glued cap. -/
@[simp]
theorem pantsGlue_vadd_left (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (a : Additive (π_ 2 X x)) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    pantsGlue P (a +ᵥ D₁) D₂ = a +ᵥ pantsGlue P D₁ D₂ := by
  have h := HSpace.pathHmul_comp D₁ (fundamentalGroupLoopSpaceMulEquiv.symm a.toMul).asHom D₂
    (𝟙 _)
  rw [Category.comp_id] at h
  rw [pantsGlue_def, pantsGlue_def, vadd_def, vadd_def, h]
  simp only [Category.assoc]
  exact congrArg (P ≫ HSpace.pathHmul D₁ D₂ ≫ ·) (HSpace.pathHmul_id_right_comp_eqToHom _)

/-- **Recapping the second input recaps the glued cap**: gluing a sphere at the centre of the
second input cap glues the same sphere at the centre of the glued cap. -/
@[simp]
theorem pantsGlue_vadd_right (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (a : Additive (π_ 2 X x)) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    pantsGlue P D₁ (a +ᵥ D₂) = a +ᵥ pantsGlue P D₁ D₂ := by
  have h := HSpace.pathHmul_comp D₁ (𝟙 _) D₂
    (fundamentalGroupLoopSpaceMulEquiv.symm a.toMul).asHom
  rw [Category.comp_id] at h
  rw [pantsGlue_def, pantsGlue_def, vadd_def, vadd_def, h]
  simp only [Category.assoc]
  exact congrArg (P ≫ HSpace.pathHmul D₁ D₂ ≫ ·) (HSpace.pathHmul_id_left_comp_eqToHom _)

/-- Gluing a homotopy of loops `p` from `γ₀'` to the output `γ₀` to a glued cap is gluing caps
along the composite pair of pants `p ≫ P`. -/
@[simp]
theorem comp_pantsGlue {γ₀' : Ω X x} (p : (⟨γ₀'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₀⟩)
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) : p ≫ pantsGlue P D₁ D₂ = pantsGlue (p ≫ P) D₁ D₂ := by
  simp only [pantsGlue_def, Category.assoc]

/-- Gluing caps glued to homotopies of loops `p₁` and `p₂` at the inputs is gluing caps along
the pair of pants `P` followed by the product `p₁ ⋀ p₂` of the homotopies. -/
theorem pantsGlue_comp_comp {γ₁' γ₂' : Ω X x}
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (p₁ : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁'⟩)
    (p₂ : (⟨γ₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂'⟩) (D₁ : RawCap γ₁') (D₂ : RawCap γ₂') :
    pantsGlue P (p₁ ≫ D₁) (p₂ ≫ D₂) = pantsGlue (P ≫ HSpace.pathHmul p₁ p₂) D₁ D₂ := by
  simp only [pantsGlue_def, HSpace.pathHmul_comp, Category.assoc]

/-- Changing the first input cap changes the glued cap by the same sphere. -/
@[simp]
theorem pantsGlue_vsub_pantsGlue_left
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (D₁' D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) : pantsGlue P D₁' D₂ -ᵥ pantsGlue P D₁ D₂ = D₁' -ᵥ D₁ := by
  have : Nonempty (RawCap γ₁) := ⟨D₁⟩
  have : Nonempty (RawCap γ₀) := ⟨pantsGlue P D₁ D₂⟩
  rw [← vsub_vadd D₁' D₁, pantsGlue_vadd_left, vadd_vsub, vsub_vadd]

/-- Changing the second input cap changes the glued cap by the same sphere. -/
@[simp]
theorem pantsGlue_vsub_pantsGlue_right
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (D₁ : RawCap γ₁)
    (D₂' D₂ : RawCap γ₂) : pantsGlue P D₁ D₂' -ᵥ pantsGlue P D₁ D₂ = D₂' -ᵥ D₂ := by
  have : Nonempty (RawCap γ₂) := ⟨D₂⟩
  have : Nonempty (RawCap γ₀) := ⟨pantsGlue P D₁ D₂⟩
  rw [← vsub_vadd D₂' D₂, pantsGlue_vadd_right, vadd_vsub, vsub_vadd]

end RawCap

end Raw

section Spherical

variable {X : Type} [TopologicalSpace X] {x : X}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

namespace SphericalCapClass

variable {γ₀ γ₁ γ₂ : Ω X x}

/-- **Gluing cap classes along a pair of pants** `P : γ₀ ⟶ γ₁ ⬝ γ₂`, computed on representatives
by `TauCeti.Floer.RawCap.pantsGlue`. -/
def pantsGlue (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) :
    SphericalCapClass ω c γ₁ → SphericalCapClass ω c γ₂ → SphericalCapClass ω c γ₀ :=
  Quotient.map₂ (sa := AddAction.orbitRel _ _) (sb := AddAction.orbitRel _ _)
    (sc := AddAction.orbitRel _ _) (RawCap.pantsGlue P)
    fun _ _ ⟨k₁, hk₁⟩ _ _ ⟨k₂, hk₂⟩ =>
      ⟨k₁ + k₂, by
        simp only [← hk₁, ← hk₂, AddSubgroup.vadd_def, RawCap.pantsGlue_vadd_left,
          RawCap.pantsGlue_vadd_right, add_vadd, add_comm (k₁ : _)]⟩

@[simp]
theorem pantsGlue_mk (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    pantsGlue P (mk ω c D₁) (mk ω c D₂) = mk ω c (RawCap.pantsGlue P D₁ D₂) := by
  rw [mk_def, mk_def, mk_def]
  rfl

/-- Gluing a homotopy of loops at the output to a glued cap class is gluing along the composite
pair of pants. -/
@[simp]
theorem glue_pantsGlue {γ₀' : Ω X x} (p : (⟨γ₀'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₀⟩)
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) : glue p (pantsGlue P q₁ q₂) = pantsGlue (p ≫ P) q₁ q₂ := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with
  | h D₂ => rw [pantsGlue_mk, pantsGlue_mk, glue_mk, RawCap.comp_pantsGlue]

/-- Gluing cap classes glued to homotopies of loops `p₁` and `p₂` at the inputs is gluing along
the pair of pants followed by the product `p₁ ⋀ p₂` of the homotopies. -/
theorem pantsGlue_glue_glue {γ₁' γ₂' : Ω X x}
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (p₁ : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁'⟩)
    (p₂ : (⟨γ₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂'⟩) (q₁ : SphericalCapClass ω c γ₁')
    (q₂ : SphericalCapClass ω c γ₂') :
    pantsGlue P (glue p₁ q₁) (glue p₂ q₂) = pantsGlue (P ≫ HSpace.pathHmul p₁ p₂) q₁ q₂ := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with
  | h D₂ => rw [glue_mk, glue_mk, pantsGlue_mk, pantsGlue_mk, RawCap.pantsGlue_comp_comp]

variable [PathConnectedSpace X]

/-- **Gluing cap classes is equivariant in the first input** under the spherical period group:
recapping the first input by `g` recaps the glued cap class by `g`. -/
@[simp]
theorem pantsGlue_vadd_left (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (g : SphericalPeriodGroup ω c) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) : pantsGlue P (g +ᵥ q₁) q₂ = g +ᵥ pantsGlue P q₁ q₂ := by
  obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with
  | h D₂ => rw [ofHomotopyGroup_vadd_mk, pantsGlue_mk, pantsGlue_mk, ofHomotopyGroup_vadd_mk,
      RawCap.pantsGlue_vadd_left]

/-- **Gluing cap classes is equivariant in the second input** under the spherical period group:
recapping the second input by `g` recaps the glued cap class by `g`. -/
@[simp]
theorem pantsGlue_vadd_right (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (g : SphericalPeriodGroup ω c) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) : pantsGlue P q₁ (g +ᵥ q₂) = g +ᵥ pantsGlue P q₁ q₂ := by
  obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with
  | h D₂ => rw [ofHomotopyGroup_vadd_mk, pantsGlue_mk, pantsGlue_mk, ofHomotopyGroup_vadd_mk,
      RawCap.pantsGlue_vadd_right]

end SphericalCapClass

end Spherical

end TauCeti.Floer
