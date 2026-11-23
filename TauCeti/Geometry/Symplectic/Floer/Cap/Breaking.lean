/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Bubbling
public import TauCeti.Geometry.Symplectic.Floer.Cap.Cylinder

/-!
# Cap classes add under Floer breaking

Let `X` be a path-connected space with a base point `x`, and let `ω`, `c` be homomorphisms on
`H₂(X; ℤ)`, for the symplectic area and the first Chern number. A homotopy of loops
`p : γ₀ ⟶ γ₁` in the fundamental groupoid of the loop space `Ω X x` is a cylinder with output
`γ₀` and input `γ₁`; gluing cap classes of `γ₁` to it is
`TauCeti.Floer.SphericalCapClass.glue p`, and its class relative to cap classes `q₁` of the input
and `q₀` of the output is `TauCeti.Floer.cylinderClass (glue p) q₁ q₀`, the class
`A = D₀ + u − D₁` of the sphere by which `q₀` differs from the glued cap
(`TauCeti.Floer.SphericalCapClass.cylinderClass_glue_mk`). A pair of pants `P : γ₀ ⟶ γ₁ ⬝ γ₂`
has the class `TauCeti.Floer.productClass (pantsGlue P) q₁ q₂ q₀`.

This file proves that these classes add up under every way a cylinder or a pair of pants breaks
at an orbit, whatever cap class is chosen at the orbit where it breaks:

* **a cylinder breaks into two cylinders**: for `p : γ₀ ⟶ γ'` and `p' : γ' ⟶ γ₁`, the class of
  `p ≫ p'` is the class of `p` plus the class of `p'`
  (`TauCeti.Floer.SphericalCapClass.cylinderClass_glue_comp`);
* **a pair of pants breaks off a cylinder at its output**: the class of `p ≫ P` is the class of
  the cylinder `p` plus the class of the pair of pants `P`
  (`TauCeti.Floer.SphericalCapClass.productClass_pantsGlue_comp`);
* **a pair of pants breaks off cylinders at its inputs**: for cylinders `p₁ : γ₁ ⟶ γ₁'` and
  `p₂ : γ₂ ⟶ γ₂'` into the inputs of `P`, placed side by side as `HSpace.pathHmul p₁ p₂`, the
  class of `P ≫ (p₁ ⋀ p₂)` is the class of `P` plus the classes of `p₁` and `p₂`
  (`TauCeti.Floer.SphericalCapClass.productClass_pantsGlue_comp_pathHmul`);
* **a cylinder bubbles off a sphere**: gluing a sphere `a` to a cylinder adds the class of `a` to
  its class (`TauCeti.Floer.SphericalCapClass.cylinderClass_glue_insertSphere`), as
  `TauCeti.Floer.SphericalCapClass.productClass_pantsGlue_insertSphere` does for a pair of pants.

The class of a configuration therefore determines the classes of the pieces it breaks into only
up to their sum: this is the bookkeeping that makes the boundary of a one-dimensional moduli space
in class `A` the union of the broken configurations with classes summing to `A`, and the
symplectic area and first Chern number of `A`, which give its energy and index, additive under
breaking. A PSS plane is a cap of its orbit, and its breaking off a cylinder is the change of caps
`TauCeti.Floer.cylinderClass_eq_add_sub`. These are statements about homotopy classes; no moduli
space or convergence theorem is used.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, the chapters on Floer homology.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy HSpaces

namespace TauCeti.Floer.SphericalCapClass

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}
  {γ₀ γ₁ γ₂ : Ω X x}

/-- The class `A = D₀ + u − D₁` of a cylinder `p : γ₀ ⟶ γ₁` relative to caps `D₁` of its input
and `D₀` of its output is the class of the sphere `D₀ -ᵥ (p ≫ D₁)` by which the output cap
differs from the glued cap. -/
@[simp]
theorem cylinderClass_glue_mk [Nonempty (RawCap γ₀)]
    (p : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁⟩) (D₁ : RawCap γ₁) (D₀ : RawCap γ₀) :
    (cylinderClass (glue p) (mk ω c D₁) (mk ω c D₀) : SphericalPeriodGroup ω c) =
      SphericalPeriodGroup.ofHomotopyGroup ω c x (D₀ -ᵥ (p ≫ D₁ : RawCap γ₀)) := by
  rw [cylinderClass_def, glue_mk, mk_vsub_mk]

/-- **A cylinder breaks into two cylinders.** The class of the composite `p ≫ p'` of cylinders
`p : γ₀ ⟶ γ'` and `p' : γ' ⟶ γ₁` is the class of `p` plus the class of `p'`, for any cap class
`q'` of the intermediate loop `γ'`. -/
theorem cylinderClass_glue_comp {γ' : Ω X x} [Nonempty (RawCap γ')] [Nonempty (RawCap γ₀)]
    (p : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ'⟩)
    (p' : (⟨γ'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁⟩) (q₁ : SphericalCapClass ω c γ₁)
    (q' : SphericalCapClass ω c γ') (q₀ : SphericalCapClass ω c γ₀) :
    (cylinderClass (glue (p ≫ p')) q₁ q₀ : SphericalPeriodGroup ω c) =
      cylinderClass (glue p) q' q₀ + cylinderClass (glue p') q₁ q' := by
  rw [← cylinderClass_comp (glue p') (glue p) (glue_vadd p) q₁ q' q₀]
  simp only [← glue_comp]

/-- **A pair of pants breaks off a cylinder at its output.** The class of the composite `p ≫ P`
of a cylinder `p : γ₀ ⟶ γ₀'` and a pair of pants `P : γ₀' ⟶ γ₁ ⬝ γ₂` is the class of `p` plus
the class of `P`, for any cap class `q₀'` of the intermediate loop `γ₀'`. -/
theorem productClass_pantsGlue_comp {γ₀' : Ω X x} [Nonempty (RawCap γ₀')] [Nonempty (RawCap γ₀)]
    (p : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₀'⟩)
    (P : (⟨γ₀'⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₀' : SphericalCapClass ω c γ₀')
    (q₀ : SphericalCapClass ω c γ₀) :
    (productClass (pantsGlue (p ≫ P)) q₁ q₂ q₀ : SphericalPeriodGroup ω c) =
      cylinderClass (glue p) q₀' q₀ + productClass (pantsGlue P) q₁ q₂ q₀' := by
  rw [← productClass_comp_out (pantsGlue P) (glue p) (glue_vadd p) q₁ q₂ q₀' q₀]
  simp only [glue_pantsGlue]

/-- **A pair of pants breaks off cylinders at its inputs.** The class of the pair of pants
`P ≫ (p₁ ⋀ p₂)` obtained from `P : γ₀ ⟶ γ₁ ⬝ γ₂` and cylinders `p₁ : γ₁ ⟶ γ₁'` and
`p₂ : γ₂ ⟶ γ₂'` into its inputs is the class of `P` plus the classes of `p₁` and `p₂`, for any cap
classes `q₁` and `q₂` of the intermediate loops `γ₁` and `γ₂`. Breaking at a single input is the
case of the identity cylinder at the other, whose class vanishes for equal caps. -/
theorem productClass_pantsGlue_comp_pathHmul {γ₁' γ₂' : Ω X x} [Nonempty (RawCap γ₁)]
    [Nonempty (RawCap γ₂)] [Nonempty (RawCap γ₀)]
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (p₁ : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁'⟩)
    (p₂ : (⟨γ₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂'⟩) (q₁' : SphericalCapClass ω c γ₁')
    (q₂' : SphericalCapClass ω c γ₂') (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₀ : SphericalCapClass ω c γ₀) :
    (productClass (pantsGlue (P ≫ HSpace.pathHmul p₁ p₂)) q₁' q₂' q₀ :
        SphericalPeriodGroup ω c) =
      productClass (pantsGlue P) q₁ q₂ q₀ + cylinderClass (glue p₁) q₁' q₁ +
        cylinderClass (glue p₂) q₂' q₂ := by
  rw [← productClass_comp_in (glue p₁) (glue p₂) (pantsGlue P) (pantsGlue_vadd_left P)
    (pantsGlue_vadd_right P) q₁' q₂' q₁ q₂ q₀]
  simp only [pantsGlue_glue_glue]

/-- **Classes split off with sphere bubbles on cylinders.** The class of a cylinder
`p : γ₀ ⟶ γ₁` relative to cap classes `q₁` of its input and `q₀` of its output increases by the
class of a sphere `a` glued to `p` in the spherical period group. -/
@[simp]
theorem cylinderClass_glue_insertSphere [Nonempty (RawCap γ₀)] (a : Additive (π_ 2 X x))
    (p : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁⟩) (q₁ : SphericalCapClass ω c γ₁)
    (q₀ : SphericalCapClass ω c γ₀) :
    (cylinderClass (glue (insertSphere a p)) q₁ q₀ : SphericalPeriodGroup ω c) =
      cylinderClass (glue p) q₁ q₀ + SphericalPeriodGroup.ofHomotopyGroup ω c x a := by
  rw [cylinderClass_eq_sub_of_eq_vadd (glue_insertSphere a p q₁) q₀, sub_neg_eq_add]

end TauCeti.Floer.SphericalCapClass
