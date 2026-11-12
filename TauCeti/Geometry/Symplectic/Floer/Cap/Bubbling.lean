/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.PairOfPants

/-!
# Spheres glued to cylinders and pairs of pants

Let `X` be a space with a base point `x`. A homotopy of loops `p : γ₁ ⟶ γ₂` in the fundamental
groupoid of the loop space `Ω X x` is a cylinder whose seam stays at `x`; when `γ₂ = γ ⬝ γ'` it is
a pair of pants with inputs `γ`, `γ'` and output `γ₁`. A sphere `a ∈ π₂(X, x)` is a loop of loops
at the constant loop (`HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv`). Concatenating it
pointwise with `p` in the loop space, `s ↦ a_s ⬝ p_s`, and reading the result back through the left
unit homotopy of `Ω X x` gives a homotopy of loops with the same ends,
`TauCeti.Floer.insertSphere a p` (`HSpace.loopHmul`): the cylinder or pair of pants with the sphere
`a` glued to it. This models the topological type of a configuration in which a sphere bubble
has split off at an interior point of a Floer cylinder or pair of pants, the degeneration in which
a sequence of Floer solutions loses the energy of a sphere.

Inserting spheres is an action of `π₂(X, x)` (`TauCeti.Floer.insertSphere_zero`,
`TauCeti.Floer.insertSphere_add`) commuting with composition of homotopies of loops on both sides
(`TauCeti.Floer.insertSphere_comp`, `TauCeti.Floer.comp_insertSphere`). If the loop `γ₁` is
contractible, any two homotopies of loops from `γ₁` to `γ₂` differ by a unique sphere
(`TauCeti.Floer.existsUnique_insertSphere_eq`), because inserting a sphere is conjugation along any
cap of `γ₁` (`HSpace.loopHmul_eq_comp_comp_inv_comp`).

For caps, the class bookkeeping is the following.

* On a raw cap, a homotopy of loops from `γ` to the constant loop, inserting a sphere is gluing it
  at the centre of the cap (`TauCeti.Floer.RawCap.insertSphere_eq_vadd`).
* Gluing a cap to a cylinder with a sphere glued to it, or caps to a pair of pants with a sphere
  glued to it, recaps the glued cap by that sphere
  (`TauCeti.Floer.RawCap.insertSphere_comp_eq_vadd`, `TauCeti.Floer.RawCap.pantsGlue_insertSphere`),
  and the same holds for cap classes, with the class of the sphere in the spherical period group
  (`TauCeti.Floer.SphericalCapClass.glue_insertSphere`,
  `TauCeti.Floer.SphericalCapClass.pantsGlue_insertSphere`).
* Consequently the product class `A = D₀ + u - D₁ - D₂` of a pair of pants relative to cap classes
  of its ends changes by the class of the sphere glued to it
  (`TauCeti.Floer.SphericalCapClass.productClass_pantsGlue_insertSphere`). Together with the
  equivariance of gluing in each input (bubbling at the centre of an input cap) and the sewing laws
  of `TauCeti.Geometry.Symplectic.Floer.Cap.Sewing` (breaking at an end), this covers the
  additivity of classes under the degenerations of a pair of pants into pieces.

The sign comes from the conventions of the cap torsor: the product class is the output cap minus
the glued cap (`TauCeti.Floer.productClass`), and the inserted sphere recaps the glued cap, so it
enters the product class with a minus sign.

These are statements about homotopy classes; no moduli space, energy or compactness theorem is
used, and the identification of a geometric bubble tree with the sphere inserted here is not
proved.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Chapter 4 (bubbling and the additivity of homology
  classes under Gromov convergence).
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  classes of pairs of pants relative to caps of their boundary orbits.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy HSpaces

namespace TauCeti.Floer

section Raw

variable {X : Type*} [TopologicalSpace X] {x : X} {γ γ₀ γ₁ γ₂ : Ω X x}

/-- **Gluing a sphere to a homotopy of loops.** For a sphere `a ∈ π₂(X, x)` and a homotopy class
`p` of homotopies of loops from `γ₁` to `γ₂`, the class of the pointwise concatenation
`s ↦ a_s ⬝ p_s` of the loop of loops `a` at the constant loop with `p`, read back as a homotopy of
loops from `γ₁` to `γ₂` through the left unit homotopy of the loop space. -/
def insertSphere (a : Additive (π_ 2 X x)) (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩ :=
  HSpace.loopHmul (fundamentalGroupLoopSpaceMulEquiv.symm a.toMul).asHom p

theorem insertSphere_def (a : Additive (π_ 2 X x))
    (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    insertSphere a p = HSpace.loopHmul (fundamentalGroupLoopSpaceMulEquiv.symm a.toMul).asHom p :=
  (rfl)

/-- Gluing the trivial sphere does not change a homotopy of loops. -/
@[simp]
theorem insertSphere_zero (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    insertSphere 0 p = p := by
  rw [insertSphere_def, toMul_zero, _root_.map_one, End.one_asHom]
  -- the neutral element of the loop space is the constant loop
  exact HSpace.loopHmul_id p

/-- Gluing two spheres one after the other is gluing their sum. -/
theorem insertSphere_add (a b : Additive (π_ 2 X x))
    (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    insertSphere (a + b) p = insertSphere a (insertSphere b p) := by
  rw [insertSphere_def, insertSphere_def, insertSphere_def, HSpace.loopHmul_loopHmul, toMul_add,
    _root_.map_mul, End.mul_asHom]

/-- Gluing a sphere commutes with composing homotopies of loops on the right. -/
theorem insertSphere_comp (a : Additive (π_ 2 X x))
    (p : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁⟩)
    (q : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    insertSphere a (p ≫ q) = insertSphere a p ≫ q :=
  HSpace.loopHmul_comp _ p q

/-- Gluing a sphere commutes with composing homotopies of loops on the left. -/
theorem comp_insertSphere (a : Additive (π_ 2 X x))
    (p : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁⟩)
    (q : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    p ≫ insertSphere a q = insertSphere a (p ≫ q) :=
  HSpace.comp_loopHmul _ p q

/-- **Homotopies of loops out of a contractible loop differ by unique spheres.** If `γ₁` bounds a
disc, then for any two homotopy classes `p`, `p'` of homotopies of loops from `γ₁` to `γ₂`, for
instance two pairs of pants with the same inputs and output, there is exactly one sphere `a` with
`insertSphere a p = p'`. -/
theorem existsUnique_insertSphere_eq [Nonempty (RawCap γ₁)]
    (p p' : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    ∃! a : Additive (π_ 2 X x), insertSphere a p = p' := by
  obtain ⟨D⟩ := ‹Nonempty (RawCap γ₁)›
  -- Gluing a sphere is precomposition with the sphere conjugated by the cap `D`.
  have key (a : Additive (π_ 2 X x)) : insertSphere a p = p' ↔
      fundamentalGroupLoopSpaceMulEquiv.symm a.toMul = End.of (inv D ≫ p' ≫ inv p ≫ D) := by
    rw [insertSphere_def, HSpace.loopHmul_eq_comp_comp_inv_comp _ D, End.ext_iff]
    constructor
    · rintro h
      simp only [← h, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id, Category.comp_id,
        IsIso.inv_hom_id_assoc]
    · rintro h
      simp only [h, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨.ofMul (fundamentalGroupLoopSpaceMulEquiv (End.of (inv D ≫ p' ≫ inv p ≫ D))), ?_,
    fun a ha => ?_⟩
  · exact (key _).2 (by rw [toMul_ofMul, MulEquiv.symm_apply_apply])
  · rw [← (MulEquiv.symm_apply_eq _).1 ((key a).1 ha), ofMul_toMul]

namespace RawCap

/-- **On a cap, gluing a sphere is recapping.** Gluing a sphere to a raw cap, a homotopy of loops
from `γ` to the constant loop, is gluing it at the centre of the cap. -/
@[simp]
theorem insertSphere_eq_vadd (a : Additive (π_ 2 X x)) (D : RawCap γ) :
    insertSphere a D = a +ᵥ D := by
  rw [insertSphere_def, HSpace.loopHmul_eq_comp_loop, vadd_def]

/-- **A sphere glued to a cylinder recaps the glued cap.** Gluing a cap of `γ₂` to a homotopy of
loops from `γ₁` to `γ₂` with a sphere glued to it gives the glued cap, recapped by the sphere. -/
@[simp]
theorem insertSphere_comp_eq_vadd (a : Additive (π_ 2 X x))
    (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) (D : RawCap γ₂) :
    (insertSphere a p ≫ D : RawCap γ₁) = a +ᵥ (p ≫ D) := by
  rw [← insertSphere_comp, insertSphere_eq_vadd]

/-- **A sphere glued to a pair of pants recaps the glued cap.** Gluing caps of the inputs to a
pair of pants with a sphere glued to it gives the glued cap of the output, recapped by the
sphere. -/
@[simp]
theorem pantsGlue_insertSphere (a : Additive (π_ 2 X x))
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) : pantsGlue (insertSphere a P) D₁ D₂ = a +ᵥ pantsGlue P D₁ D₂ := by
  rw [pantsGlue_def, pantsGlue_def, ← insertSphere_comp, insertSphere_eq_vadd]

end RawCap

end Raw

section Spherical

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

namespace SphericalCapClass

variable {γ₀ γ₁ γ₂ : Ω X x}

/-- **A sphere glued to a cylinder recaps the glued cap class** by the class of the sphere in the
spherical period group. -/
@[simp]
theorem glue_insertSphere (a : Additive (π_ 2 X x))
    (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) (q : SphericalCapClass ω c γ₂) :
    glue (insertSphere a p) q = SphericalPeriodGroup.ofHomotopyGroup ω c x a +ᵥ glue p q := by
  induction q using induction_on with
  | h D => rw [glue_mk, glue_mk, ofHomotopyGroup_vadd_mk, RawCap.insertSphere_comp_eq_vadd]

/-- **A sphere glued to a pair of pants recaps the glued cap class** by the class of the sphere in
the spherical period group. -/
@[simp]
theorem pantsGlue_insertSphere (a : Additive (π_ 2 X x))
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) :
    pantsGlue (insertSphere a P) q₁ q₂ =
      SphericalPeriodGroup.ofHomotopyGroup ω c x a +ᵥ pantsGlue P q₁ q₂ := by
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with
  | h D₂ => rw [pantsGlue_mk, pantsGlue_mk, ofHomotopyGroup_vadd_mk, RawCap.pantsGlue_insertSphere]

/-- **Classes split off with sphere bubbles.** The product class `A = D₀ + u - D₁ - D₂` of a pair
of pants `u` with a sphere `a` glued to it, relative to cap classes of its inputs and output, is
the product class of `u` minus the class of `a` in the spherical period group. -/
theorem productClass_pantsGlue_insertSphere [Nonempty (RawCap γ₀)] (a : Additive (π_ 2 X x))
    (P : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (q₁ : SphericalCapClass ω c γ₁)
    (q₂ : SphericalCapClass ω c γ₂) (q₀ : SphericalCapClass ω c γ₀) :
    productClass (ω := ω.comp (sphericalClasses X 1).subtype)
        (c := c.comp (sphericalClasses X 1).subtype) (pantsGlue (insertSphere a P)) q₁ q₂ q₀ =
      productClass (ω := ω.comp (sphericalClasses X 1).subtype)
          (c := c.comp (sphericalClasses X 1).subtype) (pantsGlue P) q₁ q₂ q₀ -
        SphericalPeriodGroup.ofHomotopyGroup ω c x a := by
  rw [productClass_def, productClass_def, pantsGlue_insertSphere, vsub_vadd_eq_vsub_sub]

end SphericalCapClass

end Spherical

end TauCeti.Floer
