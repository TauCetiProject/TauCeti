/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic

/-!
# Lifts to the generic point of the genus-two equation

Let `μ` be the generic point of the genus-two equation `[x₁, y₁][x₂, y₂] = 1` over a group `G`,
with solutions in a group `H` receiving the coefficients through `ι : G →* H`.

* The equation `z = x₁ y₁` has the lift `z = x₁ y₁`.
* Over a nontrivial `H`, `x₁` is nontrivial at the generic point, as the point `(a, 1, 1, 1)` with
  `a ≠ 1` is a solution, while the trivial solution kills it. So `z = x₁` is a lift of
  `[z, x₁] = 1 ∧ z ≠ 1` whose specialization at the trivial solution does not satisfy `z ≠ 1`: a
  lift of a system with an inequation need not specialize to a solution at every solution of the
  system.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.4 (the radical and the coordinate group) and §6, Definitions 24–27 (lifts to a
  generic point).
-/

open Monoid.Coprod TauCeti.GroupAlgGeom TauCeti.GroupAlgGeom.Lift TauCeti.GroupAlgGeom.Quadratic
open scoped commutatorElement

variable {G H X : Type*} [Group G] [Group H] (ι : G →* H) {x y : Fin 2 → X}
  (inj : (Sum.elim x y).Injective)

/-- For the genus-two equation `[x₁, y₁][x₂, y₂] = 1`, the equation `z = x₁ y₁` has the lift
`z = x₁ y₁`. -/
example : HasLift ι {(Standard.orientable 2 Nat.two_pos x y inj).toWord}
    {(inr (FreeGroup.of (Sum.inr ())) : GX G (X ⊕ Unit)) *
      (inr (FreeGroup.of (Sum.inl (x 0))) * inr (FreeGroup.of (Sum.inl (y 0))))⁻¹} := by
  have h := hasLift_range_mul_inv ι {(Standard.orientable 2 Nat.two_pos x y inj).toWord}
    fun _ : Unit => (inr (FreeGroup.of (x 0)) * inr (FreeGroup.of (y 0)) : GX G X)
  simp only [Set.range_unique, PUnit.default_eq_unit, _root_.map_mul, map_apply_inr,
    FreeGroup.map.of] at h
  exact h

/-- For the genus-two equation `[x₁, y₁][x₂, y₂] = 1` over a nontrivial group, with generic point
`μ`: the trivial point is a solution, at which `x₁ = 1`; the system `[z, x₁] = 1 ∧ z ≠ 1` is
compatible, also over that solution; and `z = x₁` is a lift, as the point `(μ, z = μ x₁)` solves
`[z, x₁] = 1` and `μ x₁ ≠ 1`. -/
example [Nontrivial H] :
    let S : Set (GX G X) := {(Standard.orientable 2 Nat.two_pos x y inj).toWord}
    let μ := CoordGroup.genericPoint ι S
    (1 : X → H) ∈ V ι S ∧
      IsCompatibleNe ι S
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX G (X ⊕ Unit)), inr (FreeGroup.of (Sum.inl (x 0)))⁆}
        (inr (FreeGroup.of (Sum.inr ()))) ∧
      Sum.elim μ (fun _ : Unit => μ (x 0)) ∈ V (CoordGroup.coeff ι S)
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX G (X ⊕ Unit)),
          inr (FreeGroup.of (Sum.inl (x 0)))⁆} ∧
      eval (CoordGroup.coeff ι S) (Sum.elim μ (fun _ : Unit => μ (x 0)))
        (inr (FreeGroup.of (Sum.inr ()))) ≠ 1 := by
  classical
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  -- The point `(h, 1, 1, 1)` is a solution: the values of `Pi.mulSingle (x 0) h` commute.
  have hv : Pi.mulSingle (x 0) h ∈ V ι {(Standard.orientable 2 Nat.two_pos x y inj).toWord} :=
    Standard.mem_V_orientable_of_commute ι Nat.two_pos inj fun i => by
      simp only [Pi.mulSingle_apply]
      split_ifs <;> simp
  refine ⟨Standard.one_mem_V_orientable ι Nat.two_pos inj, isCompatibleNe_commutator_iff.2 ‹_›,
    mem_V_commutator_iff.2 (by simp), ?_⟩
  simpa using CoordGroup.genericPoint_ne_one_iff.2 ⟨_, hv, by simpa using hh⟩
