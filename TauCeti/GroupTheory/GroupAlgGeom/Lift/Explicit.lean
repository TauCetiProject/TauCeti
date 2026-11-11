/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic

/-!
# Explicit lifts to the generic point

Let `S ⊆ G[X]` be a system of equations over a group `G`, with solutions taken in a group `H`
receiving the coefficients through `ι : G →* H`, and let `μ : X → G_{R(S)}` be its generic
point, the tuple of the images of the variables in the coordinate group. This file treats the
systems whose lifts to `μ` can be written down explicitly.

A coordinate `μ x` is trivial exactly when `x` takes the value `1` at every solution of `S`
(`TauCeti.GroupAlgGeom.CoordGroup.genericPoint_eq_one_iff`). So the generic point is nontrivial
at a variable as soon as one solution is, even when other solutions kill it.

* The system `y = u_y(X)`, for words `u_y ∈ G[X]`, has the lift `y = u_y(μ)` over every system.
* The system `[y, x] = 1 ∧ y ≠ 1` is compatible with a system `S` exactly when `H` is nontrivial:
  over a solution with `x ≠ 1` take `y = x`, over one with `x = 1` any `y ≠ 1`. It admits an
  `S`-lift exactly when the coordinate group of `S` is nontrivial, `y = μ x` being a lift when
  `μ x ≠ 1`. So over the trivial coefficient group and a nontrivial `H`, it is compatible with
  the equation `x = 1` in one variable but has no lift to its generic point: the only solution
  is `x = 1`, so the coordinate group is trivial.

For the genus-two equation `[x₁, y₁][x₂, y₂] = 1` over a nontrivial group, `x₁` is nontrivial at
the generic point, as the point `(a, 1, 1, 1)` with `a ≠ 1` is a solution, while the trivial
solution kills it. So `z = x₁` is a lift of `[z, x₁] = 1 ∧ z ≠ 1` whose specialization at the
trivial solution does not satisfy `z ≠ 1`: a lift of a system with an inequation need not
specialize to a solution at every solution of `S`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.hasLift_range_mul_inv`: the system `y = u_y(X)` admits an `S`-lift
  for every system `S`.
* `TauCeti.GroupAlgGeom.Lift.isCompatibleNe_commutator_iff`: the system `[y, x] = 1 ∧ y ≠ 1` is
  compatible with a system if and only if the group of values is nontrivial.
* `TauCeti.GroupAlgGeom.Lift.hasLiftNe_commutator_iff`: the system `[y, x] = 1 ∧ y ≠ 1` admits an
  `S`-lift if and only if the coordinate group of `S` is nontrivial.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.4 (the radical and the coordinate group, pp. 5–6) and §6, Definitions 24–27
  (lifts to a generic point, pp. 66–67).
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

open Monoid.Coprod
open scoped commutatorElement

variable {G H X Y : Type*} [Group G] [Group H]

/-! ### Explicit lifts -/

/-- The equations `y = u_y(X)`, for words `u_y ∈ G[X]`, admit the lift `y = u_y` to the generic
point of every system. -/
theorem hasLift_range_mul_inv (ι : G →* H) (S : Set (GX G X)) (u : Y → GX G X) :
    HasLift ι S (Set.range fun y : Y => (inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) *
      (Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inl) (u y))⁻¹) :=
  hasLift_of_mem_V_inl (w := u) <| mem_V.2 fun _ ⟨y, hy⟩ => by simp [← hy]

private theorem exists_sumElim_commutator_iff {K : Type*} [Group K] {κ : G →* K} {p : X → K} {x : X}
    {y : Y} :
    (∃ w : Y → K, Sum.elim p w ∈
        V κ {⁅(inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)), inr (FreeGroup.of (Sum.inl x))⁆} ∧
      eval κ (Sum.elim p w) (inr (FreeGroup.of (Sum.inr y))) ≠ 1) ↔ Nontrivial K := by
  refine ⟨fun ⟨w, _, hw⟩ => nontrivial_of_ne _ _ (by simpa using hw), fun _ => ?_⟩
  -- Over the point `p`, take `y = p x` when `p x ≠ 1`, and any `y ≠ 1` otherwise.
  by_cases hp : p x = 1
  · obtain ⟨c, hc⟩ := exists_ne (1 : K)
    exact ⟨fun _ => c, mem_V_commutator_iff.2 (by simp [hp]), by simpa using hc⟩
  · exact ⟨fun _ => p x, mem_V_commutator_iff.2 (by simp), by simpa using hp⟩

/-- The system `[y, x] = 1 ∧ y ≠ 1` is compatible with a system `S` if and only if `H` is
nontrivial: over a solution with `x ≠ 1` take `y = x`, and over a solution with `x = 1` any
`y ≠ 1`. -/
theorem isCompatibleNe_commutator_iff {ι : G →* H} {S : Set (GX G X)} {x : X} {y : Y} :
    IsCompatibleNe ι S
        {⁅(inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)), inr (FreeGroup.of (Sum.inl x))⁆}
        (inr (FreeGroup.of (Sum.inr y))) ↔ Nontrivial H := by
  refine ⟨fun h => not_subsingleton_iff_nontrivial.1 fun _ => not_isCompatibleNe_of_subsingleton h,
    fun _ => isCompatibleNe_iff.2 fun _ _ => exists_sumElim_commutator_iff.2 ‹_›⟩

/-- The system `[y, x] = 1 ∧ y ≠ 1` has a solution at the generic point of `S` if and only if the
coordinate group of `S` is nontrivial. -/
theorem hasLiftNe_commutator_iff {ι : G →* H} {S : Set (GX G X)} {x : X} {y : Y} :
    HasLiftNe ι S
        {⁅(inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)), inr (FreeGroup.of (Sum.inl x))⁆}
        (inr (FreeGroup.of (Sum.inr y))) ↔ Nontrivial (CoordGroup ι S) :=
  hasLiftNe_iff.trans exists_sumElim_commutator_iff

/-! ### Examples -/

section Examples

open Quadratic

variable (ι : G →* H) {x y : Fin 2 → X} (inj : (Sum.elim x y).Injective)

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

/-- For the empty system over a nontrivial group, with generic point `μ`: the system
`[y, x] = 1 ∧ y ≠ 1` is compatible, also over the solutions with `x = 1`, and `y = x` is a lift,
as the point `(μ, y = μ x)` solves `[y, x] = 1` and `μ x ≠ 1`. -/
example [Nontrivial H] (x : X) :
    let μ := CoordGroup.genericPoint ι (∅ : Set (GX G X))
    IsCompatibleNe ι (∅ : Set (GX G X))
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX G (X ⊕ Unit)), inr (FreeGroup.of (Sum.inl x))⁆}
        (inr (FreeGroup.of (Sum.inr ()))) ∧
      Sum.elim μ (fun _ : Unit => μ x) ∈ V (CoordGroup.coeff ι ∅)
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX G (X ⊕ Unit)), inr (FreeGroup.of (Sum.inl x))⁆} ∧
      eval (CoordGroup.coeff ι ∅) (Sum.elim μ (fun _ : Unit => μ x))
        (inr (FreeGroup.of (Sum.inr ()))) ≠ 1 := by
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  refine ⟨isCompatibleNe_commutator_iff.2 ‹_›, mem_V_commutator_iff.2 (by simp), ?_⟩
  simpa using CoordGroup.genericPoint_ne_one_iff.2 ⟨fun _ => h, by simp, hh⟩

/-- Over the trivial coefficient group and a nontrivial group `H`, the system `[y, x] = 1 ∧ y ≠ 1`
is compatible with the equation `x = 1` but has no lift to its generic point: the only solution
of `x = 1` is trivial, so its coordinate group is trivial. -/
example [Nontrivial H] (κ : Unit →* H) :
    IsCompatibleNe κ {(inr (FreeGroup.of ()) : GX Unit Unit)}
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX Unit (Unit ⊕ Unit)),
          inr (FreeGroup.of (Sum.inl ()))⁆} (inr (FreeGroup.of (Sum.inr ()))) ∧
      ¬HasLiftNe κ {(inr (FreeGroup.of ()) : GX Unit Unit)}
        {⁅(inr (FreeGroup.of (Sum.inr ())) : GX Unit (Unit ⊕ Unit)),
          inr (FreeGroup.of (Sum.inl ()))⁆} (inr (FreeGroup.of (Sum.inr ()))) := by
  refine ⟨isCompatibleNe_commutator_iff.2 ‹_›, ?_⟩
  -- Every word vanishes at the only solution `x = 1`, so the coordinate group is trivial.
  obtain rfl : κ = 1 := Subsingleton.elim _ _
  have : Subsingleton (CoordGroup (1 : Unit →* H) {(inr (FreeGroup.of ()) : GX Unit Unit)}) :=
    CoordGroup.subsingleton_iff.2 fun v hv => by
      obtain rfl : v = 1 := funext fun _ => by simpa using hv
      exact eval_one_one
  exact not_hasLiftNe_of_subsingleton

end Examples

end TauCeti.GroupAlgGeom.Lift
