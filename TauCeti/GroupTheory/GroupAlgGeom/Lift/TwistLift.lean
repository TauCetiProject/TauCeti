/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.Twist
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Discrimination

/-!
# Twists of a point in an extension of a centralizer

Let `A` be an element of the free `G`-group `G[X]`, attach to every variable `x` a pair of
integers `(l, r) = e x`, and let `v : X → H` be a point. The substitution
`x ↦ A ^ (k * l) * x * A ^ (k * r)` (`TauCeti.GroupAlgGeom.twistHom (A ^ k) e`) composed with `v`
gives a one-parameter family of points of `H`. Following [IFT], §7.2, (84)–(85), the parameter
`k` is replaced by a new letter: in the extension `H(u, t)` of the centralizer of `u = A(v)` the
point `twistLift u v e` takes the value `t ^ l * v x * t ^ r` at `x`. The retractions
`t ↦ u ^ k` of `H(u, t)` map it back to the twisted points (`retraction_comp_twistLift`).

When `H` is a CSA group with the big powers property, `A(v) ≠ 1` and the substitution fixes `A`,
every element `w` of `G[X]` fixed by the substitution takes the same value at the lifted point as
at `v` (`eval_twistLift`): the retractions `t ↦ u ^ k` with `k` large separate `H(u, t)` and send
both values to `w(v)`. In particular the lifted point of a solution of a system fixed by the
substitution is again a solution (`twistLift_mem_V`). This is one step of the construction, in
[IFT], Proposition 4, of a `G`-homomorphism from the coordinate group of a regular quadratic
equation to an iterated extension of centralizers.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.twistLift u v e`: the point `x ↦ t ^ l * v x * t ^ r` of the
  extension of the centralizer of `u`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.retraction_comp_twistLift`: the retraction `t ↦ A(v) ^ k` maps the
  lifted point to `v` composed with the substitution for `A ^ k`.
* `TauCeti.GroupAlgGeom.Lift.eval_twistLift`: elements fixed by the substitution take the same
  value at the lifted point as at `v`.
* `TauCeti.GroupAlgGeom.Lift.twistLift_mem_V`: lifting along a substitution fixing a system takes
  solutions to solutions.
* `TauCeti.GroupAlgGeom.Lift.twistLift_mem_V_oneCommutatorEquation`: for the equation
  `x⁻¹ y⁻¹ x y = a⁻¹ b⁻¹ a b` over the free group `F(a, b)`
  (`TauCeti.GroupAlgGeom.Quadratic.oneCommutatorEquation`) and the twist `y ↦ x y`, the solution
  `(a, b)` lifts to the solution `(a, t b)`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.5 and §7.2, (84)–(88) and Proposition 4.
-/

public section

open Monoid.Coprod TauCeti.LimitGroup

namespace TauCeti.GroupAlgGeom.Lift

variable {G H X : Type*} [Group G] [Group H]

section TwistLift

variable (u : H) (v : X → H) (e : X → ℤ × ℤ)

/-- The point of the extension `H(u, t)` of the centralizer of `u` whose value at the variable `x`
is `t ^ l * v x * t ^ r`, where `(l, r) = e x`. For `u = A(v)` this is the lift of `v` along the
twist `x ↦ A ^ l * x * A ^ r`, the parameter of the powers of the twist being replaced by `t`. -/
def twistLift : X → CentralizerExt u 1 :=
  fun x => CentralizerExt.t 0 ^ (e x).1 * CentralizerExt.of (v x) * CentralizerExt.t 0 ^ (e x).2

@[simp]
theorem twistLift_apply (x : X) : twistLift u v e x =
    CentralizerExt.t 0 ^ (e x).1 * CentralizerExt.of (v x) * CentralizerExt.t 0 ^ (e x).2 := (rfl)

end TwistLift

section Retraction

variable (ι : G →* H) (v : X → H) {A : GX G X} {e : X → ℤ × ℤ}

/-- The retraction `t ↦ u ^ k` of the extension of the centralizer of `u = A(v)` maps the lifted
point to the composite of `v` with the substitution `x ↦ A ^ (k * l) * x * A ^ (k * r)`. When the
substitutions for `A` and for `A⁻¹` fix `A`, the substitution for `A` is the automorphism
`twist A e h₁ h₂`, and this is `v` composed with its `k`-th power (`twist_zpow_apply`). -/
theorem retraction_comp_twistLift (k : ℤ) :
    ⇑(CentralizerExt.retraction fun _ => k) ∘ twistLift (eval ι v A) v e =
      wordMap ι (fun x => twistHom (A ^ k) e (inr (FreeGroup.of x))) v := by
  funext x
  simp

/-- The retraction `t ↦ u ^ k` of the value of `w` at the lifted point is the value at `v` of the
substitution for `A ^ k` applied to `w`. -/
private theorem retraction_eval_twistLift (k : ℤ) (w : GX G X) :
    CentralizerExt.retraction (fun _ => k)
        (eval (CentralizerExt.of.comp ι) (twistLift (eval ι v A) v e) w) =
      eval ι v (twistHom (A ^ k) e w) := by
  -- Move the retraction inside the evaluation; it is the identity on `H`.
  rw [← MonoidHom.comp_apply, MonoidHom.comp_eval]
  simp [← MonoidHom.comp_assoc, Function.comp_def]

variable {ι v}

/-- An element of `G[X]` fixed by the twist by `A` has the same value at the lifted point as at
`v`, when `H` is a CSA group with the big powers property, `A(v) ≠ 1` and the twist fixes `A`. -/
theorem eval_twistLift (hBP : Group.IsBP H) (hCSA : Group.IsCSA H) (hA : eval ι v A ≠ 1)
    (h₁ : twistHom A e A = A) {w : GX G X} (hw : twistHom A e w = w) :
    eval (CentralizerExt.of.comp ι) (twistLift (eval ι v A) v e) w =
      CentralizerExt.of (eval ι v w) := by
  -- Otherwise the quotient of the two sides would survive the retractions `t ↦ u ^ n` for all
  -- large `n`, but each of them sends both sides to `w(v)`.
  by_contra hne
  obtain ⟨N, hN⟩ := CentralizerExt.exists_forall_retraction_ne_one hBP hCSA hA
    (mul_inv_eq_one.not.mpr hne)
  exact hN N le_rfl <| by
    simp [retraction_eval_twistLift, twistHom_pow_apply_eq_self_of_apply_eq_self h₁ hw]

/-- Lifting along a twist by `A` that fixes `A` and every equation of a system `S` takes the
solutions `v` of `S` in a CSA group `H` with the big powers property, with `A(v) ≠ 1`, to
solutions of `S` in the extension of the centralizer of `A(v)`. -/
theorem twistLift_mem_V (hBP : Group.IsBP H) (hCSA : Group.IsCSA H) (hA : eval ι v A ≠ 1)
    (h₁ : twistHom A e A = A) {S : Set (GX G X)} (hS : ∀ s ∈ S, twistHom A e s = s)
    (hv : v ∈ V ι S) : twistLift (eval ι v A) v e ∈ V (CentralizerExt.of.comp ι) S :=
  mem_V.2 fun s hs => by rw [eval_twistLift hBP hCSA hA h₁ (hS s hs), mem_V.1 hv s hs, map_one]

end Retraction

/-! ### The one-commutator equation -/

/-- For the equation `x⁻¹ y⁻¹ x y = a⁻¹ b⁻¹ a b` over the free group `F(a, b)`, lifting the
solution `(a, b)` along the twist `y ↦ x y` gives the solution `(a, t b)` in the extension of the
centralizer of `a`. -/
theorem twistLift_mem_V_oneCommutatorEquation :
    twistLift (eval (.id _) ![.of 0, .of 1] (inr (.of 0) : GX (FreeGroup (Fin 2)) (Fin 2)))
        ![.of 0, .of 1] (Pi.single 1 (1, 0)) ∈
      V (CentralizerExt.of.comp (.id _)) {Quadratic.oneCommutatorEquation (.of 0) (.of 1)} := by
  refine twistLift_mem_V FreeGroup.isBP IsFreeGroup.isCSA (by simp) (by simp) ?_ ?_ <;>
    simp [mem_V, Quadratic.oneCommutatorEquation_def, commutatorElement_def, mul_assoc]

end TauCeti.GroupAlgGeom.Lift
