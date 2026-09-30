/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path

/-!
# The degree of a loop in the circle

A loop `γ` in the unit circle `Circle`, based at `x`, lifts along the universal covering
`Circle.exp : ℝ → Circle`, `t ↦ e^{it}`, to a continuous angle function `θ : [0, 1] → ℝ` with
`exp (θ t) = γ t` (Mathlib's path lifting, `IsCoveringMap.liftPath`). Since the loop is closed,
`θ 1 - θ 0` is an integer multiple of `2π`, and since two continuous lifts of the same map differ
by a constant, this integer does not depend on the lift. It is the **degree** (or winding number)
`Circle.degree γ` of the loop: the number of times it runs counterclockwise around the circle.

The degree is characterized by any one continuous lift (`Circle.sub_eq_degree_mul` and
`Circle.degree_eq_of_sub_eq`), which is how it is computed in practice. It is invariant under
homotopies through loops, whose basepoint may move (`Circle.degree_eq_of_homotopy`), in particular
under homotopies of based loops (`Circle.degree_eq_of_homotopic`). It is additive under the
concatenation (`Circle.degree_trans`) and the pointwise product (`Circle.degree_mul`) of loops,
because angle functions concatenate and add, and reversing a loop negates it
(`Circle.degree_symm`).

The degree is the integer that Tau Ceti's identification
`Circle.fundamentalGroupMulEquiv : π₁(Circle, x) ≃* Multiplicative ℤ` assigns to the class of the
loop (`Circle.fundamentalGroupMulEquiv_fromPath`); the lift description is what makes it computable
and gives its invariance under free homotopies, changes of basepoint
(`Circle.degree_symm_trans_trans`) and pointwise products. It is the invariant through
which the Maslov index of a loop of totally real subspaces is defined.

## Main declarations

* `Circle.degree`: the degree of a loop in the circle.
* `Circle.sub_eq_degree_mul`: every continuous lift `θ` of a loop satisfies
  `θ 1 - θ 0 = degree γ * (2 * π)`.
* `Circle.degree_eq_of_homotopy`: the degree is invariant under free homotopies of loops.
* `Circle.degree_symm_trans_trans`: the degree is invariant under change of basepoint.
* `Circle.degree_trans`, `Circle.degree_symm`: the degree of a concatenation of loops is the sum
  of the degrees, and reversing a loop negates its degree.
* `Circle.degree_mul`: the degree of a pointwise product of loops is the sum of the degrees.
-/

public section

open Real
open scoped unitInterval

namespace Circle

/-- The closing condition of a loop: along any continuous lift of a loop in the circle, the
angle changes by an integer multiple of `2π`, and this integer is the same for every lift. -/
private theorem exists_forall_sub_eq {x : Circle} (γ : Path x x) :
    ∃ n : ℤ, ∀ θ : I → ℝ, Continuous θ → (∀ t, exp (θ t) = γ t) →
      θ 1 - θ 0 = n * (2 * π) := by
  obtain ⟨Θ, hΘ', -⟩ := isCoveringMap_exp.exists_path_lifts γ.toContinuousMap (Complex.arg x)
    (by simp [exp_arg])
  have hΘ (t : I) : exp (Θ t) = γ t := congr_fun hΘ' t
  obtain ⟨n, hn⟩ := exp_eq_exp.1 ((hΘ 1).trans (γ.target.trans (hΘ 0 ▸ γ.source).symm))
  refine ⟨n, fun θ hθ hθγ => ?_⟩
  -- Two continuous lifts of the same path differ by a constant.
  have := isCoveringMap_exp.const_of_comp (hθ.sub Θ.continuous)
    (fun a b => by simp [exp_sub, hθγ, hΘ]) 1 0
  simp only [Pi.sub_apply] at this
  linarith

/-- The **degree** of a loop `γ` in the circle: the integer `n` such that every continuous angle
function `θ` of the loop, `exp (θ t) = γ t`, satisfies `θ 1 - θ 0 = n * (2 * π)`. It counts how
many times the loop runs counterclockwise around the circle. -/
noncomputable def degree {x : Circle} (γ : Path x x) : ℤ :=
  (exists_forall_sub_eq γ).choose

/-- Every continuous lift `θ` of a loop `γ` along `Circle.exp` changes by `degree γ` full turns:
`θ 1 - θ 0 = degree γ * (2 * π)`. -/
theorem sub_eq_degree_mul {x : Circle} (γ : Path x x) {θ : I → ℝ} (hθ : Continuous θ)
    (hθγ : ∀ t, exp (θ t) = γ t) : θ 1 - θ 0 = degree γ * (2 * π) :=
  (exists_forall_sub_eq γ).choose_spec θ hθ hθγ

/-- The degree of a loop can be read off from any one continuous lift. -/
theorem degree_eq_of_sub_eq {x : Circle} (γ : Path x x) {θ : I → ℝ} (hθ : Continuous θ)
    (hθγ : ∀ t, exp (θ t) = γ t) {n : ℤ} (hn : θ 1 - θ 0 = n * (2 * π)) : degree γ = n := by
  have h := (sub_eq_degree_mul γ hθ hθγ).symm.trans hn
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) h

/-- The constant loop has degree zero. -/
@[simp]
theorem degree_refl (x : Circle) : degree (Path.refl x) = 0 :=
  degree_eq_of_sub_eq _ continuous_const (fun _ => exp_arg x) (by simp)

/-- **Homotopy invariance of the degree.** If `F` is a homotopy from the loop `γ₀` to the loop
`γ₁` through loops (`F (s, 0) = F (s, 1)` for every `s`; the basepoint may move), then the two
loops have the same degree. -/
theorem degree_eq_of_homotopy {x y : Circle} (γ₀ : Path x x) (γ₁ : Path y y) (F : C(I × I, Circle))
    (h₀ : ∀ t, F (0, t) = γ₀ t) (h₁ : ∀ t, F (1, t) = γ₁ t) (hF : ∀ s, F (s, 0) = F (s, 1)) :
    degree γ₀ = degree γ₁ := by
  -- Lift `F`, read with the loop parameter first, starting from a lift of the basepoint path.
  let G : C(I × I, Circle) := F.comp ⟨Prod.swap, continuous_swap⟩
  let β : C(I, Circle) := G.comp ⟨fun s => (0, s), by fun_prop⟩
  have hβ : β 0 = exp (Complex.arg (β 0)) := (exp_arg _).symm
  let f := isCoveringMap_exp.liftPath β _ hβ
  have hG0 (s : I) : G (0, s) = exp (f s) :=
    (congr_fun (isCoveringMap_exp.liftPath_lifts β _ hβ) s).symm
  let Θ := isCoveringMap_exp.liftHomotopy G f hG0
  have hΘ (t s : I) : exp (Θ (t, s)) = F (s, t) :=
    congr_fun (isCoveringMap_exp.liftHomotopy_lifts G f hG0) (t, s)
  -- The total angle `Θ (1, s) - Θ (0, s)` is a continuous function of `s` with values in `2πℤ`.
  have hconst := isCoveringMap_exp.const_of_comp
    (g := fun s : I => Θ (1, s) - Θ (0, s)) (by fun_prop)
    (fun a b => by simp [exp_sub, hΘ, hF]) 0 1
  rw [sub_eq_degree_mul γ₀ (θ := fun t => Θ (t, 0)) (by fun_prop)
      (fun t => (hΘ t 0).trans (h₀ t)),
    sub_eq_degree_mul γ₁ (θ := fun t => Θ (t, 1)) (by fun_prop)
      (fun t => (hΘ t 1).trans (h₁ t))] at hconst
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) hconst

/-- Homotopic loops, relative to their basepoint, have the same degree. -/
theorem degree_eq_of_homotopic {x : Circle} {γ₀ γ₁ : Path x x} (h : γ₀.Homotopic γ₁) :
    degree γ₀ = degree γ₁ := by
  obtain ⟨F⟩ := h
  exact degree_eq_of_homotopy γ₀ γ₁ F.toContinuousMap (by simp) (by simp)
    (fun s => by simp)

/-- The degree of the concatenation of two loops is the sum of their degrees. -/
@[simp]
theorem degree_trans {x : Circle} (γ₁ γ₂ : Path x x) :
    degree (γ₁.trans γ₂) = degree γ₁ + degree γ₂ := by
  obtain ⟨θ₁, hθ₁', -⟩ := isCoveringMap_exp.exists_path_lifts γ₁.toContinuousMap (Complex.arg x)
    (by simp [exp_arg])
  have hθ₁ (t : I) : exp (θ₁ t) = γ₁ t := congr_fun hθ₁' t
  obtain ⟨θ₂, hθ₂', hθ₂0⟩ := isCoveringMap_exp.exists_path_lifts γ₂.toContinuousMap (θ₁ 1)
    (by simp [hθ₁])
  have hθ₂ (t : I) : exp (θ₂ t) = γ₂ t := congr_fun hθ₂' t
  -- The lift of `γ₂` starts where the lift of `γ₁` ends, so the two lifts concatenate.
  let Θ₁ : Path (θ₁ 0) (θ₁ 1) := ⟨θ₁, rfl, rfl⟩
  let Θ₂ : Path (θ₁ 1) (θ₂ 1) := ⟨θ₂, hθ₂0, rfl⟩
  refine degree_eq_of_sub_eq _ (θ := Θ₁.trans Θ₂) (Θ₁.trans Θ₂).continuous (fun t => ?_) ?_
  · simp only [Path.trans_apply]
    split_ifs <;> simp [Θ₁, Θ₂, hθ₁, hθ₂]
  · have h₁ := sub_eq_degree_mul γ₁ θ₁.continuous hθ₁
    have h₂ := sub_eq_degree_mul γ₂ θ₂.continuous hθ₂
    rw [hθ₂0] at h₂
    simp only [Path.source, Path.target, Int.cast_add]
    linarith

/-- Reversing a loop negates its degree. -/
@[simp]
theorem degree_symm {x : Circle} (γ : Path x x) : degree γ.symm = -degree γ := by
  obtain ⟨θ, hθ', -⟩ := isCoveringMap_exp.exists_path_lifts γ.toContinuousMap (Complex.arg x)
    (by simp [exp_arg])
  have hθ (t : I) : exp (θ t) = γ t := congr_fun hθ' t
  refine degree_eq_of_sub_eq _ (θ := fun t => θ (σ t)) (by fun_prop) (fun t => by simp [hθ]) ?_
  have h := sub_eq_degree_mul γ θ.continuous hθ
  simp only [unitInterval.symm_one, unitInterval.symm_zero, Int.cast_neg]
  linarith

/-- Conjugating a loop by a path does not change its degree: `p⁻¹ ⬝ γ ⬝ p` has the degree of `γ`.
This is the invariance of the degree under change of basepoint. -/
theorem degree_symm_trans_trans {x y : Circle} (γ : Path x x) (p : Path x y) :
    degree (p.symm.trans (γ.trans p)) = degree γ := by
  obtain ⟨θ, hθ', -⟩ := isCoveringMap_exp.exists_path_lifts γ.toContinuousMap (Complex.arg x)
    (by simp [exp_arg])
  have hθ (t : I) : exp (θ t) = γ t := congr_fun hθ' t
  obtain ⟨φ, hφ', hφ0⟩ := isCoveringMap_exp.exists_path_lifts p.toContinuousMap (θ 1)
    (by simp [hθ])
  have hφ (t : I) : exp (φ t) = p t := congr_fun hφ' t
  have hexp : exp (θ 1 - θ 0) = 1 := by simp [exp_sub, hθ]
  -- Lift `p⁻¹` by the reversed lift of `p`, shifted back by the total angle of `γ`, so that the
  -- lifts of `p⁻¹`, `γ` and `p` concatenate.
  let Φ : Path (φ 1 - (θ 1 - θ 0)) (θ 0) :=
    { toFun := fun t => φ (σ t) - (θ 1 - θ 0)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp [hφ0] }
  let Θ : Path (θ 0) (θ 1) := ⟨θ, rfl, rfl⟩
  let Ψ : Path (θ 1) (φ 1) := ⟨φ, hφ0, rfl⟩
  refine degree_eq_of_sub_eq _ (θ := Φ.trans (Θ.trans Ψ)) (Φ.trans (Θ.trans Ψ)).continuous
    (fun t => ?_) (by simp [sub_eq_degree_mul γ θ.continuous hθ])
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs <;> simp [Φ, Θ, Ψ, exp_sub, hθ, hφ, hexp]

/-- The degree of the pointwise product of two loops is the sum of their degrees. -/
@[simp]
theorem degree_mul {x y : Circle} (γ₁ : Path x x) (γ₂ : Path y y) :
    degree (γ₁.mul γ₂) = degree γ₁ + degree γ₂ := by
  obtain ⟨Θ₁, hΘ₁', -⟩ := isCoveringMap_exp.exists_path_lifts γ₁.toContinuousMap (Complex.arg x)
    (by simp [exp_arg])
  obtain ⟨Θ₂, hΘ₂', -⟩ := isCoveringMap_exp.exists_path_lifts γ₂.toContinuousMap (Complex.arg y)
    (by simp [exp_arg])
  have hΘ₁ (t : I) : exp (Θ₁ t) = γ₁ t := congr_fun hΘ₁' t
  have hΘ₂ (t : I) : exp (Θ₂ t) = γ₂ t := congr_fun hΘ₂' t
  refine degree_eq_of_sub_eq _ (θ := fun t => Θ₁ t + Θ₂ t) (by fun_prop)
    (fun t => by simp [exp_add, hΘ₁, hΘ₂]) ?_
  rw [Int.cast_add, add_mul, ← sub_eq_degree_mul γ₁ Θ₁.continuous hΘ₁,
    ← sub_eq_degree_mul γ₂ Θ₂.continuous hΘ₂]
  ring

end Circle
