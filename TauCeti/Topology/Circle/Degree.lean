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
# The degree of a loop and the angle swept by a path in the circle

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
(`Circle.degree_symm`). Raising a loop pointwise to the `n`-th power multiplies its degree by `n`
(`Circle.degree_map_pow`), and inverting it pointwise negates its degree (`Circle.degree_inv`).

The degree is the integer that Tau Ceti's identification
`Circle.fundamentalGroupMulEquiv : π₁(Circle, x) ≃* Multiplicative ℤ` assigns to the class of the
loop (`Circle.fundamentalGroupMulEquiv_fromPath`); the lift description is what makes it computable
and gives its invariance under free homotopies, changes of basepoint
(`Circle.degree_symm_trans_trans`) and pointwise products. It is the invariant through
which the Maslov index of a loop of totally real subspaces is defined.

More generally, a path `γ` from `x` to `y`, not necessarily closed, has a well-defined **swept
angle** `Circle.angleChange γ = θ 1 - θ 0`, for any continuous lift `θ`. Its exponential is
`y / x`, it is `2π` times the degree on loops, and it is additive under concatenation and pointwise
products, odd under reversal and pointwise inversion, and invariant under homotopies fixing the
endpoints. It is the
continuous part of the Maslov index of a path of Lagrangian frames.

## Main declarations

* `Circle.degree`: the degree of a loop in the circle.
* `Circle.sub_eq_degree_mul`: every continuous lift `θ` of a loop satisfies
  `θ 1 - θ 0 = degree γ * (2 * π)`.
* `Circle.degree_eq_of_homotopy`: the degree is invariant under free homotopies of loops.
* `Circle.degree_symm_trans_trans`: the degree is invariant under change of basepoint.
* `Circle.degree_trans`, `Circle.degree_symm`: the degree of a concatenation of loops is the sum
  of the degrees, and reversing a loop negates its degree.
* `Circle.degree_mul`: the degree of a pointwise product of loops is the sum of the degrees.
* `Circle.degree_map_pow`: the pointwise `n`-th power of a loop has `n` times its degree.
* `Circle.degree_inv`: the pointwise inverse of a loop has the opposite degree.
* `Circle.degree_congr`: loops agreeing pointwise have the same degree.
* `Circle.exists_lift`: every path in the circle has a continuous lift through `Circle.exp`.
* `Circle.angleChange`: the angle swept by a path in the circle.
* `Circle.angleChange_eq_sub`: it is `θ 1 - θ 0` for every continuous lift `θ`.
* `Circle.angleChange_eq_of_homotopic`, `Circle.angleChange_trans`, `Circle.angleChange_mul`:
  it is invariant under homotopies fixing the endpoints and additive under concatenation and
  pointwise products; the corresponding laws of the degree are derived from these.
* `Circle.exists_forall_eq_add_of_exp_eq`: on a preconnected space, two continuous lifts of the
  same map through `Circle.exp` differ by a constant.
* `Circle.exists_int_forall_eq_add_of_exp_eq`: on a preconnected space, two continuous lifts of
  the same map through `Circle.exp` differ by a constant integer multiple of `2π`.
-/

public section

open Real
open scoped unitInterval

namespace Circle

/-- **Lifts through `exp` are unique up to a constant.** On a preconnected space, two continuous
real functions with the same exponential differ by a constant. -/
theorem exists_forall_eq_add_of_exp_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {G G' : A → ℝ} (hG : Continuous G) (hG' : Continuous G')
    (h : ∀ a, exp (G a) = exp (G' a)) : ∃ c : ℝ, ∀ a, G a = G' a + c := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a₀⟩⟩
  · exact ⟨0, isEmptyElim⟩
  refine ⟨G a₀ - G' a₀, fun a ↦ ?_⟩
  have := isCoveringMap_exp.const_of_comp (g := fun a ↦ G a - G' a) (hG.sub hG')
    (fun a a' ↦ by simp [exp_sub, h]) a a₀
  linarith

/-- **Lifts through `exp` are unique up to a full turn.** On a preconnected space, two continuous
real functions with the same exponential differ by a constant integer multiple of `2π`. -/
theorem exists_int_forall_eq_add_of_exp_eq {A : Type*} [TopologicalSpace A]
    [PreconnectedSpace A] {G G' : A → ℝ} (hG : Continuous G) (hG' : Continuous G')
    (h : ∀ a, exp (G a) = exp (G' a)) : ∃ m : ℤ, ∀ a, G a = G' a + m * (2 * π) := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a₀⟩⟩
  · exact ⟨0, isEmptyElim⟩
  obtain ⟨c, hc⟩ := exists_forall_eq_add_of_exp_eq hG hG' h
  have hexp : exp c = 1 := by
    have := h a₀
    rwa [hc a₀, exp_add, mul_eq_left] at this
  obtain ⟨m, hm⟩ := exp_eq_one.1 hexp
  exact ⟨m, fun a ↦ by rw [hc a, hm]⟩

/-- Every path in the circle has a continuous lift through `Circle.exp`. -/
theorem exists_lift {x y : Circle} (γ : Path x y) :
    ∃ θ : C(I, ℝ), ∀ t, exp (θ t) = γ t := by
  obtain ⟨θ, hθ, -⟩ := isCoveringMap_exp.exists_path_lifts γ.toContinuousMap (Complex.arg x)
    (by simp [exp_arg])
  exact ⟨θ, fun t => congr_fun hθ t⟩

/-- The closing condition of a loop: along any continuous lift of a loop in the circle, the
angle changes by an integer multiple of `2π`, and this integer is the same for every lift. -/
private theorem exists_forall_sub_eq {x : Circle} (γ : Path x x) :
    ∃ n : ℤ, ∀ θ : I → ℝ, Continuous θ → (∀ t, exp (θ t) = γ t) →
      θ 1 - θ 0 = n * (2 * π) := by
  obtain ⟨Θ, hΘ⟩ := exists_lift γ
  obtain ⟨n, hn⟩ := exp_eq_exp.1 ((hΘ 1).trans (γ.target.trans (hΘ 0 ▸ γ.source).symm))
  refine ⟨n, fun θ hθ hθγ => ?_⟩
  -- Two continuous lifts of the same path differ by a constant.
  obtain ⟨c, hc⟩ := exists_forall_eq_add_of_exp_eq hθ Θ.continuous fun t => by rw [hθγ, hΘ]
  rw [hc 1, hc 0]
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

/-! ### The angle swept by a path -/

/-- The **angle swept** by a path `γ` in the circle: the difference `θ 1 - θ 0` along a continuous
lift `θ` of `γ` through `Circle.exp`. It does not depend on the lift
(`Circle.angleChange_eq_sub`); for a loop it is `2π` times the degree
(`Circle.angleChange_eq_degree_mul`). -/
noncomputable def angleChange {x y : Circle} (γ : Path x y) : ℝ :=
  isCoveringMap_exp.liftPath γ.toContinuousMap (Complex.arg x) (by simp [exp_arg]) 1 -
    isCoveringMap_exp.liftPath γ.toContinuousMap (Complex.arg x) (by simp [exp_arg]) 0

/-- The angle swept by a path is `θ 1 - θ 0` for every continuous lift `θ` of the path. -/
theorem angleChange_eq_sub {x y : Circle} (γ : Path x y) {θ : I → ℝ} (hθ : Continuous θ)
    (hθγ : ∀ t, exp (θ t) = γ t) : angleChange γ = θ 1 - θ 0 := by
  have hΘ (t : I) : exp (isCoveringMap_exp.liftPath γ.toContinuousMap (Complex.arg x)
      (by simp [exp_arg]) t) = γ t :=
    congr_fun (isCoveringMap_exp.liftPath_lifts γ.toContinuousMap _ (by simp [exp_arg])) t
  obtain ⟨c, hc⟩ := exists_forall_eq_add_of_exp_eq
    (isCoveringMap_exp.liftPath γ.toContinuousMap _ _).continuous hθ fun t => by rw [hΘ, hθγ]
  rw [angleChange, hc 1, hc 0]
  ring

/-- Paths that agree pointwise sweep the same angle, however their endpoints are written. -/
theorem angleChange_congr {x y x' y' : Circle} (γ : Path x y) (γ' : Path x' y')
    (h : ∀ t, γ t = γ' t) : angleChange γ = angleChange γ' := by
  obtain ⟨θ, hθ⟩ := exists_lift γ
  rw [angleChange_eq_sub γ θ.continuous hθ,
    angleChange_eq_sub γ' θ.continuous fun t => (hθ t).trans (h t)]

/-- The exponential of the angle swept by a path from `x` to `y` is `y / x`. -/
theorem exp_angleChange {x y : Circle} (γ : Path x y) : exp (angleChange γ) = y / x := by
  obtain ⟨θ, hθ⟩ := exists_lift γ
  rw [angleChange_eq_sub γ θ.continuous hθ, exp_sub, hθ, hθ, γ.source, γ.target]

/-- The angle swept by a loop is `2π` times its degree. -/
theorem angleChange_eq_degree_mul {x : Circle} (γ : Path x x) :
    angleChange γ = degree γ * (2 * π) := by
  obtain ⟨θ, hθ⟩ := exists_lift γ
  rw [angleChange_eq_sub γ θ.continuous hθ, sub_eq_degree_mul γ θ.continuous hθ]

/-- The constant path sweeps no angle. -/
@[simp]
theorem angleChange_refl (x : Circle) : angleChange (Path.refl x) = 0 := by
  rw [angleChange_eq_degree_mul, degree_refl, Int.cast_zero, zero_mul]

/-- **Homotopy invariance of the swept angle.** Paths that are homotopic relative to their
endpoints sweep the same angle. -/
theorem angleChange_eq_of_homotopic {x y : Circle} {γ₀ γ₁ : Path x y} (h : γ₀.Homotopic γ₁) :
    angleChange γ₀ = angleChange γ₁ := by
  obtain ⟨F⟩ := h
  -- Lift `F`, read with the path parameter first, starting from a constant lift of `x`.
  let G : C(I × I, Circle) := F.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩
  let f : C(I, ℝ) := ContinuousMap.const I (Complex.arg x)
  have hG0 (s : I) : G (0, s) = exp (f s) := by simp [G, f, exp_arg]
  let Θ := isCoveringMap_exp.liftHomotopy G f hG0
  have hΘ (t s : I) : exp (Θ (t, s)) = F (s, t) :=
    congr_fun (isCoveringMap_exp.liftHomotopy_lifts G f hG0) (t, s)
  -- The swept angle `Θ (1, s) - Θ (0, s)` is a continuous function of `s` with values in a
  -- single fibre of `exp`, hence constant.
  have hconst := isCoveringMap_exp.const_of_comp
    (g := fun s : I => Θ (1, s) - Θ (0, s)) (by fun_prop)
    (fun a b => by simp [exp_sub, hΘ]) 0 1
  rwa [← angleChange_eq_sub γ₀ (θ := fun t => Θ (t, 0)) (by fun_prop)
      (fun t => (hΘ t 0).trans (by simp)),
    ← angleChange_eq_sub γ₁ (θ := fun t => Θ (t, 1)) (by fun_prop)
      (fun t => (hΘ t 1).trans (by simp))] at hconst

/-- The angle swept by the concatenation of two paths is the sum of the angles they sweep. -/
@[simp]
theorem angleChange_trans {x y z : Circle} (γ₁ : Path x y) (γ₂ : Path y z) :
    angleChange (γ₁.trans γ₂) = angleChange γ₁ + angleChange γ₂ := by
  obtain ⟨θ₁, hθ₁⟩ := exists_lift γ₁
  obtain ⟨θ₂, hθ₂', hθ₂0⟩ := isCoveringMap_exp.exists_path_lifts γ₂.toContinuousMap (θ₁ 1)
    (by simp [hθ₁])
  have hθ₂ (t : I) : exp (θ₂ t) = γ₂ t := congr_fun hθ₂' t
  -- The lift of `γ₂` starts where the lift of `γ₁` ends, so the two lifts concatenate.
  let Θ₁ : Path (θ₁ 0) (θ₁ 1) := ⟨θ₁, rfl, rfl⟩
  let Θ₂ : Path (θ₁ 1) (θ₂ 1) := ⟨θ₂, hθ₂0, rfl⟩
  rw [angleChange_eq_sub _ (θ := Θ₁.trans Θ₂) (Θ₁.trans Θ₂).continuous (fun t => ?_),
    angleChange_eq_sub γ₁ θ₁.continuous hθ₁, angleChange_eq_sub γ₂ θ₂.continuous hθ₂, hθ₂0]
  · simp
  · simp only [Path.trans_apply]
    split_ifs <;> simp [Θ₁, Θ₂, hθ₁, hθ₂]

/-- Reversing a path negates the angle it sweeps. -/
@[simp]
theorem angleChange_symm {x y : Circle} (γ : Path x y) : angleChange γ.symm = -angleChange γ := by
  obtain ⟨θ, hθ⟩ := exists_lift γ
  rw [angleChange_eq_sub _ (θ := fun t => θ (σ t)) (by fun_prop) (fun t => by simp [hθ]),
    angleChange_eq_sub γ θ.continuous hθ]
  simp

/-- The angle swept by the pointwise product of two paths is the sum of the angles they sweep. -/
@[simp]
theorem angleChange_mul {x₁ y₁ x₂ y₂ : Circle} (γ₁ : Path x₁ y₁) (γ₂ : Path x₂ y₂) :
    angleChange (γ₁.mul γ₂) = angleChange γ₁ + angleChange γ₂ := by
  obtain ⟨θ₁, hθ₁⟩ := exists_lift γ₁
  obtain ⟨θ₂, hθ₂⟩ := exists_lift γ₂
  rw [angleChange_eq_sub _ (θ := fun t => θ₁ t + θ₂ t) (by fun_prop)
      (fun t => by simp [exp_add, hθ₁, hθ₂]),
    angleChange_eq_sub γ₁ θ₁.continuous hθ₁, angleChange_eq_sub γ₂ θ₂.continuous hθ₂]
  ring

/-- Inverting a path pointwise negates the angle it sweeps. -/
@[simp]
theorem angleChange_inv {x y : Circle} (γ : Path x y) : angleChange γ.inv = -angleChange γ := by
  obtain ⟨θ, hθ⟩ := exists_lift γ
  rw [angleChange_eq_sub _ (θ := fun t => -θ t) (by fun_prop) (fun t => by simp [exp_neg, hθ]),
    angleChange_eq_sub γ θ.continuous hθ]
  ring

/-- A loop sweeping the angle `n * (2 * π)` has degree `n`. -/
private theorem degree_eq_of_angleChange_eq {x : Circle} (γ : Path x x) {n : ℤ}
    (h : angleChange γ = n * (2 * π)) : degree γ = n := by
  rw [angleChange_eq_degree_mul] at h
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) h

/-! ### Laws of the degree -/

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

/-- Loops that agree pointwise have the same degree, however their basepoints are written. -/
theorem degree_congr {x y : Circle} (γ₀ : Path x x) (γ₁ : Path y y) (h : ∀ t, γ₀ t = γ₁ t) :
    degree γ₀ = degree γ₁ :=
  degree_eq_of_homotopy γ₀ γ₁ (γ₀.toContinuousMap.comp ⟨Prod.snd, continuous_snd⟩)
    (fun _ => rfl) h (fun _ => by simp)

/-- Homotopic loops, relative to their basepoint, have the same degree. -/
theorem degree_eq_of_homotopic {x : Circle} {γ₀ γ₁ : Path x x} (h : γ₀.Homotopic γ₁) :
    degree γ₀ = degree γ₁ :=
  degree_eq_of_angleChange_eq _
    ((angleChange_eq_of_homotopic h).trans (angleChange_eq_degree_mul γ₁))

/-- The degree of the concatenation of two loops is the sum of their degrees. -/
@[simp]
theorem degree_trans {x : Circle} (γ₁ γ₂ : Path x x) :
    degree (γ₁.trans γ₂) = degree γ₁ + degree γ₂ :=
  degree_eq_of_angleChange_eq _ (by
    rw [angleChange_trans, angleChange_eq_degree_mul, angleChange_eq_degree_mul]; push_cast; ring)

/-- Reversing a loop negates its degree. -/
@[simp]
theorem degree_symm {x : Circle} (γ : Path x x) : degree γ.symm = -degree γ :=
  degree_eq_of_angleChange_eq _ (by
    rw [angleChange_symm, angleChange_eq_degree_mul]; push_cast; ring)

/-- Conjugating a loop by a path does not change its degree: `p⁻¹ ⬝ γ ⬝ p` has the degree of `γ`.
This is the invariance of the degree under change of basepoint. -/
theorem degree_symm_trans_trans {x y : Circle} (γ : Path x x) (p : Path x y) :
    degree (p.symm.trans (γ.trans p)) = degree γ :=
  degree_eq_of_angleChange_eq _ (by
    rw [angleChange_trans, angleChange_trans, angleChange_symm, angleChange_eq_degree_mul]; ring)

/-- The degree of the pointwise product of two loops is the sum of their degrees. -/
@[simp]
theorem degree_mul {x y : Circle} (γ₁ : Path x x) (γ₂ : Path y y) :
    degree (γ₁.mul γ₂) = degree γ₁ + degree γ₂ :=
  degree_eq_of_angleChange_eq _ (by
    rw [angleChange_mul, angleChange_eq_degree_mul, angleChange_eq_degree_mul]; push_cast; ring)

/-- The pointwise `n`-th power of a loop has `n` times its degree. -/
@[simp]
theorem degree_map_pow {x : Circle} (γ : Path x x) (n : ℕ) :
    degree (γ.map (continuous_pow n)) = n * degree γ := by
  induction n with
  | zero => simpa using degree_congr _ (Path.refl 1) fun t => by simp
  | succ n ih =>
    rw [degree_congr _ ((γ.map (continuous_pow n)).mul γ) fun t => by simp [pow_succ], degree_mul,
      ih]
    push_cast
    ring

/-- The pointwise inverse of a loop has the opposite degree. -/
@[simp]
theorem degree_inv {x : Circle} (γ : Path x x) : degree γ.inv = -degree γ :=
  degree_eq_of_angleChange_eq _ (by
    rw [angleChange_inv, angleChange_eq_degree_mul]; push_cast; ring)

end Circle
