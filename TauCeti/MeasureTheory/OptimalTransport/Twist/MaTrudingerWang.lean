/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Twist.CExponential
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.InnerProductSpace.CompleteSquare

/-!
# The Ma–Trudinger–Wang tensor and conditions

Let `c : E × Y → ℝ` be a cost on a real normed space `E` and a type `Y`, twisted on a target set
`V`, so that the `c`-exponential `TauCeti.cExp c V x` recovers a point of `V` from its momentum
`-Dₓ c (x, y)` at `x`. In these *momentum coordinates* the cost becomes the function
`(x', q) ↦ c (x', cExp c V x q)` of a source point `x'` and a momentum `q`. Minus its fourth mixed
derivative, twice in a source direction `ξ` and twice in a momentum direction `η`, is the
*Ma–Trudinger–Wang tensor*

`𝔖_c (x, y) (ξ, η) = -∂²/∂s² ∂²/∂t² c (x + t • ξ, cExp c V x (p + s • η))` at `s = t = 0`,

where `p = -Dₓ c (x, y)` is the momentum of `y` at `x` (`TauCeti.mtwTensor`). Only the base point
`x` of the `c`-exponential is frozen; the source point moves along `x + t • ξ`. The derivatives are
taken along lines with Mathlib's one-variable `deriv`, so `𝔖_c (x, y) (ξ, η)` is defined for every
cost, and it is homogeneous of degree two in `ξ` and in `η` with no regularity assumption at all
(`TauCeti.mtwTensor_smul_left`, `TauCeti.mtwTensor_smul_right`). For a cost that is smooth in
momentum coordinates it is minus the mixed fourth derivative `D²_q D²_x` evaluated at
`(ξ, ξ, η, η)`, but no regularity is needed to define it.

The tensor at `(x, y)` only sees the `c`-exponential at momenta near the momentum `p` of `y`. It
reflects the cost only when `V` is a neighbourhood of `y`: otherwise `cExp c V x` may take
unspecified values at momenta arbitrarily close to `p` (for `V = {y}` it equals `y` at `p` and
one arbitrary default point at every other momentum, so the tensor vanishes). So, for a topology
on the target space, the conditions below quantify over the target points in the interior of `V`.

The sign of this tensor on *orthogonal* pairs, those with `η ξ = 0`, decides the regularity of
optimal transport maps. The **weak Ma–Trudinger–Wang condition** (A3w) asks that
`𝔖_c (x, y) (ξ, η) ≥ 0` for all such pairs, at every `x ∈ U` and every `y` in the interior of
`V` (`TauCeti.SatisfiesWeakMTW`); Loeper showed that without it, optimal maps between smooth
positive densities can be discontinuous. The **strong condition** (A3s) asks for the uniform bound
`𝔖_c (x, y) (ξ, η) ≥ C ‖ξ‖² ‖η‖²` with a constant `C > 0` (`TauCeti.SatisfiesStrongMTW`).

Three examples calibrate these definitions.

* For the quadratic cost `‖x - y‖ ^ 2 / 2` on a real inner product space the cost is a quadratic
  polynomial in `t` whose `t²` coefficient does not involve the target, so the tensor vanishes
  identically, whatever the target set (`TauCeti.mtwTensor_norm_sub_sq_div_two`). The quadratic
  cost satisfies the weak condition but, on a nonempty source set and a target set with nonempty
  interior, as soon as the space has dimension at least two, not the strong one
  (`TauCeti.satisfiesStrongMTW_norm_sub_sq_div_two_iff`).
* In dimension one, a momentum annihilating a nonzero direction is zero, so every cost satisfies
  the strong condition (`TauCeti.satisfiesStrongMTW_of_rank_le_one`). The conditions only carry
  information in dimension at least two.
* For the cost `√(1 + ‖x - y‖ ^ 2)` on a real Hilbert space, one of the examples of Ma, Trudinger
  and Wang, the tensor at an orthogonal pair is
  `((1 + ‖y - x‖²) ‖ξ‖² - ⟪y - x, ξ⟫²) (‖η‖² + η (y - x)²) / √(1 + ‖y - x‖²)`
  (`TauCeti.mtwTensor_sqrt_one_add_norm_sub_sq`), which is at least
  `‖ξ‖² ‖η‖² / √(1 + ‖y - x‖²)`. So this cost satisfies the strong condition on every pair of
  sets at bounded distance (`TauCeti.satisfiesStrongMTW_sqrt_one_add_norm_sub_sq`).

The normalization follows Loeper. Villani writes the same tensor with an extra factor `3 / 2`,
which changes neither condition.

## Main definitions

* `TauCeti.mtwTensor c V x y ξ η` — the Ma–Trudinger–Wang tensor of `c` at `(x, y)`;
* `TauCeti.SatisfiesWeakMTW c U V` — the weak Ma–Trudinger–Wang condition (A3w) on `U × V`;
* `TauCeti.SatisfiesStrongMTW c U V` — the strong Ma–Trudinger–Wang condition (A3s) on `U × V`.

## Main statements

* `TauCeti.mtwTensor_smul_left` and `TauCeti.mtwTensor_smul_right` — the tensor is homogeneous of
  degree two in each direction;
* `TauCeti.SatisfiesStrongMTW.mtwTensor_pos` — under the strong condition the tensor is positive
  on nonzero orthogonal pairs;
* `TauCeti.satisfiesStrongMTW_of_rank_le_one` — every cost on a source space of dimension at most
  one satisfies the strong condition;
* `TauCeti.mtwTensor_norm_sub_sq_div_two`, `TauCeti.satisfiesWeakMTW_norm_sub_sq_div_two` and
  `TauCeti.satisfiesStrongMTW_norm_sub_sq_div_two_iff` — the quadratic cost has vanishing tensor,
  satisfies the weak condition, and, on a nonempty source set and a target set with nonempty
  interior, satisfies the strong one exactly in dimension at most one;
* `TauCeti.mtwTensor_sqrt_one_add_norm_sub_sq` and
  `TauCeti.satisfiesStrongMTW_sqrt_one_add_norm_sub_sq` — the tensor of `√(1 + ‖x - y‖ ^ 2)` and
  the strong condition for it at bounded distance.

## References

* X.-N. Ma, N. S. Trudinger and X.-J. Wang, *Regularity of potential functions of the optimal
  transportation problem*, Arch. Ration. Mech. Anal. 177 (2005), 151--183, for the conditions
  A3w and A3s and the cost `√(1 + ‖x - y‖ ^ 2)`.
* G. Loeper, *On the regularity of solutions of optimal transportation problems*, Acta Math.
  202 (2009), 241--283, for the tensor in momentum coordinates and the necessity of A3w.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 12.
-/

public section

noncomputable section

open Set Filter Function InnerProductSpace
open scoped Topology RealInnerProductSpace

namespace TauCeti

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The tensor and the conditions -/

section Tensor

variable [Nonempty Y] {c : E × Y → ℝ} {U U' : Set E} {V : Set Y} {x : E} {y : Y} {ξ : E}
  {η : StrongDual ℝ E}

/-- The **Ma–Trudinger–Wang tensor** of a cost `c` at `(x, y)`, with respect to the target set
`V` of its `c`-exponential, on a source direction `ξ` and a momentum direction `η`. Writing
`p = -Dₓ c (x, y)` for the momentum of `y` at `x`, it is minus the second derivative in `s` at `0`
of the second derivative in `t` at `0` of `c (x + t • ξ, cExp c V x (p + s • η))`. -/
def mtwTensor (c : E × Y → ℝ) (V : Set Y) (x : E) (y : Y) (ξ : E) (η : StrongDual ℝ E) : ℝ :=
  -deriv (deriv fun s : ℝ ↦ deriv (deriv fun t : ℝ ↦
    c (x + t • ξ, cExp c V x (-fderiv ℝ (fun x' ↦ c (x', y)) x + s • η))) 0) 0

theorem mtwTensor_def : mtwTensor c V x y ξ η =
    -deriv (deriv fun s : ℝ ↦ deriv (deriv fun t : ℝ ↦
      c (x + t • ξ, cExp c V x (-fderiv ℝ (fun x' ↦ c (x', y)) x + s • η))) 0) 0 :=
  (rfl)

/-- The Ma–Trudinger–Wang tensor is homogeneous of degree two in the source direction. -/
theorem mtwTensor_smul_left (a : ℝ) :
    mtwTensor c V x y (a • ξ) η = a ^ 2 * mtwTensor c V x y ξ η := by
  have h (q : StrongDual ℝ E) : deriv (deriv fun t : ℝ ↦ c (x + t • a • ξ, cExp c V x q)) 0 =
      a ^ 2 * deriv (deriv fun t : ℝ ↦ c (x + t • ξ, cExp c V x q)) 0 := by
    simpa [smul_smul, mul_comm] using
      deriv_deriv_comp_mul_left a (fun t : ℝ ↦ c (x + t • ξ, cExp c V x q)) 0
  simp only [mtwTensor_def, h, deriv_const_mul_field', mul_neg]

/-- The Ma–Trudinger–Wang tensor is homogeneous of degree two in the momentum direction. -/
theorem mtwTensor_smul_right (b : ℝ) :
    mtwTensor c V x y ξ (b • η) = b ^ 2 * mtwTensor c V x y ξ η := by
  have h := deriv_deriv_comp_mul_left b (fun s : ℝ ↦ deriv (deriv fun t : ℝ ↦
    c (x + t • ξ, cExp c V x (-fderiv ℝ (fun x' ↦ c (x', y)) x + s • η))) 0) 0
  simp only [mul_zero, smul_eq_mul] at h
  simp only [mtwTensor_def, smul_smul, mul_comm _ b, h, mul_neg]

@[simp]
theorem mtwTensor_zero_left : mtwTensor c V x y 0 η = 0 := by
  simpa using mtwTensor_smul_left (c := c) (V := V) (x := x) (y := y) (ξ := 0) (η := η) 0

@[simp]
theorem mtwTensor_zero_right : mtwTensor c V x y ξ 0 = 0 := by
  simpa using mtwTensor_smul_right (c := c) (V := V) (x := x) (y := y) (ξ := ξ) (η := 0) 0

@[simp]
theorem mtwTensor_neg_left : mtwTensor c V x y (-ξ) η = mtwTensor c V x y ξ η := by
  simpa using mtwTensor_smul_left (c := c) (V := V) (x := x) (y := y) (ξ := ξ) (η := η) (-1)

@[simp]
theorem mtwTensor_neg_right : mtwTensor c V x y ξ (-η) = mtwTensor c V x y ξ η := by
  rw [← neg_one_smul ℝ η, mtwTensor_smul_right]
  norm_num

variable [TopologicalSpace Y]

/-- A cost satisfies the **weak Ma–Trudinger–Wang condition** (A3w) on `U × V` if, at every
`x ∈ U` and every `y` in the interior of `V`, its Ma–Trudinger–Wang tensor with respect to `V` is
nonnegative on every source direction `ξ` and momentum direction `η` with `η ξ = 0`. Points on
the boundary of `V` are excluded: there the tensor may only see unspecified values of the
`c`-exponential. -/
def SatisfiesWeakMTW (c : E × Y → ℝ) (U : Set E) (V : Set Y) : Prop :=
  ∀ x ∈ U, ∀ y ∈ interior V, ∀ (ξ : E) (η : StrongDual ℝ E), η ξ = 0 →
    0 ≤ mtwTensor c V x y ξ η

/-- A cost satisfies the **strong Ma–Trudinger–Wang condition** (A3s) on `U × V` if there is a
constant `C > 0` such that, at every `x ∈ U` and every `y` in the interior of `V`, its
Ma–Trudinger–Wang tensor with respect to `V` is at least `C * ‖ξ‖ ^ 2 * ‖η‖ ^ 2` on every source
direction `ξ` and momentum direction `η` with `η ξ = 0`. As for `TauCeti.SatisfiesWeakMTW`, points
on the boundary of `V` are excluded. -/
def SatisfiesStrongMTW (c : E × Y → ℝ) (U : Set E) (V : Set Y) : Prop :=
  ∃ C > 0, ∀ x ∈ U, ∀ y ∈ interior V, ∀ (ξ : E) (η : StrongDual ℝ E), η ξ = 0 →
    C * ‖ξ‖ ^ 2 * ‖η‖ ^ 2 ≤ mtwTensor c V x y ξ η

theorem satisfiesWeakMTW_iff : SatisfiesWeakMTW c U V ↔
    ∀ x ∈ U, ∀ y ∈ interior V, ∀ (ξ : E) (η : StrongDual ℝ E), η ξ = 0 →
      0 ≤ mtwTensor c V x y ξ η :=
  Iff.rfl

theorem satisfiesStrongMTW_iff : SatisfiesStrongMTW c U V ↔
    ∃ C > 0, ∀ x ∈ U, ∀ y ∈ interior V, ∀ (ξ : E) (η : StrongDual ℝ E), η ξ = 0 →
      C * ‖ξ‖ ^ 2 * ‖η‖ ^ 2 ≤ mtwTensor c V x y ξ η :=
  Iff.rfl

theorem SatisfiesWeakMTW.mtwTensor_nonneg (h : SatisfiesWeakMTW c U V) (hx : x ∈ U)
    (hy : y ∈ interior V) (hηξ : η ξ = 0) : 0 ≤ mtwTensor c V x y ξ η :=
  h x hx y hy ξ η hηξ

theorem SatisfiesWeakMTW.mono (h : SatisfiesWeakMTW c U V) (hU : U' ⊆ U) :
    SatisfiesWeakMTW c U' V :=
  fun x hx ↦ h x (hU hx)

theorem SatisfiesStrongMTW.mono (h : SatisfiesStrongMTW c U V) (hU : U' ⊆ U) :
    SatisfiesStrongMTW c U' V :=
  let ⟨C, hC, h⟩ := h
  ⟨C, hC, fun x hx ↦ h x (hU hx)⟩

/-- Under the strong Ma–Trudinger–Wang condition the tensor is positive on nonzero orthogonal
pairs. -/
theorem SatisfiesStrongMTW.mtwTensor_pos (h : SatisfiesStrongMTW c U V) (hx : x ∈ U)
    (hy : y ∈ interior V) (hξ : ξ ≠ 0) (hη : η ≠ 0) (hηξ : η ξ = 0) :
    0 < mtwTensor c V x y ξ η := by
  obtain ⟨C, hC, h⟩ := h
  exact lt_of_lt_of_le (by positivity) (h x hx y hy ξ η hηξ)

/-- The strong Ma–Trudinger–Wang condition implies the weak one. -/
theorem SatisfiesStrongMTW.satisfiesWeakMTW (h : SatisfiesStrongMTW c U V) :
    SatisfiesWeakMTW c U V := by
  obtain ⟨C, hC, h⟩ := h
  exact fun x hx y hy ξ η hηξ ↦ le_trans (by positivity) (h x hx y hy ξ η hηξ)

/-- **The Ma–Trudinger–Wang conditions are void in dimension one.** On a source space of dimension
at most one, a momentum annihilating a nonzero direction is zero, so every cost satisfies the
strong Ma–Trudinger–Wang condition. -/
theorem satisfiesStrongMTW_of_rank_le_one (hE : Module.rank ℝ E ≤ 1) (c : E × Y → ℝ) (U : Set E)
    (V : Set Y) : SatisfiesStrongMTW c U V := by
  obtain ⟨v, hv⟩ := rank_le_one_iff.1 hE
  refine ⟨1, one_pos, fun x _ y _ ξ η hηξ ↦ ?_⟩
  obtain ⟨r, rfl⟩ := hv ξ
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hηv : η v = 0 := by simpa [hr] using hηξ
  have hη : η = 0 := by
    ext w
    obtain ⟨s, rfl⟩ := hv w
    simp [hηv]
  simp [hη]

end Tensor

/-! ### The quadratic cost -/

section Quadratic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The quadratic cost has vanishing Ma–Trudinger–Wang tensor.** For `‖x - y‖ ^ 2 / 2` on a real
inner product space, the cost in momentum coordinates is a quadratic polynomial in `t` whose `t²`
coefficient `‖ξ‖ ^ 2 / 2` does not depend on the momentum, whatever the target set `V`. -/
@[simp]
theorem mtwTensor_norm_sub_sq_div_two (V : Set F) (x y ξ : F) (η : StrongDual ℝ F) :
    mtwTensor (fun z : F × F ↦ ‖z.1 - z.2‖ ^ 2 / 2) V x y ξ η = 0 := by
  have h (z : F) : deriv (deriv fun t : ℝ ↦ ‖x + t • ξ - z‖ ^ 2 / 2) 0 = ‖ξ‖ ^ 2 := by
    have hf : (fun t : ℝ ↦ ‖x + t • ξ - z‖ ^ 2 / 2) =
        fun t ↦ ‖x - z‖ ^ 2 / 2 + ⟪ξ, x - z⟫ * t + ‖ξ‖ ^ 2 / 2 * t ^ 2 := by
      funext t
      rw [norm_add_smul_sub_sq]
      ring
    rw [hf, deriv_deriv_quadratic]
    ring
  simp only [mtwTensor_def, h, deriv_const', neg_zero]

/-- The quadratic cost satisfies the weak Ma–Trudinger–Wang condition. -/
theorem satisfiesWeakMTW_norm_sub_sq_div_two (U V : Set F) :
    SatisfiesWeakMTW (fun z : F × F ↦ ‖z.1 - z.2‖ ^ 2 / 2) U V := by
  intro x _ y _ ξ η _
  simp

/-- **The quadratic cost and the strong Ma–Trudinger–Wang condition.** On a nonempty source set
and a target set with nonempty interior, the quadratic cost satisfies the strong condition exactly
when the space has dimension at most one. -/
theorem satisfiesStrongMTW_norm_sub_sq_div_two_iff {U V : Set F} (hU : U.Nonempty)
    (hV : (interior V).Nonempty) :
    SatisfiesStrongMTW (fun z : F × F ↦ ‖z.1 - z.2‖ ^ 2 / 2) U V ↔ Module.rank ℝ F ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ satisfiesStrongMTW_of_rank_le_one h _ _ _⟩
  by_contra! hF
  have : Nontrivial F := rank_pos_iff_nontrivial.1 (zero_lt_one.trans hF)
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : F)
  obtain ⟨ζ, hζ⟩ := exists_linearIndependent_pair_of_one_lt_rank hF hξ
  -- Remove from `ζ` its component along `ξ`; what remains is nonzero and orthogonal to `ξ`.
  set ζ' := ζ - (⟪ξ, ζ⟫ / ‖ξ‖ ^ 2) • ξ
  have hζ' : ζ' ≠ 0 := fun h0 ↦ (LinearIndependent.pair_iff' hξ).1 hζ _ (sub_eq_zero.1 h0).symm
  have hξζ' : innerSL ℝ ζ' ξ = 0 := by
    have : ‖ξ‖ ^ 2 ≠ 0 := by positivity
    simp only [innerSL_apply_apply, ζ', inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_comm ξ ζ]
    field_simp
    ring
  have hη : innerSL ℝ ζ' ≠ 0 := by
    rw [← norm_ne_zero_iff, innerSL_apply_norm]
    exact norm_ne_zero_iff.2 hζ'
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, hy⟩ := hV
  simpa using h.mtwTensor_pos hx hy hξ hη hξζ'

end Quadratic

/-! ### The cost `√(1 + ‖x - y‖ ^ 2)` -/

section SqrtOneAddNormSubSq

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Near `s = 0`, the momentum `p + s • η`, a perturbation of the momentum `p` of `y` at `x`, has
norm less than `1`, and its explicit preimage `x + q / √(1 - ‖q‖ ^ 2)` under the momentum map stays
in a neighbourhood `V` of `y`. -/
private theorem eventually_cExp_sqrt_one_add_norm_sub_sq_mem {V : Set F} {x y : F} (hV : V ∈ 𝓝 y)
    (η : StrongDual ℝ F) :
    ∀ᶠ s : ℝ in 𝓝 0, ‖-fderiv ℝ (fun x' ↦ √(1 + ‖x' - y‖ ^ 2)) x + s • η‖ < 1 ∧
      x + OpenPartialHomeomorph.univUnitBall.symm
        ((toDual ℝ F).symm (-fderiv ℝ (fun x' ↦ √(1 + ‖x' - y‖ ^ 2)) x + s • η)) ∈ V := by
  set p := -fderiv ℝ (fun x' ↦ √(1 + ‖x' - y‖ ^ 2)) x with hp_def
  have hp : (toDual ℝ F).symm p = OpenPartialHomeomorph.univUnitBall (y - x) :=
    toDual_symm_neg_fderiv_sqrt_one_add_norm_sub_sq x y
  have hball : (toDual ℝ F).symm p ∈ Metric.ball (0 : F) 1 :=
    hp ▸ OpenPartialHomeomorph.univUnitBall.map_source (mem_univ _)
  have hline : Continuous fun s : ℝ ↦ (toDual ℝ F).symm (p + s • η) := by fun_prop
  have hcont : ContinuousAt (fun s : ℝ ↦
      x + OpenPartialHomeomorph.univUnitBall.symm ((toDual ℝ F).symm (p + s • η))) 0 :=
    continuousAt_const.add ((OpenPartialHomeomorph.univUnitBall.continuousAt_symm (by
      simpa only [zero_smul, add_zero, OpenPartialHomeomorph.univUnitBall_target] using hball)).comp
        hline.continuousAt)
  have hy : x + OpenPartialHomeomorph.univUnitBall.symm ((toDual ℝ F).symm (p + (0 : ℝ) • η)) =
      y := by
    rw [zero_smul, add_zero, hp, OpenPartialHomeomorph.univUnitBall.left_inv (mem_univ _),
      add_sub_cancel]
  have hnorm : Continuous fun s : ℝ ↦ ‖p + s • η‖ := by fun_prop
  have hp1 : ‖p‖ < 1 := by simpa using hball
  exact (hnorm.continuousAt.eventually_lt continuousAt_const (by simpa using hp1)).and
    (hcont.eventually_mem (by rwa [hy]))

/-- The second `t`-derivative at `0` of `√(1 + ‖x + t • ξ - cExp c V x q‖ ^ 2)`: the second
derivative in the source direction `ξ` of the cost in momentum coordinates. -/
private theorem deriv_deriv_sqrt_one_add_norm_sub_sq_cExp {V : Set F} {x ξ : F}
    {q : StrongDual ℝ F} (hq : ‖q‖ < 1)
    (hV : x + OpenPartialHomeomorph.univUnitBall.symm ((toDual ℝ F).symm q) ∈ V) :
    deriv (deriv fun t : ℝ ↦ √(1 + ‖x + t • ξ -
      cExp (fun z : F × F ↦ √(1 + ‖z.1 - z.2‖ ^ 2)) V x q‖ ^ 2)) 0 =
      (‖ξ‖ ^ 2 - q ξ ^ 2) * √(1 - ‖q‖ ^ 2) := by
  have hr : 0 < 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  have hσ : 0 < √(1 - ‖q‖ ^ 2) := Real.sqrt_pos.2 hr
  set σ := (√(1 - ‖q‖ ^ 2))⁻¹
  have hσsq : σ ^ 2 = (1 - ‖q‖ ^ 2)⁻¹ := by rw [inv_pow, Real.sq_sqrt hr.le]
  have hf : (fun t : ℝ ↦ √(1 + ‖x + t • ξ - (x + σ • (toDual ℝ F).symm q)‖ ^ 2)) =
      fun t ↦ √((1 + σ ^ 2 * ‖q‖ ^ 2) + (-2 * σ * q ξ) * t + ‖ξ‖ ^ 2 * t ^ 2) := by
    funext t
    rw [norm_add_smul_sub_sq, sub_add_cancel_left, real_inner_comm]
    simp only [norm_neg, norm_smul, Real.norm_eq_abs, norm_map, mul_pow, sq_abs, inner_neg_left,
      real_inner_smul_left, toDual_symm_apply, mul_neg, neg_mul]
    congr 1
    ring
  have hA : 1 + σ ^ 2 * ‖q‖ ^ 2 = (1 - ‖q‖ ^ 2)⁻¹ := by
    rw [hσsq]
    field_simp
    ring
  rw [cExp_sqrt_one_add_norm_sub_sq hq hV, OpenPartialHomeomorph.univUnitBall_symm_apply,
    LinearIsometryEquiv.norm_map, hf, deriv_deriv_sqrt_quadratic_zero (by positivity), hA,
    Real.sqrt_inv]
  field_simp
  rw [hσsq]
  field_simp
  ring

/-- **The Ma–Trudinger–Wang tensor of `√(1 + ‖x - y‖ ^ 2)`.** On a real Hilbert space, at a target
point `y` interior to `V` and on an orthogonal pair `η ξ = 0`, the tensor of the cost
`√(1 + ‖x - y‖ ^ 2)` is
`((1 + ‖y - x‖ ^ 2) ‖ξ‖ ^ 2 - ⟪y - x, ξ⟫ ^ 2) (‖η‖ ^ 2 + η (y - x) ^ 2) / √(1 + ‖y - x‖ ^ 2)`. -/
theorem mtwTensor_sqrt_one_add_norm_sub_sq {V : Set F} {x y ξ : F} {η : StrongDual ℝ F}
    (hV : V ∈ 𝓝 y) (hηξ : η ξ = 0) :
    mtwTensor (fun z : F × F ↦ √(1 + ‖z.1 - z.2‖ ^ 2)) V x y ξ η =
      ((1 + ‖y - x‖ ^ 2) * ‖ξ‖ ^ 2 - ⟪y - x, ξ⟫ ^ 2) * (‖η‖ ^ 2 + η (y - x) ^ 2) /
        √(1 + ‖y - x‖ ^ 2) := by
  set ρ := √(1 + ‖y - x‖ ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  have hρsq : ρ ^ 2 = 1 + ‖y - x‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hev := eventually_cExp_sqrt_one_add_norm_sub_sq_mem (x := x) hV η
  set p := -fderiv ℝ (fun x' ↦ √(1 + ‖x' - y‖ ^ 2)) x with hp_def
  have hp : p = innerSL ℝ (ρ⁻¹ • (y - x)) := by
    rw [hp_def, neg_fderiv_sqrt_one_add_norm_sub_sq, OpenPartialHomeomorph.univUnitBall_apply]
  have hpr : 1 - ‖p‖ ^ 2 = (ρ ^ 2)⁻¹ := by
    rw [hp, innerSL_apply_norm, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, mul_pow, inv_pow]
    field_simp
    linarith
  -- There, the second `t`-derivative is `‖ξ‖² - (p ξ)²` times the square root of a quadratic
  -- polynomial in `s`.
  have hG : (fun s : ℝ ↦ deriv (deriv fun t : ℝ ↦ √(1 + ‖x + t • ξ -
      cExp (fun z : F × F ↦ √(1 + ‖z.1 - z.2‖ ^ 2)) V x (p + s • η)‖ ^ 2)) 0) =ᶠ[𝓝 0]
      fun s ↦ (‖ξ‖ ^ 2 - p ξ ^ 2) * √((1 - ‖p‖ ^ 2) + (-2 * η ((toDual ℝ F).symm p)) * s +
        (-‖η‖ ^ 2) * s ^ 2) := by
    have hsymm : p ((toDual ℝ F).symm η) = η ((toDual ℝ F).symm p) := by
      rw [← toDual_symm_apply, ← toDual_symm_apply, real_inner_comm]
    filter_upwards [hev] with s hs
    rw [deriv_deriv_sqrt_one_add_norm_sub_sq_cExp hs.1 hs.2]
    congr 2
    · simp [hηξ]
    · rw [← LinearIsometryEquiv.norm_map (toDual ℝ F).symm]
      simp only [map_add, map_smul, norm_add_sq_real, norm_map, toDual_symm_apply, hsymm,
        smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_mul]
      ring
  have hpη : η ((toDual ℝ F).symm p) = ρ⁻¹ * η (y - x) := by
    rw [hp_def, toDual_symm_neg_fderiv_sqrt_one_add_norm_sub_sq,
      OpenPartialHomeomorph.univUnitBall_apply, map_smul, smul_eq_mul]
  have hpξ : p ξ = ρ⁻¹ * ⟪y - x, ξ⟫ := by
    rw [hp]
    simp [innerSL_apply_apply, inner_sub_left]
  simp only [mtwTensor_def]
  rw [← hp_def, hG.deriv.deriv_eq]
  simp only [deriv_const_mul_field']
  rw [deriv_deriv_sqrt_quadratic_zero (by rw [hpr]; positivity)]
  simp only [hpr, hpη, hpξ, Real.sqrt_inv, Real.sqrt_sq hρ.le]
  field_simp
  rw [hρsq]
  ring

/-- **The cost `√(1 + ‖x - y‖ ^ 2)` satisfies the strong Ma–Trudinger–Wang condition at bounded
distance.** On a real Hilbert space, if every pair of points of `U` and `V` lies at distance at
most `R`, the condition holds on `U × V` with the constant `1 / √(1 + R ^ 2)`. -/
theorem satisfiesStrongMTW_sqrt_one_add_norm_sub_sq {U V : Set F} {R : ℝ}
    (hR : ∀ x ∈ U, ∀ y ∈ V, dist x y ≤ R) :
    SatisfiesStrongMTW (fun z : F × F ↦ √(1 + ‖z.1 - z.2‖ ^ 2)) U V := by
  refine ⟨(√(1 + R ^ 2))⁻¹, by positivity, fun x hx y hy ξ η hηξ ↦ ?_⟩
  rw [mtwTensor_sqrt_one_add_norm_sub_sq (mem_interior_iff_mem_nhds.1 hy) hηξ]
  have hz : ‖y - x‖ ≤ R := by
    rw [← dist_eq_norm, dist_comm]
    exact hR x hx y (interior_subset hy)
  have hCS : ⟪y - x, ξ⟫ ^ 2 ≤ ‖y - x‖ ^ 2 * ‖ξ‖ ^ 2 := by
    have := real_inner_mul_inner_self_le (y - x) ξ
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    nlinarith
  have h₁ : ‖ξ‖ ^ 2 ≤ (1 + ‖y - x‖ ^ 2) * ‖ξ‖ ^ 2 - ⟪y - x, ξ⟫ ^ 2 := by nlinarith
  have h₂ : ‖η‖ ^ 2 ≤ ‖η‖ ^ 2 + η (y - x) ^ 2 := by nlinarith [sq_nonneg (η (y - x))]
  have hρ : √(1 + ‖y - x‖ ^ 2) ≤ √(1 + R ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (y - x)])
  have hρpos : 0 < √(1 + ‖y - x‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  calc (√(1 + R ^ 2))⁻¹ * ‖ξ‖ ^ 2 * ‖η‖ ^ 2
      = ‖ξ‖ ^ 2 * ‖η‖ ^ 2 * (√(1 + R ^ 2))⁻¹ := by ring
    _ ≤ ‖ξ‖ ^ 2 * ‖η‖ ^ 2 * (√(1 + ‖y - x‖ ^ 2))⁻¹ := by gcongr
    _ ≤ ((1 + ‖y - x‖ ^ 2) * ‖ξ‖ ^ 2 - ⟪y - x, ξ⟫ ^ 2) * (‖η‖ ^ 2 + η (y - x) ^ 2) *
        (√(1 + ‖y - x‖ ^ 2))⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul h₁ h₂ (by positivity) ((sq_nonneg _).trans h₁)) (by positivity)
    _ = _ := (div_eq_mul_inv _ _).symm

end SqrtOneAddNormSubSq

end TauCeti
