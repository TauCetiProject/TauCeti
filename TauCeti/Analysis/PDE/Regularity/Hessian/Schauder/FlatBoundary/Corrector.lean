/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.PoissonIntegral.HalfSpace
public import TauCeti.Analysis.Holder.HalfSpace
public import TauCeti.Analysis.InnerProductSpace.Euclidean.CoordinateHyperplane
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Projection

/-!
# The boundary corrector for Poisson's equation at a flat boundary

This file builds the corrector used to prove `C^{2,α}` regularity up to the hyperplane `y 0 = 0`
of `ℝ^{n+1}` for solutions of Poisson's equation with zero Dirichlet data there
(`TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.Basic`). Let `g` be bounded and
`α`-Hölder on the hyperplane, `0 < α < 1`, and let `P[g]` be its Poisson integral in the half-space
`0 < y 0` (`TauCeti.halfSpacePoissonIntegral`). The corrector is

`P = halfSq · P[g]`, `halfSq y = y₀² / 2` (`TauCeti.PDE.FlatBoundary.corrector`).

It vanishes on the hyperplane together with its first derivatives, its Laplacian tends to `g`
there from the half-space `0 < y 0`, and so does its second derivative to
`g D²halfSq = g e₀* ⊗ e₀*`. Quantitatively, at height
`t = y 0 > 0` (`TauCeti.PDE.FlatBoundary.exists_corrector_bounds`),

`|P y| = O(t²)`, `‖DP y‖ = O(t^(α + 1) + t)`, `‖D²P y - g(y') D²halfSq‖ = O(t^α)`,
`‖D³P y‖ = O(t^(α - 1))`,

`y'` the foot of `y` on the hyperplane. These follow from the derivative estimates
`‖D^k P[g]‖ = O(t^(α - k))` of the Poisson integral of Hölder data
(`TauCeti.exists_norm_iteratedFDeriv_halfSpacePoissonIntegral_le`) and the Leibniz rule. Hence the
second derivative of `P`, extended to the hyperplane by `g D²halfSq`, is `α`-Hölder up to the
hyperplane on half-balls centred on it (`TauCeti.PDE.FlatBoundary.correctorHessian`,
`TauCeti.PDE.FlatBoundary.exists_holderOnWith_correctorHessian`), by the weighted derivative
criterion `TauCeti.holderOnWith_of_norm_fderiv_le_mul_rpow`.

## Main declarations

* `TauCeti.PDE.FlatBoundary.corrector`: the corrector `halfSq · P[g]`.
* `TauCeti.PDE.FlatBoundary.exists_corrector_bounds`: its estimates near the hyperplane.
* `TauCeti.PDE.FlatBoundary.correctorHessian` and
  `TauCeti.PDE.FlatBoundary.exists_holderOnWith_correctorHessian`: its second derivative,
  extended to the hyperplane, is Hölder up to the hyperplane.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.10 (interior derivative estimates for harmonic functions).
-/

public section

noncomputable section

open InnerProductSpace Laplacian Metric Set Filter Topology
open Submodule (orthogonalProjectionOnto)
open scoped NNReal RealInnerProductSpace
namespace TauCeti

namespace PDE

namespace FlatBoundary

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The first coordinate vector `e₀`, the inner normal of the half-space `0 < x 0`. -/
local notation "e₀" => (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) : E)

/-- The first coordinate, the height above the hyperplane `x 0 = 0`. -/
local notation "ℓ₀" => (EuclideanSpace.proj (0 : Fin (n + 1)) : E →L[ℝ] ℝ)

/-! ### The quadratic `a(y) = y₀² / 2` -/

/-- The quadratic `y ↦ y₀² / 2`, which vanishes to second order on the hyperplane `y 0 = 0` and
whose second derivative is `e₀* ⊗ e₀*`. -/
def halfSq (y : E) : ℝ := y 0 ^ 2 / 2

theorem halfSq_apply (y : E) : halfSq y = y 0 ^ 2 / 2 := (rfl)

theorem hasFDerivAt_halfSq (y : E) : HasFDerivAt halfSq (y 0 • ℓ₀) y := by
  have h := (ContinuousLinearMap.hasFDerivAt ℓ₀ (x := y)).mul
    (ContinuousLinearMap.hasFDerivAt ℓ₀ (x := y))
  have : halfSq = fun z : E ↦ (1 / 2 : ℝ) * (ℓ₀ z * ℓ₀ z) := by
    funext z
    simp [halfSq]
    ring
  rw [this]
  convert h.const_mul (1 / 2 : ℝ) using 1
  ext m
  simp
  ring

theorem fderiv_halfSq : fderiv ℝ (halfSq (n := n)) = fun y ↦ y 0 • ℓ₀ :=
  funext fun y ↦ (hasFDerivAt_halfSq y).fderiv

theorem hasFDerivAt_fderiv_halfSq (y : E) :
    HasFDerivAt (fderiv ℝ (halfSq (n := n))) (ContinuousLinearMap.smulRight ℓ₀ ℓ₀) y := by
  rw [fderiv_halfSq]
  have := (ContinuousLinearMap.hasFDerivAt ℓ₀ (x := y)).smul_const ℓ₀
  convert this using 1
  funext z
  simp

theorem fderiv_fderiv_halfSq (y : E) :
    fderiv ℝ (fderiv ℝ (halfSq (n := n))) y = ContinuousLinearMap.smulRight ℓ₀ ℓ₀ :=
  (hasFDerivAt_fderiv_halfSq y).fderiv

theorem contDiff_halfSq : ContDiff ℝ ⊤ (halfSq (n := n)) := by
  have : halfSq = fun z : E ↦ ℓ₀ z ^ 2 / 2 := by
    funext z
    simp [halfSq]
  rw [this]
  fun_prop

/-- The second derivative of `halfSq` is the constant bilinear form `(m, m') ↦ m₀ m'₀`. -/
theorem iteratedFDeriv_two_halfSq_apply (y : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 halfSq y m = m 0 0 * m 1 0 := by
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_halfSq]
  simp

/-- The second derivative of `halfSq` does not depend on the point. -/
theorem iteratedFDeriv_two_halfSq_eq_iteratedFDeriv_two_halfSq (y y' : E) :
    iteratedFDeriv ℝ 2 (halfSq (n := n)) y = iteratedFDeriv ℝ 2 halfSq y' := by
  ext m
  rw [iteratedFDeriv_two_halfSq_apply, iteratedFDeriv_two_halfSq_apply]

private theorem norm_iteratedFDeriv_zero_halfSq (y : E) :
    ‖iteratedFDeriv ℝ 0 (halfSq (n := n)) y‖ = y 0 ^ 2 / 2 := by
  rw [norm_iteratedFDeriv_zero, halfSq, Real.norm_of_nonneg (by positivity)]

private theorem norm_iteratedFDeriv_one_halfSq_le (y : E) :
    ‖iteratedFDeriv ℝ 1 (halfSq (n := n)) y‖ ≤ |y 0| := by
  rw [norm_iteratedFDeriv_one, fderiv_halfSq, norm_smul, Real.norm_eq_abs]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun m ↦ ?_
  simpa using PiLp.norm_apply_le m 0

private theorem norm_proj_zero_le : ‖ℓ₀‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun m ↦ by
    simpa using PiLp.norm_apply_le m 0

theorem norm_iteratedFDeriv_two_halfSq_le (y : E) :
    ‖iteratedFDeriv ℝ 2 (halfSq (n := n)) y‖ ≤ 1 := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, fderiv_fderiv_halfSq]
  calc ‖ContinuousLinearMap.smulRight ℓ₀ ℓ₀‖ = ‖ℓ₀‖ * ‖ℓ₀‖ :=
        ContinuousLinearMap.norm_smulRight_apply _ _
    _ ≤ 1 * 1 := mul_le_mul norm_proj_zero_le norm_proj_zero_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private theorem iteratedFDeriv_three_halfSq (y : E) :
    iteratedFDeriv ℝ 3 (halfSq (n := n)) y = 0 := by
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_one, funext fderiv_fderiv_halfSq, fderiv_fun_const]
  simp

/-- The Laplacian of `halfSq` is `1`. -/
@[simp]
theorem laplacian_halfSq (y : E) : Δ (halfSq (n := n)) y = 1 := by
  have h : halfSq (n := n) = (1 / 2 : ℝ) • fun z : E ↦ ⟪e₀, z⟫ ^ 2 := by
    funext z
    rw [halfSq_apply, Pi.smul_apply, real_inner_comm, EuclideanSpace.real_inner_single_one_right,
      smul_eq_mul]
    ring
  have hd : ContDiff ℝ 2 fun z : E ↦ ⟪e₀, z⟫ ^ 2 := (contDiff_const.inner ℝ contDiff_id).pow 2
  rw [h, laplacian_smul _ hd.contDiffAt, laplacian_inner_sq]
  simp

/-! ### Leibniz bounds for `halfSq * (f - c)` -/

/-- **Leibniz bounds.** Let `f` be `C³` on an open set containing `y`, at height `t = y 0 > 0`,
with `|f y - c| ≤ B₀ t^α` and `‖D^j f y‖ ≤ B t^(α - j)` for `j = 1, 2, 3`. Then the derivatives of
order `1`, `2` and `3` of `halfSq * (f - c)` at `y` are at most multiples of `t^(α + 1)`, `t^α`
and `t^(α - 1)`. -/
private theorem norm_iteratedFDeriv_halfSq_mul_sub_le {s : Set E} (hs : IsOpen s) {f : E → ℝ}
    (hf : ContDiffOn ℝ 3 f s) {y : E} (hy : y ∈ s) (ht : 0 < y 0) {c α B₀ B : ℝ}
    (h₀ : |f y - c| ≤ B₀ * y 0 ^ α) (hB : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j f y‖ ≤ B * y 0 ^ (α - j)) :
    ‖iteratedFDeriv ℝ 1 (fun z ↦ halfSq z * (f z - c)) y‖ ≤ (B / 2 + B₀) * y 0 ^ (α + 1) ∧
    ‖iteratedFDeriv ℝ 2 (fun z ↦ halfSq z * (f z - c)) y‖ ≤ (5 * B / 2 + B₀) * y 0 ^ α ∧
    ‖iteratedFDeriv ℝ 3 (fun z ↦ halfSq z * (f z - c)) y‖ ≤ (13 * B / 2) * y 0 ^ (α - 1) := by
  set t := y 0
  have hfc : ContDiffOn ℝ 3 (fun z ↦ f z - c) s := hf.sub contDiffOn_const
  have hleib : ∀ k : ℕ, k ≤ 3 →
      ‖iteratedFDeriv ℝ k (fun z ↦ halfSq z * (f z - c)) y‖ ≤
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i halfSq y‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun z ↦ f z - c) y‖ := by
    intro k hk
    have h := norm_iteratedFDerivWithin_mul_le ((contDiff_halfSq (n := n)).contDiffOn.of_le
      le_top) hfc hs.uniqueDiffOn hy (n := k) (by exact_mod_cast hk)
    simpa only [iteratedFDerivWithin_of_isOpen _ hs hy] using h
  have hfj : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j (fun z ↦ f z - c) y‖ ≤ B * t ^ (α - j) := by
    intro j hj1 hj3
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj1
    simp_rw [sub_eq_add_neg]
    rw [iteratedFDeriv_succ_add_const]
    exact hB _ hj1 hj3
  have hf0 : ‖iteratedFDeriv ℝ 0 (fun z ↦ f z - c) y‖ ≤ B₀ * t ^ α := by
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have ha0 := norm_iteratedFDeriv_zero_halfSq y
  have ha1 := norm_iteratedFDeriv_one_halfSq_le y
  have ha2 := norm_iteratedFDeriv_two_halfSq_le y
  have ha3 : ‖iteratedFDeriv ℝ 3 (halfSq (n := n)) y‖ = 0 := by
    rw [iteratedFDeriv_three_halfSq, norm_zero]
  rw [abs_of_pos ht] at ha1
  have e1 : t ^ 2 * t ^ (α - 1) = t ^ (α + 1) := by
    rw [mul_comm, ← Real.rpow_add_natCast ht.ne']; push_cast; ring_nf
  have e2 : t ^ 2 * t ^ (α - 2) = t ^ α := by
    rw [mul_comm, ← Real.rpow_add_natCast ht.ne']; push_cast; ring_nf
  have e3 : t ^ 2 * t ^ (α - 3) = t ^ (α - 1) := by
    rw [mul_comm, ← Real.rpow_add_natCast ht.ne']; push_cast; ring_nf
  have e4 : t * t ^ α = t ^ (α + 1) := by
    rw [mul_comm, ← Real.rpow_add_one ht.ne']
  have e5 : t * t ^ (α - 1) = t ^ α := by
    rw [mul_comm, ← Real.rpow_add_one ht.ne', sub_add_cancel]
  have e6 : t * t ^ (α - 2) = t ^ (α - 1) := by
    rw [mul_comm, ← Real.rpow_add_one ht.ne']
    ring_nf
  have c21 : ((2 : ℕ).choose 1 : ℝ) = 2 := by norm_num
  have c31 : ((3 : ℕ).choose 1 : ℝ) = 3 := by norm_num
  have c32 : ((3 : ℕ).choose 2 : ℝ) = 3 := by norm_num [Nat.choose]
  have h1 := hfj 1 le_rfl (by norm_num)
  have h2 := hfj 2 (by norm_num) (by norm_num)
  have h3 := hfj 3 (by norm_num) le_rfl
  push_cast at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · refine (hleib 1 (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, one_mul, Nat.reduceSub]
    calc ‖iteratedFDeriv ℝ 0 halfSq y‖ * ‖iteratedFDeriv ℝ 1 (fun z ↦ f z - c) y‖ +
          ‖iteratedFDeriv ℝ 1 halfSq y‖ * ‖iteratedFDeriv ℝ 0 (fun z ↦ f z - c) y‖
        ≤ t ^ 2 / 2 * (B * t ^ (α - 1)) + t * (B₀ * t ^ α) := by
          rw [ha0]
          gcongr
      _ = B / 2 * (t ^ 2 * t ^ (α - 1)) + B₀ * (t * t ^ α) := by ring
      _ = (B / 2 + B₀) * t ^ (α + 1) := by
          rw [e1, e4]
          ring
  · refine (hleib 2 (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, one_mul, Nat.reduceSub, c21]
    calc ‖iteratedFDeriv ℝ 0 halfSq y‖ * ‖iteratedFDeriv ℝ 2 (fun z ↦ f z - c) y‖ +
          2 * ‖iteratedFDeriv ℝ 1 halfSq y‖ * ‖iteratedFDeriv ℝ 1 (fun z ↦ f z - c) y‖ +
          ‖iteratedFDeriv ℝ 2 halfSq y‖ * ‖iteratedFDeriv ℝ 0 (fun z ↦ f z - c) y‖
        ≤ t ^ 2 / 2 * (B * t ^ (α - 2)) + 2 * t * (B * t ^ (α - 1)) + 1 * (B₀ * t ^ α) := by
          rw [ha0]
          gcongr
      _ = B / 2 * (t ^ 2 * t ^ (α - 2)) + 2 * B * (t * t ^ (α - 1)) + B₀ * t ^ α := by ring
      _ = (5 * B / 2 + B₀) * t ^ α := by
          rw [e2, e5]
          ring
  · refine (hleib 3 le_rfl).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, one_mul, Nat.reduceSub, c31, c32, ha3, zero_mul, add_zero]
    calc ‖iteratedFDeriv ℝ 0 halfSq y‖ * ‖iteratedFDeriv ℝ 3 (fun z ↦ f z - c) y‖ +
          3 * ‖iteratedFDeriv ℝ 1 halfSq y‖ * ‖iteratedFDeriv ℝ 2 (fun z ↦ f z - c) y‖ +
          3 * ‖iteratedFDeriv ℝ 2 halfSq y‖ * ‖iteratedFDeriv ℝ 1 (fun z ↦ f z - c) y‖
        ≤ t ^ 2 / 2 * (B * t ^ (α - 3)) + 3 * t * (B * t ^ (α - 2)) +
            3 * 1 * (B * t ^ (α - 1)) := by
          rw [ha0]
          gcongr
      _ = B / 2 * (t ^ 2 * t ^ (α - 3)) + 3 * B * (t * t ^ (α - 2)) +
            3 * B * t ^ (α - 1) := by ring
      _ = 13 * B / 2 * t ^ (α - 1) := by
          rw [e3, e6]
          ring

/-! ### The corrector `halfSq · P[g]` -/

/-- The unit normal `e₀`, as a point of the unit sphere for the Poisson integral. -/
def unitNormal : {w : E // ‖w‖ = 1} := ⟨e₀, by simp⟩

local notation "v₀" => (unitNormal (n := n))

@[simp]
theorem coe_unitNormal : ((v₀ : {w : E // ‖w‖ = 1}) : E) = e₀ := (rfl)

/-- The bounding hyperplane `y 0 = 0`, as a subspace. -/
local notation "V" => (ℝ ∙ ((v₀ : {w : E // ‖w‖ = 1}) : E))ᗮ

/-- The height above the hyperplane is the first coordinate. -/
theorem inner_unitNormal (y : E) : ⟪((v₀ : {w : E // ‖w‖ = 1}) : E), y⟫ = y 0 := by
  rw [coe_unitNormal, real_inner_comm, EuclideanSpace.real_inner_single_one_right]

theorem mem_hyperplane_iff (y : E) : y ∈ V ↔ y 0 = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_unitNormal]

/-- The orthogonal projection of `y` onto the hyperplane, its foot, is `y - y₀ e₀`. -/
theorem coe_orthogonalProjectionOnto_hyperplane (y : E) :
    (orthogonalProjectionOnto V y : E) = y - y 0 • e₀ :=
  coe_orthogonalProjectionOnto_single_one_apply 0 y

/-- A point of the hyperplane is its own foot. -/
theorem coe_orthogonalProjectionOnto_hyperplane_of_apply_eq_zero {y : E} (hy : y 0 = 0) :
    (orthogonalProjectionOnto V y : E) = y := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply]
  exact Submodule.starProjection_eq_self_iff.2 ((mem_hyperplane_iff y).2 hy)

/-- The corrector `halfSq · P[g]`: it vanishes on the hyperplane together with its first
derivatives, while its second derivative tends to `g e₀* ⊗ e₀*` at the hyperplane from the
half-space `0 < y 0`. -/
def corrector (g : V → ℝ) (y : E) : ℝ :=
  halfSq y * halfSpacePoissonIntegral v₀ g y

theorem corrector_apply (g : V → ℝ) (y : E) :
    corrector g y = halfSq y * halfSpacePoissonIntegral v₀ g y :=
  (rfl)

/-- The corrector vanishes on the hyperplane. -/
theorem corrector_eq_zero (g : V → ℝ) {y : E} (hy : y 0 = 0) : corrector g y = 0 := by
  simp [corrector_apply, halfSq_apply, hy]

/-- **Estimates for the corrector.** For bounded `α`-Hölder data `g` there is `C` such that at
every point `y` at height `t = y 0 > 0` the corrector `P = halfSq · P[g]` is smooth and
`|P y| ≤ C t²`, `‖DP y‖ ≤ C (t^(α + 1) + t)`, `‖D²P y - g(y') D²halfSq‖ ≤ C t^α` and
`‖D³P y‖ ≤ C t^(α - 1)`, `y'` the foot of `y`. -/
theorem exists_corrector_bounds {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {g : V → ℝ}
    {Mg : ℝ} {Kg : ℝ≥0} (hgb : ∀ y, |g y| ≤ Mg) (hgH : HolderWith Kg α g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E, 0 < y 0 →
      ContDiffAt ℝ ⊤ (corrector g) y ∧
      |corrector g y| ≤ C * y 0 ^ 2 ∧
      ‖iteratedFDeriv ℝ 1 (corrector g) y‖ ≤ C * (y 0 ^ ((α : ℝ) + 1) + y 0) ∧
      ‖iteratedFDeriv ℝ 2 (corrector g) y -
          g (orthogonalProjectionOnto V y) • iteratedFDeriv ℝ 2 halfSq y‖ ≤ C * y 0 ^ (α : ℝ) ∧
      ‖iteratedFDeriv ℝ 3 (corrector g) y‖ ≤ C * y 0 ^ ((α : ℝ) - 1) := by
  obtain ⟨A, hA, hdev⟩ := exists_abs_halfSpacePoissonIntegral_sub_le v₀ hα hα1
  obtain ⟨C₁, hC₁, hD₁⟩ := exists_norm_iteratedFDeriv_halfSpacePoissonIntegral_le v₀ hα hα1 1
  obtain ⟨C₂, hC₂, hD₂⟩ := exists_norm_iteratedFDeriv_halfSpacePoissonIntegral_le v₀ hα hα1 2
  obtain ⟨C₃, hC₃, hD₃⟩ := exists_norm_iteratedFDeriv_halfSpacePoissonIntegral_le v₀ hα hα1 3
  have hgm : MeasureTheory.AEStronglyMeasurable g := (hgH.continuous hα).aestronglyMeasurable
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgb 0)
  set B : ℝ := (C₁ + C₂ + C₃) * Kg
  set B₀ : ℝ := Kg * (A + 1)
  have hB : 0 ≤ B := by positivity
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨13 * B + 2 * B₀ + Mg, by positivity, fun y hy ↦ ?_⟩
  set t := y 0
  set h := halfSpacePoissonIntegral v₀ g
  set c := g (orthogonalProjectionOnto V y)
  have hharm := harmonicOnNhd_halfSpacePoissonIntegral v₀ hgm hgb
  have hcd : ∀ z : E, 0 < z 0 → ContDiffAt ℝ ⊤ h z := fun z hz ↦
    (InnerProductSpace.HarmonicAt.analyticAt
      (hharm z (by rwa [mem_ofPred_eq, inner_unitNormal]))).contDiffAt
  have hf3 : ContDiffOn ℝ 3 h {z : E | 0 < z 0} := fun z hz ↦
    ((hcd z hz).of_le le_top).contDiffWithinAt
  have h₀ : |h y - c| ≤ B₀ * t ^ (α : ℝ) := by
    have := hdev hgb hgH (by rwa [inner_unitNormal]) (orthogonalProjectionOnto V y)
    rw [coe_orthogonalProjectionOnto_hyperplane, sub_sub_cancel, norm_smul,
      Real.norm_of_nonneg hy.le, show ‖e₀‖ = 1 by simp, mul_one, inner_unitNormal]
      at this
    calc |h y - c| ≤ Kg * (A * t ^ (α : ℝ) + t ^ (α : ℝ)) := this
      _ = B₀ * t ^ (α : ℝ) := by ring
  have hBj : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ‖iteratedFDeriv ℝ j h y‖ ≤ B * t ^ ((α : ℝ) - j) := by
    intro j hj1 hj3
    have ht := Real.rpow_pos_of_pos hy ((α : ℝ) - j)
    have hKt : 0 ≤ (Kg : ℝ) * t ^ ((α : ℝ) - j) := by positivity
    have hCj : ∀ C' : ℝ, C' ≤ C₁ + C₂ + C₃ → C' * Kg * t ^ ((α : ℝ) - j) ≤
        B * t ^ ((α : ℝ) - j) := fun C' hC' ↦ by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right hC' hKt
    interval_cases j
    · refine (hD₁ hgb hgH (by rwa [inner_unitNormal]) le_rfl).trans ?_
      rw [inner_unitNormal]
      exact hCj C₁ (by linarith)
    · refine (hD₂ hgb hgH (by rwa [inner_unitNormal]) (by norm_num)).trans ?_
      rw [inner_unitNormal]
      exact hCj C₂ (by linarith)
    · refine (hD₃ hgb hgH (by rwa [inner_unitNormal]) (by norm_num)).trans ?_
      rw [inner_unitNormal]
      exact hCj C₃ (by linarith)
  obtain ⟨L1, L2, L3⟩ := norm_iteratedFDeriv_halfSq_mul_sub_le
    (EuclideanSpace.isOpen_setOf_pos_apply 0) hf3 hy hy h₀ hBj
  -- The corrector is `halfSq · (h - c) + c · halfSq`.
  set F : E → ℝ := fun z ↦ halfSq z * (h z - c)
  have hdecomp : corrector g = F + c • halfSq := by
    funext z
    simp only [corrector_apply, F, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hFcd : ContDiffAt ℝ ⊤ F y :=
    (contDiff_halfSq.contDiffAt).mul ((hcd y hy).sub contDiffAt_const)
  have hacd : ContDiffAt ℝ ⊤ (c • halfSq (n := n)) y := (contDiff_halfSq.const_smul c).contDiffAt
  have hiter : ∀ k : ℕ, iteratedFDeriv ℝ k (corrector g) y =
      iteratedFDeriv ℝ k F y + c • iteratedFDeriv ℝ k halfSq y := by
    intro k
    rw [hdecomp, iteratedFDeriv_add_apply (hFcd.of_le le_top) (hacd.of_le le_top),
      iteratedFDeriv_const_smul_apply ((contDiff_halfSq.contDiffAt).of_le le_top)]
  have hc : |c| ≤ Mg := hgb _
  have hp : ∀ x : ℝ, 0 ≤ t ^ x := fun x ↦ (Real.rpow_pos_of_pos hy x).le
  refine ⟨hdecomp ▸ hFcd.add hacd, ?_, ?_, ?_, ?_⟩
  · rw [corrector_apply, abs_mul, abs_of_nonneg (by rw [halfSq_apply]; positivity)]
    calc halfSq y * |h y| ≤ t ^ 2 / 2 * Mg := by
          rw [halfSq_apply]
          exact mul_le_mul_of_nonneg_left
            (abs_halfSpacePoissonIntegral_le v₀ hgm hgb
              (by rwa [inner_unitNormal]))
            (by positivity)
      _ ≤ (13 * B + 2 * B₀ + Mg) * t ^ 2 := by nlinarith [sq_nonneg t]
  · rw [hiter 1]
    calc ‖iteratedFDeriv ℝ 1 F y + c • iteratedFDeriv ℝ 1 halfSq y‖
        ≤ ‖iteratedFDeriv ℝ 1 F y‖ + |c| * ‖iteratedFDeriv ℝ 1 halfSq y‖ := by
          rw [← Real.norm_eq_abs, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ (B / 2 + B₀) * t ^ ((α : ℝ) + 1) + Mg * t := by
          gcongr
          exact (norm_iteratedFDeriv_one_halfSq_le y).trans_eq (abs_of_pos hy)
      _ ≤ (13 * B + 2 * B₀ + Mg) * (t ^ ((α : ℝ) + 1) + t) := by
          have := hp ((α : ℝ) + 1)
          nlinarith
  · rw [hiter 2, add_sub_cancel_right]
    refine L2.trans ?_
    have := hp (α : ℝ)
    nlinarith
  · rw [hiter 3, iteratedFDeriv_three_halfSq, smul_zero, add_zero]
    refine L3.trans ?_
    have := hp ((α : ℝ) - 1)
    nlinarith

/-- The second derivative of the corrector above the hyperplane, extended to the hyperplane by
its boundary value `g(y') D²halfSq`. -/
def correctorHessian (g : V → ℝ) (y : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ :=
  if 0 < y 0 then iteratedFDeriv ℝ 2 (corrector g) y
  else g (orthogonalProjectionOnto V y) • iteratedFDeriv ℝ 2 halfSq y

@[simp]
theorem correctorHessian_of_pos (g : V → ℝ) {y : E} (hy : 0 < y 0) :
    correctorHessian g y = iteratedFDeriv ℝ 2 (corrector g) y := by
  simp only [correctorHessian, hy, ↓reduceIte]

theorem correctorHessian_of_apply_eq_zero (g : V → ℝ) {y : E} (hy : y 0 = 0) :
    correctorHessian g y = g (orthogonalProjectionOnto V y) • iteratedFDeriv ℝ 2 halfSq y := by
  simp only [correctorHessian, hy, lt_irrefl, ↓reduceIte]

/-- **The extended Hessian of the corrector is Hölder up to the hyperplane.** On every closed
half-ball centred on the hyperplane, `correctorHessian g` is `α`-Hölder, by the weighted
derivative criterion: its derivative above the hyperplane is `D³P = O(t^(α - 1))`, it is within
`O(t^α)` of its value at the foot, and on the hyperplane it is `g D²halfSq`. -/
theorem exists_holderOnWith_correctorHessian {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {g : V → ℝ} {Mg : ℝ} {Kg : ℝ≥0} (hgb : ∀ y, |g y| ≤ Mg) (hgH : HolderWith Kg α g) {x : E}
    (hx : x 0 = 0) (r : ℝ) :
    ∃ K : ℝ≥0, HolderOnWith K α (correctorHessian g) (closedBall x r ∩ {y | 0 ≤ y 0}) := by
  obtain ⟨C, hC, hP⟩ := exists_corrector_bounds hα hα1 hgb hgH
  set S := closedBall x r ∩ {y : E | 0 ≤ y 0}
  set K : ℝ≥0 := C.toNNReal + Kg with hKdef
  have hK : (K : ℝ) = C + Kg := by rw [hKdef, NNReal.coe_add, Real.coe_toNNReal _ hC]
  have hCK : C ≤ K := by
    rw [hK]
    linarith [NNReal.coe_nonneg Kg]
  have hinner : ∀ z : E, ⟪z, e₀⟫ = z 0 := fun z ↦ EuclideanSpace.real_inner_single_one_right z 0
  have hfootE : ∀ y : E, y - ⟪y, e₀⟫ • e₀ = (orthogonalProjectionOnto V y : E) := fun y ↦ by
    rw [hinner, coe_orthogonalProjectionOnto_hyperplane]
  have he₀ : ‖e₀‖ = 1 := by simp
  refine ⟨5 * K, ?_⟩
  refine holderOnWith_of_norm_fderiv_le_mul_rpow he₀ hα1.le
    ((convex_closedBall x r).inter ?_) (fun y hy ↦ by rw [hinner]; exact hy.2) ?_ ?_ ?_ ?_
  · exact convex_halfSpace_ge (ℓ₀).isLinear 0
  · -- The foot of a point of the half-ball lies in the half-ball.
    intro y hy
    rw [hfootE]
    refine ⟨?_, by rw [coe_orthogonalProjectionOnto_hyperplane]; simp⟩
    rw [mem_closedBall, dist_eq_norm,
      ← coe_orthogonalProjectionOnto_hyperplane_of_apply_eq_zero hx, ← Submodule.coe_sub,
      ← map_sub, Submodule.norm_coe]
    exact (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans hy.1
  · intro y _ hy0
    rw [hinner] at hy0
    obtain ⟨hcd, -, -, -, h3⟩ := hP y hy0
    have heq : correctorHessian g =ᶠ[𝓝 y] iteratedFDeriv ℝ 2 (corrector g) :=
      eventually_of_mem ((EuclideanSpace.isOpen_setOf_pos_apply 0).mem_nhds hy0)
        fun z (hz : 0 < z 0) ↦ correctorHessian_of_pos g hz
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 (corrector g)) y :=
      hcd.differentiableAt_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
    refine ⟨heq.differentiableAt_iff.2 hd, ?_⟩
    rw [heq.fderiv_eq, norm_fderiv_iteratedFDeriv, hinner]
    exact h3.trans (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hy0.le _))
  · intro y _
    rw [hfootE, hinner]
    by_cases hy0 : 0 < y 0
    · obtain ⟨-, -, -, h2, -⟩ := hP y hy0
      have hf0 : ¬ 0 < (orthogonalProjectionOnto V y : E) 0 := by
        rw [coe_orthogonalProjectionOnto_hyperplane]
        simp
      simp only [correctorHessian, hy0, hf0, ↓reduceIte,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        iteratedFDeriv_two_halfSq_eq_iteratedFDeriv_two_halfSq (orthogonalProjectionOnto V y : E) y]
      exact h2.trans (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hy0.le _))
    · have hy0' : y 0 = 0 := le_antisymm (not_lt.1 hy0) (by
        rcases ‹y ∈ S› with ⟨-, h⟩
        exact h)
      rw [coe_orthogonalProjectionOnto_hyperplane_of_apply_eq_zero hy0', sub_self, norm_zero]
      positivity
  · -- On the hyperplane the extended Hessian is `g D²halfSq`.
    refine HolderOnWith.of_dist_le fun y hy y' hy' ↦ ?_
    have hy0 : y 0 = 0 := by rw [← hinner]; exact hy.2
    have hy0' : y' 0 = 0 := by rw [← hinner]; exact hy'.2
    simp only [correctorHessian, hy0, hy0', lt_irrefl, ↓reduceIte]
    rw [iteratedFDeriv_two_halfSq_eq_iteratedFDeriv_two_halfSq y' y, dist_eq_norm,
      ← sub_smul (g (orthogonalProjectionOnto V y)) (g (orthogonalProjectionOnto V y'))
        (iteratedFDeriv ℝ 2 halfSq y), norm_smul]
    have hgd : ‖g (orthogonalProjectionOnto V y) - g (orthogonalProjectionOnto V y')‖ ≤
        Kg * dist y y' ^ (α : ℝ) := by
      have := hgH.dist_le (orthogonalProjectionOnto V y) (orthogonalProjectionOnto V y')
      rwa [Subtype.dist_eq, coe_orthogonalProjectionOnto_hyperplane_of_apply_eq_zero hy0,
        coe_orthogonalProjectionOnto_hyperplane_of_apply_eq_zero hy0',
        dist_eq_norm (g (orthogonalProjectionOnto V y))] at this
    calc ‖g (orthogonalProjectionOnto V y) - g (orthogonalProjectionOnto V y')‖ *
          ‖iteratedFDeriv ℝ 2 halfSq y‖
        ≤ Kg * dist y y' ^ (α : ℝ) * 1 :=
          mul_le_mul hgd (norm_iteratedFDeriv_two_halfSq_le y) (norm_nonneg _) (by positivity)
      _ ≤ (K : ℝ) * dist y y' ^ (α : ℝ) := by
          rw [mul_one]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hK]
          linarith

end FlatBoundary

end PDE

end TauCeti
