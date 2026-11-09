/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
import TauCeti.Analysis.InnerProductSpace.Coercive

/-!
# Lyapunov forms of bounded operators

A bounded operator `A` on a real inner product space *has a Lyapunov form* if there are a symmetric
operator `S` and a constant `c > 0` with

`c ‖v‖² ≤ ⟪S (A v), v⟫` for every `v`.

For matrices this is the Lyapunov inequality `S A + Aᵀ S ≥ 2c > 0`. The quadratic form
`q(v) = ⟪S v, v⟫` then decreases at rate at least `2c ‖v‖²` along every solution of `v' = -A v`,
and this monotonicity is what turns the condition into coercive estimates for the first-order
operator `d/ds + A` on the line. No symmetry of `A` is required, and `S` may be indefinite. A
symmetric operator with `α ‖v‖ ≤ ‖A v‖` has the Lyapunov form `S = A` with `c = α²`.

In finite dimensions, the inertia theorem of Ostrowski and Schneider identifies the operators with
a Lyapunov form as the hyperbolic ones, those without eigenvalues on the imaginary axis. This file
proves the easy half: an operator with a Lyapunov form has no purely imaginary eigenvalue
(`ContinuousLinearMap.HasLyapunovForm.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul`). The converse,
which needs the spectral splitting of `A`, is not proved here.

## Main declarations

* `ContinuousLinearMap.HasLyapunovForm`: `A` has a Lyapunov form, unfolded by
  `ContinuousLinearMap.hasLyapunovForm_iff`.
* `ContinuousLinearMap.hasLyapunovForm_of_isSymmetric`: a symmetric operator bounded below has a
  Lyapunov form; `ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric` applies this to a
  limit of symmetric operators.
* `ContinuousLinearMap.HasLyapunovForm.exists_eventually_nhds`: one Lyapunov form serves every
  operator close enough to `A`; `ContinuousLinearMap.isOpen_setOf_hasLyapunovForm` is the
  corresponding openness statement.
* `ContinuousLinearMap.HasLyapunovForm.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul`: `A` has no
  purely imaginary eigenvalue, and in particular is injective.
* `ContinuousLinearMap.HasLyapunovForm.neg_adjoint`: in finite dimensions, `-A†` has a Lyapunov
  form whenever `A` does. The formal adjoint of `d/ds + A` is `-d/ds + A†`; multiplying it by `-1`
  gives `d/ds - A†`, whose coefficient is `-A†`.

## References

* A. Ostrowski and H. Schneider, *Some theorems on the inertia of general matrices*, J. Math. Anal.
  Appl. **4** (1962), 72–84.
* R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press, 1991,
  §2.4 (the inertia theorem).
-/

public section

open Filter
open scoped InnerProductSpace Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : E →L[ℝ] E}

/-- A bounded operator `A` has a *Lyapunov form* if there are a symmetric operator `S` and a
constant `c > 0` with `c ‖v‖² ≤ ⟪S (A v), v⟫` for every `v`: the matrix inequality
`S A + Aᵀ S ≥ 2c`. In finite dimensions this characterizes hyperbolic operators. -/
def HasLyapunovForm (A : E →L[ℝ] E) : Prop :=
  ∃ S : E →L[ℝ] E, (S : E →ₗ[ℝ] E).IsSymmetric ∧ ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ

/-- Unfolding `ContinuousLinearMap.HasLyapunovForm`. -/
theorem hasLyapunovForm_iff : A.HasLyapunovForm ↔
    ∃ S : E →L[ℝ] E, (S : E →ₗ[ℝ] E).IsSymmetric ∧ ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ :=
  Iff.rfl

/-- **A symmetric operator bounded below has a Lyapunov form**, namely `S = A` with `c = α²`. -/
theorem hasLyapunovForm_of_isSymmetric (hA : (A : E →ₗ[ℝ] E).IsSymmetric) {α : ℝ} (hα : 0 < α)
    (hgap : ∀ v, α * ‖v‖ ≤ ‖A v‖) : A.HasLyapunovForm := by
  refine ⟨A, hA, α ^ 2, by positivity, fun v ↦ ?_⟩
  have h : ⟪A (A v), v⟫_ℝ = ‖A v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hA.apply_clm]
  rw [h, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (hgap v) 2

/-- **A limit of symmetric operators bounded below has a Lyapunov form.** If symmetric operators
`F i` tend to `A` and `α ‖v‖ ≤ ‖A v‖` with `α > 0`, then `A` is symmetric, so it has the Lyapunov
form `S = A`. -/
theorem hasLyapunovForm_of_tendsto_of_isSymmetric {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → E →L[ℝ] E} (hF : ∀ i, (F i : E →ₗ[ℝ] E).IsSymmetric) (hlim : Tendsto F l (𝓝 A))
    {α : ℝ} (hα : 0 < α) (hgap : ∀ v, α * ‖v‖ ≤ ‖A v‖) : A.HasLyapunovForm :=
  hasLyapunovForm_of_isSymmetric (isClosed_setOf_isSymmetric.mem_of_tendsto hlim (.of_forall hF))
    hα hgap

/-- **A Lyapunov form survives small perturbations.** If `A` has a Lyapunov form, then a single
symmetric `S` and a single constant `c > 0` satisfy `c ‖v‖² ≤ ⟪S (B v), v⟫` for every `B`
close enough to `A`. -/
theorem HasLyapunovForm.exists_eventually_nhds (h : A.HasLyapunovForm) :
    ∃ S : E →L[ℝ] E, (S : E →ₗ[ℝ] E).IsSymmetric ∧ ∃ c > 0,
      ∀ᶠ B in 𝓝 A, ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (B v), v⟫_ℝ := by
  obtain ⟨S, hS, c, hc, hcS⟩ := h
  refine ⟨S, hS, c / 2, by positivity, ?_⟩
  have hδ : 0 < c / (2 * (‖S‖ + 1)) := by positivity
  filter_upwards [Metric.ball_mem_nhds A hδ] with B hB v
  rw [Metric.mem_ball, dist_eq_norm] at hB
  have hSB : ‖S‖ * ‖B - A‖ ≤ c / 2 := by
    calc ‖S‖ * ‖B - A‖ ≤ (‖S‖ + 1) * (c / (2 * (‖S‖ + 1))) := by
          gcongr
          linarith
      _ = c / 2 := by field_simp
  have := inner_apply_apply_sub_le S A B v
  nlinarith [hcS v, sq_nonneg ‖v‖]

/-- The operators with a Lyapunov form are an open set. -/
theorem isOpen_setOf_hasLyapunovForm : IsOpen {A : E →L[ℝ] E | A.HasLyapunovForm} := by
  refine isOpen_iff_mem_nhds.mpr fun A hA ↦ ?_
  obtain ⟨S, hS, c, hc, hB⟩ := hA.exists_eventually_nhds
  filter_upwards [hB] with B hB using ⟨S, hS, c, hc, hB⟩

/-- **An operator with a Lyapunov form has no purely imaginary eigenvalue.** If `A v = -ω • w`
and `A w = ω • v`, so that `v + i w` is an eigenvector of the complexification of `A` with
eigenvalue `i ω`, then `v = 0` and `w = 0`. -/
theorem HasLyapunovForm.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul (h : A.HasLyapunovForm)
    {ω : ℝ} {v w : E} (hv : A v = -ω • w) (hw : A w = ω • v) : v = 0 ∧ w = 0 := by
  obtain ⟨S, hS, c, hc, hcS⟩ := h
  have h₁ := hcS v
  have h₂ := hcS w
  rw [hv, map_smul, inner_smul_left, RCLike.conj_to_real] at h₁
  rw [hw, map_smul, inner_smul_left, RCLike.conj_to_real, hS.apply_clm v w, real_inner_comm] at h₂
  have hv0 : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]
  have hw0 : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]
  exact ⟨norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hv0),
    norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hw0)⟩

/-- An operator with a Lyapunov form is injective. -/
theorem HasLyapunovForm.injective (h : A.HasLyapunovForm) : Function.Injective A := by
  refine (injective_iff_map_eq_zero A).mpr fun v hv ↦ ?_
  exact (h.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul (ω := 0) (w := 0) (by simp [hv])
    (by simp)).1

/-- **The negated adjoint has a Lyapunov form.** In finite dimensions, if `A` has the Lyapunov
form `S`, then `-A†` has the Lyapunov form `-S⁻¹`. The operator `-A†` is the coefficient of
`d/ds - A†`, the negative of the formal adjoint `-d/ds + A†` of `d/ds + A`. -/
theorem HasLyapunovForm.neg_adjoint [FiniteDimensional ℝ E] (h : A.HasLyapunovForm) :
    (-adjoint A).HasLyapunovForm := by
  obtain ⟨S, hS, c, hc, hcS⟩ := h
  -- `S` is injective, hence invertible since `E` is finite dimensional.
  have hinj : Function.Injective (S : E →ₗ[ℝ] E) := by
    refine (injective_iff_map_eq_zero (S : E →ₗ[ℝ] E)).mpr fun x hx ↦ ?_
    have hx' : S x = 0 := by rwa [coe_coe] at hx
    have h₁ := hcS x
    rw [hS.apply_clm, hx', inner_zero_right] at h₁
    have : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  obtain ⟨e, he⟩ : ∃ e : E ≃ₗ[ℝ] E, ∀ x, e x = S x :=
    ⟨LinearEquiv.ofInjectiveEndo (S : E →ₗ[ℝ] E) hinj, fun x ↦ by
      rw [LinearEquiv.coe_ofInjectiveEndo, coe_coe]⟩
  set T : E →L[ℝ] E := LinearMap.toContinuousLinearMap e.symm.toLinearMap with hT
  have hST (w : E) : S (T w) = w := by
    rw [← he, hT, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  have hTsym : (T : E →ₗ[ℝ] E).IsSymmetric := fun a b ↦ by
    simp only [coe_coe]
    conv_lhs => rw [← hST b]
    conv_rhs => rw [← hST a]
    rw [← hS.apply_clm]
  have hnegT : ((-T : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := fun a b ↦ by
    simp only [coe_coe, neg_apply, inner_neg_left, inner_neg_right, hTsym.apply_clm]
  refine ⟨-T, hnegT, c / (‖S‖ ^ 2 + 1), by positivity, fun w ↦ ?_⟩
  set x := T w
  have hwx : S x = w := hST w
  -- The quadratic form of `-T` against `-A†` at `w = S x` is that of `S` against `A` at `x`.
  have hform : ⟪(-T) ((-adjoint A) w), w⟫_ℝ = ⟪S (A x), x⟫_ℝ := by
    simp only [neg_apply, map_neg, neg_neg]
    conv_lhs => rw [← hwx]
    rw [← hS.apply_clm, hST, adjoint_inner_left, hS.apply_clm, real_inner_comm]
  rw [hform]
  have hnorm : ‖w‖ ^ 2 ≤ (‖S‖ ^ 2 + 1) * ‖x‖ ^ 2 := by
    rw [← hwx]
    calc ‖S x‖ ^ 2 ≤ (‖S‖ * ‖x‖) ^ 2 := by gcongr; exact S.le_opNorm x
      _ ≤ (‖S‖ ^ 2 + 1) * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  calc c / (‖S‖ ^ 2 + 1) * ‖w‖ ^ 2 ≤ c / (‖S‖ ^ 2 + 1) * ((‖S‖ ^ 2 + 1) * ‖x‖ ^ 2) := by
        gcongr
    _ = c * ‖x‖ ^ 2 := by field_simp
    _ ≤ ⟪S (A x), x⟫_ℝ := hcS x

end ContinuousLinearMap
