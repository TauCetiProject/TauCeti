/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.PDE.GreenFunction.HalfSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.IteratedFDeriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Converse
import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Poisson integral of a Euclidean half-space and the Dirichlet problem

Let `v` be a unit vector of `ℝⁿ`. For boundary data `g` on the hyperplane `H = (ℝ ∙ v)ᗮ`, the
**Poisson integral**

`P[g](x) = ∫_H K(x, y) g(y) dy`

averages `g` against the Poisson kernel `K = TauCeti.halfSpacePoissonKernel` of the half-space
`0 < ⟪v, x⟫`, with respect to the Lebesgue measure of `H`. It is the candidate solution of the
Dirichlet problem `Δu = 0` in the half-space, `u = g` on `H`.

The kernel has **mass one**: `∫_H K(x, y) dy = 1` for every pole `x` in the open half-space. For a
pole at height `t = ⟪v, x⟫` above the foot `p ∈ H`, the kernel restricted to `H` is
`2 t / (n ωₙ) (‖y - p‖ ^ 2 + t ^ 2) ^ (-n / 2)`, where `ωₙ` is the volume of the unit ball;
translating by `p` and rescaling by `t` reduce the integral to that of the Japanese bracket
`(1 + ‖y‖ ^ 2) ^ (-n / 2)` over the `(n - 1)`-dimensional space `H`, which is
`π ^ (n / 2) / Γ(n / 2) = n ωₙ / 2` (`TauCeti.integral_rpow_neg_one_add_norm_sq`).

The other estimates all come from one comparison of kernels, proved alongside the kernel
(`TauCeti.halfSpacePoissonKernel_le_mul`): `K(x, y) = 2 ⟪v, x⟫ / (n ωₙ ‖y - x‖ ⁿ)`, so a lower
bound `‖y - x₁‖ ≤ A ‖y - x‖` on distances to the hyperplane point `y` bounds `K(x, ·)` by a
multiple of the integrable `K(x₁, ·)`. Near a pole `x₀` this dominates the integrand uniformly,
so `P[g]` is continuous and Fubini's theorem moves the mean-value property of each harmonic
kernel `K(·, y)` onto `P[g]`, which is therefore harmonic by the converse of the mean-value
property. Far from a boundary point `ξ` it bounds the kernel by `⟪v, x⟫` times a fixed integrable
function, so mass one makes `K` an approximate identity: `P[g](x) → g ξ` as `x → ξ` whenever `g`
is bounded, almost everywhere strongly measurable, and continuous at `ξ`. Together these solve the
Dirichlet problem on the half-space for bounded continuous data.

Uniqueness is not addressed here. Without a growth condition it fails: `x ↦ ⟪v, x⟫` is harmonic
in the half-space, continuous up to `H` and zero there.

For `α`-Hölder data, `0 < α < 1`, the Poisson integral is `α`-Hölder up to the hyperplane at its
points: `|P[g](x) - g(p)| ≤ K (A ⟪v, x⟫^α + ‖x - p‖^α)` for `p ∈ H`, because the Hölder moment
`∫_H K(x, y) ‖y - x'‖^α dy` of the kernel about the foot `x'` of `x` is a constant times
`⟪v, x⟫^α`, finite since `α < 1`. Its derivatives blow up at the hyperplane at the matching rate,
`‖D^k P[g](x)‖ ≤ C K ⟪v, x⟫^(α - k)` for `k ≥ 1`: on the ball of radius `⟪v, x⟫ / 2` about `x`
the harmonic function `P[g] - g(x')` is `O(⟪v, x⟫^α)`, and the interior derivative estimates for
harmonic functions apply.

## Main declarations

* `TauCeti.integral_halfSpacePoissonKernel`: the Poisson kernel of the half-space has mass one.
* `TauCeti.halfSpacePoissonIntegral`: the Poisson integral of data on the hyperplane.
* `TauCeti.abs_halfSpacePoissonIntegral_le`: the maximum principle for the Poisson integral.
* `TauCeti.halfSpacePoissonIntegral_const`, `TauCeti.halfSpacePoissonIntegral_add`,
  `TauCeti.halfSpacePoissonIntegral_smul`, `TauCeti.halfSpacePoissonIntegral_mono`: in the open
  half-space the Poisson integral is a positive linear operator preserving constants.
* `TauCeti.tendsto_halfSpacePoissonIntegral`: the Poisson integral of bounded almost everywhere
  strongly measurable data attains the boundary value at every point of continuity.
* `TauCeti.harmonicOnNhd_halfSpacePoissonIntegral`: the Poisson integral of bounded measurable
  data is harmonic in the open half-space.
* `TauCeti.exists_harmonicOnNhd_continuousOn_halfSpace_eq`: existence of a solution of the
  Dirichlet problem on the half-space for bounded continuous data.
* `TauCeti.exists_abs_halfSpacePoissonIntegral_sub_le`: the Poisson integral of Hölder data is
  Hölder up to the hyperplane at its points.
* `TauCeti.exists_norm_iteratedFDeriv_halfSpacePoissonIntegral_le`: the derivatives of the Poisson
  integral of `α`-Hölder data are `O(⟪v, x⟫^(α - k))`.

## References

The operator API and the boundary argument are adapted from the ball case in
`TauCeti/Analysis/PDE/PoissonIntegral/Ball.lean`.

* L. C. Evans, *Partial Differential Equations*, Section 2.2.4, Theorem 14.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.10 (interior derivative estimates for harmonic functions).
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Module Set Filter Real

open scoped RealInnerProductSpace Topology NNReal

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "U" => {w : EuclideanSpace ℝ (Fin n) // ‖w‖ = 1}

/-- A unit vector is nonzero. -/
private theorem unit_ne_zero (v : U) : (v : E) ≠ 0 :=
  ne_of_apply_ne norm (by simp [v.property])

/-- The bounding hyperplane `⟪v, ·⟫ = 0` of the half-space has dimension `n - 1`. -/
private theorem finrank_orthogonal_unit (v : U) : finrank ℝ (ℝ ∙ (v : E))ᗮ = n - 1 := by
  have : Fact (finrank ℝ E = n - 1 + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin, Nat.sub_add_cancel
      (pos_of_ne_euclideanSpace (unit_ne_zero v))]⟩
  exact Submodule.finrank_orthogonal_span_singleton (unit_ne_zero v)

/-- The foot of `x` on the bounding hyperplane `⟪v, ·⟫ = 0` of the half-space, its orthogonal
projection onto the hyperplane. -/
private abbrev foot (v : U) : E →L[ℝ] (ℝ ∙ (v : E))ᗮ := (ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto

/-- On the hyperplane, the Poisson kernel with a pole `x` at height `t > 0` is a rescaled and
translated copy of the Japanese bracket `(1 + ‖·‖ ^ 2) ^ (-n / 2)`. -/
private theorem halfSpacePoissonKernel_eq_rpow_one_add (v : U) {x : E}
    (hx : 0 < ⟪(v : E), x⟫) (y : (ℝ ∙ (v : E))ᗮ) :
    halfSpacePoissonKernel n v x y =
      2 * ((n : ℝ) * volume.real (ball (0 : E) 1))⁻¹ *
        (⟪(v : E), x⟫ * (⟪(v : E), x⟫ ^ 2) ^ (-(n : ℝ) / 2)) *
        (1 + ‖⟪(v : E), x⟫⁻¹ • (y - foot v x)‖ ^ 2) ^ (-(n : ℝ) / 2) := by
  have hy : ⟪(v : E), y⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 y.property
  have hnorm : ‖y - foot v x‖ = ‖(y : E) - (x - ⟪(v : E), x⟫ • (v : E))‖ := by
    rw [← Submodule.coe_orthogonalProjectionOnto_orthogonal_singleton v.property x,
      ← Submodule.coe_sub, Submodule.norm_coe]
  have h1 : ‖(y : E) - x‖ ^ 2 =
      ⟪(v : E), x⟫ ^ 2 * (1 + ‖⟪(v : E), x⟫⁻¹ • (y - foot v x)‖ ^ 2) := by
    rw [norm_smul, mul_pow, hnorm, norm_sub_sq_eq_of_inner_eq_zero v.property x hy,
        Real.norm_eq_abs,
      abs_inv, abs_of_pos hx]
    field_simp
    ring
  rw [halfSpacePoissonKernel_def, ← Real.sq_rpow_div_two (norm_nonneg _), h1,
    Real.mul_rpow (by positivity) (by positivity)]
  ring

/-- For a pole in the open half-space, the Poisson kernel is integrable over the hyperplane. -/
theorem integrable_halfSpacePoissonKernel (v : U) {x : E} (hx : 0 < ⟪(v : E), x⟫) :
    Integrable (fun y : (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v x y) := by
  have hn : (finrank ℝ (ℝ ∙ (v : E))ᗮ : ℝ) < n := by
    rw [finrank_orthogonal_unit, Nat.cast_sub (pos_of_ne_euclideanSpace (unit_ne_zero v)),
      Nat.cast_one]
    linarith
  simp_rw [halfSpacePoissonKernel_eq_rpow_one_add v hx]
  exact (((integrable_rpow_neg_one_add_norm_sq hn).comp_smul (inv_ne_zero hx.ne')).comp_sub_right
    (foot v x)).const_mul _

/-- The powers of the height `t` of the pole cancel in the rescaled kernel:
`t (t²)^(-n/2) t^(n-1) = 1`. -/
private theorem mul_rpow_neg_mul_pow_eq_one (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    t * (t ^ 2) ^ (-(n : ℝ) / 2) * t ^ (n - 1) = 1 := by
  have h1 : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hn, Nat.cast_one]
  have h : t * (t ^ 2) ^ (-(n : ℝ) / 2) * t ^ (n - 1) =
      t ^ ((1 : ℝ) + 2 * (-(n : ℝ) / 2) + ((n : ℝ) - 1)) := by
    rw [Real.rpow_add ht, Real.rpow_add ht, Real.rpow_one, Real.rpow_mul ht.le, h1,
      Real.rpow_natCast, Real.rpow_two]
  rw [h]
  ring_nf
  exact Real.rpow_zero t

/-- **The Poisson kernel of the half-space has mass one.** For a pole `x` in the open half-space
`0 < ⟪v, x⟫`, the integral of `y ↦ K(x, y)` over the bounding hyperplane is `1`. -/
theorem integral_halfSpacePoissonKernel (v : U) {x : E} (hx : 0 < ⟪(v : E), x⟫) :
    ∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y = 1 := by
  set t := ⟪(v : E), x⟫
  have hn : 0 < n := pos_of_ne_euclideanSpace (unit_ne_zero v)
  have hfin : (finrank ℝ (ℝ ∙ (v : E))ᗮ : ℝ) = n - 1 := by
    rw [finrank_orthogonal_unit, Nat.cast_sub hn, Nat.cast_one]
  -- Translating by the foot of `x` and rescaling by `t` reduces to the Japanese bracket.
  have hI : ∫ y : (ℝ ∙ (v : E))ᗮ, (1 + ‖t⁻¹ • (y - foot v x)‖ ^ 2) ^ (-(n : ℝ) / 2) =
      t ^ (n - 1) * (π ^ (((n : ℝ) - 1) / 2) * Real.Gamma (1 / 2) / Real.Gamma (n / 2)) := by
    rw [integral_sub_right_eq_self
        (fun y : (ℝ ∙ (v : E))ᗮ ↦ (1 + ‖t⁻¹ • y‖ ^ 2) ^ (-(n : ℝ) / 2)) (foot v x),
      Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
        (fun y : (ℝ ∙ (v : E))ᗮ ↦ (1 + ‖y‖ ^ 2) ^ (-(n : ℝ) / 2)) hx.le,
      integral_rpow_neg_one_add_norm_sq (by rw [hfin]; linarith), hfin,
      finrank_orthogonal_unit, smul_eq_mul]
    congr 3
    ring_nf
  simp_rw [halfSpacePoissonKernel_eq_rpow_one_add v hx]
  rw [integral_const_mul, hI]
  have : Nontrivial E := nontrivial_of_ne (v : E) 0 (unit_ne_zero v)
  have htpow := mul_rpow_neg_mul_pow_eq_one hn hx
  have hπ : π ^ (((n : ℝ) - 1) / 2) * Real.Gamma (1 / 2) = π ^ ((n : ℝ) / 2) := by
    rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, ← Real.rpow_add pi_pos]
    ring_nf
  rw [volume_real_unitBall, finrank_euclideanSpace_fin, Real.Gamma_add_one (by positivity)]
  calc _ = 2 * ((n : ℝ) * (π ^ ((n : ℝ) / 2) / ((n : ℝ) / 2 * Real.Gamma (n / 2))))⁻¹ *
        (π ^ (((n : ℝ) - 1) / 2) * Real.Gamma (1 / 2) / Real.Gamma (n / 2)) *
        (t * (t ^ 2) ^ (-(n : ℝ) / 2) * t ^ (n - 1)) := by ring
    _ = 1 := by
      rw [hπ, htpow]
      field_simp

/-- The **Poisson integral** `P[g](x) = ∫ K(x, y) g(y) dy` of boundary data `g` on the
hyperplane `⟪v, ·⟫ = 0`, against the Poisson kernel `K = TauCeti.halfSpacePoissonKernel` of the
half-space `0 < ⟪v, ·⟫` and the Lebesgue measure of the hyperplane. -/
def halfSpacePoissonIntegral (v : U) (g : (ℝ ∙ (v : E))ᗮ → ℝ) (x : E) : ℝ :=
  ∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y * g y

/-- The defining formula for the Poisson integral of the half-space. -/
theorem halfSpacePoissonIntegral_def (v : U) (g : (ℝ ∙ (v : E))ᗮ → ℝ) (x : E) :
    halfSpacePoissonIntegral v g x =
      ∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y * g y := by
  rw [halfSpacePoissonIntegral]

/-- For a pole in the open half-space, the Poisson integrand of bounded measurable data is
integrable over the hyperplane. -/
theorem integrable_halfSpacePoissonKernel_mul (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable g) (hC : ∀ y, |g y| ≤ C) {x : E} (hx : 0 < ⟪(v : E), x⟫) :
    Integrable (fun y : (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v x y * g y) :=
  (integrable_halfSpacePoissonKernel v hx).mul_bdd hg (ae_of_all _ hC)

/-- The Poisson integral of zero boundary data is zero. -/
@[simp] theorem halfSpacePoissonIntegral_zero (v : U) (x : E) :
    halfSpacePoissonIntegral v (fun _ : (ℝ ∙ (v : E))ᗮ ↦ 0) x = 0 := by
  simp [halfSpacePoissonIntegral_def]

/-- The Poisson integral commutes with real scalar multiplication of the boundary data. -/
@[simp] theorem halfSpacePoissonIntegral_smul (v : U) (a : ℝ) (g : (ℝ ∙ (v : E))ᗮ → ℝ)
    (x : E) : halfSpacePoissonIntegral v (a • g) x = a • halfSpacePoissonIntegral v g x := by
  simp only [halfSpacePoissonIntegral_def, Pi.smul_apply, smul_eq_mul, mul_left_comm _ a,
    integral_const_mul]

/-- The Poisson integral is additive in boundary data whose Poisson integrands are integrable.
-/
theorem halfSpacePoissonIntegral_add (v : U) {g₁ g₂ : (ℝ ∙ (v : E))ᗮ → ℝ} {x : E}
    (hg₁ : Integrable fun y : (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v x y * g₁ y)
    (hg₂ : Integrable fun y : (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v x y * g₂ y) :
    halfSpacePoissonIntegral v (g₁ + g₂) x =
      halfSpacePoissonIntegral v g₁ x + halfSpacePoissonIntegral v g₂ x := by
  simp only [halfSpacePoissonIntegral_def, Pi.add_apply, mul_add]
  exact integral_add hg₁ hg₂

/-- The Poisson integral reproduces constants in the open half-space. -/
@[simp] theorem halfSpacePoissonIntegral_const (v : U) {x : E} (hx : 0 < ⟪(v : E), x⟫)
    (a : ℝ) : halfSpacePoissonIntegral v (fun _ ↦ a) x = a := by
  rw [halfSpacePoissonIntegral_def, integral_mul_const, integral_halfSpacePoissonKernel v hx,
    one_mul]

/-- In the open half-space, the Poisson integral preserves order between boundary data whose
Poisson integrands are integrable. -/
theorem halfSpacePoissonIntegral_mono (v : U) {g₁ g₂ : (ℝ ∙ (v : E))ᗮ → ℝ} {x : E}
    (hg₁ : Integrable fun y : (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v x y * g₁ y)
    (hg₂ : Integrable fun y : (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v x y * g₂ y)
    (hle : g₁ ≤ g₂) (hx : 0 < ⟪(v : E), x⟫) :
    halfSpacePoissonIntegral v g₁ x ≤ halfSpacePoissonIntegral v g₂ x :=
  integral_mono hg₁ hg₂ fun y ↦
    mul_le_mul_of_nonneg_left (hle y) (halfSpacePoissonKernel_pos_on_hyperplane v hx y).le

/-- Nonnegative boundary data have a nonnegative Poisson integral in the open half-space. -/
theorem halfSpacePoissonIntegral_nonneg (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ} (hg : 0 ≤ g) {x : E}
    (hx : 0 < ⟪(v : E), x⟫) : 0 ≤ halfSpacePoissonIntegral v g x :=
  integral_nonneg fun y ↦ mul_nonneg (halfSpacePoissonKernel_pos_on_hyperplane v hx y).le (hg y)

/-- **Maximum principle.** In the open half-space, the Poisson integral of measurable data bounded
by `M` in absolute value is bounded by `M` in absolute value. -/
theorem abs_halfSpacePoissonIntegral_le (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ} {M : ℝ}
    (hg : AEStronglyMeasurable g) (hM : ∀ y, |g y| ≤ M) {x : E} (hx : 0 < ⟪(v : E), x⟫) :
    |halfSpacePoissonIntegral v g x| ≤ M := by
  have hK := halfSpacePoissonKernel_pos_on_hyperplane (n := n) v hx
  rw [halfSpacePoissonIntegral_def]
  calc |∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y * g y|
      ≤ ∫ y : (ℝ ∙ (v : E))ᗮ, |halfSpacePoissonKernel n v x y * g y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y * M :=
        integral_mono (integrable_halfSpacePoissonKernel_mul v hg hM hx).abs
          ((integrable_halfSpacePoissonKernel v hx).mul_const M) fun y ↦ by
          rw [abs_mul, abs_of_pos (hK y)]
          exact mul_le_mul_of_nonneg_left (hM y) (hK y).le
    _ = M := by rw [integral_mul_const, integral_halfSpacePoissonKernel v hx, one_mul]

/-- In the open half-space, the Poisson integral minus a constant is the Poisson integral of the
data minus that constant, for data whose Poisson integrand is integrable. -/
theorem halfSpacePoissonIntegral_sub_const (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ} {x : E}
    (hg : Integrable fun y : (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v x y * g y)
    (hx : 0 < ⟪(v : E), x⟫) (c : ℝ) :
    halfSpacePoissonIntegral v g x - c =
      ∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y * (g y - c) := by
  conv_lhs => rw [← halfSpacePoissonIntegral_const v hx c]
  simp only [halfSpacePoissonIntegral_def, mul_sub]
  exact (integral_sub hg ((integrable_halfSpacePoissonKernel v hx).mul_const c)).symm

/-- The pointwise estimate behind boundary recovery at a point `ξ` of the hyperplane: where the
data are `ε`-close to `g ξ`, the integrand is at most `ε` times the kernel; elsewhere, at distance
at least `δ` from `ξ`, it is at most `⟪v, x⟫ (2 (1 + δ⁻¹))ⁿ` times the bound `C'` on the data times
the kernel with pole `ξ + v`. -/
private theorem abs_halfSpacePoissonKernel_mul_sub_le (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ}
    {ξ y : (ℝ ∙ (v : E))ᗮ} {x : E} {C' ε δ : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hx : 0 < ⟪(v : E), x⟫) (hxξ : ‖x - ξ‖ ≤ δ / 2) (hC' : |g y - g ξ| ≤ C')
    (hnear : dist y ξ < δ → |g y - g ξ| < ε) :
    |halfSpacePoissonKernel n v x y * (g y - g ξ)| ≤
      ε * halfSpacePoissonKernel n v x y +
        ⟪(v : E), x⟫ * (2 * (1 + δ⁻¹)) ^ n * C' * halfSpacePoissonKernel n v (ξ + v) y := by
  have hv : ‖(v : E)‖ = 1 := v.property
  have hy : ⟪(v : E), (y : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1
      y.property
  have hx₁ : 0 < ⟪(v : E), (ξ : E) + v⟫ := by
    rw [inner_add_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 ξ.property,
      real_inner_self_eq_norm_sq, hv]
    norm_num
  have hK := (halfSpacePoissonKernel_pos_on_hyperplane (n := n) v hx y).le
  have hK₁ := (halfSpacePoissonKernel_pos_on_hyperplane (n := n) v hx₁ y).le
  have hC'0 : 0 ≤ C' := (abs_nonneg _).trans hC'
  rw [abs_mul, abs_of_nonneg hK]
  by_cases hyξ : dist y ξ < δ
  · nlinarith [mul_le_mul_of_nonneg_left (hnear hyξ).le hK,
      mul_nonneg (mul_nonneg (mul_nonneg hx.le (by positivity : (0 : ℝ) ≤ (2 * (1 + δ⁻¹)) ^ n))
        hC'0) hK₁]
  rw [not_lt, Subtype.dist_eq, dist_eq_norm] at hyξ
  -- Far from `ξ`, distances to `x` and to `ξ + v` are comparable.
  have hfar : ‖(y : E) - (ξ + v)‖ ≤ 2 * (1 + δ⁻¹) * ‖(y : E) - x‖ := by
    have h1 : ‖(y : E) - (ξ + v)‖ ≤ ‖(y : E) - ξ‖ + 1 :=
      (norm_sub_le _ _).trans_eq' (by rw [sub_add_eq_sub_sub]) |>.trans_eq (by rw [hv])
    have h2 : 1 ≤ δ⁻¹ * ‖(y : E) - ξ‖ := by
      rw [inv_mul_eq_div, one_le_div hδ]
      exact hyξ
    have h3 : ‖(y : E) - ξ‖ ≤ 2 * ‖(y : E) - x‖ := by
      linarith [norm_sub_le_norm_sub_add_norm_sub (y : E) x ξ]
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 + δ⁻¹)]
  have hcomp := halfSpacePoissonKernel_le_mul (n := n) v hy hx.le hx₁ hfar
  rw [inner_add_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 ξ.property,
    real_inner_self_eq_norm_sq, hv, one_pow, zero_add, div_one] at hcomp
  calc halfSpacePoissonKernel n v x y * |g y - g ξ|
      ≤ (⟪(v : E), x⟫ * (2 * (1 + δ⁻¹)) ^ n * halfSpacePoissonKernel n v (ξ + v) y) * C' :=
        mul_le_mul hcomp hC' (abs_nonneg _) (by positivity)
    _ = ⟪(v : E), x⟫ * (2 * (1 + δ⁻¹)) ^ n * C' * halfSpacePoissonKernel n v (ξ + v) y := by
        ring
    _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hε hK)

/-- **The Poisson integral attains the boundary values.** For bounded measurable data `g` on the
hyperplane `⟪v, ·⟫ = 0` and a point `ξ` of the hyperplane at which `g` is continuous, the Poisson
integral `P[g](x)` tends to `g ξ` as `x` tends to `ξ` through the open half-space. -/
theorem tendsto_halfSpacePoissonIntegral (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable g) (hC : ∀ y, |g y| ≤ C) {ξ : (ℝ ∙ (v : E))ᗮ}
    (hξ : ContinuousAt g ξ) :
    Tendsto (halfSpacePoissonIntegral v g) (𝓝[{x | 0 < ⟪(v : E), x⟫}] (ξ : E)) (𝓝 (g ξ)) := by
  have hξv : ⟪(v : E), (ξ : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1
      ξ.property
  have hx₁ : 0 < ⟪(v : E), (ξ : E) + v⟫ := by
    rw [inner_add_right, hξv, real_inner_self_eq_norm_sq, v.property]
    norm_num
  have hgC : ∀ y, |g y - g ξ| ≤ 2 * C := fun y ↦
    (abs_sub (g y) (g ξ)).trans (by linarith [hC y, hC ξ])
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hξ (ε / 2) (half_pos hε)
  -- The far-field contribution `B x` is `O(⟪v, x⟫)`, so it tends to zero at `ξ`.
  set B : E → ℝ := fun x ↦ ⟪(v : E), x⟫ * (2 * (1 + δ⁻¹)) ^ n * (2 * C)
  have hBlim : Tendsto B (𝓝[{x | 0 < ⟪(v : E), x⟫}] (ξ : E)) (𝓝 0) := by
    have hcont : Continuous B := by fun_prop
    simpa only [B, hξv, zero_mul] using (hcont.tendsto (ξ : E)).mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ x : E in 𝓝[{x | 0 < ⟪(v : E), x⟫}] (ξ : E), ‖x - (ξ : E)‖ ≤ δ / 2 :=
    eventually_nhdsWithin_of_eventually_nhds (mem_of_superset
      (closedBall_mem_nhds (ξ : E) (half_pos hδ)) fun _ ↦ mem_closedBall_iff_norm.1)
  filter_upwards [self_mem_nhdsWithin, hBlim.eventually_lt_const (half_pos hε), hnear] with x
    (hx : 0 < ⟪(v : E), x⟫) hxsmall hxnear
  -- Positivity and mass one turn the pointwise majorant into the required integral estimate.
  have hKi := integrable_halfSpacePoissonKernel (n := n) v hx
  have hK₁i := integrable_halfSpacePoissonKernel (n := n) v hx₁
  rw [Real.dist_eq, halfSpacePoissonIntegral_sub_const v
    (integrable_halfSpacePoissonKernel_mul v hg hC hx) hx]
  calc |∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y * (g y - g ξ)|
      ≤ ∫ y : (ℝ ∙ (v : E))ᗮ, |halfSpacePoissonKernel n v x y * (g y - g ξ)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y : (ℝ ∙ (v : E))ᗮ, (ε / 2 * halfSpacePoissonKernel n v x y +
          B x * halfSpacePoissonKernel n v (ξ + v) y) :=
        integral_mono (hKi.mul_bdd (hg.sub aestronglyMeasurable_const) (ae_of_all _ hgC)).abs
          ((hKi.const_mul _).add (hK₁i.const_mul _)) fun y ↦
          abs_halfSpacePoissonKernel_mul_sub_le v hδ (half_pos hε).le hx hxnear (hgC y)
            fun h ↦ by simpa only [Real.dist_eq] using hδg h
    _ = ε / 2 + B x := by
        rw [integral_add (hKi.const_mul _) (hK₁i.const_mul _), integral_const_mul,
          integral_const_mul, integral_halfSpacePoissonKernel v hx,
          integral_halfSpacePoissonKernel v hx₁]
        ring
    _ < ε := by linarith

/-- The Poisson kernel is jointly measurable in the pole and the point of the hyperplane. -/
private theorem measurable_halfSpacePoissonKernel (v : U) :
    Measurable fun p : E × (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v p.1 p.2 := by
  simp_rw [halfSpacePoissonKernel_def]
  fun_prop

/-- The Poisson integral is continuous on the open half-space. -/
private theorem continuousOn_halfSpacePoissonIntegral (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable g) (hC : ∀ y, |g y| ≤ C) :
    ContinuousOn (halfSpacePoissonIntegral v g) {x | 0 < ⟪(v : E), x⟫} := by
  intro x₀ (hx₀ : 0 < ⟪(v : E), x₀⟫)
  refine ContinuousAt.continuousWithinAt ?_
  have hnear : ∀ᶠ x in 𝓝 x₀, x ∈ closedBall x₀ (⟪(v : E), x₀⟫ / 2) :=
    closedBall_mem_nhds _ (half_pos hx₀)
  refine continuousAt_of_dominated (bound := fun y ↦
      3 / 2 * 2 ^ n * halfSpacePoissonKernel n v x₀ y * C) ?_ ?_
    (((integrable_halfSpacePoissonKernel v hx₀).const_mul _).mul_const _) (ae_of_all _ fun y ↦ ?_)
  · filter_upwards [hnear] with x hx
    have hy := (halfSpacePoissonKernel_le_of_norm_sub_le (n := n) v hx₀
      (mem_closedBall_iff_norm.1 hx) (inner_zero_right (v : E))).1
    exact (integrable_halfSpacePoissonKernel_mul v hg hC hy).aestronglyMeasurable
  · filter_upwards [hnear] with x hx
    refine ae_of_all _ fun y ↦ ?_
    have hy : ⟪(v : E), (y : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1
        y.property
    obtain ⟨hxpos, hK⟩ := halfSpacePoissonKernel_le_of_norm_sub_le (n := n) v hx₀
      (mem_closedBall_iff_norm.1 hx) hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (halfSpacePoissonKernel_pos_on_hyperplane v hxpos y)]
    exact mul_le_mul hK (hC y) (abs_nonneg _)
      (mul_nonneg (by positivity) (halfSpacePoissonKernel_pos_on_hyperplane v hx₀ y).le)
  · have hy : ⟪(v : E), (y : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1
      y.property
    exact ((harmonicAt_halfSpacePoissonKernel_left v hy
      fun h ↦ hx₀.ne' (by rwa [h])).1.continuousAt).mul continuousAt_const

/-- The Poisson integral has the mean-value property on small balls in the open half-space. -/
private theorem setAverage_ball_halfSpacePoissonIntegral (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ}
    {C : ℝ} (hg : AEStronglyMeasurable g) (hC : ∀ y, |g y| ≤ C) {x₀ : E}
    (hx₀ : 0 < ⟪(v : E), x₀⟫) {r : ℝ} (hr : r ∈ Ioo 0 (⟪(v : E), x₀⟫ / 2)) :
    ⨍ z in ball x₀ r, halfSpacePoissonIntegral v g z = halfSpacePoissonIntegral v g x₀ := by
  set F : E → (ℝ ∙ (v : E))ᗮ → ℝ := fun z y ↦ halfSpacePoissonKernel n v z y * g y
  -- On the ball the integrand is dominated by a product, so Fubini applies.
  have hint : Integrable (Function.uncurry F) ((volume.restrict (ball x₀ r)).prod volume) := by
    refine Integrable.mono' ((integrableOn_const (C := 3 / 2 * 2 ^ n * C)
      measure_ball_lt_top.ne).mul_prod (integrable_halfSpacePoissonKernel (n := n) v hx₀)) ?_ ?_
    · exact ((measurable_halfSpacePoissonKernel v).aestronglyMeasurable).mul hg.comp_snd
    · filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_ball)]
        with p hp
      have hy : ⟪(v : E), (p.2 : E)⟫ = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.1 p.2.property
      obtain ⟨hxpos, hK⟩ := halfSpacePoissonKernel_le_of_norm_sub_le (n := n) v hx₀
        ((mem_ball_iff_norm.1 hp).le.trans hr.2.le) hy
      simp only [Function.uncurry, F, norm_mul, Real.norm_eq_abs,
        abs_of_pos (halfSpacePoissonKernel_pos_on_hyperplane v hxpos p.2)]
      calc halfSpacePoissonKernel n v p.1 p.2 * |g p.2|
          ≤ 3 / 2 * 2 ^ n * halfSpacePoissonKernel n v x₀ p.2 * C :=
            mul_le_mul hK (hC p.2) (abs_nonneg _)
              (mul_nonneg (by positivity) (halfSpacePoissonKernel_pos_on_hyperplane v hx₀ p.2).le)
        _ = _ := by ring
  -- Each kernel `K(·, y)` has the mean-value property on the ball.
  have hmean : ∀ y : (ℝ ∙ (v : E))ᗮ, ∫ z in ball x₀ r, F z y =
      volume.real (ball x₀ r) * (halfSpacePoissonKernel n v x₀ y * g y) := by
    intro y
    have hy : ⟪(v : E), (y : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1
        y.property
    have hsub : closedBall x₀ r ⊆ {x | 0 < ⟪(v : E), x⟫} := fun z hz ↦
      (halfSpacePoissonKernel_le_of_norm_sub_le (n := n) v hx₀
        ((mem_closedBall_iff_norm.1 hz).trans hr.2.le) hy).1
    rw [integral_mul_const, InnerProductSpace.HarmonicOnNhd.setIntegral_ball_eq
      ((harmonicOnNhd_halfSpacePoissonKernel_left v hy).mono hsub), smul_eq_mul, mul_assoc]
  have hpos : 0 < volume.real (ball x₀ r) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume x₀ hr.1).ne' measure_ball_lt_top.ne
  simp_rw [setAverage_eq, halfSpacePoissonIntegral_def]
  rw [integral_integral_swap hint]
  simp_rw [hmean]
  rw [integral_const_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- **The Poisson integral is harmonic.** For bounded measurable data `g` on the hyperplane
`⟪v, ·⟫ = 0`, the Poisson integral `P[g]` is harmonic on the open half-space `0 < ⟪v, ·⟫`. -/
theorem harmonicOnNhd_halfSpacePoissonIntegral (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable g) (hC : ∀ y, |g y| ≤ C) :
    HarmonicOnNhd (halfSpacePoissonIntegral v g) {x | 0 < ⟪(v : E), x⟫} := by
  have hΩ : IsOpen {x : E | 0 < ⟪(v : E), x⟫} := isOpen_lt continuous_const (by fun_prop)
  refine (harmonicOnNhd_iff_continuousOn_setAverage_ball_eq (μ := volume) hΩ).2
    ⟨continuousOn_halfSpacePoissonIntegral v hg hC, fun x₀ hx₀ ↦ ?_⟩
  exact (eventually_of_mem (Ioo_mem_nhdsGT (half_pos hx₀)) fun r hr ↦
    setAverage_ball_halfSpacePoissonIntegral v hg hC hx₀ hr).frequently

/-- **The Dirichlet problem on a half-space.** For bounded continuous data `g` on the hyperplane
`⟪v, ·⟫ = 0` there is a function harmonic in the open half-space `0 < ⟪v, ·⟫`, continuous on the
closed half-space `0 ≤ ⟪v, ·⟫`, and equal to `g` on the hyperplane: the Poisson integral of `g`
in the open half-space, extended by `g` on the hyperplane. -/
theorem exists_harmonicOnNhd_continuousOn_halfSpace_eq (v : U) {g : (ℝ ∙ (v : E))ᗮ → ℝ}
    {C : ℝ} (hg : Continuous g) (hC : ∀ y, |g y| ≤ C) :
    ∃ u : E → ℝ, HarmonicOnNhd u {x | 0 < ⟪(v : E), x⟫} ∧
      ContinuousOn u {x | 0 ≤ ⟪(v : E), x⟫} ∧ ∀ y : (ℝ ∙ (v : E))ᗮ, u y = g y := by
  classical
  set S : Set E := (ℝ ∙ (v : E))ᗮ
  let u : E → ℝ := fun x ↦ if hx : x ∈ S then g ⟨x, hx⟩ else halfSpacePoissonIntegral v g x
  have hΩ : IsOpen {x : E | 0 < ⟪(v : E), x⟫} := isOpen_lt continuous_const (by fun_prop)
  have hS : ∀ x ∈ {x : E | 0 < ⟪(v : E), x⟫}, x ∉ S := fun x hx hxS ↦
    (ne_of_gt hx) (Submodule.mem_orthogonal_singleton_iff_inner_right.1 hxS)
  have hu : EqOn u (halfSpacePoissonIntegral v g) {x | 0 < ⟪(v : E), x⟫} :=
    fun x hx ↦ dite_eq_right (hS x hx)
  have hP := harmonicOnNhd_halfSpacePoissonIntegral v hg.aestronglyMeasurable hC
  have huP : ∀ x ∈ {x : E | 0 < ⟪(v : E), x⟫}, u =ᶠ[𝓝 x] halfSpacePoissonIntegral v g :=
    fun x hx ↦ eventually_of_mem (hΩ.mem_nhds hx) hu
  refine ⟨u, fun x hx ↦ (harmonicAt_congr_nhds (huP x hx)).2 (hP x hx), ?_,
    fun y ↦ dite_eq_left y.property⟩
  have hunion : {x : E | 0 ≤ ⟪(v : E), x⟫} = {x | 0 < ⟪(v : E), x⟫} ∪ S := by
    ext x
    simp only [mem_ofPred_eq, mem_union, S, SetLike.mem_coe,
      Submodule.mem_orthogonal_singleton_iff_inner_right, le_iff_lt_or_eq, eq_comm]
  rw [hunion]
  rintro x (hx | hx)
  · exact ((hP x hx).1.continuousAt.congr (huP x hx).symm).continuousWithinAt
  · -- At a boundary point, approach from the open half-space and along the hyperplane separately.
    have hux : u x = g ⟨x, hx⟩ := dite_eq_left hx
    refine continuousWithinAt_union.2 ⟨?_, ?_⟩
    · rw [ContinuousWithinAt, hux]
      exact (tendsto_halfSpacePoissonIntegral v hg.aestronglyMeasurable hC
        hg.continuousAt).congr' (eventually_of_mem self_mem_nhdsWithin fun y hy ↦ (hu hy).symm)
    · have hres : S.domRestrict u = g := funext fun y ↦ dite_eq_left y.property
      exact (continuousOn_iff_continuous_domRestrict.2 (hres ▸ hg)) x hx

/-! ### Hölder continuous boundary data -/

/-- A point at height `t ≥ 0` above the hyperplane lies at distance `t` from its foot. -/
private theorem norm_sub_foot (v : U) {x : E} (hx : 0 ≤ ⟪(v : E), x⟫) :
    ‖x - foot v x‖ = ⟪(v : E), x⟫ := by
  rw [Submodule.coe_orthogonalProjectionOnto_orthogonal_singleton v.property x, sub_sub_cancel,
    norm_smul, v.property, mul_one, Real.norm_eq_abs, abs_of_nonneg hx]

/-- **Hölder moments of the Poisson kernel.** For `0 ≤ α < 1` there is a constant `A` with
`∫_H K(x, y) ‖y - x'‖^α dy = A ⟪v, x⟫^α` for every pole `x` in the open half-space, `x'` its foot:
the substitution `y = x' + ⟪v, x⟫ z` reduces the moment to that of the Japanese bracket, which is
finite because `α < 1`. -/
private theorem exists_integral_halfSpacePoissonKernel_mul_rpow (v : U) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {x : E}, 0 < ⟪(v : E), x⟫ →
      Integrable (fun y : (ℝ ∙ (v : E))ᗮ ↦
        halfSpacePoissonKernel n v x y * ‖y - foot v x‖ ^ α) ∧
      ∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y * ‖y - foot v x‖ ^ α =
        A * ⟪(v : E), x⟫ ^ α := by
  have hn : 0 < n := pos_of_ne_euclideanSpace (unit_ne_zero v)
  have hfin : (finrank ℝ (ℝ ∙ (v : E))ᗮ : ℝ) < n - α := by
    rw [finrank_orthogonal_unit, Nat.cast_sub hn, Nat.cast_one]
    linarith
  set c : ℝ := 2 * ((n : ℝ) * volume.real (ball (0 : E) 1))⁻¹
  set φ : (ℝ ∙ (v : E))ᗮ → ℝ := fun z ↦ (1 + ‖z‖ ^ 2) ^ (-(n : ℝ) / 2) * ‖z‖ ^ α
  have hφle : ∀ z, φ z ≤ (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) - α) / 2) := by
    intro z
    have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
    have h1 : ‖z‖ ^ α ≤ (1 + ‖z‖ ^ 2) ^ (α / 2) := by
      rw [← Real.sq_rpow_div_two (norm_nonneg z)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    calc φ z ≤ (1 + ‖z‖ ^ 2) ^ (-(n : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (α / 2) := by
          simp only [φ]
          gcongr
      _ = _ := by
          rw [← Real.rpow_add hpos]
          ring_nf
  have hφm : Measurable φ := by
    simp only [φ]
    fun_prop
  have hφint : Integrable φ :=
    (integrable_rpow_neg_one_add_norm_sq hfin).mono' hφm.aestronglyMeasurable
      (ae_of_all _ fun z ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hφle z)
  refine ⟨c * ∫ z, φ z, mul_nonneg (by positivity) (integral_nonneg fun z ↦ by positivity),
    fun {x} hx ↦ ?_⟩
  set t := ⟪(v : E), x⟫
  -- The integrand is a rescaled and translated copy of `φ`.
  have hform : (fun y : (ℝ ∙ (v : E))ᗮ ↦
      halfSpacePoissonKernel n v x y * ‖y - foot v x‖ ^ α) =
      fun y ↦ (c * (t * (t ^ 2) ^ (-(n : ℝ) / 2)) * t ^ α) * φ (t⁻¹ • (y - foot v x)) := by
    funext y
    have hy : ‖y - foot v x‖ = t * ‖t⁻¹ • (y - foot v x)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hx, ← mul_assoc,
        mul_inv_cancel₀ hx.ne', one_mul]
    rw [halfSpacePoissonKernel_eq_rpow_one_add v hx, hy, Real.mul_rpow hx.le (norm_nonneg _)]
    simp only [φ]
    ring
  have hint : Integrable fun y : (ℝ ∙ (v : E))ᗮ ↦ φ (t⁻¹ • (y - foot v x)) :=
    (hφint.comp_smul (inv_ne_zero hx.ne')).comp_sub_right (foot v x)
  refine ⟨hform ▸ hint.const_mul _, ?_⟩
  rw [hform, integral_const_mul,
    integral_sub_right_eq_self (fun y : (ℝ ∙ (v : E))ᗮ ↦ φ (t⁻¹ • y)) (foot v x),
    Measure.integral_comp_inv_smul_of_nonneg (μ := volume) φ hx.le, finrank_orthogonal_unit,
    smul_eq_mul]
  calc c * (t * (t ^ 2) ^ (-(n : ℝ) / 2)) * t ^ α * (t ^ (n - 1) * ∫ z, φ z)
      = c * (∫ z, φ z) * (t * (t ^ 2) ^ (-(n : ℝ) / 2) * t ^ (n - 1)) * t ^ α := by ring
    _ = _ := by rw [mul_rpow_neg_mul_pow_eq_one hn hx, mul_one]

/-- **The Poisson integral of Hölder data.** Let `0 < α < 1`. There is a constant `A`, depending
only on `n`, `v` and `α`, such that for bounded boundary data `g` that are `α`-Hölder with
constant `K`, every `x` in the open half-space and every point `p` of the hyperplane,

`|P[g](x) - g(p)| ≤ K (A ⟪v, x⟫^α + ‖x - p‖^α)`.

So the Poisson integral, extended by `g`, is `α`-Hölder up to the hyperplane at the boundary
points. -/
theorem exists_abs_halfSpacePoissonIntegral_sub_le (v : U) {α : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {g : (ℝ ∙ (v : E))ᗮ → ℝ} {C : ℝ} {K : ℝ≥0}, (∀ y, |g y| ≤ C) →
      HolderWith K α g → ∀ {x : E}, 0 < ⟪(v : E), x⟫ → ∀ p : (ℝ ∙ (v : E))ᗮ,
        |halfSpacePoissonIntegral v g x - g p| ≤
          K * (A * ⟪(v : E), x⟫ ^ (α : ℝ) + ‖x - p‖ ^ (α : ℝ)) := by
  obtain ⟨A, hA, hmom⟩ :=
    exists_integral_halfSpacePoissonKernel_mul_rpow (n := n) v α.property (by exact_mod_cast hα1)
  refine ⟨A, hA, fun {g C K} hC hg {x} hx p ↦ ?_⟩
  obtain ⟨hint, hval⟩ := hmom hx
  have hgm : AEStronglyMeasurable g := (hg.continuous hα0).aestronglyMeasurable
  have hK0 := halfSpacePoissonKernel_pos_on_hyperplane (n := n) v hx
  set d := ‖foot v x - p‖
  have hpt : ∀ y : (ℝ ∙ (v : E))ᗮ, |halfSpacePoissonKernel n v x y * (g y - g p)| ≤
      K * (halfSpacePoissonKernel n v x y * ‖y - foot v x‖ ^ (α : ℝ) +
        d ^ (α : ℝ) * halfSpacePoissonKernel n v x y) := by
    intro y
    rw [abs_mul, abs_of_pos (hK0 y)]
    have h1 : |g y - g p| ≤ K * ‖y - p‖ ^ (α : ℝ) := by
      simpa [Real.dist_eq, dist_eq_norm] using hg.dist_le y p
    have h2 : ‖y - p‖ ^ (α : ℝ) ≤ ‖y - foot v x‖ ^ (α : ℝ) + d ^ (α : ℝ) :=
      (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le_norm_sub_add_norm_sub y (foot v x) p)
        α.property).trans (Real.rpow_add_le_add_rpow (norm_nonneg _)
            (norm_nonneg _) α.property hα1.le)
    calc halfSpacePoissonKernel n v x y * |g y - g p|
        ≤ halfSpacePoissonKernel n v x y *
            (K * (‖y - foot v x‖ ^ (α : ℝ) + d ^ (α : ℝ))) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 K.property)) (hK0 y).le
      _ = _ := by ring
  have hgp : Integrable fun y : (ℝ ∙ (v : E))ᗮ ↦ halfSpacePoissonKernel n v x y * (g y - g p) :=
    integrable_halfSpacePoissonKernel_mul v (hgm.sub aestronglyMeasurable_const)
      (fun y ↦ (abs_sub _ _).trans (add_le_add (hC y) (hC p))) hx
  rw [halfSpacePoissonIntegral_sub_const v (integrable_halfSpacePoissonKernel_mul v hgm hC hx) hx]
  calc |∫ y : (ℝ ∙ (v : E))ᗮ, halfSpacePoissonKernel n v x y * (g y - g p)|
      ≤ ∫ y : (ℝ ∙ (v : E))ᗮ, |halfSpacePoissonKernel n v x y * (g y - g p)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y : (ℝ ∙ (v : E))ᗮ, K *
          (halfSpacePoissonKernel n v x y * ‖y - foot v x‖ ^ (α : ℝ) +
            d ^ (α : ℝ) * halfSpacePoissonKernel n v x y) :=
        integral_mono hgp.abs ((hint.add ((integrable_halfSpacePoissonKernel v hx).const_mul
          _)).const_mul _) hpt
    _ = K * (A * ⟪(v : E), x⟫ ^ (α : ℝ) + d ^ (α : ℝ)) := by
        rw [integral_const_mul]
        congr 1
        have h2 := (integrable_halfSpacePoissonKernel v hx).const_mul (d ^ (α : ℝ))
        have := integral_add hint h2
        refine this.trans ?_
        rw [integral_const_mul, integral_halfSpacePoissonKernel v hx, hval, mul_one]
        -- The sum produced by `integral_add` uses the addition of `NormedAddCommGroup ℝ`, which
        -- `rfl` unfolds to the addition of `ℝ` on the right-hand side.
        rfl
    _ ≤ _ := by
        gcongr
        rw [show d = ‖foot v (x - p)‖ by simp [d]]
        exact Submodule.norm_orthogonalProjectionOnto_apply_le _ _

/-- **Derivative estimates for the Poisson integral of Hölder data.** Let `0 < α < 1` and
`k ≥ 1`. There is a constant `C`, depending only on `n`, `v`, `α` and `k`, such that for bounded
boundary data `g` that are `α`-Hölder with constant `K` and every `x` in the open half-space,

`‖D^k P[g](x)‖ ≤ C K ⟪v, x⟫^(α - k)`.

The derivatives blow up at the hyperplane at most at the rate allowed by the Hölder exponent of
the data. -/
theorem exists_norm_iteratedFDeriv_halfSpacePoissonIntegral_le (v : U) {α : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α < 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : (ℝ ∙ (v : E))ᗮ → ℝ} {M : ℝ} {K : ℝ≥0}, (∀ y, |g y| ≤ M) →
      HolderWith K α g → ∀ {x : E}, 0 < ⟪(v : E), x⟫ → 1 ≤ k →
        ‖iteratedFDeriv ℝ k (halfSpacePoissonIntegral v g) x‖ ≤
          C * K * ⟪(v : E), x⟫ ^ ((α : ℝ) - k) := by
  obtain ⟨A, hA, hdev⟩ := exists_abs_halfSpacePoissonIntegral_sub_le (n := n) v hα0 hα1
  refine ⟨(2 ^ (finrank ℝ E + 2) * finrank ℝ E * k) ^ k * (2 * (A + 1)), by positivity,
    fun {g M K} hM hg {x} hx hk ↦ ?_⟩
  set t := ⟪(v : E), x⟫
  set c := g (foot v x)
  have hgm : AEStronglyMeasurable g := (hg.continuous hα0).aestronglyMeasurable
  have hP := harmonicOnNhd_halfSpacePoissonIntegral v hgm hM
  have hv : ‖(v : E)‖ = 1 := v.property
  -- Points of `ball x (t / 2)` have heights between `t / 2` and `3 t / 2`.
  have hheight : ∀ y ∈ ball x (t / 2), t / 2 < ⟪(v : E), y⟫ ∧ ⟪(v : E), y⟫ ≤ 3 / 2 * t := by
    intro y hy
    have h := abs_inner_sub_inner_le hv y x
    rw [real_inner_comm (v : E) y, real_inner_comm (v : E) x, abs_le] at h
    have hy' : dist y x < t / 2 := mem_ball.1 hy
    constructor <;> linarith
  have hball : ball x (t / 2) ⊆ {y | 0 < ⟪(v : E), y⟫} := fun y hy ↦
    (half_pos hx).trans (hheight y hy).1
  have hharm : HarmonicOnNhd (fun y ↦ halfSpacePoissonIntegral v g y - c) (ball x (t / 2)) :=
    (hP.mono hball).sub (harmonicOnNhd_const c)
  have hbound : ∀ y ∈ ball x (t / 2),
      ‖halfSpacePoissonIntegral v g y - c‖ ≤ K * (2 * (A + 1)) * t ^ (α : ℝ) := by
    intro y hy
    obtain ⟨hy₁, hy₂⟩ := hheight y hy
    have hyf : ‖y - foot v x‖ ≤ 3 / 2 * t := by
      calc ‖y - foot v x‖ ≤ ‖y - x‖ + ‖x - foot v x‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ t / 2 + t := add_le_add (mem_ball_iff_norm.1 hy).le (norm_sub_foot v hx.le).le
        _ = 3 / 2 * t := by ring
    have h32 : (3 / 2 * t) ^ (α : ℝ) ≤ 2 * t ^ (α : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hx.le]
      have : (3 / 2 : ℝ) ^ (α : ℝ) ≤ (3 / 2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hα1.le)
      rw [Real.rpow_one] at this
      nlinarith [Real.rpow_nonneg hx.le (α : ℝ)]
    rw [Real.norm_eq_abs]
    refine (hdev hM hg (hball hy) (foot v x)).trans ?_
    calc (K : ℝ) * (A * ⟪(v : E), y⟫ ^ (α : ℝ) + ‖y - foot v x‖ ^ (α : ℝ))
        ≤ K * (A * (3 / 2 * t) ^ (α : ℝ) + (3 / 2 * t) ^ (α : ℝ)) := by
          gcongr
          · exact (half_pos hx).le.trans hy₁.le
      _ = K * (A + 1) * (3 / 2 * t) ^ (α : ℝ) := by ring
      _ ≤ K * (A + 1) * (2 * t ^ (α : ℝ)) := by gcongr
      _ = _ := by ring
  have hest := InnerProductSpace.HarmonicOnNhd.norm_iteratedFDeriv_le_of_norm_le hharm hbound
    (half_pos hx) k
  -- The constant `c` does not affect derivatives of positive order.
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' hk
  simp_rw [sub_eq_add_neg] at hest
  rw [hj, iteratedFDeriv_succ_add_const, ← hj] at hest
  refine hest.trans_eq ?_
  have hk' : (t ^ ((α : ℝ) - k)) = t ^ (α : ℝ) / t ^ k := by
    rw [Real.rpow_sub hx, Real.rpow_natCast]
  have e1 : (2 ^ (finrank ℝ E + 1) * finrank ℝ E * k / (t / 2) : ℝ) =
      2 ^ (finrank ℝ E + 2) * finrank ℝ E * k / t := by
    field_simp
    ring
  rw [e1, div_pow, hk']
  ring

end TauCeti
