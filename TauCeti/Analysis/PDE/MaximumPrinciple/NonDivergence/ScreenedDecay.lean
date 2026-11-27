/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.HopfLemma

/-!
# Exponential decay of subsolutions of screened operators in non-divergence form

Let `B = ball x R` be a ball in `ℝⁿ = EuclideanSpace ℝ ι` and consider the second-order operator
in non-divergence form

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`,

with a coefficient matrix that is degenerate elliptic and bounded above on `B`,
`0 ≤ ξᵀ a(y) ξ ≤ Λ ‖ξ‖²`, and a drift bounded by `β`. Suppose that `u` is a subsolution of the
screened operator `-L + V` with a constant forcing `K ≥ 0`,

`V u - K ≤ L u`  on `B`,  with `V ≥ c² > 0`,

and that `u ≤ M` on the boundary sphere, with `M ≥ 0`. Then `u` is exponentially small at the
centre, up to the forcing level `K / c²`:

`u x ≤ K / c² + M exp (-c² R² / (4 c R √Λ + 2 (n Λ + β R)))`

(`TauCeti.PDE.le_div_sq_add_mul_exp_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv`), and, for `u`
bounded by `M` on the open ball,

`u x ≤ K / c² + exp (n / 8) M exp (-c² R / (4 c √Λ + 2 β))`

(`TauCeti.PDE.le_div_sq_add_exp_mul_mul_exp_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv`).
For the Laplacian, `a = 1` and `b = 0`, the rate is `c R / 4`, as in
`TauCeti.le_div_sq_add_exp_mul_mul_exp_of_mul_sub_le_laplacian`. In general the rate is
`c R / (4 √Λ)` up to the drift, which only matters once it is comparable with `c`: when `c` is
large, as for the screening constants `c² ∼ r` of the Seiberg–Witten equations at large parameter
`r`, a fixed bound on the drift costs a factor `1 + O(β / (c √Λ))` in the rate. No lower
ellipticity bound and no regularity of the coefficients is needed, and the constants depend only
on `n`, `Λ` and `β`.

The estimates apply to the Laplace–Beltrami operator of a Riemannian metric written in a chart,
`Δ_g u = gⁱʲ ∂ᵢ∂ⱼu - gⁱʲ Γᵏᵢⱼ ∂ₖu`, which is in non-divergence form with `a = g⁻¹` and a drift
bounded by the Christoffel symbols, so the constants depend on the metric only through bounds on
`g⁻¹` and on its first derivatives. This is the comparison step behind the decay estimates
`C / r + C exp (-c √r d)`, with `d` the distance to the zero set of a spinor component, in
Taubes's analysis of the Seiberg–Witten equations on a symplectic four-manifold at large
parameter `r`, once the screened inequality is read in a chart of a curved metric rather than in
a flat one.

The proof compares `u - K / c²` with the Gaussian barrier

`g y = M exp (μ (‖y - x‖² - R²))`,  `μ = c² / (4 c R √Λ + 2 (n Λ + β R))`,

which equals `M` on the sphere. Since
`L g = (4 μ² (y - x)ᵀ a (y - x) + 2 μ tr a + 2 μ ⟪y - x, b⟫) g`
(`TauCeti.PDE.sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq`), the bounds on `a` and
`b` and the choice of `μ` give `L g ≤ c² g` on the ball, so `K / c² + g` is a supersolution of
`-L + V`. The comparison runs through the weak maximum principle for `-L + V` with `V > 0`
(`TauCeti.PDE.le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier_of_pos`), which needs no
ellipticity beyond `0 ≤ ξᵀ a ξ`.

## Main declarations

* `TauCeti.PDE.le_div_sq_add_mul_exp_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv`: the
  estimate with the barrier exponent, for `u` continuous on the closed ball with `u ≤ M` on the
  sphere.
* `TauCeti.PDE.le_div_sq_add_exp_mul_mul_exp_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv`: the
  estimate with the rate `c² R / (4 c √Λ + 2 β)`, for `u` bounded by `M` on the open ball.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, Chapter 3 (the maximum principle and comparison with barriers).
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Matrix Metric Set Filter Topology RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponent `μ = c² / (4 c R s + 2 T)` of the Gaussian barrier satisfies
`4 s² R² μ² + 2 T μ ≤ c²`. -/
private theorem four_mul_sq_mul_sq_mul_sq_add_two_mul_mul_le {c R s T : ℝ} (hc : 0 < c)
    (hR : 0 ≤ R) (hs : 0 ≤ s) (hT : 0 ≤ T) :
    4 * s ^ 2 * R ^ 2 * (c ^ 2 / (4 * c * R * s + 2 * T)) ^ 2 +
      2 * T * (c ^ 2 / (4 * c * R * s + 2 * T)) ≤ c ^ 2 := by
  set D := 4 * c * R * s + 2 * T
  set μ := c ^ 2 / D
  rcases (show 0 ≤ D by positivity).eq_or_lt with hD | hD
  · simp [μ, ← hD, sq_nonneg]
  have hμ : 0 ≤ μ := by positivity
  have hμD : μ * D = c ^ 2 := div_mul_cancel₀ _ hD.ne'
  have hsRμ : 0 ≤ s * R * μ := by positivity
  -- From `μ D = c²` and `D ≥ 4 c R s`: `4 s R μ ≤ c`, so `4 s² R² μ² ≤ 4 c s R μ = μ D - 2 T μ`.
  have hle : 4 * (s * R * μ) ≤ c := by
    have : c * (4 * (s * R * μ)) ≤ c * c := by nlinarith [mul_nonneg hT hμ]
    exact le_of_mul_le_mul_left this hc
  nlinarith [mul_le_mul_of_nonneg_left hle hsRμ]

/-- **The Gaussian barrier.** Let the matrix `A` satisfy `ξᵀ A ξ ≤ s² ‖ξ‖²` and let
`tr A + ⟪y - x, v⟫ ≤ T`. If `‖y - x‖ ≤ R`, then the barrier
`g = M exp (μ (‖· - x‖² - R²))`, `μ = c² / (4 c R s + 2 T)`, satisfies
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼg + ∂_v g ≤ c² g` at `y`. -/
private theorem sum_mul_fderiv_fderiv_add_fderiv_gaussian_le {A : Matrix ι ι ℝ}
    {x y v : EuclideanSpace ℝ ι} {c R s T M : ℝ} (hc : 0 < c) (hR : 0 ≤ R) (hs : 0 ≤ s)
    (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ s ^ 2 * ‖ξ‖ ^ 2)
    (htr : A.trace + ⟪y - x, v⟫ ≤ T) (hy : ‖y - x‖ ≤ R) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ M * Real.exp (c ^ 2 / (4 * c * R * s + 2 * T) *
        (‖z - x‖ ^ 2 - R ^ 2))) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z ↦ M * Real.exp (c ^ 2 / (4 * c * R * s + 2 * T) *
        (‖z - x‖ ^ 2 - R ^ 2))) y v ≤
      c ^ 2 * (M * Real.exp (c ^ 2 / (4 * c * R * s + 2 * T) * (‖y - x‖ ^ 2 - R ^ 2))) := by
  set μ := c ^ 2 / (4 * c * R * s + 2 * T)
  set r := M * Real.exp (-(μ * R ^ 2))
  -- The barrier is a constant multiple of the Gaussian `exp (μ ‖· - x‖²)`.
  have hfun : (fun z : EuclideanSpace ℝ ι ↦ M * Real.exp (μ * (‖z - x‖ ^ 2 - R ^ 2))) =
      r • fun z ↦ Real.exp (-(-μ) * ‖z - x‖ ^ 2) := by
    funext z
    simp only [r, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Real.exp_add]
    ring_nf
  have hG := sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq A (-μ) x y v
  rw [hfun, fderiv_fderiv_const_smul, fderiv_const_smul_field]
  simp only [Pi.smul_apply, _root_.smul_apply, smul_eq_mul]
  have hlin : ∑ i, ∑ j, A i j * (r * fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-(-μ) * ‖z - x‖ ^ 2))
      y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
      r * fderiv ℝ (fun z ↦ Real.exp (-(-μ) * ‖z - x‖ ^ 2)) y v =
      r * (∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-(-μ) * ‖z - x‖ ^ 2)) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        fderiv ℝ (fun z ↦ Real.exp (-(-μ) * ‖z - x‖ ^ 2)) y v) := by
    simp only [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hlin, hG]
  set G := Real.exp (-(-μ) * ‖y - x‖ ^ 2)
  have hrG : r * G = M * Real.exp (μ * (‖y - x‖ ^ 2 - R ^ 2)) := by
    simp only [r, G, mul_assoc, ← Real.exp_add]
    ring_nf
  have hrG0 : 0 ≤ r * G := by positivity
  have hQ : A.toQuadraticForm' (y - x) ≤ s ^ 2 * R ^ 2 :=
    (hA _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 2) (sq_nonneg s))
  have hcoef : 4 * (-μ) ^ 2 * A.toQuadraticForm' (y - x) - 2 * (-μ) * A.trace -
      2 * (-μ) * ⟪y - x, v⟫ ≤ c ^ 2 := by
    have h := four_mul_sq_mul_sq_mul_sq_add_two_mul_mul_le hc hR hs hT
    nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 4 * μ ^ 2),
      mul_le_mul_of_nonneg_left htr (by positivity : (0 : ℝ) ≤ 2 * μ)]
  rw [← hrG]
  nlinarith [mul_le_mul_of_nonneg_left hcoef hrG0]

/-- **The comparison step.** If `u` is a subsolution of `-L + V` with forcing `K`,
`V u - K ≤ L u`, and `g ≥ 0` satisfies `L g ≤ c² g` with `c² ≤ V`, then `u - (K / c² + g)` is a
subsolution of `-L + V` without forcing, at the point `y`. -/
private theorem mul_le_sum_mul_fderiv_fderiv_add_fderiv_add_neg_one_mul {A : Matrix ι ι ℝ}
    {v y : EuclideanSpace ℝ ι} {u g : EuclideanSpace ℝ ι → ℝ} {c K V : ℝ} (hc : 0 < c)
    (hK : 0 ≤ K) (hV : c ^ 2 ≤ V) (hu : ContDiffAt ℝ 2 u y) (hg : ContDiffAt ℝ 2 g y)
    (hg0 : 0 ≤ g y)
    (hsub : V * u y - K ≤ ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ u y v)
    (hbar : ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ g) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ g y v ≤ c ^ 2 * g y) :
    V * (u y + (-1 : ℝ) * (K / c ^ 2 + g y)) ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ u z + (-1 : ℝ) * (K / c ^ 2 + g z)) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z ↦ u z + (-1 : ℝ) * (K / c ^ 2 + g z)) y v := by
  -- The constant `K / c²` is invisible to `L`, which is linear.
  have hsplit : (fun z ↦ u z + (-1 : ℝ) * (K / c ^ 2 + g z)) =
      (fun z ↦ u z + -(K / c ^ 2)) + (-1 : ℝ) • g := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hshift : fderiv ℝ (fun z ↦ u z + -(K / c ^ 2)) = fderiv ℝ u :=
    funext fun z ↦ fderiv_add_const _
  rw [hsplit, sum_mul_fderiv_fderiv_add_fderiv_add_smul (hu.add contDiffAt_const) hg, hshift]
  -- `V ≥ c²` and `K ≥ 0` give `K ≤ V K / c²`, and `L g ≤ c² g ≤ V g`.
  have hKV : K ≤ V * (K / c ^ 2) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hV hg0]

/-- If `0 ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²`, `‖v‖ ≤ β` and `‖y - x‖ ≤ R`, then `0 ≤ n Λ + β R` and
`tr A + ⟪y - x, v⟫ ≤ n Λ + β R`: the diagonal entries of `A` lie between `0` and `Λ`. -/
private theorem trace_add_inner_le {A : Matrix ι ι ℝ} {x y v : EuclideanSpace ℝ ι} {R Λ β : ℝ}
    (ha : ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ A.toQuadraticForm' ξ)
    (hΛ : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Λ * ‖ξ‖ ^ 2) (hv : ‖v‖ ≤ β)
    (hy : ‖y - x‖ ≤ R) :
    0 ≤ Fintype.card ι * Λ + β * R ∧ A.trace + ⟪y - x, v⟫ ≤ Fintype.card ι * Λ + β * R := by
  have hdiag (i : ι) : A.toQuadraticForm' (Pi.single i 1) = A i i := by
    simp [toQuadraticForm'_apply, dotProduct, mulVec, Pi.single_apply]
  have hle (i : ι) : A i i ≤ Λ := by
    have h := hΛ (EuclideanSpace.single i 1)
    simpa [hdiag] using h
  have htr : 0 ≤ A.trace ∧ A.trace ≤ Fintype.card ι * Λ := by
    refine ⟨Finset.sum_nonneg fun i _ ↦ ?_, ?_⟩
    · simpa [hdiag] using ha (EuclideanSpace.single i 1)
    calc A.trace = ∑ i, A i i := rfl
      _ ≤ ∑ _i : ι, Λ := Finset.sum_le_sum fun i _ ↦ hle i
      _ = Fintype.card ι * Λ := by simp
  have hinner : ⟪y - x, v⟫ ≤ β * R :=
    (real_inner_le_norm _ _).trans (by
      rw [mul_comm β]
      exact mul_le_mul hy hv (norm_nonneg _) ((norm_nonneg _).trans hy))
  have hβR : 0 ≤ β * R := mul_nonneg ((norm_nonneg _).trans hv) ((norm_nonneg _).trans hy)
  exact ⟨by linarith [htr.1.trans htr.2], by linarith [htr.2]⟩

/-- **Exponential decay of subsolutions of a screened non-divergence operator, barrier form.** On
the ball of radius `R > 0` about `x`, let `0 ≤ ξᵀ a(y) ξ ≤ Λ ‖ξ‖²` and `‖b(y)‖ ≤ β`. Let `u` be
continuous on the closed ball and `C²` on the open ball, where it satisfies
`V u - K ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` for a potential `V ≥ c²`, `c > 0`, and a forcing `K ≥ 0`. If
`u ≤ M` on the sphere, with `M ≥ 0`, then at the centre, with `n` the dimension,

`u x ≤ K / c² + M exp (-c² R² / (4 c R √Λ + 2 (n Λ + β R)))`. -/
theorem le_div_sq_add_mul_exp_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u V : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι} {c R K M Λ β : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (ha : ∀ y ∈ ball x R, ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ (a y).toQuadraticForm' ξ)
    (hΛ : ∀ y ∈ ball x R, ∀ ξ : EuclideanSpace ℝ ι, (a y).toQuadraticForm' ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hb : ∀ y ∈ ball x R, ‖b y‖ ≤ β) (hcont : ContinuousOn u (closedBall x R))
    (hcd : ∀ y ∈ ball x R, ContDiffAt ℝ 2 u y) (hV : ∀ y ∈ ball x R, c ^ 2 ≤ V y)
    (hsub : ∀ y ∈ ball x R, V y * u y - K ≤
      ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u y (b y))
    (hbdry : ∀ y ∈ sphere x R, u y ≤ M) :
    u x ≤ K / c ^ 2 + M * Real.exp (-(c ^ 2 * R ^ 2 /
      (4 * c * R * √Λ + 2 * (Fintype.card ι * Λ + β * R)))) := by
  set T := Fintype.card ι * Λ + β * R
  set μ := c ^ 2 / (4 * c * R * √Λ + 2 * T)
  set g : EuclideanSpace ℝ ι → ℝ := fun z ↦ M * Real.exp (μ * (‖z - x‖ ^ 2 - R ^ 2))
  have hg : ContDiff ℝ 2 g := by
    have : ContDiff ℝ 2 fun z : EuclideanSpace ℝ ι ↦ ‖z - x‖ ^ 2 :=
      (contDiff_id.sub contDiff_const).norm_sq ℝ
    fun_prop
  have hint : interior (closedBall x R) = ball x R := interior_closedBall x hR.ne'
  have hx : x ∈ ball x R := mem_ball_self hR
  have hT : 0 ≤ T := (trace_add_inner_le (ha x hx) (hΛ x hx) (hb x hx)
    (show ‖x - x‖ ≤ R by simpa using hR.le)).1
  -- The upper bound on `a` in the form `ξᵀ a ξ ≤ (√Λ)² ‖ξ‖²`, valid also when `Λ < 0`.
  have hΛ' (y : EuclideanSpace ℝ ι) (hy : y ∈ ball x R) (ξ : EuclideanSpace ℝ ι) :
      (a y).toQuadraticForm' ξ ≤ √Λ ^ 2 * ‖ξ‖ ^ 2 := by
    rcases le_total 0 Λ with h | h
    · rw [Real.sq_sqrt h]
      exact hΛ y hy ξ
    · rw [Real.sqrt_eq_zero'.mpr h]
      nlinarith [hΛ y hy ξ, mul_nonneg (neg_nonneg.mpr h) (sq_nonneg ‖ξ‖)]
  -- Compare `u - K / c²` with the barrier `g` through the maximum principle for `-L + V`.
  have key := le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier_of_pos
    (isCompact_closedBall x R) (a := a) (b := b) (c := V) (m := 0)
    (f := fun y ↦ u y + (-1 : ℝ) * (K / c ^ 2 + g y))
    (fun y hy ↦ ha y (hint ▸ hy)) (fun y hy ↦ (sq_pos_of_pos hc).trans_le (hV y (hint ▸ hy)))
    le_rfl (hcont.add (continuousOn_const.mul (continuousOn_const.add hg.continuous.continuousOn)))
    (fun y hy ↦ (hcd y (hint ▸ hy)).add (contDiffAt_const.mul (contDiffAt_const.add hg.contDiffAt)))
    (fun y hy ↦ by
      rw [hint] at hy
      exact mul_le_sum_mul_fderiv_fderiv_add_fderiv_add_neg_one_mul hc hK (hV y hy) (hcd y hy)
        hg.contDiffAt (by positivity) (hsub y hy)
        (sum_mul_fderiv_fderiv_add_fderiv_gaussian_le hc hR.le (Real.sqrt_nonneg Λ) hT hM
          (hΛ' y hy) (trace_add_inner_le (ha y hy) (hΛ y hy) (hb y hy)
            (mem_ball_iff_norm.1 hy).le).2 (mem_ball_iff_norm.1 hy).le))
    (fun y hy ↦ by
      have hyx : ‖y - x‖ = R := mem_sphere_iff_norm.1 (frontier_closedBall_subset_sphere hy)
      have hu := hbdry y (frontier_closedBall_subset_sphere hy)
      simp only [g, hyx, sub_self, mul_zero, Real.exp_zero, mul_one]
      linarith [div_nonneg hK (sq_nonneg c)])
    (mem_closedBall_self hR.le)
  simp only [g, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_sub] at key
  have hμR : μ * -R ^ 2 = -(c ^ 2 * R ^ 2 / (4 * c * R * √Λ + 2 * T)) := by
    simp only [μ]
    ring
  rw [hμR] at key
  linarith

/-- The barrier exponent `c² s² / (4 c s σ + 2 (P + β s))` of the decay estimate on the ball of
radius `s` is at least `c² s / (4 c σ + 2 β) - n / 8` when `0 ≤ P ≤ n σ²`. -/
private theorem neg_div_le_div_eight_add_neg_div {c s σ β P n : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hσ : 0 ≤ σ) (hβ : 0 ≤ β) (hn : 0 ≤ n) (hP : 0 ≤ P) (hPn : P ≤ n * σ ^ 2) :
    -(c ^ 2 * s ^ 2 / (4 * c * s * σ + 2 * (P + β * s))) ≤
      n / 8 + -(c ^ 2 * s / (4 * c * σ + 2 * β)) := by
  set A := 4 * c * σ + 2 * β
  have hDA : 4 * c * s * σ + 2 * (P + β * s) = s * A + 2 * P := by ring
  rw [hDA]
  rcases (show 0 ≤ A by positivity).eq_or_lt with hA | hA
  · -- Then `σ = β = 0`, so `P = 0` and both exponents vanish.
    have hσ0 : σ = 0 := by nlinarith
    have hP0 : P = 0 := le_antisymm (by simpa [hσ0] using hPn) hP
    simp only [← hA, hP0, mul_zero, add_zero, div_zero, neg_zero]
    positivity
  -- The difference of the exponents is `2 c² s P / (A (s A + 2 P)) ≤ 2 c² P / A² ≤ n / 8`.
  have h1 : c ^ 2 * s / A - c ^ 2 * s ^ 2 / (s * A + 2 * P) =
      2 * c ^ 2 * s * P / (A * (s * A + 2 * P)) := by
    field_simp
    ring
  have h2 : 2 * c ^ 2 * s * P / (A * (s * A + 2 * P)) ≤ 2 * c ^ 2 * P / A ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c) hP) (mul_nonneg hA.le hP)]
  have h3 : 2 * c ^ 2 * P / A ^ 2 ≤ n / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hA2 : 16 * c ^ 2 * σ ^ 2 ≤ A ^ 2 := by nlinarith [mul_nonneg hc.le hσ]
    nlinarith [mul_le_mul_of_nonneg_left hPn (sq_nonneg c), mul_le_mul_of_nonneg_left hA2 hn]
  linarith

/-- **Exponential decay of subsolutions of a screened non-divergence operator inside a ball.** On
the ball of radius `R > 0` about `x`, let `0 ≤ ξᵀ a(y) ξ ≤ Λ ‖ξ‖²` and `‖b(y)‖ ≤ β`. Let `u` be
`C²` on the ball, where it satisfies `V u - K ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` for a potential `V ≥ c²`,
`c > 0`, and a forcing `K ≥ 0`, and is bounded by `M ≥ 0`. Then at the centre, with `n` the
dimension,

`u x ≤ K / c² + exp (n / 8) M exp (-c² R / (4 c √Λ + 2 β))`. -/
theorem le_div_sq_add_exp_mul_mul_exp_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u V : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι} {c R K M Λ β : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (ha : ∀ y ∈ ball x R, ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ (a y).toQuadraticForm' ξ)
    (hΛ : ∀ y ∈ ball x R, ∀ ξ : EuclideanSpace ℝ ι, (a y).toQuadraticForm' ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hb : ∀ y ∈ ball x R, ‖b y‖ ≤ β) (hcd : ∀ y ∈ ball x R, ContDiffAt ℝ 2 u y)
    (hV : ∀ y ∈ ball x R, c ^ 2 ≤ V y)
    (hsub : ∀ y ∈ ball x R, V y * u y - K ≤
      ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u y (b y))
    (hle : ∀ y ∈ ball x R, u y ≤ M) :
    u x ≤ K / c ^ 2 + Real.exp ((Fintype.card ι : ℝ) / 8) * M *
      Real.exp (-(c ^ 2 * R / (4 * c * √Λ + 2 * β))) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set F : ℝ → ℝ := fun s ↦
    K / c ^ 2 + Real.exp (n / 8) * M * Real.exp (-(c ^ 2 * s / (4 * c * √Λ + 2 * β)))
  have hx : x ∈ ball x R := mem_ball_self hR
  -- The coefficient bounds at the centre give `β ≥ 0` and `0 ≤ n Λ ≤ n (√Λ)²`.
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hb x hx)
  have hnΛ : 0 ≤ n * Λ := by
    simpa using (trace_add_inner_le (ha x hx) (hΛ x hx) (hb x hx)
      (show ‖x - x‖ ≤ 0 by simp)).1
  have hnσ : n * Λ ≤ n * √Λ ^ 2 := by
    rcases le_total 0 Λ with h | h
    · rw [Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero'.mpr h]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)) (neg_nonneg.mpr h)]
  -- The bound holds on every smaller closed ball, and `F` is continuous in the radius.
  have hsmall : ∀ s ∈ Ioo 0 R, u x ≤ F s := by
    rintro s ⟨hs, hsR⟩
    have hcl : closedBall x s ⊆ ball x R := closedBall_subset_ball hsR
    have hball : ball x s ⊆ ball x R := ball_subset_ball hsR.le
    have h := le_div_sq_add_mul_exp_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv hc hs hK hM
      (fun y hy ↦ ha y (hball hy)) (fun y hy ↦ hΛ y (hball hy)) (fun y hy ↦ hb y (hball hy))
      (fun y hy ↦ (hcd y (hcl hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ hcd y (hball hy)) (fun y hy ↦ hV y (hball hy)) (fun y hy ↦ hsub y (hball hy))
      (fun y hy ↦ hle y (hcl (sphere_subset_closedBall hy)))
    have hexp := neg_div_le_div_eight_add_neg_div hc hs (Real.sqrt_nonneg Λ) hβ
      (Nat.cast_nonneg _) hnΛ hnσ
    calc u x ≤ K / c ^ 2 + M * Real.exp (-(c ^ 2 * s ^ 2 /
          (4 * c * s * √Λ + 2 * (n * Λ + β * s)))) := h
      _ ≤ K / c ^ 2 + M * Real.exp (n / 8 + -(c ^ 2 * s / (4 * c * √Λ + 2 * β))) := by gcongr
      _ = F s := by
        simp only [F, Real.exp_add]
        ring
  have hF : Continuous F := by fun_prop
  exact ge_of_tendsto (hF.tendsto R |>.mono_left nhdsWithin_le_nhds)
    (eventually_of_mem (Ioo_mem_nhdsLT hR) hsmall)

end PDE

end TauCeti
