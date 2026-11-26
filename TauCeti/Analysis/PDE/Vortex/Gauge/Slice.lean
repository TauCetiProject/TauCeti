/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Gauge.Laplacian
import TauCeti.Analysis.PDE.Vortex.EquationMap
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The infinitesimal Coulomb slice and local uniqueness of the Coulomb gauge

The framed degree-`m` plane vortex fields form the affine space `A_m^k = x_m + H^k`
(`TauCeti.Vortex.framedFieldSpace`), acted on by the Sobolev framed gauge group `G_(k+1)`. At a
field `x`, the infinitesimal gauge action `d₀ = TauCeti.Vortex.gaugeDirection x` sends a real phase
`u` to the variation `(-∂₁u, -∂₂u, -u q, u p)`, and its formal `L²` adjoint
`d₀* = TauCeti.Vortex.gaugeAdjoint x` is the Coulomb gauge-fixing operator. Their composite is the
gauge Laplacian `d₀* d₀ u = -Δu + (p² + q²) u` (`TauCeti.Vortex.gaugeAdjoint_gaugeDirection`).

This file proves that the Coulomb condition `d₀* y = 0` is a slice for the infinitesimal gauge
action on the tangent space `H^k` of `A_m^k`: every variation splits uniquely as an infinitesimal
gauge transformation plus a Coulomb variation,

`y = d₀ u + (y - d₀ u)`,  `d₀* (y - d₀ u) = 0`,  `u ∈ H^(k+1)`.

Here `x` is a continuous field of `A_m^k` and `y` a continuous variation in `H^k`, with `k ≥ 3`, so
that `y` is `C¹` by the Sobolev embedding and `d₀* y` is defined pointwise.

* **Existence** (`TauCeti.Vortex.exists_gaugeAdjoint_sub_gaugeDirection_eq_zero`). The phase `u`
  solves `d₀* d₀ u = d₀* y`. Since `d₀* y ∈ H^(k-1)`
  (`TauCeti.Vortex.gaugeAdjoint_mem_realSobolevFunctions`), the gauge Laplacian has a weak solution
  `u ∈ H^(k+1)`
  (`TauCeti.Vortex.exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq`),
  whose continuous representative is `C²`. A `C²` weak solution is a classical solution
  (`TauCeti.Vortex.gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq`), so the Coulomb condition
  holds at every point, and `d₀ u ∈ H^k` (`TauCeti.Vortex.gaugeDirection_mem_sobolevFields`).
* **Uniqueness** (`TauCeti.Vortex.existsUnique_gaugeAdjoint_sub_gaugeDirection_eq_zero`). No
  nonzero infinitesimal gauge transformation is Coulomb: a `C²` solution of `d₀* d₀ u = 0` tending
  to zero at infinity vanishes (`TauCeti.Vortex.eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero`),
  and a continuous `u ∈ H^(k+1)` tends to zero at infinity by the Sobolev embedding.

At a vortex the infinitesimal gauge transformations solve the linearized equation,
`d₁ d₀ = 0` (`TauCeti.Vortex.linearizedEquation_gaugeDirection_eq_zero`). The splitting then
carries a solution `y ∈ H^k` of the linearized equation `d₁ y = 0` to the element `y - d₀ u` of the
kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.exists_gaugeFixedOperator_sub_gaugeDirection_eq_zero`). As consequences of
these results, not statements of this file: with uniqueness, the continuous solutions of
`d₁ y = 0` in `H^k` are the direct sum of the infinitesimal gauge transformations `d₀ u`,
`u ∈ H^(k+1)` continuous, and the continuous variations in `H^k` lying in the kernel of `L_x`;
so these elements of the kernel of the gauge-fixed operator represent the first cohomology
`ker d₁ / im d₀` of the deformation complex at `x`.

**Local uniqueness of the nonlinear Coulomb gauge.** A phase gauge transformation
`y ↦ e^{iF} y` (`TauCeti.Vortex.phaseGauge`) changes the Coulomb defect by

`d₀* (e^{iF} y) - d₀* y = -ΔF + sin F (p y₂ + q y₃) + (cos F - 1) (p y₃ - q y₂)`

(`TauCeti.Vortex.gaugeAdjoint_phaseGauge`), where `(p, q)` are the section coordinates of `x`.
If the two defects agree, `F` solves `ΔF = Q F` for a potential `Q` within a constant times
`sup |F| + sup |y_α - x_α|` of the potential `p² + q²` of the gauge Laplacian. So for a continuous
field `x` of `A_m^s`, `s > 1`, there is `ε > 0` such that a square-integrable `C²` phase with
`|F| ≤ ε`, acting on a field `y` whose section is within `ε` of that of `x`, preserves the
Coulomb defect only if `F = 0`
(`TauCeti.Vortex.exists_pos_forall_eq_zero_of_gaugeAdjoint_phaseGauge_eq`). The potential `Q` may
be negative near the zeros of the section of `x`; the argument uses that uniqueness of weak
solutions of `-Δh + P h = 0` survives small bounded perturbations of `P`
(`TauCeti.exists_pos_forall_ae_eq_zero_of_integral_mul_neg_laplacian_add_mul_eq_zero`). This is the
uniqueness half of the slice theorem; its statement for the Sobolev gauge group acting on `A_m^k`
is in `TauCeti.Analysis.PDE.Vortex.FramedGauge.Slice`. The existence half, which puts a field of
`A_m^k` near `x` into the Coulomb slice `d₀* (· - x) = 0` by an element of `G_(k+1)`, is not
treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory TemperedDistribution Filter Topology
open scoped Laplacian ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- For `k ≥ 3`, a continuous field of `A_m^k` and a continuous variation in `H^k` are `C¹`, by
the Sobolev embedding. -/
private theorem contDiff_one_of_three_le {k : ℕ} (hk : 3 ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hxc : Continuous x) {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k)
    (hyc : Continuous y) : ContDiff ℝ 1 x ∧ ContDiff ℝ 1 y := by
  have hk1 : ((1 : ℕ) : ℝ) + 1 < k := by exact_mod_cast (by omega : 1 + 1 < k)
  exact ⟨contDiff_of_mem_framedFieldSpace hk1 hxc hx, contDiff_of_mem_sobolevFields hk1 hy hyc⟩

/-- The Coulomb defect of `y - d₀ u` is that of `y` minus the gauge Laplacian of `u`. -/
private theorem gaugeAdjoint_sub_gaugeDirection (hx : ContDiff ℝ 1 x)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 1 y) {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (z : ℂ) :
    gaugeAdjoint x (y - gaugeDirection x u) z =
      gaugeAdjoint x y z - (-Δ u z + (x z 2 ^ 2 + x z 3 ^ 2) * u z) := by
  have hx' := differentiableAt_euclidean.1 (hx.differentiable one_ne_zero z)
  have hy' := differentiableAt_euclidean.1 (hy.differentiable one_ne_zero z)
  have hdu := differentiableAt_euclidean.1
    (differentiableAt_gaugeDirection hu.contDiffAt (hx' 2) (hx' 3))
  rw [gaugeAdjoint_sub x (hy' 0) (hy' 1) (hdu 0) (hdu 1),
    gaugeAdjoint_gaugeDirection x hu.contDiffAt]

/-- **The infinitesimal Coulomb slice.** Let `x` be a continuous field of `A_m^k`, `k ≥ 3`, and `y`
a continuous variation in `H^k`. Then there is a `C²` phase `u ∈ H^(k+1)` whose infinitesimal gauge
transformation `d₀ u` lies in `H^k` and moves `y` into the Coulomb slice: `d₀* (y - d₀ u) = 0` at
every point. The phase is unique by
`TauCeti.Vortex.existsUnique_gaugeAdjoint_sub_gaugeDirection_eq_zero`. -/
theorem exists_gaugeAdjoint_sub_gaugeDirection_eq_zero {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hxc : Continuous x) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields k) (hyc : Continuous y) :
    ∃ u ∈ realSobolevFunctions ℂ (k + 1) 2, ContDiff ℝ 2 u ∧
      gaugeDirection x u ∈ sobolevFields k ∧
        ∀ z, gaugeAdjoint x (y - gaugeDirection x u) z = 0 := by
  obtain ⟨hx1, hy1⟩ := contDiff_one_of_three_le hk hx hxc hy hyc
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := Nat.cast_succ n
  rw [hcast] at hx hy ⊢
  -- The source `d₀* y` lies in `H^n` and is continuous.
  have hg : gaugeAdjoint x y ∈ realSobolevFunctions ℂ n 2 :=
    gaugeAdjoint_mem_realSobolevFunctions (by omega) hx hy hy1
  have hgc : Continuous (gaugeAdjoint x y) := continuous_gaugeAdjoint hxc hy1
  -- Solve `d₀* d₀ u₀ = d₀* y` weakly with `u₀ ∈ H^(n+2)`, and take a `C²` representative `u`.
  obtain ⟨u₀, hu₀, hw₀⟩ :=
    exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq (k := n + 1)
      (j := n) (by omega) (by omega) (by exact_mod_cast hx) hxc hg
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  obtain ⟨u, hu2, hu₀u⟩ := exists_contDiff_ae_eq_of_mem_realSobolevFunctions (k := 2)
    (finrank_real_complex_add_two_mul_lt_two_mul (by push_cast; linarith)) hu₀
  have hu : u ∈ realSobolevFunctions ℂ (n + 2) 2 := mem_realSobolevFunctions_of_ae_eq hu₀ hu₀u
  have hw (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
      ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, gaugeAdjoint x y z * φ z := by
    rw [← hw₀ φ (hφ.of_le (by simp)) hφc]
    exact integral_congr_ae (hu₀u.mono fun z hz ↦ by simp only [hz])
  have hcl := gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq hxc hu2 hgc hw
  refine ⟨u, by convert hu using 2; ring, hu2,
    gaugeDirection_mem_sobolevFields (by omega) hx (by convert hu using 2) (hu2.of_le one_le_two),
    fun z ↦ ?_⟩
  rw [gaugeAdjoint_sub_gaugeDirection hx1 hy1 hu2, ← gaugeAdjoint_gaugeDirection x hu2.contDiffAt,
    hcl z, sub_self]

/-- **Uniqueness of the infinitesimal Coulomb slice.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 3`, and `y` a continuous variation in `H^k`. Exactly one continuous phase `u ∈ H^(k+1)`
satisfies `d₀* (y - d₀ u) = 0` at every point. -/
theorem existsUnique_gaugeAdjoint_sub_gaugeDirection_eq_zero {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hxc : Continuous x) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields k) (hyc : Continuous y) :
    ∃! u : ℂ → ℝ, (u ∈ realSobolevFunctions ℂ (k + 1) 2 ∧ Continuous u) ∧
      ∀ z, gaugeAdjoint x (y - gaugeDirection x u) z = 0 := by
  obtain ⟨u, hu, hu2, -, hcoul⟩ := exists_gaugeAdjoint_sub_gaugeDirection_eq_zero hk hx hxc hy hyc
  refine ⟨u, ⟨⟨hu, hu2.continuous⟩, hcoul⟩, fun v ⟨⟨hv, hvc⟩, hvcoul⟩ ↦ ?_⟩
  -- A continuous phase in `H^(k+1)` is `C²` and tends to zero at infinity.
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (Module.finrank ℝ ℂ : ℝ) + 2 * (2 : ℕ) < 2 * (k + 1) :=
    finrank_real_complex_add_two_mul_lt_two_mul (by push_cast; linarith)
  have hv2 : ContDiff ℝ 2 v := contDiff_of_mem_realSobolevFunctions hs hv hvc
  have hlim (w : ℂ → ℝ) (hw : w ∈ realSobolevFunctions ℂ (k + 1) 2) (hwc : Continuous w) :
      Tendsto w (cocompact ℂ) (𝓝 0) :=
    tendsto_cocompact_of_mem_realSobolevFunctions (by linarith) hw hwc
  obtain ⟨hx1, hy1⟩ := contDiff_one_of_three_le hk hx hxc hy hyc
  -- The difference `v - u` is an infinitesimal gauge transformation in the Coulomb slice.
  have hdiff : ∀ z, gaugeAdjoint x (gaugeDirection x (v - u)) z = 0 := by
    intro z
    have h₁ := hvcoul z
    have h₂ := hcoul z
    rw [gaugeAdjoint_sub_gaugeDirection hx1 hy1 hv2] at h₁
    rw [gaugeAdjoint_sub_gaugeDirection hx1 hy1 hu2] at h₂
    rw [gaugeAdjoint_gaugeDirection (f := v - u) x (hv2.sub hu2).contDiffAt,
      hv2.contDiffAt.laplacian_sub hu2.contDiffAt, Pi.sub_apply]
    linear_combination h₂ - h₁
  have h0 := eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero x (hv2.sub hu2)
    (by simpa using (hlim v hv hvc).sub (hlim u hu hu2.continuous)) hdiff
  exact sub_eq_zero.1 h0

/-- **Every linearized solution is gauge-equivalent to an element of `ker L_x`.** Let `x` be a
continuous vortex of `A_m^k`, `k ≥ 3`, and `y` a continuous variation in `H^k` solving the
linearized equation `d₁ y = 0`. Then there is a `C²` phase `u ∈ H^(k+1)`, with `d₀ u ∈ H^k`, such
that `y - d₀ u` lies in the kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁`. Among continuous
phases in `H^(k+1)` this `u` is unique
(`TauCeti.Vortex.existsUnique_gaugeAdjoint_sub_gaugeDirection_eq_zero`); in particular no nonzero
`d₀ v` with `v` continuous in `H^(k+1)` lies in `ker L_x`. -/
theorem exists_gaugeFixedOperator_sub_gaugeDirection_eq_zero {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hxc : Continuous x) (hsol : ∀ z, equation x z = 0)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) (hyc : Continuous y)
    (hlin : ∀ z, linearizedEquation x y z = 0) :
    ∃ u ∈ realSobolevFunctions ℂ (k + 1) 2, ContDiff ℝ 2 u ∧
      gaugeDirection x u ∈ sobolevFields k ∧
        ∀ z, gaugeFixedOperator x (y - gaugeDirection x u) z = 0 := by
  obtain ⟨u, hu, hu2, hdu, hcoul⟩ :=
    exists_gaugeAdjoint_sub_gaugeDirection_eq_zero hk hx hxc hy hyc
  refine ⟨u, hu, hu2, hdu, fun z ↦ ?_⟩
  obtain ⟨hx1, hy1⟩ := contDiff_one_of_three_le hk hx hxc hy hyc
  have hxi := differentiableAt_euclidean.1 (hx1.differentiable one_ne_zero z)
  -- `L_x` is additive, and `L_x (d₀ u)` has vanishing equation rows since `d₁ d₀ = 0`.
  have hsplit := gaugeFixedOperator_sub x (hy1.differentiable one_ne_zero z)
    (differentiableAt_gaugeDirection hu2.contDiffAt (hxi 2) (hxi 3))
  have hL := linearizedEquation_gaugeDirection_eq_zero (hxi 2) (hxi 3) hu2.contDiffAt (hsol z)
  ext i
  fin_cases i
  · simpa using hcoul z
  all_goals simp [hsplit, hlin z, hL]

/-! ### Local uniqueness of the Coulomb gauge -/

/-- **The Coulomb defect of a phase gauge transformation.** Let `y` be a variation whose connection
coordinates are differentiable at `z`, and `F` a phase which is `C²` at `z`. The gauge
transformation `e^{iF} y` (`TauCeti.Vortex.phaseGauge`) changes the Coulomb defect at the field
`x = (b₁, b₂, p, q)` by

`d₀* (e^{iF} y) - d₀* y = -ΔF + sin F (p y₂ + q y₃) + (cos F - 1) (p y₃ - q y₂)`.

At `y = x` its linear part in `F` is the gauge Laplacian `-ΔF + (p² + q²) F` of
`TauCeti.Vortex.gaugeAdjoint_gaugeDirection`. -/
theorem gaugeAdjoint_phaseGauge (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} {F : ℂ → ℝ} {z : ℂ}
    (hy₀ : DifferentiableAt ℝ (fun w ↦ y w 0) z) (hy₁ : DifferentiableAt ℝ (fun w ↦ y w 1) z)
    (hF : ContDiffAt ℝ 2 F z) :
    gaugeAdjoint x (phaseGauge y F) z = gaugeAdjoint x y z - Δ F z +
      Real.sin (F z) * (x z 2 * y z 2 + x z 3 * y z 3) +
        (Real.cos (F z) - 1) * (x z 2 * y z 3 - x z 3 * y z 2) := by
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd (v : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ F w v) z :=
    hdf.clm_apply (differentiableAt_const v)
  simp only [gaugeAdjoint_def, phaseGauge_apply_zero, phaseGauge_apply_one,
    phaseGauge_apply_two, phaseGauge_apply_three]
  rw [fderiv_fun_sub hy₀ (hd 1), fderiv_fun_sub hy₁ (hd Complex.I),
    laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI hdf]
  simp only [Fin.isValue, sub_apply, Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The pointwise estimate behind the local uniqueness of the Coulomb gauge: if `|a|, |b| ≤ M`
and `|y₂ - a|, |y₃ - b|, |t| ≤ ε ≤ 1 / 2`, the potential
`sinc t (a y₂ + b y₃) - (t / 2) sinc (t / 2)² (a y₃ - b y₂)` is within `ε (2 M² + 5 M)` of
`a² + b²`. -/
private theorem abs_sinc_mul_sub_le {M ε a b y₂ y₃ t : ℝ} (hM : 0 ≤ M) (ha : |a| ≤ M)
    (hb : |b| ≤ M) (hc : |y₂ - a| ≤ ε) (hd : |y₃ - b| ≤ ε) (ht : |t| ≤ ε) (hε : ε ≤ 1 / 2) :
    |Real.sinc t * (a * y₂ + b * y₃) - t / 2 * Real.sinc (t / 2) ^ 2 * (a * y₃ - b * y₂) -
      (a ^ 2 + b ^ 2)| ≤ ε * (2 * M ^ 2 + 5 * M) := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans ht
  have hs₁ : |Real.sinc t - 1| ≤ ε :=
    (Real.abs_sinc_sub_one_le t).trans (by nlinarith [sq_abs t, abs_nonneg t])
  have hk : |t / 2 * Real.sinc (t / 2) ^ 2| ≤ ε / 2 := by
    rw [abs_mul, abs_pow, abs_div, abs_two]
    have h1 := pow_le_one₀ (n := 2) (abs_nonneg _) (Real.abs_sinc_le_one (t / 2))
    nlinarith [abs_nonneg t, pow_nonneg (abs_nonneg (Real.sinc (t / 2))) 2]
  set c := y₂ - a
  set d := y₃ - b
  have e : Real.sinc t * (a * y₂ + b * y₃) - t / 2 * Real.sinc (t / 2) ^ 2 * (a * y₃ - b * y₂) -
      (a ^ 2 + b ^ 2) = a * c + b * d + (Real.sinc t - 1) * (a * (a + c) + b * (b + d)) -
        t / 2 * Real.sinc (t / 2) ^ 2 * (a * d - b * c) := by
    simp only [c, d]
    ring
  have h₁ : |a * c + b * d| ≤ 2 * M * ε := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [mul_le_mul ha hc (abs_nonneg _) hM, mul_le_mul hb hd (abs_nonneg _) hM]
  have h₂ : |a * (a + c) + b * (b + d)| ≤ 2 * M * (M + 1) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hac : |a + c| ≤ M + 1 := (abs_add_le _ _).trans (by linarith)
    have hbd : |b + d| ≤ M + 1 := (abs_add_le _ _).trans (by linarith)
    nlinarith [mul_le_mul ha hac (abs_nonneg _) hM, mul_le_mul hb hbd (abs_nonneg _) hM]
  have h₃ : |a * d - b * c| ≤ 2 * M * ε := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [mul_le_mul ha hd (abs_nonneg _) hM, mul_le_mul hb hc (abs_nonneg _) hM]
  rw [e]
  refine ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
  rw [abs_mul, abs_mul]
  have i₁ := mul_le_mul hs₁ h₂ (abs_nonneg _) hε0
  have i₂ := mul_le_mul hk h₃ (abs_nonneg _) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hε (mul_nonneg hM hε0)]

/-- **Local uniqueness of the Coulomb gauge.** Let `x` be a continuous field of `A_m^s`, `s > 1`.
There is `ε > 0` with the following property. Let `y` be a continuous field whose connection
coordinates are differentiable and whose section coordinates are within `ε` of those of `x`, and
let `F` be a square-integrable `C²` phase with `|F| ≤ ε`. If the gauge transformation `e^{iF} y`
has the same Coulomb defect at `x` as `y`, `d₀* (e^{iF} y) = d₀* y`, then `F = 0`. For the
Coulomb slice `d₀* (· - x) = 0` of a `C¹` field `x`, see
`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_smul_mem_coulombSlice`. -/
theorem exists_pos_forall_eq_zero_of_gaugeAdjoint_phaseGauge_eq {s : ℝ} (hs : 1 < s)
    (hx : x ∈ framedFieldSpace f m s) (hxc : Continuous x) :
    ∃ ε > 0, ∀ {y : ℂ → EuclideanSpace ℝ (Fin 4)} {F : ℂ → ℝ}, Continuous y →
      (Differentiable ℝ fun w ↦ y w 0) → (Differentiable ℝ fun w ↦ y w 1) →
      (∀ z, |y z 2 - x z 2| ≤ ε ∧ |y z 3 - x z 3| ≤ ε) →
      ContDiff ℝ 2 F → MemLp F 2 volume → (∀ z, |F z| ≤ ε) →
      (∀ z, gaugeAdjoint x (phaseGauge y F) z = gaugeAdjoint x y z) → F = 0 := by
  have hlim := tendsto_normSq_of_mem_framedFieldSpace hs hx hxc
  obtain ⟨C, hC⟩ := exists_forall_sq_add_sq_le hxc hlim
  obtain ⟨R, hV, hV₀, hVa⟩ := exists_memLp_top_sq_add_sq_and_le hxc hlim
  set V : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2
  have hV0 (z : ℂ) : 0 ≤ V z := by positivity
  obtain ⟨ε₀, hε₀, huniq⟩ :=
    exists_pos_forall_ae_eq_zero_of_integral_mul_neg_laplacian_add_mul_eq_zero hV hV₀
      (by norm_num : (0 : ℝ) < 1 / 8) hVa
  -- A bound `M` for the section coordinates of `x`.
  set M := C + 1
  have hC0 : 0 ≤ C := (hV0 0).trans (hC 0)
  have hM (z : ℂ) : |x z 2| ≤ M ∧ |x z 3| ≤ M := by
    have h := hC z
    constructor <;> nlinarith [abs_nonneg (x z 2), sq_abs (x z 2), abs_nonneg (x z 3),
      sq_abs (x z 3), sq_nonneg (|x z 2| - 1 / 2), sq_nonneg (|x z 3| - 1 / 2)]
  set K := 2 * M ^ 2 + 5 * M
  refine ⟨min (1 / 2) (ε₀ / (K + 1)), by positivity,
    fun {y F} hyc hy₀ hy₁ hyx hF hF2 hFε hcoul ↦ ?_⟩
  set ε := min (1 / 2) (ε₀ / (K + 1))
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hεK : ε * K ≤ ε₀ := by
    have h := min_le_right (1 / 2) (ε₀ / (K + 1))
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith [(by positivity : 0 ≤ ε)]
  -- The perturbed potential `Q`, with `Q F = sin F (p y₂ + q y₃) + (cos F - 1) (p y₃ - q y₂)`.
  set Q : ℂ → ℝ := fun z ↦ Real.sinc (F z) * (x z 2 * y z 2 + x z 3 * y z 3) -
    F z / 2 * Real.sinc (F z / 2) ^ 2 * (x z 2 * y z 3 - x z 3 * y z 2) with hQdef
  have hQc : Continuous Q := by have := hF.continuous; fun_prop
  have hΔ (z : ℂ) : Δ F z = Q z * F z := by
    have h := gaugeAdjoint_phaseGauge x (hy₀ z) (hy₁ z) hF.contDiffAt
    rw [hcoul z] at h
    have e₁ := Real.mul_sinc (F z)
    have e₂ := Real.one_sub_cos_eq_sq_div_two_mul_sinc_sq (F z)
    simp only [hQdef]
    linear_combination h - (x z 2 * y z 2 + x z 3 * y z 3) * e₁ -
      (x z 2 * y z 3 - x z 3 * y z 2) * e₂
  -- `Q` is within `ε₀` of the potential `p² + q²` of the gauge Laplacian.
  have hQV (z : ℂ) : |Q z - V z| ≤ ε₀ :=
    (abs_sinc_mul_sub_le (by positivity) (hM z).1 (hM z).2 (hyx z).1 (hyx z).2 (hFε z) hε1).trans
      hεK
  have hQ : MemLp Q ⊤ volume := memLp_top_of_bound hQc.aestronglyMeasurable (C + ε₀)
    (Eventually.of_forall fun z ↦ by
      have h := abs_le.1 (hQV z)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hV0 z, hC z])
  -- `F` is a weak solution of `-ΔF + Q F = 0`.
  have hweak := integral_mul_neg_laplacian_add_mul_eq_zero_of_laplacian_eq_mul hF hΔ
  have hae := huniq hQ (ae_of_all _ hQV) hF2 hweak
  exact (hF.continuous.ae_eq_iff_eq volume continuous_const).1 hae

end TauCeti.Vortex
