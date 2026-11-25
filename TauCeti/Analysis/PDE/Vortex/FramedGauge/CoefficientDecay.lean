/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Family
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import TauCeti.Analysis.PDE.Vortex.Divisor.JointSmooth
import TauCeti.Analysis.PDE.Vortex.FramedGauge.DerivativeDecay
import TauCeti.Analysis.PDE.Vortex.FramedGauge.UniformDerivativeDecay
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.PDE.Vortex.ModulusBound
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.SymmetricPower
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Exponentially decaying dependence of the normalized plane vortices on the divisor

For lower coefficients `a ∈ ℂᵐ` let `P_a` be the monic polynomial with these coefficients, `x_a`
the plane vortex with zero divisor `P_a` (`TauCeti.Vortex.polynomialVortex`) and `g_a` its
end-normalizing polynomial gauge (`TauCeti.Vortex.polynomialGauge`), and write `y_a` for the
winding-`m` end trivialization of `g_a · x_a`. The fields `y_a` tend to the vacuum `(0, 1)` at
the rate `exp (-c |z|)` for every `c < 1 / 2`, uniformly over bounded sets of coefficients
(`exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded`). This
file proves that their dependence on the coefficients decays at the same rates: over a bounded
set `S` of coefficients there are `K` and `R` with

`‖y_b(z) - y_a(z)‖ ≤ K ‖b - a‖ exp (-c |z|)`  for `a, b ∈ S` and `|z| ≥ R`

(`exists_norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_norm_sub_mul_exp_of_isBounded`).
Consequently the first derivatives in the coefficients decay exponentially:
`‖D_a y_a(z)‖ ≤ K exp (-c |z|)` for `a ∈ S` and `|z| ≥ R`
(`TauCeti.Vortex.exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isBounded`), and the same
holds over every compact window of divisors in `Sym ℂ m`, collisions of zeros included, in the
symmetric coordinates
(`TauCeti.Vortex.exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isCompact`).
A uniform bound on the derivative alone would only follow from the joint smoothness of
`(a, z) ↦ y_a(z)` on compact sets of points, not at infinity.

**Two vortices.** The estimate rests on a comparison, proved in
`TauCeti.Analysis.PDE.Vortex.DerivativeDecay` and
`TauCeti.Analysis.PDE.Vortex.FramedGauge.DerivativeDecay`, of two vortices `x` and `y` whose
sections do not vanish outside a disc. There the logarithmic moduli `ℓ = log |α|²` solve the
scalar equation `Δ ℓ = (exp ℓ - 1) / 4`
(`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`), and two solutions of that equation
with `exp ℓ ≥ 4 c²` approach each other like `exp (-c (|z| - R))`, with the constant their largest
difference on the boundary circle
(`TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one`). Since `|α| ≤ 1`, the exponential is
`1`-Lipschitz on the values of `ℓ`, so the difference `u = ℓ_x - ℓ_y` has `|Δ u| ≤ |u| / 4`, and
the interior gradient estimate for Poisson's equation
(`TauCeti.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le`) bounds `D u` by the same
exponential (`TauCeti.Vortex.norm_fderiv_log_normSq_sub_log_normSq_le_mul_exp`). In an end
trivialization a vortex is determined by `ℓ`, as the end field
`(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` plus the vacuum
(`TauCeti.Vortex.gaugeTransform_inv_apply_sub_vacuumField_eq`), so the end trivializations of `x`
and `y` differ by at most `‖D u‖ + |u|`
(`TauCeti.Vortex.norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_exp`). The constants are
explicit; besides the lower bound on the moduli, only the boundary value of `u` enters.

**The normalized family.** For the vortices `g_a · x_a`, the moduli exceed every `2 c < 1` outside
a disc that is uniform over bounded sets of coefficients
(`TauCeti.Vortex.exists_forall_lt_normSq_of_forall_mem_norm_le`, with the zeros bounded by
`TauCeti.Polynomial.norm_lt_of_isRoot_monicOfCoeff`), and on a circle `|z| = R` of that
exterior, `(a, z) ↦ log |α_a(z)|²` is smooth near the compact set of pairs with `a` in a closed
ball (`TauCeti.Vortex.contDiff_normalizedVortex_uncurry`), hence Lipschitz
there. So the boundary value of `u = ℓ_b - ℓ_a` is at most `L ‖b - a‖`, and the comparison
above gives the Lipschitz bound with the decaying constant.

Higher derivatives in the coefficients, and mixed derivatives in the coefficients and the point,
are not treated here.

## Main results

* `exists_norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_norm_sub_mul_exp_of_isBounded`:
  the Lipschitz bound `‖y_b(z) - y_a(z)‖ ≤ K ‖b - a‖ exp (-c |z|)` for the normalized family.
* `TauCeti.Vortex.exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isBounded`,
  `TauCeti.Vortex.exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isCompact`: the first
  derivatives in the coefficients decay like `exp (-c |z|)`, uniformly over bounded sets of
  coefficients and over compact windows of divisors.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Complex Filter Metric Set Topology InnerProductSpace Laplacian
open TauCeti.Polynomial
open scoped ContDiff

namespace TauCeti.Vortex

/-! ### The normalized vortices of a bounded set of coefficients -/

section Family

variable {m : ℕ}

/-- On a circle on which the moduli of the normalized vortices do not vanish, their logarithmic
moduli are Lipschitz in the coefficients, uniformly over a closed ball of coefficients. -/
private theorem exists_abs_log_normSq_sub_le_mul_norm_sub (r : ℝ) {R : ℝ}
    (hpos : ∀ a ∈ closedBall (0 : Fin m → ℂ) r, ∀ z : ℂ, ‖z‖ = R →
      0 < 4 * (normalizedVortex a z 2 ^ 2 + normalizedVortex a z 3 ^ 2)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a ∈ closedBall (0 : Fin m → ℂ) r, ∀ b ∈ closedBall (0 : Fin m → ℂ) r,
      ∀ z : ℂ, ‖z‖ = R →
        |Real.log (4 * (normalizedVortex b z 2 ^ 2 + normalizedVortex b z 3 ^ 2)) -
          Real.log (4 * (normalizedVortex a z 2 ^ 2 + normalizedVortex a z 3 ^ 2))| ≤
          L * ‖b - a‖ := by
  set F : (Fin m → ℂ) × ℂ → ℝ := fun p ↦ Real.log (4 *
    (normalizedVortex p.1 p.2 2 ^ 2 + normalizedVortex p.1 p.2 3 ^ 2))
  have hX := contDiff_normalizedVortex_uncurry (m := m)
  have h₂ := (contDiff_piLp 2).1 hX 2
  have h₃ := (contDiff_piLp 2).1 hX 3
  -- `F` is smooth, so locally Lipschitz, near the compact set of pairs `(a, z)` with `a` in the
  -- ball and `z` on the circle, where the modulus does not vanish.
  have hloc : LocallyLipschitzOn (closedBall (0 : Fin m → ℂ) r ×ˢ sphere (0 : ℂ) R) F := by
    intro p hp
    obtain ⟨K, t, ht, hlip⟩ := ContDiffAt.exists_lipschitzOnWith (𝕂 := ℝ) (f := F)
      (((contDiff_const.mul ((h₂.pow 2).add (h₃.pow 2))).contDiffAt.log
        (hpos p.1 hp.1 p.2 (by simpa using hp.2)).ne').of_le (by simp))
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact
    ((isCompact_closedBall _ _).prod (isCompact_sphere _ _))
  refine ⟨L, L.coe_nonneg, fun a ha b hb z hz ↦ ?_⟩
  have h := hL.dist_le_mul (b, z) ⟨hb, by simpa using hz⟩ (a, z) ⟨ha, by simpa using hz⟩
  rwa [Real.dist_eq, Prod.dist_eq, dist_self, dist_eq_norm, max_eq_left (norm_nonneg _)] at h

/-- **Lipschitz dependence of the normalized vortices on the coefficients, with exponentially
decaying constant.** For lower coefficients `a ∈ ℂᵐ` let `y_a` be the winding-`m` end
trivialization of the plane vortex with zero divisor the monic polynomial `P_a`, normalized at its
end by the polynomial gauge `g_a`. For every bounded set `S` of coefficients and rate `c < 1 / 2`
there are constants `K ≥ 0` and `R` such that

`‖y_b(z) - y_a(z)‖ ≤ K ‖b - a‖ exp (-c |z|)`  for `a, b ∈ S` and `|z| ≥ R`. -/
theorem exists_norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_norm_sub_mul_exp_of_isBounded
    {S : Set (Fin m → ℂ)} (hS : Bornology.IsBounded S) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ a ∈ S, ∀ b ∈ S, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖gaugeTransform (windingPhase m)⁻¹
          (gaugeTransform (polynomialGauge b) (polynomialVortex (monicOfCoeff b))) z -
        gaugeTransform (windingPhase m)⁻¹
          (gaugeTransform (polynomialGauge a) (polynomialVortex (monicOfCoeff a))) z‖ ≤
        K * ‖b - a‖ * Real.exp (-(c * ‖z‖)) := by
  -- For `m = 0` there is only one coefficient vector.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, 0, le_rfl, fun a _ b _ z _ ↦ by simp [Subsingleton.elim b a]⟩
  obtain ⟨r, hr⟩ := hS.exists_norm_le
  have hSr : S ⊆ closedBall 0 r := fun a ha ↦ mem_closedBall_zero_iff.2 (hr a ha)
  -- A rate `c' ∈ [c, 1 / 2)` that is positive.
  set c' := max c (1 / 4)
  have hc'₀ : 0 ≤ c' := le_max_of_le_right (by norm_num)
  have hc' : c' < 1 / 2 := max_lt hc (by norm_num)
  -- Outside the disc of radius `R₀` every modulus `|α|²` exceeds `4 c'²`, since the roots of the
  -- monic polynomials have norm less than `r + 1`.
  obtain ⟨R, hR⟩ := exists_forall_lt_normSq_of_forall_mem_norm_le m (r + 1) (θ := 4 * c' ^ 2)
    (by nlinarith)
  obtain ⟨R₀, hRR₀, hR₀⟩ : ∃ R₀, R + 1 ≤ R₀ ∧ 0 < R₀ :=
    ⟨max (R + 1) 1, le_max_left _ _, lt_max_of_lt_right one_pos⟩
  have hgt (a : Fin m → ℂ) (ha : a ∈ closedBall 0 r) (z : ℂ) (hz : R₀ ≤ ‖z‖) :
      4 * c' ^ 2 < 4 * (normalizedVortex a z 2 ^ 2 + normalizedVortex a z 3 ^ 2) := by
    obtain ⟨hx, hsol, hframe, hD⟩ := gaugeTransform_polynomialGauge_polynomialVortex_spec hm a
    rw [← normalizedVortex_def] at hx hsol hframe hD
    refine hR _ _ hx hsol hframe hD (fun b hb ↦ ?_) z (by linarith)
    have := norm_lt_of_isRoot_monicOfCoeff a (_root_.Polynomial.isRoot_of_mem_roots hb)
    linarith [mem_closedBall_zero_iff.1 ha]
  -- On the circle `|z| = R₀` the logarithmic moduli are `L`-Lipschitz in the coefficients.
  obtain ⟨L, hL, hlip⟩ := exists_abs_log_normSq_sub_le_mul_norm_sub r (R := R₀)
    fun a ha z hz ↦ (by positivity : (0 : ℝ) ≤ 4 * c' ^ 2).trans_lt (hgt a ha z hz.ge)
  -- Outside the disc of radius `R'` the sections are `|α|` times the winding phase.
  obtain ⟨R', hR'⟩ := exists_eventually_sectionValue_eq_norm_mul_windingPhase hS
  refine ⟨94 * L * Real.exp (c' * (R₀ + 3)), max (R₀ + 3) (R' + 1), by positivity,
    fun a ha b hb z hz ↦ ?_⟩
  have hphase (d : Fin m → ℂ) (hd : d ∈ S) := hR' d hd z (by linarith [le_of_max_le_right hz])
  obtain ⟨hxb, hsb, hfb, -⟩ := gaugeTransform_polynomialGauge_polynomialVortex_spec hm b
  obtain ⟨hxa, hsa, hfa, -⟩ := gaugeTransform_polynomialGauge_polynomialVortex_spec hm a
  simp only [← normalizedVortex_def] at hxb hsb hfb hxa hsa hfa hphase ⊢
  have h := norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_exp
    (((contDiff_piLp 2).1 hxb 2).of_le (by simp)) (((contDiff_piLp 2).1 hxb 3).of_le (by simp))
    (((contDiff_piLp 2).1 hxa 2).of_le (by simp)) (((contDiff_piLp 2).1 hxa 3).of_le (by simp))
    hsb hsa
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hfb)
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hfa) hR₀ hc'₀ (hgt b (hSr hb))
    (hgt a (hSr ha)) (M := L * ‖b - a‖) (fun w hw ↦ hlip a (hSr ha) b (hSr hb) w hw)
    (le_of_max_le_left hz) (hphase b hb) (hphase a ha)
  refine h.trans ?_
  have hexp : Real.exp (-(c' * ‖z‖)) ≤ Real.exp (-(c * ‖z‖)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left c (1 / 4))
      (norm_nonneg z)))
  rw [exp_neg_mul_sub]
  calc 94 * (L * ‖b - a‖) * (Real.exp (c' * (R₀ + 3)) * Real.exp (-(c' * ‖z‖))) ≤
        94 * (L * ‖b - a‖) * (Real.exp (c' * (R₀ + 3)) * Real.exp (-(c * ‖z‖))) := by gcongr
    _ = 94 * L * Real.exp (c' * (R₀ + 3)) * ‖b - a‖ * Real.exp (-(c * ‖z‖)) := by ring

/-- **The first derivatives of the normalized vortices in the coefficients decay
exponentially.** For lower coefficients `a ∈ ℂᵐ` let `y_a` be the winding-`m` end trivialization
of the plane vortex with zero divisor the monic polynomial `P_a`, normalized at its end by the
polynomial gauge `g_a`. For every bounded set `S` of coefficients and rate `c < 1 / 2` there are
constants `K ≥ 0` and `R` such that the derivative of `a ↦ y_a(z)`
satisfies `‖D_a y_a(z)‖ ≤ K exp (-c |z|)` for every `a ∈ S` and `|z| ≥ R`. -/
theorem exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isBounded {S : Set (Fin m → ℂ)}
    (hS : Bornology.IsBounded S) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ a ∈ S, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖fderiv ℝ (fun b ↦ gaugeTransform (windingPhase m)⁻¹
          (gaugeTransform (polynomialGauge b) (polynomialVortex (monicOfCoeff b))) z) a‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨r, hr⟩ := hS.exists_norm_le
  obtain ⟨K, R, hK, h⟩ :=
    exists_norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_norm_sub_mul_exp_of_isBounded
      (isBounded_ball (x := (0 : Fin m → ℂ)) (r := r + 1)) hc
  refine ⟨K, R, hK, fun a ha z hz ↦ ?_⟩
  have ha' : a ∈ ball (0 : Fin m → ℂ) (r + 1) := mem_ball_zero_iff.2 (by linarith [hr a ha])
  -- On the open ball the map `b ↦ y_b(z)` is Lipschitz with constant `K exp (-c |z|)`.
  have hlip : LipschitzOnWith (Real.toNNReal (K * Real.exp (-(c * ‖z‖))))
      (fun b : Fin m → ℂ ↦ gaugeTransform (windingPhase m)⁻¹
        (gaugeTransform (polynomialGauge b) (polynomialVortex (monicOfCoeff b))) z)
      (ball (0 : Fin m → ℂ) (r + 1)) := by
    refine LipschitzOnWith.of_dist_le_mul fun b hb b' hb' ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    calc _ ≤ K * ‖b - b'‖ * Real.exp (-(c * ‖z‖)) := h b' hb' b hb z hz
      _ = K * Real.exp (-(c * ‖z‖)) * ‖b - b'‖ := by ring
  have := norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds ha') hlip
  rwa [Real.coe_toNNReal _ (by positivity)] at this

/-- **The first derivatives of the normalized vortices in the symmetric coordinates decay
exponentially over a compact window of divisors.** For lower coefficients `a ∈ ℂᵐ` let `y_a` be
the winding-`m` end trivialization of the plane vortex with zero divisor the monic polynomial `P_a`,
normalized at its end by the polynomial gauge `g_a`. For every compact set `S` of divisors in
`Sym ℂ m`, collisions of zeros included, and rate `c < 1 / 2` there are
constants `K ≥ 0` and `R` such that `‖D_a y_a(z)‖ ≤ K exp (-c |z|)` at the symmetric coordinates
`a` of every `D ∈ S`, for `|z| ≥ R`. -/
theorem exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isCompact {S : Set (Sym ℂ m)}
    (hS : IsCompact S) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ D ∈ S, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖fderiv ℝ (fun b ↦ gaugeTransform (windingPhase m)⁻¹
          (gaugeTransform (polynomialGauge b) (polynomialVortex (monicOfCoeff b))) z)
        (Sym.coeffEquiv ℂ m D)‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hS' : IsCompact (Sym.coeffEquiv ℂ m '' S) := by
    simpa only [Sym.coeffHomeomorph_apply] using hS.image (Sym.coeffHomeomorph ℂ m).continuous
  obtain ⟨K, R, hK, h⟩ :=
    exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isBounded hS'.isBounded hc
  exact ⟨K, R, hK, fun D hD z hz ↦ h _ ⟨D, hD, rfl⟩ z hz⟩

end Family

end TauCeti.Vortex
