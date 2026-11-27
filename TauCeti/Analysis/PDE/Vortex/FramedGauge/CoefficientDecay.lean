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
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.InnerProductSpace.Laplacian.DerivativeDecay
import TauCeti.Analysis.Normed.Group.Prod
import TauCeti.Analysis.PDE.Vortex.ScalarEquation
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
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

**Derivatives of every order.** For `m ≥ 1`, all joint derivatives of `(a, z) ↦ y_a(z) - (0, 1)`
in the coefficients and the point decay at the same rates, uniformly over bounded sets of
coefficients and over compact windows of divisors, collisions of zeros included
(`exists_norm_iteratedFDeriv_uncurry_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded`,
`exists_norm_iteratedFDeriv_uncurry_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isCompact`).
Outside a disc, `y_a(z) - (0, 1)` is the end field
`(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` of the logarithmic modulus
`ℓ(a, z) = log |α_a(z)|²`, a family of solutions of `Δ_z ℓ = (exp ℓ - 1) / 4` that decays like
`exp (-c |z|)` uniformly over bounded sets of coefficients
(`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub`). The joint derivatives
of such a family decay at the same rate
(`TauCeti.exists_forall_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_exp_sub_one`), and those of
the end field follow, its section part by the Faà di Bruno bound
(`ContDiffAt.norm_iteratedFDeriv_exp_sub_one_le`) since `ℓ ≤ 0`.

## Main results

* `exists_norm_gaugeTransform_inv_sub_gaugeTransform_inv_le_mul_norm_sub_mul_exp_of_isBounded`:
  the Lipschitz bound `‖y_b(z) - y_a(z)‖ ≤ K ‖b - a‖ exp (-c |z|)` for the normalized family.
* `TauCeti.Vortex.exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isBounded`,
  `TauCeti.Vortex.exists_norm_fderiv_gaugeTransform_inv_le_mul_exp_of_isCompact`: the first
  derivatives in the coefficients decay like `exp (-c |z|)`, uniformly over bounded sets of
  coefficients and over compact windows of divisors.
* `exists_norm_iteratedFDeriv_uncurry_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded`,
  `exists_norm_iteratedFDeriv_uncurry_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isCompact`:
  for `m ≥ 1`, the joint derivatives of every order in the coefficients and the point decay like
  `exp (-c |z|)`, uniformly over bounded sets of coefficients and over compact windows of
  divisors.

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

/-! ### Derivatives of every order in the coefficients and the point -/

section Joint

variable {m : ℕ}

/-- The squared modulus `|α_a(z)|²` of the normalized vortices, jointly in the coefficients and
the point. -/
private noncomputable def normSqFamily (q : (Fin m → ℂ) × ℂ) : ℝ :=
  4 * (normalizedVortex q.1 q.2 2 ^ 2 + normalizedVortex q.1 q.2 3 ^ 2)

/-- **The logarithmic moduli of the normalized vortices.** For `m ≥ 1`, coefficients of norm less
than `r + 1` and a rate `0 < c < 1 / 2`, outside a disc the family `ℓ(a, z) = log |α_a(z)|²`
is smooth, solves `Δ_z ℓ = (exp ℓ - 1) / 4` and is at most `K exp (-c |z|)`, with `|α|² > 1 / 2`
there. -/
private theorem exists_log_normSqFamily_spec (hm : 0 < m) (r : ℝ) {c : ℝ} (hc₀ : 0 < c)
    (hc : c < 1 / 2) :
    ∃ R₀ K, ∀ q : (Fin m → ℂ) × ℂ, ‖q.1‖ < r + 1 → R₀ < ‖q.2‖ → 1 / 2 < normSqFamily q ∧
      ContDiffAt ℝ ∞ (fun q ↦ Real.log (normSqFamily q)) q ∧
      Δ (fun y ↦ Real.log (normSqFamily (q.1, y))) q.2 =
        1 / 4 * (Real.exp (Real.log (normSqFamily q)) - 1) ∧
      |Real.log (normSqFamily q)| ≤ K * Real.exp (-(c * ‖q.2‖)) := by
  have hX := contDiff_normalizedVortex_uncurry (m := m)
  have hs : ContDiff ℝ ∞ (normSqFamily (m := m)) :=
    contDiff_const.mul ((((contDiff_piLp 2).1 hX 2).pow 2).add (((contDiff_piLp 2).1 hX 3).pow 2))
  have hspec (a : Fin m → ℂ) := gaugeTransform_polynomialGauge_polynomialVortex_spec hm a
  simp only [← normalizedVortex_def] at hspec
  -- The zeros of the vortices with coefficients of norm less than `r + 1` have norm at most
  -- `r + 2`, so outside a disc their moduli exceed `1 / 2`.
  have hroots : ∀ a : Fin m → ℂ, ‖a‖ < r + 1 → ∀ b ∈ (monicOfCoeff a).roots, ‖b‖ ≤ r + 2 :=
    fun a ha b hb ↦ by
      have := norm_lt_of_isRoot_monicOfCoeff a (_root_.Polynomial.isRoot_of_mem_roots hb)
      linarith
  obtain ⟨R₀, hR₀⟩ := exists_forall_lt_normSq_of_forall_mem_norm_le m (r + 2) (θ := 1 / 2)
    (by norm_num)
  obtain ⟨K₁, -, hK₁⟩ := exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀.le hc
  refine ⟨R₀, 2 * K₁ * Real.exp (c * (r + 2)), fun q h₁ h₂ ↦ ?_⟩
  obtain ⟨hx, hsol, hframe, hD⟩ := hspec q.1
  have hpos : 1 / 2 < normSqFamily q := hR₀ _ _ hx hsol hframe hD (hroots q.1 h₁) q.2 h₂
  refine ⟨hpos, hs.contDiffAt.log (by linarith), ?_, ?_⟩
  · -- The scalar equation of the vortex.
    simp only [normSqFamily]
    rw [laplacian_log_normSq_eq_exp (((contDiff_piLp 2).1 hx 2).contDiffAt.of_le (by simp))
      (((contDiff_piLp 2).1 hx 3).contDiffAt.of_le (by simp))
      ((by norm_num : (0 : ℝ) < 1 / 2).trans hpos) (Eventually.of_forall hsol)]
    ring
  · -- `|log |α|²| ≤ 2 (1 - |α|²)`, and `1 - |α|²` decays at distance from the zeros.
    have h₃ := hK₁ _ _ hx hsol hframe hD q.2 (‖q.2‖ - (r + 2)) fun b hb ↦ by
      linarith [norm_sub_norm_le q.2 b, hroots q.1 h₁ b hb]
    have h₁' := normSq_le_one_of_tendsto_sectionValue_mul_inv_pow (hx.of_le (by simp)) hsol
      hframe q.2
    calc |Real.log (normSqFamily q)| ≤ 2 * (1 - normSqFamily q) :=
          Real.abs_log_le_two_mul_one_sub hpos.le h₁'
      _ ≤ 2 * (K₁ * Real.exp (-(c * (‖q.2‖ - (r + 2))))) := by
          simp only [normSqFamily]
          gcongr
      _ = 2 * K₁ * Real.exp (c * (r + 2)) * Real.exp (-(c * ‖q.2‖)) := by
        rw [exp_neg_mul_sub]
        ring

/-- **The end field of the logarithmic moduli.** Outside a disc, for coefficients of norm less
than `r + 1`, the end trivialization of the normalized vortices minus the vacuum is
`L₁ (Dℓ) + L₂ (exp (ℓ / 2) - 1)` for the joint derivative `Dℓ` of `ℓ = log |α|²`. -/
private theorem exists_gaugeTransform_inv_sub_vacuumField_eq_add (hm : 0 < m) (r : ℝ)
    {L₁ : ((Fin m → ℂ) × ℂ →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)}
    {L₂ : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4)}
    (hL : ∀ (φ : (Fin m → ℂ) × ℂ →L[ℝ] ℝ) (t : ℝ),
      !₂[-(φ (0, I) / 2), φ (0, 1) / 2, t / 2, 0] = L₁ φ + L₂ t) :
    ∃ R₁, ∀ q : (Fin m → ℂ) × ℂ, ‖q.1‖ < r + 1 → R₁ < ‖q.2‖ →
      gaugeTransform (windingPhase m)⁻¹ (normalizedVortex q.1) q.2 - vacuumField q.2 =
        L₁ (fderiv ℝ (fun q ↦ Real.log (normSqFamily q)) q) +
          L₂ (Real.exp (Real.log (normSqFamily q) / 2) - 1) := by
  obtain ⟨R₀, _, hR₀⟩ := exists_log_normSqFamily_spec hm r (c := 1 / 4) (by norm_num)
    (by norm_num)
  -- Outside a disc the sections have the winding phase.
  obtain ⟨R', hR'⟩ := exists_eventually_sectionValue_eq_norm_mul_windingPhase
    (isBounded_ball (x := (0 : Fin m → ℂ)) (r := r + 1))
  simp only [← normalizedVortex_def] at hR'
  refine ⟨max R₀ R', fun q h₁ h₂ ↦ ?_⟩
  obtain ⟨hpos, hsmooth, -, -⟩ := hR₀ q h₁ ((le_max_left _ _).trans_lt h₂)
  obtain ⟨hx, hsol, -, -⟩ := gaugeTransform_polynomialGauge_polynomialVortex_spec hm q.1
  rw [← normalizedVortex_def] at hx hsol
  -- The derivative in `z` is the joint derivative along `(0, v)`.
  have hpart : ∀ v : ℂ, fderiv ℝ (fun y ↦ Real.log (normSqFamily (q.1, y))) q.2 v =
      fderiv ℝ (fun q ↦ Real.log (normSqFamily q)) q (0, v) := by
    have hq : DifferentiableAt ℝ (fun q ↦ Real.log (normSqFamily q)) (q.1, q.2) := by
      rw [Prod.mk.eta]
      exact hsmooth.differentiableAt (by simp)
    intro v
    simp [fderiv_slice_right hq]
  have h := gaugeTransform_inv_apply_sub_vacuumField_eq (u := windingPhase m)
    (ℓ := fun y ↦ Real.log (normSqFamily (q.1, y)))
    (((contDiff_piLp 2).1 hx 2).differentiable (by simp) q.2)
    (((contDiff_piLp 2).1 hx 3).differentiable (by simp) q.2)
    (right_ne_zero_of_mul (by linarith : normSqFamily q ≠ 0))
    (by simp [hsol q.2]) (by simp [hsol q.2])
    (hR' q.1 (mem_ball_zero_iff.2 h₁) q.2 ((le_max_right _ _).trans_lt h₂)) EventuallyEq.rfl
  rw [h, hpart, hpart, ← hL]

/-- **The derivatives of every order of the normalized vortices in the coefficients and the
point decay exponentially.** Let `m ≥ 1`, and for lower coefficients `a ∈ ℂᵐ` let `y_a` be the
winding-`m` end trivialization of the plane vortex with zero divisor the monic polynomial `P_a`,
normalized at its end by the polynomial gauge `g_a`. For every bounded set `S` of coefficients,
order `n` and rate `c < 1 / 2` there are constants `K` and `R` such that the `n`-th joint
derivative of `(a, z) ↦ y_a(z) - (0, 1)` in the coefficients and the point satisfies
`‖Dⁿ (y_a(z) - (0, 1))‖ ≤ K exp (-c |z|)` for every `a ∈ S` and `|z| ≥ R`. -/
theorem
    exists_norm_iteratedFDeriv_uncurry_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded
    (hm : 0 < m) {S : Set (Fin m → ℂ)} (hS : Bornology.IsBounded S) (n : ℕ) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K R, ∀ a ∈ S, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ n (fun q : (Fin m → ℂ) × ℂ ↦ gaugeTransform (windingPhase m)⁻¹
          (gaugeTransform (polynomialGauge q.1) (polynomialVortex (monicOfCoeff q.1))) q.2 -
        vacuumField q.2) (a, z)‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨r, hr⟩ := hS.exists_norm_le
  set r₀ := max r 0
  -- A positive rate `c' ≥ c` below `1 / 2`.
  set c' := max c (1 / 4)
  have hc'₀ : 0 < c' := lt_max_of_lt_right (by norm_num)
  have hc' : c' < 1 / 2 := max_lt hc (by norm_num)
  -- All joint derivatives of `ℓ = log |α|²` of order at most `n + 1` decay like
  -- `exp (-c' |z|)`.
  obtain ⟨R₀, K₀, hspec⟩ := exists_log_normSqFamily_spec hm r₀ hc'₀ hc'
  obtain ⟨C, R, hCR⟩ := exists_forall_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_exp_sub_one
    (κ := 1 / 4) (r := r₀) (r₁ := r₀ + 1) hc'₀ (by nlinarith) (by linarith)
    (fun q h₁ h₂ ↦ (hspec q h₁ h₂).2.1) (fun q h₁ h₂ ↦ (hspec q h₁ h₂).2.2.1)
    (fun q h₁ h₂ ↦ (hspec q h₁ h₂).2.2.2) (n + 1)
  -- Outside a disc, the field is the end field of `ℓ`.
  obtain ⟨L₁, L₂, hL⟩ := exists_endField_eq_add ((0 : Fin m → ℂ), I) ((0 : Fin m → ℂ), (1 : ℂ))
  obtain ⟨R₁, hend⟩ := exists_gaugeTransform_inv_sub_vacuumField_eq_add hm r₀ hL
  refine ⟨‖L₁‖ * C + ‖L₂‖ * ((Nat.factorial n : ℝ) * max 1 C ^ (n + 1)),
    max (max R (R₀ + 1)) (R₁ + 1), fun a ha z hz ↦ ?_⟩
  have ha₁ : ‖a‖ < r₀ + 1 := by linarith [hr a ha, le_max_left r 0]
  have hzR : R ≤ ‖z‖ := (le_max_left _ _).trans ((le_max_left _ _).trans hz)
  have hzR₀ : R₀ < ‖z‖ := by
    linarith [le_max_right R (R₀ + 1), le_max_left (max R (R₀ + 1)) (R₁ + 1)]
  have hzR₁ : R₁ < ‖z‖ := by linarith [le_max_right (max R (R₀ + 1)) (R₁ + 1)]
  have hε₁ : Real.exp (-(c' * ‖z‖)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg z])
  have hD := hCR (a, z) ((hr a ha).trans (le_max_left _ _)) hzR
  have hC₀ : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((norm_nonneg _).trans (hD 0 (Nat.zero_le _)))
  -- Near `(a, z)` the field is the end field of `ℓ`.
  have hloc : (fun q : (Fin m → ℂ) × ℂ ↦ gaugeTransform (windingPhase m)⁻¹
      (gaugeTransform (polynomialGauge q.1) (polynomialVortex (monicOfCoeff q.1))) q.2 -
        vacuumField q.2) =ᶠ[𝓝 (a, z)] fun q ↦ L₁ (fderiv ℝ (fun q ↦ Real.log (normSqFamily q)) q) +
          L₂ (Real.exp (Real.log (normSqFamily q) / 2) - 1) := by
    filter_upwards [(isOpen_setOf_norm_fst_lt_and_lt_norm_snd (r₀ + 1) R₁).mem_nhds ⟨ha₁, hzR₁⟩]
      with q hq
    rw [← normalizedVortex_def]
    exact hend q hq.1 hq.2
  have hℓ₀ : Real.log (normSqFamily (a, z)) ≤ 0 := by
    obtain ⟨hx, hsol, hframe, -⟩ := gaugeTransform_polynomialGauge_polynomialVortex_spec hm a
    rw [← normalizedVortex_def] at hx hsol hframe
    exact log_normSq_nonpos (((contDiff_piLp 2).1 hx 2).of_le (by simp))
      (((contDiff_piLp 2).1 hx 3).of_le (by simp)) hsol
      (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) z
  rw [(hloc.iteratedFDeriv ℝ n).eq_of_nhds]
  refine (norm_iteratedFDeriv_endField_le L₁ L₂ (hspec (a, z) ha₁ hzR₀).2.1 hℓ₀
    (Real.exp_pos _).le hε₁ hD).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left c (1 / 4))
    (norm_nonneg z)))

/-- **The derivatives of every order of the normalized vortices in the symmetric coordinates and
the point decay exponentially over a compact window of divisors.** Let `m ≥ 1`, and for lower
coefficients `a ∈ ℂᵐ` let `y_a` be the winding-`m` end trivialization of the plane vortex with zero
divisor the monic polynomial `P_a`, normalized at its end by the polynomial gauge `g_a`. For every
compact set `S` of divisors in `Sym ℂ m`, collisions of zeros included, order `n` and rate
`c < 1 / 2` there are constants `K` and `R` such that the `n`-th joint derivative of
`(a, z) ↦ y_a(z) - (0, 1)` at the symmetric coordinates `a` of every `D ∈ S` and every `|z| ≥ R`
is at most `K exp (-c |z|)`. -/
theorem
    exists_norm_iteratedFDeriv_uncurry_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isCompact
    (hm : 0 < m) {S : Set (Sym ℂ m)} (hS : IsCompact S) (n : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K R, ∀ D ∈ S, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ n (fun q : (Fin m → ℂ) × ℂ ↦ gaugeTransform (windingPhase m)⁻¹
          (gaugeTransform (polynomialGauge q.1) (polynomialVortex (monicOfCoeff q.1))) q.2 -
        vacuumField q.2) (Sym.coeffEquiv ℂ m D, z)‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hS' : IsCompact (Sym.coeffEquiv ℂ m '' S) := by
    simpa only [Sym.coeffHomeomorph_apply] using hS.image (Sym.coeffHomeomorph ℂ m).continuous
  obtain ⟨K, R, h⟩ :=
    exists_norm_iteratedFDeriv_uncurry_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded
      hm hS'.isBounded n hc
  exact ⟨K, R, fun D hD z hz ↦ h _ ⟨D, hD, rfl⟩ z hz⟩

end Joint

end TauCeti.Vortex
