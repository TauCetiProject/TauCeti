/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub

/-!
# Sobolev representatives of smooth framed vortices

The framed degree-`m` plane vortex fields of the Sobolev model form the affine space
`A_m^s = x_ref + (L² ∩ H^s)(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`; this is
`x_ref + H^s` for `s ≥ 0`), centered at a smooth reference pair equal to `(-i m dθ, (z / |z|)^m)`
outside a disc. A smooth vortex with the degree-`m` end framing `α (z / |z|)^(-m) → 1` need not
lie in `A_m^s`: its phase may approach the winding phase only like `1 / |z|`, which is not square
integrable. This file shows that every such vortex is carried into `A_m^s`, for every order `s`
at once, by a smooth framed gauge transformation
(`TauCeti.Vortex.exists_framedGaugeGroup_forall_smul_mem_framedFieldSpace`). Since two fields
of `A_m^k`, `k ≥ 2`, related by a smooth framed gauge are related by an element of the Sobolev
gauge group `G_(k+1)` (`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`), the smooth
framed gauge orbits of smooth framed vortices are thereby compared with the
`G_(k+1)`-orbits of vortices in `A_m^k`.

The gauge is the one making the section `|α|` times the winding phase outside a compact set
(`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`). For such an end-normalized
vortex, the end trivialization by the inverse winding phase has the positive real section `|α|`,
and the holomorphicity rows of the vortex equation then determine its connection from
`ℓ = log |α|²` (`TauCeti.Vortex.sub_referenceField_apply_eq`). Outside a large disc,

`x - x_ref = (-∂_t ℓ / 2, ∂_s ℓ / 2, x_ref,₂ (exp (ℓ / 2) - 1), x_ref,₃ (exp (ℓ / 2) - 1))`

in the coordinates `x = (b₁, b₂, p, q)` with `a = i (b₁ ds + b₂ dt)`, `α = 2 (p + i q)`. A cutoff
`v` of `ℓ` vanishing near the zeros of `α` solves `Δv = (exp v - 1) / 4 + g` with `g` smooth and
compactly supported, by the scalar equation `Δ log |α|² = (|α|² - 1) / 4`
(`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`). It is bounded and square integrable,
since `|v| ≤ 2 (1 - |α|²)` and the modulus defect is square integrable
(`TauCeti.Vortex.memLp_one_sub_normSq`). Elliptic regularity for this semilinear equation
(`TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian_eq_mul_exp_sub_one_add`)
puts `v` in every `H^s`, and then each coordinate of `x - x_ref` lies in `H^s`: the connection
part as a derivative of `v`, and the section part because `H^s(ℂ)` is closed under
`w ↦ exp (w / 2) - 1` for `s > 1` and under multiplication by the reference coefficients, which
have bounded derivatives.

## Main results

* `TauCeti.Vortex.mem_framedFieldSpace_of_eventually_sectionValue_eq`: a smooth vortex with
  `|α| → 1` whose section is `|α|` times the winding phase outside a compact set lies in `A_m^s`
  for every `s`.
* `TauCeti.Vortex.exists_framedGaugeGroup_forall_smul_mem_framedFieldSpace`: every smooth framed
  degree-`m` vortex has a smooth framed gauge transform, normalized at its end, lying in `A_m^s`
  for every `s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory TemperedDistribution
open scoped Topology ContDiff Laplacian

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-- **A cutoff of `log |α|²`.** Let `x` be a smooth plane vortex with `|α| → 1` at infinity, and
let `R ≥ 0` be such that `|α|² > 1 / 2` outside the disc of radius `R`. Then some smooth function
`v` with `|v| ≤ 2 (1 - |α|²)` agrees with `ℓ = log |α|²` near every point outside the disc of
radius `R + 2`. -/
private theorem exists_abs_le_two_mul_one_sub_normSq_eventuallyEq_log_normSq
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ z : ℂ, R < ‖z‖ → 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧ (∀ z, |v z| ≤ 2 * (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2))) ∧
      ∀ z : ℂ, R + 2 < ‖z‖ → v =ᶠ[𝓝 z] fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  set n : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  set ℓ : ℂ → ℝ := fun z ↦ Real.log (n z)
  have hn : ContDiff ℝ ∞ n := contDiff_const.mul (((hxi 2).pow 2).add ((hxi 3).pow 2))
  have hn1 (z : ℂ) : n z ≤ 1 :=
    normSq_le_one_of_tendsto ((hxi 2).of_le (by norm_cast)) ((hxi 3).of_le (by norm_cast)) hsol
      hlim z
  have hn0 (z : ℂ) : 0 ≤ n z := by positivity
  -- The cutoff `v = (1 - b) ℓ` of `ℓ = log |α|²`, vanishing on the disc of radius `R + 1`.
  let b : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  set v : ℂ → ℝ := fun z ↦ (1 - b z) * ℓ z
  have hvnear (z : ℂ) (hz : ‖z‖ < R + 1) : v =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
    simp [v, b.one_of_mem_closedBall (ball_subset_closedBall hw)]
  have hvfar (z : ℂ) (hz : R + 2 < ‖z‖) : v =ᶠ[𝓝 z] ℓ := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    have hb : b w = 0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact le_of_lt hw)
    simp [v, hb]
  have hℓ (z : ℂ) (hz : R < ‖z‖) : ContDiffAt ℝ ∞ ℓ z :=
    hn.contDiffAt.log (by linarith [(hR z hz)])
  have hv : ContDiff ℝ ∞ v := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : ‖z‖ < R + 1
    · exact contDiffAt_const.congr_of_eventuallyEq (hvnear z hz)
    · exact ((contDiff_const.sub b.contDiff).contDiffAt).mul (hℓ z (by linarith))
  -- `|v| ≤ 2 (1 - |α|²)`.
  have hvbound (z : ℂ) : |v z| ≤ 2 * (1 - n z) := by
    by_cases hz : ‖z‖ < R + 1
    · rw [(hvnear z hz).self_of_nhds, abs_zero]
      linarith [hn1 z]
    · have hnz := (hR z (by linarith))
      have hlog : |ℓ z| ≤ 2 * (1 - n z) := by
        have h := Real.neg_log_one_sub_le_two_mul (x := 1 - n z) (by linarith [hn1 z])
          (by linarith)
        rw [sub_sub_cancel] at h
        rwa [abs_of_nonpos (Real.log_nonpos (hn0 z) (hn1 z))]
      have hb0 := b.nonneg (x := z)
      have hb1 := b.le_one (x := z)
      calc |v z| = |1 - b z| * |ℓ z| := abs_mul _ _
        _ ≤ 1 * (2 * (1 - n z)) := by
          gcongr
          rw [abs_le]
          constructor <;> linarith
        _ = 2 * (1 - n z) := one_mul _
  exact ⟨v, hv, hvbound, hvfar⟩

/-- **A Sobolev cutoff of `log |α|²`.** Let `x` be a smooth plane vortex with `|α| → 1` at
infinity, and let `R ≥ 0` be such that `|α|² > 1 / 2` outside the disc of radius `R`. Then some
smooth function `v` lying in every `H^s` agrees with `ℓ = log |α|²` near every point outside the
disc of radius `R + 2`. -/
private theorem exists_forall_mem_realSobolevFunctions_eventuallyEq_log_normSq
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ z : ℂ, R < ‖z‖ → 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧ (∀ s, v ∈ realSobolevFunctions ℂ s 2) ∧
      ∀ z : ℂ, R + 2 < ‖z‖ → v =ᶠ[𝓝 z] fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  have hp : ContDiff ℝ 2 (fun z ↦ x z 2) := (hxi 2).of_le (by norm_cast)
  have hq : ContDiff ℝ 2 (fun z ↦ x z 3) := (hxi 3).of_le (by norm_cast)
  obtain ⟨v, hv, hvbound, hvfar⟩ :=
    exists_abs_le_two_mul_one_sub_normSq_eventuallyEq_log_normSq hx hsol hlim hR0 hR
  have hn1 := normSq_le_one_of_tendsto hp hq hsol hlim
  -- `v` is bounded and square integrable, since `1 - |α|²` is square integrable and at most one.
  have hv2 : MemLp v 2 volume :=
    (memLp_one_sub_normSq volume hp hq hsol hlim).of_le_mul hv.continuous.aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (by linarith [hn1 z])]
        exact hvbound z)
  have hvC (z : ℂ) : v z ≤ 2 := by
    have h0 : 0 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by positivity
    linarith [le_abs_self (v z), hvbound z]
  -- `v` solves `Δv = (exp v - 1) / 4 + g` with `g` smooth and compactly supported.
  set g : ℂ → ℝ := fun z ↦ Δ v z - 1 / 4 * (Real.exp (v z) - 1) with hg_def
  have hgc : ContDiff ℝ ∞ g :=
    (hv.laplacian (m := ∞) (by simp)).sub
      (contDiff_const.mul ((Real.contDiff_exp.comp hv).sub contDiff_const))
  have hgs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 (R + 2)) fun z hz ↦ ?_
    have hz' : R + 2 < ‖z‖ := by simpa using hz
    have hnz := (hR z (by linarith))
    have hΔ : Δ v z = (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 4 := by
      rw [(InnerProductSpace.laplacian_congr_nhds (hvfar z hz')).eq_of_nhds]
      exact laplacian_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt
        (by linarith) (Eventually.of_forall hsol)
    simp only [g, hΔ, (hvfar z hz').self_of_nhds,
      Real.exp_log (by linarith : (0 : ℝ) < 4 * (x z 2 ^ 2 + x z 3 ^ 2))]
    ring
  have hvS (s : ℝ) : v ∈ realSobolevFunctions ℂ s 2 := by
    simpa only [sub_add_cancel] using
      mem_realSobolevFunctions_add_two_of_laplacian_eq_mul_exp_sub_one_add (c := 1 / 4)
        (by rw [Complex.finrank_real_complex]; norm_num) (hv.of_le (by norm_cast)) hv2 hvC
        (mem_realSobolevFunctions_of_hasCompactSupport hgc hgs (s - 2))
        fun z ↦ by rw [hg_def]; ring
  exact ⟨v, hv, hvS, hvfar⟩

/-- A reference coefficient times `exp (v / 2) - 1` lies in every `H^s` when `v` does. This is the
section part of `x - x_ref` for an end-normalized vortex. -/
private theorem referenceField_apply_mul_exp_sub_one_mem_realSobolevFunctions
    (f : ContDiffBump (0 : ℝ)) (i : Fin 4) {v : ℂ → ℝ}
    (hvS : ∀ s, v ∈ realSobolevFunctions ℂ s 2) (s : ℝ) :
    (fun z ↦ referenceField f m z i * (Real.exp (v z / 2) - 1)) ∈ realSobolevFunctions ℂ s 2 := by
  obtain ⟨k, hk⟩ := exists_nat_ge (max s 2)
  have hk1 : (1 : ℝ) < k := by linarith [le_max_right s 2]
  have he : (fun z ↦ Real.exp (v z / 2) - 1) ∈ realSobolevFunctions ℂ k 2 := by
    simpa only [Pi.smul_apply, smul_eq_mul, one_div_mul_eq_div] using
      exp_sub_one_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hk1)
        (Submodule.smul_mem _ (1 / 2 : ℝ) (hvS k))
  exact realSobolevFunctions_mono (by norm_num) (by norm_num) ((le_max_left s 2).trans hk)
    (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by exact_mod_cast hk1)
      (referenceField_mem_framedFieldSpace f m k) i he)

/-- Half a directional derivative of a smooth function lying in every `H^s` lies in every `H^s`.
This is the connection part of `x - x_ref` for an end-normalized vortex. -/
private theorem fderiv_apply_div_two_mem_realSobolevFunctions {v : ℂ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvS : ∀ s, v ∈ realSobolevFunctions ℂ s 2) (u : ℂ) (s : ℝ) :
    (fun z ↦ fderiv ℝ v z u / 2) ∈ realSobolevFunctions ℂ s 2 := by
  simpa only [Pi.smul_def, smul_eq_mul, inv_mul_eq_div] using
    Submodule.smul_mem _ (2⁻¹ : ℝ) (realSobolevFunctions_mono (by norm_num) (by norm_num)
      (le_max_left s 0) (fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num)
        (le_max_right s 0) (hv.of_le (by norm_cast)) (hvS _) u))

/-- **`x - x_ref` from a cutoff of `log |α|²`.** Let `z` lie outside the cutoff disc, let the
section of a vortex `x` be `|α|` times the winding phase near `z` with `α(z) ≠ 0`, and let `v` agree
with `ℓ = log |α|²` near `z`. Then at `z`,
`x - x_ref = (-∂_t v / 2, ∂_s v / 2, x_ref,₂ (exp (v / 2) - 1), x_ref,₃ (exp (v / 2) - 1))`. -/
private theorem sub_referenceField_apply_eq_of_eventuallyEq_log_normSq
    (f : ContDiffBump (0 : ℝ)) {z : ℂ} {v : ℂ → ℝ} (hrOut : f.rOut ≤ ‖z‖ ^ 2)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hsol : equation x z = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hα : sectionValue x z ≠ 0)
    (hv : v =ᶠ[𝓝 z] fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) :
    x z 0 - referenceField f m z 0 = -fderiv ℝ v z I / 2 ∧
      x z 1 - referenceField f m z 1 = fderiv ℝ v z 1 / 2 ∧
      x z 2 - referenceField f m z 2 = referenceField f m z 2 * (Real.exp (v z / 2) - 1) ∧
      x z 3 - referenceField f m z 3 = referenceField f m z 3 * (Real.exp (v z / 2) - 1) := by
  have hexp : Real.exp (v z / 2) = ‖sectionValue x z‖ := by
    rw [hv.self_of_nhds]
    simp only [← sq_norm_sectionValue, Real.log_pow]
    rw [Nat.cast_ofNat, mul_div_cancel_left₀ _ two_ne_zero, Real.exp_log (norm_pos_iff.2 hα)]
  have hd := hv.fderiv_eq (𝕜 := ℝ)
  obtain ⟨h0, h1, h2, h3⟩ := sub_referenceField_apply_eq f hrOut hp hq (by simp [hsol])
    (by simp [hsol]) hphase hα
  exact ⟨by rw [hd]; exact h0, by rw [hd]; exact h1, by rw [hexp]; exact h2,
    by rw [hexp]; exact h3⟩

/-- **End-normalized vortices lie in every Sobolev field space.** Let `x` be a smooth plane
vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m`
outside a compact set. Then `x` lies in the affine space `A_m^s` of framed degree-`m` fields for
every order `s`: `x - x_ref ∈ L² ∩ H^s`. -/
theorem mem_framedFieldSpace_of_eventually_sectionValue_eq (f : ContDiffBump (0 : ℝ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (s : ℝ) : x ∈ framedFieldSpace f m s := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  have hxd (i : Fin 4) (z : ℂ) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    (hxi i).differentiable (by simp) z
  -- A radius beyond which the section is end-normalized, `|α|² > 1 / 2`, and the reference
  -- field is the winding pair.
  obtain ⟨R₀, hR₀⟩ := closedBall_compl_subset_of_mem_cocompact (hphase.and
    ((hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))).and
      (tendsto_norm_cocompact_atTop.eventually_gt_atTop (max 1 f.rOut)))) 0
  set R := max R₀ 0
  have hR (z : ℂ) (hz : R < ‖z‖) : sectionValue x z = ‖sectionValue x z‖ * windingPhase m z ∧
      1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) ∧ max 1 f.rOut < ‖z‖ :=
    hR₀ (by simpa using (le_max_left R₀ 0).trans_lt hz)
  obtain ⟨v, hv, hvS, hvfar⟩ := exists_forall_mem_realSobolevFunctions_eventuallyEq_log_normSq
    hx hsol hlim (le_max_right R₀ 0) fun z hz ↦ (hR z hz).2.1
  -- Outside the disc of radius `R + 2`, `x - x_ref` is read off from `v`.
  have hfar (z : ℂ) (hz : R + 2 < ‖z‖) :
      x z 0 - referenceField f m z 0 = -fderiv ℝ v z I / 2 ∧
        x z 1 - referenceField f m z 1 = fderiv ℝ v z 1 / 2 ∧
        x z 2 - referenceField f m z 2 = referenceField f m z 2 * (Real.exp (v z / 2) - 1) ∧
        x z 3 - referenceField f m z 3 = referenceField f m z 3 * (Real.exp (v z / 2) - 1) := by
    obtain ⟨-, hnz, hz1⟩ := hR z (by linarith)
    refine sub_referenceField_apply_eq_of_eventuallyEq_log_normSq f (rOut_le_norm_sq f hz1)
      (hxd 2 z) (hxd 3 z) (hsol z) ?_ (fun h ↦ ?_) (hvfar z hz)
    · filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        ((by linarith : R < R + 2).trans hz)] with w hw
      exact (hR w hw).1
    · have := sq_norm_sectionValue x z
      rw [h, norm_zero] at this
      linarith
  -- A coordinate of `x - x_ref` lies in `H^s` once it agrees far out with a smooth function in
  -- every `H^s`.
  have key (i : Fin 4) (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F)
      (hFs : ∀ s, F ∈ realSobolevFunctions ℂ s 2)
      (hFeq : ∀ z, R + 2 < ‖z‖ → x z i - referenceField f m z i = F z) :
      (fun z ↦ x z i - referenceField f m z i) ∈ realSobolevFunctions ℂ s 2 :=
    mem_realSobolevFunctions_of_eventuallyEq_cocompact
      (((hxi i).sub (contDiff_euclidean.1 (contDiff_referenceField f m) i)).sub hF)
      ((tendsto_norm_cocompact_atTop.eventually_gt_atTop (R + 2)).mono hFeq) (hFs s)
  -- The connection part is half a derivative of `v`, and the section part is a reference
  -- coefficient times `exp (v / 2) - 1`.
  have hdv (u : ℂ) : ContDiff ℝ ∞ fun z ↦ fderiv ℝ v z u / 2 :=
    ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).div_const 2
  have hdvS := fderiv_apply_div_two_mem_realSobolevFunctions hv hvS
  have hexpC (i : Fin 4) :
      ContDiff ℝ ∞ (fun z ↦ referenceField f m z i * (Real.exp (v z / 2) - 1)) :=
    (contDiff_euclidean.1 (contDiff_referenceField f m) i).mul
      ((Real.contDiff_exp.comp (hv.div_const 2)).sub contDiff_const)
  rw [mem_framedFieldSpace, mem_sobolevFields]
  intro i
  simp only [Pi.sub_apply, PiLp.sub_apply]
  fin_cases i
  · exact key 0 (fun z ↦ -fderiv ℝ v z I / 2) (by simpa only [neg_div] using (hdv I).neg)
      (fun s ↦ by simpa only [Pi.neg_def, neg_div] using neg_mem (hdvS I s))
      fun z hz ↦ (hfar z hz).1
  · exact key 1 _ (hdv 1) (hdvS 1) fun z hz ↦ (hfar z hz).2.1
  · exact key 2 _ (hexpC 2) (referenceField_apply_mul_exp_sub_one_mem_realSobolevFunctions f 2 hvS)
      fun z hz ↦ (hfar z hz).2.2.1
  · exact key 3 _ (hexpC 3) (referenceField_apply_mul_exp_sub_one_mem_realSobolevFunctions f 3 hvS)
      fun z hz ↦ (hfar z hz).2.2.2

/-- **Every smooth framed vortex has a representative in every Sobolev field space.** A smooth
plane vortex with the degree-`m` end framing `α (z / |z|)^(-m) → 1` is carried by a smooth framed
gauge transformation into the affine space `A_m^s` of framed degree-`m` fields, for every order
`s` at once, and the transformed section is `|α|` times the winding phase outside a compact set. -/
theorem exists_framedGaugeGroup_forall_smul_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup,
      (∀ᶠ z in cocompact ℂ, sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z) ∧
        ∀ s, u • x ∈ framedFieldSpace f m s := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  refine ⟨u, hu, fun s ↦ ?_⟩
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_framedGaugeGroup_smul_eq_zero_iff u
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  exact mem_framedFieldSpace_of_eventually_sectionValue_eq f (contDiff_framedGaugeGroup_smul u hx)
    hsol' ((tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe).congr fun z ↦ by
      simp [framedGaugeGroup_smul]) hu s

end TauCeti.Vortex
