/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Complex.ReProdIm
import TauCeti.MeasureTheory.Integral.Lebesgue.ReProdIm
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Geometry.Symplectic.Floer.Breaking
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Bounded derivatives and broken-off orbits of finite-energy Floer solutions on cylindrical ends

On a cylindrical end of a punctured Floer domain, such as an end of a pair of pants or of a Floer
cylinder, a solution is read in the coordinate `z = s + i t`, with `s` running along the end and
`t ∈ ℝ / ℤ` the circle coordinate. In the local coordinates of
`TauCeti.Geometry.Symplectic.Floer.Compactness` it solves

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`

on a half-plane `s > a`, and it is periodic, `u(z + i) = u(z)`. On the end the Floer data are
cylindrical, `J = J_t` and Hamiltonian perturbation `H_t dt`, so `J` and `X` do not depend on
`s` and are periodic in `t`. The results below only use that `J(·, x)` and `X(·, x)` are periodic
under both `z ↦ z + 1` and `z ↦ z + i`.

The main result is that bubbling cannot occur along a cylindrical end of finite energy: if `u` has
image in a compact set `K` and finite energy `∫ ‖∂ₛu‖²` over the half-strip `(a, ∞) × [0, 1]`,
then its derivative is bounded on every half-plane `s ≥ b` with `b > a`
(`TauCeti.Floer.exists_forall_norm_fderiv_le_of_lintegral_ne_top`), so `u` is Lipschitz there
(`TauCeti.Floer.exists_lipschitzOnWith_of_lintegral_ne_top`). The argument has two steps.

* For doubly periodic data the threshold of the mean-value inequality
  (`TauCeti.Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy`) can be
  chosen uniformly over the whole plane, since every disc of radius at most `1` is a lattice
  translate of a disc in a fixed compact window
  (`TauCeti.Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_periodic`).
* The energy of the end over the discs of a fixed small radius `r` about points far out along the
  end tends to zero, since such a disc lies in two periods of a far-out half-strip
  (`Function.Periodic.setLIntegral_ball_le_two_mul_setLIntegral_reProdIm_Ioi`,
  `TauCeti.tendsto_setLIntegral_reProdIm_Ioi_atTop`). Far out, the mean-value inequality therefore
  bounds `‖∂ₛu‖`, and on the remaining compact part of the end `du` is bounded by continuity.
  The equation bounds `∂ₜu` in terms of `∂ₛu`
  (`TauCeti.Floer.exists_forall_norm_fderiv_le_mul_one_add_norm_fderiv_one`).

The same bounds hold for a solution `u : ℝ × ℝ → V` of the Floer equation
`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on a half-cylinder `(a, ∞) × ℝ / ℤ`, for a `C³`
`1`-periodic Hamiltonian `H` and a `C²` `1`-periodic family `J_t(x)` tamed by `ω` on a compact set
`K` containing the image of `u`, with finite Floer energy over `(a, ∞) × [0, 1]`. Read in the
complex coordinate, `u` solves the coordinate equation above with `J(z, x) = J_(im z)(x)` and the
`dt`-component of `X` given by `X_{H_(im z)}`. The taming constant of `J` on `[0, 1] × K` bounds
`‖∂ₛu‖²` by a multiple of the Floer energy density, so the energy `∫ ‖∂ₛu‖²` is finite too. Hence
`du` is bounded and `u` is Lipschitz on every half-cylinder `s ≥ b` with `b > a`
(`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`,
`TauCeti.SymplecticForm.exists_lipschitzOnWith_of_floer`).

This gives **breaking off an orbit at the end**
(`TauCeti.SymplecticForm.exists_subseq_periodic_hasDerivAt_tendstoLocallyUniformly_of_floer`):
for every sequence `σ_n → ∞` there are a subsequence `σ_(φ n)` and a `1`-periodic orbit `x` of
`X_{H_t}` such that the translates `(s, t) ↦ u(s + σ_(φ n), t)` converge to the stationary
cylinder `(s, t) ↦ x(t)`, locally uniformly on `ℝ × ℝ`. The translates, cut off at `s = b`, are
uniformly Lipschitz with values in `K`, so the Arzelà–Ascoli theorem
(`ArzelaAscoli.isCompact_closure_range_of_equicontinuous`) gives a convergent subsequence, and
`TauCeti.Geometry.Symplectic.Floer.Breaking` identifies every such limit as a stationary cylinder
over a Hamiltonian orbit. Convergence of the whole end, rather than of a subsequence of
translates, needs isolated orbits, and the convergence of the derivatives needs elliptic
estimates; neither is treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer cylinders and their behaviour at the
  ends.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.3
  (the mean-value inequality) and Section 4.6 (bubbling).
-/

public section

open Complex Filter Function Metric MeasureTheory Set Topology
open scoped ENNReal NNReal Real

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V]

section NormedSpace

variable [NormedSpace ℝ V] {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {K : Set V}

/-- **The equation bounds the full derivative by `∂ₛu`.** Let `J` and `X` be continuous on
`ℂ × K` for a compact `K ⊆ V`, and let `J(·, x)` and `X(·, x)` be periodic under `z ↦ z + 1` and
`z ↦ z + i`. There is `A ≥ 0` such that `‖du(z)‖ ≤ A (1 + ‖∂ₛu(z)‖)` at every point `z` where `u`
takes a value in `K` and solves `∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`. -/
theorem exists_forall_norm_fderiv_le_mul_one_add_norm_fderiv_one
    (hJ : ContinuousOn J (univ ×ˢ K)) (hX : ContinuousOn X (univ ×ˢ K)) (hK : IsCompact K)
    (hJ1 : ∀ x, Periodic (fun z ↦ J (z, x)) 1) (hJI : ∀ x, Periodic (fun z ↦ J (z, x)) I)
    (hX1 : ∀ x, Periodic (fun z ↦ X (z, x)) 1) (hXI : ∀ x, Periodic (fun z ↦ X (z, x)) I) :
    ∃ A, 0 ≤ A ∧ ∀ ⦃u : ℂ → V⦄ ⦃z : ℂ⦄, u z ∈ K →
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1) →
      ‖fderiv ℝ u z‖ ≤ A * (1 + ‖fderiv ℝ u z 1‖) := by
  -- Bound the data on the compact set `[0, 1]² × K`, which meets every lattice orbit.
  have hc : IsCompact ((Icc 0 1 ×ℂ Icc 0 1) ×ˢ K) := (isCompact_Icc.reProdIm isCompact_Icc).prod hK
  have hsub : (Icc 0 1 ×ℂ Icc 0 1) ×ˢ K ⊆ univ ×ˢ K := prod_mono (subset_univ _) le_rfl
  obtain ⟨a, ha⟩ := hc.exists_bound_of_continuousOn (hJ.mono hsub)
  obtain ⟨c, hc⟩ := hc.exists_bound_of_continuousOn (hX.mono hsub)
  have hred (z : ℂ) {x : V} (hx : x ∈ K) : ‖J (z, x)‖ ≤ max a 0 ∧ ‖X (z, x)‖ ≤ max c 0 := by
    have hmem : (z - ((⌊z.re⌋ : ℂ) + ⌊z.im⌋ * I), x) ∈ (Icc 0 1 ×ℂ Icc 0 1) ×ˢ K :=
      ⟨reProdIm_subset_iff.2 (prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
        (sub_floor_mem_reProdIm z), hx⟩
    have hJx := (hJ1 x).int_mul_add_int_mul (hJI x) ⌊z.re⌋ ⌊z.im⌋
    have hXx := (hX1 x).int_mul_add_int_mul (hXI x) ⌊z.re⌋ ⌊z.im⌋
    rw [mul_one] at hJx hXx
    rw [← hJx.sub_eq z, ← hXx.sub_eq z]
    exact ⟨(ha _ hmem).trans (le_max_left _ _), (hc _ hmem).trans (le_max_left _ _)⟩
  set a' := max a 0
  set c' := max c 0
  have ha' : 0 ≤ a' := le_max_right _ _
  have hc' : 0 ≤ c' := le_max_right _ _
  refine ⟨(1 + a') * (1 + c'), by positivity, fun u z huz hCR ↦ ?_⟩
  obtain ⟨hJz, hXz⟩ := hred z huz
  set L := fderiv ℝ u z
  have hXv (v : ℂ) (hv : ‖v‖ = 1) : ‖X (z, u z) v‖ ≤ c' :=
    ((X (z, u z)).le_opNorm v).trans (by rw [hv, mul_one]; exact hXz)
  -- `∂ₜu = X(z, u) i + J(z, u) (∂ₛu - X(z, u) 1)`.
  have hI : ‖L I‖ ≤ a' * (‖L 1‖ + c') + c' := by
    rw [← sub_add_cancel (L I) (X (z, u z) I), hCR]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hXv I norm_I))
    refine ((J (z, u z)).le_opNorm _).trans ?_
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hXv 1 norm_one))
  have hL : ‖L‖ ≤ ‖L 1‖ + ‖L I‖ :=
    L.opNorm_le_bound (by positivity) L.norm_apply_le_norm_one_add_norm_I
  have h1 : 0 ≤ ‖L 1‖ := norm_nonneg _
  nlinarith [mul_nonneg ha' hc', mul_nonneg ha' h1, mul_nonneg hc' h1,
    mul_nonneg (mul_nonneg ha' hc') h1]

end NormedSpace

variable [InnerProductSpace ℝ V]
  {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {K : Set V}

/-- **The mean-value inequality for doubly periodic data.** Let `J` and `X` be `C²` on an open set
`W ⊆ ℂ × V` containing `ℂ × K` for a compact `K ⊆ V`, with `J(z, x)² = -1` on `ℂ × K`, and let
`J(·, x)` and `X(·, x)` be periodic under `z ↦ z + 1` and `z ↦ z + i`. Then the threshold of the
mean-value inequality is uniform over the plane: there is `δ > 0` such that for every disc
`B_r(z₀)` of radius `r ≤ 1` and every `C³` solution `u` on it with image in `K`, `∂ₛu` continuous
up to the boundary and `π r² + ∫_{B_r(z₀)} ‖∂ₛu‖² < δ`, we have
`π r² ‖∂ₛu(z₀)‖² ≤ 7 π r² + 8 ∫_{B_r(z₀)} ‖∂ₛu‖²`. -/
theorem exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_periodic
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : univ ×ˢ K ⊆ W) (hJsq : ∀ z, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hJ1 : ∀ x, Periodic (fun z ↦ J (z, x)) 1) (hJI : ∀ x, Periodic (fun z ↦ J (z, x)) I)
    (hX1 : ∀ x, Periodic (fun z ↦ X (z, x)) 1) (hXI : ∀ x, Periodic (fun z ↦ X (z, x)) I) :
    ∃ δ > 0, ∀ ⦃u : ℂ → V⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄, 0 ≤ r → r ≤ 1 →
      ContDiffOn ℝ 3 u (ball z₀ r) → ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y I - X (y, u y) I =
        J (y, u y) (fderiv ℝ u y 1 - X (y, u y) 1)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      π * r ^ 2 + ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤
        7 * π * r ^ 2 + 8 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
  -- Apply the mean-value inequality on the compact window `closedBall 0 3`, which contains every
  -- disc of radius at most `1` about a point of the unit square.
  obtain ⟨δ, hδ, hmean⟩ := exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy
    hW hJ hX (isCompact_closedBall (0 : ℂ) 3) hK (fun p hp ↦ hKW ⟨mem_univ _, hp.2⟩)
    fun z _ x hx v ↦ hJsq z x hx v
  refine ⟨δ, hδ, fun u z₀ r hr hr1 hu hu' hCR huK hE ↦ ?_⟩
  -- Translate `z₀` by a lattice vector `w` into the unit square; the data do not change.
  set w : ℂ := (⌊z₀.re⌋ : ℂ) + ⌊z₀.im⌋ * I
  have hJw (y : ℂ) (x : V) : J (y + w, x) = J (y, x) := by
    simpa only [mul_one] using (hJ1 x).int_mul_add_int_mul (hJI x) ⌊z₀.re⌋ ⌊z₀.im⌋ y
  have hXw (y : ℂ) (x : V) : X (y + w, x) = X (y, x) := by
    simpa only [mul_one] using (hX1 x).int_mul_add_int_mul (hXI x) ⌊z₀.re⌋ ⌊z₀.im⌋ y
  have hpre : (· + w) ⁻¹' ball z₀ r = ball (z₀ - w) r := preimage_add_right_ball w z₀ r
  have hmaps : MapsTo (· + w) (ball (z₀ - w) r) (ball z₀ r) := hpre ▸ mapsTo_preimage _ _
  have hdv (y : ℂ) : fderiv ℝ (fun y ↦ u (y + w)) y = fderiv ℝ u (y + w) :=
    fderiv_comp_add_right w
  have hball : ball (z₀ - w) r ⊆ closedBall 0 3 := by
    intro y hy
    have hsq := sub_floor_mem_reProdIm z₀
    simp only [mem_reProdIm, mem_Ico] at hsq
    have hnorm := norm_le_abs_re_add_abs_im (z₀ - w)
    rw [abs_of_nonneg hsq.1.1, abs_of_nonneg hsq.2.1] at hnorm
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_le_norm_add_norm_sub' y (z₀ - w)]
  have henergy : ∫ y in ball (z₀ - w) r, ‖fderiv ℝ (fun y ↦ u (y + w)) y 1‖ ^ 2 =
      ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
    simp_rw [hdv, ← hpre]
    exact (measurePreserving_add_right volume w).setIntegral_preimage_emb
      (measurableEmbedding_addRight w) (fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) _
  have hmapsC : MapsTo (· + w) (closedBall (z₀ - w) r) (closedBall z₀ r) := by
    rw [← preimage_add_right_closedBall]
    exact mapsTo_preimage _ _
  have h := hmean (u := fun y ↦ u (y + w)) (z₀ := z₀ - w) hr hball
    (hu.comp (by fun_prop : ContDiff ℝ 3 fun y : ℂ ↦ y + w).contDiffOn hmaps)
    ((hu'.comp (by fun_prop : Continuous fun y : ℂ ↦ y + w).continuousOn hmapsC).congr
      fun y _ ↦ by simp only [hdv, comp_apply])
    (fun y hy ↦ by rw [hdv]; simpa only [hJw, hXw] using hCR _ (hmaps hy))
    (fun y hy ↦ huK _ (hmaps hy)) (by rwa [henergy])
  rwa [henergy, hdv, sub_add_cancel] at h

/-- **Finite-energy Floer solutions have bounded derivatives on cylindrical ends.** Let `J` and `X`
be `C²` on an open set `W ⊆ ℂ × V` containing `ℂ × K` for a compact `K ⊆ V`, with
`J(z, x)² = -1` on `ℂ × K`, and let `J(·, x)` and `X(·, x)` be periodic under `z ↦ z + 1` and
`z ↦ z + i`. Let `u` be `C³` and `i`-periodic on the half-plane `re z > a`, solving
`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` there with image in `K`, and with finite energy
`∫ ‖∂ₛu‖²` over the half-strip `(a, ∞) × [0, 1]`. Then `du` is bounded on the half-plane
`re z ≥ b` for every `b > a`: no energy bubbles off along the end. -/
theorem exists_forall_norm_fderiv_le_of_lintegral_ne_top
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : univ ×ˢ K ⊆ W) (hJsq : ∀ z, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hJ1 : ∀ x, Periodic (fun z ↦ J (z, x)) 1) (hJI : ∀ x, Periodic (fun z ↦ J (z, x)) I)
    (hX1 : ∀ x, Periodic (fun z ↦ X (z, x)) 1) (hXI : ∀ x, Periodic (fun z ↦ X (z, x)) I)
    {u : ℂ → V} {a b : ℝ} (hab : a < b) (hu : ContDiffOn ℝ 3 u {z | a < z.re})
    (hper : Periodic u I)
    (hCR : ∀ z, a < z.re → fderiv ℝ u z I - X (z, u z) I =
      J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : ∀ z, a < z.re → u z ∈ K)
    (hfin : ∫⁻ z in Ioi a ×ℂ Icc 0 1, ‖fderiv ℝ u z 1‖ₑ ^ 2 ≠ ∞) :
    ∃ M, ∀ z, b ≤ z.re → ‖fderiv ℝ u z‖ ≤ M := by
  obtain ⟨δ, hδ, hmean⟩ := exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_periodic
    hW hJ hX hK hKW hJsq hJ1 hJI hX1 hXI
  obtain ⟨A, hA0, hA⟩ := exists_forall_norm_fderiv_le_mul_one_add_norm_fderiv_one
    (hJ.continuousOn.mono hKW) (hX.continuousOn.mono hKW) hK hJ1 hJI hX1 hXI
  have hU : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const continuous_re
  have hdu : ContinuousOn (fderiv ℝ u) {z | a < z.re} :=
    hu.continuousOn_fderiv_of_isOpen hU (by norm_num)
  -- Fix a radius `r ≤ 1/2`, below the gap `b - a`, whose disc area `π r²` is below `δ / 2`.
  set r : ℝ := min (min (1 / 2) ((b - a) / 2)) (δ / 8)
  have hr : 0 < r := lt_min (lt_min (by norm_num) (by linarith)) (by linarith)
  have hr2 : r ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hrab : r ≤ (b - a) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hrδ : r ≤ δ / 8 := min_le_right _ _
  have hπr : π * r ^ 2 < δ / 2 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  -- Far out along the end, the energy over one period of the half-strip is below `δ / 4`.
  obtain ⟨R, hR, hRa⟩ := ((tendsto_setLIntegral_reProdIm_Ioi_atTop hfin).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (by linarith : 0 < δ / 4)))).and
    (eventually_ge_atTop a) |>.exists
  -- On the compact part `b ≤ re z ≤ R + r` of the end, `du` is bounded by continuity.
  obtain ⟨M₁, hM₁⟩ := (hper.fderiv (𝕜 := ℝ)).exists_bound_of_continuousOn_reProdIm_univ
    (isCompact_Icc (a := b) (b := R + r)) (hdu.mono fun z hz ↦ hab.trans_le hz.1.1)
  set B : ℝ := 8 + 4 * δ / (π * r ^ 2)
  refine ⟨max M₁ (A * (1 + B)), fun z hz ↦ ?_⟩
  rcases le_or_gt z.re (R + r) with hzR | hzR
  · exact (hM₁ z ⟨⟨hz, hzR⟩, mem_univ _⟩).trans (le_max_left _ _)
  · -- Far out, the mean-value inequality bounds `∂ₛu`, and the equation bounds `du`.
    have hball : closedBall z r ⊆ {z | a < z.re} := fun y hy ↦ by
      have := abs_re_le_norm (y - z)
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [sub_re, abs_le] at this
      exact (by linarith : a < y.re)
    have hcont : ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z r) :=
      (hdu.clm_apply continuousOn_const).mono hball
    -- The energy over the disc is at most twice the energy over one far-out period.
    have hper' : Periodic (fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) I := fun y ↦ by
      simp only [hper.fderiv y]
    have hR' : ∫⁻ y in Ioi R ×ℂ Icc 0 1, ENNReal.ofReal (‖fderiv ℝ u y 1‖ ^ 2) ≤
        ENNReal.ofReal (δ / 4) := by
      simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using hR.le
    have hE := hper'.setIntegral_ball_le_two_mul (fun _ ↦ sq_nonneg _) hr2 (by linarith)
      (by linarith) ((hcont.mono ball_subset_closedBall).norm.pow 2 |>.aestronglyMeasurable
        measurableSet_ball) hR'
    have hE0 : 0 ≤ ∫ y in ball z r, ‖fderiv ℝ u y 1‖ ^ 2 :=
      setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
    have hmv := hmean hr.le (by linarith) (hu.mono (ball_subset_closedBall.trans hball)) hcont
      (fun y hy ↦ hCR y (hball (ball_subset_closedBall hy)))
      (fun y hy ↦ huK y (hball (ball_subset_closedBall hy))) (by linarith)
    have hπr0 : 0 < π * r ^ 2 := by positivity
    have hsq : ‖fderiv ℝ u z 1‖ ^ 2 ≤ 7 + 4 * δ / (π * r ^ 2) := by
      rw [← sub_le_iff_le_add', le_div_iff₀ hπr0]
      nlinarith
    have hs : ‖fderiv ℝ u z 1‖ ≤ B := by nlinarith [sq_nonneg (‖fderiv ℝ u z 1‖ - 1)]
    have hza : a < z.re := by linarith
    exact (hA (huK z hza) (hCR z hza)).trans
      ((mul_le_mul_of_nonneg_left (by linarith) hA0).trans (le_max_right _ _))

/-- **Finite-energy Floer solutions are Lipschitz on cylindrical ends.** Under the hypotheses of
`TauCeti.Floer.exists_forall_norm_fderiv_le_of_lintegral_ne_top`, the solution `u` is Lipschitz on
the half-plane `re z ≥ b` for every `b > a`. In particular its translates `u(· + σ)` along the end
are uniformly Lipschitz. -/
theorem exists_lipschitzOnWith_of_lintegral_ne_top
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : univ ×ˢ K ⊆ W) (hJsq : ∀ z, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hJ1 : ∀ x, Periodic (fun z ↦ J (z, x)) 1) (hJI : ∀ x, Periodic (fun z ↦ J (z, x)) I)
    (hX1 : ∀ x, Periodic (fun z ↦ X (z, x)) 1) (hXI : ∀ x, Periodic (fun z ↦ X (z, x)) I)
    {u : ℂ → V} {a b : ℝ} (hab : a < b) (hu : ContDiffOn ℝ 3 u {z | a < z.re})
    (hper : Periodic u I)
    (hCR : ∀ z, a < z.re → fderiv ℝ u z I - X (z, u z) I =
      J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : ∀ z, a < z.re → u z ∈ K)
    (hfin : ∫⁻ z in Ioi a ×ℂ Icc 0 1, ‖fderiv ℝ u z 1‖ₑ ^ 2 ≠ ∞) :
    ∃ L : ℝ≥0, LipschitzOnWith L u {z | b ≤ z.re} := by
  obtain ⟨M, hM⟩ := exists_forall_norm_fderiv_le_of_lintegral_ne_top hW hJ hX hK hKW hJsq hJ1 hJI
    hX1 hXI hab hu hper hCR huK hfin
  have hU : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const continuous_re
  refine ⟨Real.toNNReal M, (convex_halfSpace_re_ge b).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (fun z hz ↦ ?_) (fun z hz ↦ ?_)⟩
  · have hz' : z ∈ {z : ℂ | a < z.re} := hab.trans_le hz
    exact (hu.differentiableOn (by norm_num) z hz').differentiableAt (hU.mem_nhds hz')
  · rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hM z hz).trans (Real.le_coe_toNNReal M)

end TauCeti.Floer

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V}
  {W : Set (ℝ × V)} {K : Set V} {u : ℝ × ℝ → V} {a : ℝ}

/-- A `1`-periodic family `J_t(x)`, continuous on `ℝ × K` for a compact `K` and tamed by `ω` there,
has uniform taming and norm constants: `c ‖v‖² ≤ ω(v, J_t(x) v)` and `‖J_t(x) v‖ ≤ M ‖v‖` for
all `t` and all `x ∈ K`, with `c > 0`. -/
private theorem exists_pos_forall_mul_norm_sq_le_and_norm_le (hK : IsCompact K)
    (hJ : ContinuousOn (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (univ ×ˢ K))
    (hJper : Periodic J 1) (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x)) :
    ∃ c > 0, ∃ M, ∀ t, ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J t x v) ∧ ‖J t x v‖ ≤ M * ‖v‖ := by
  set Jc : ℝ × V → V →L[ℝ] V := fun p ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap
  have hD : IsCompact (Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have hJD : ContinuousOn Jc (Icc (0 : ℝ) 1 ×ˢ K) := hJ.mono (prod_mono (subset_univ _) le_rfl)
  obtain ⟨c, hc, hJc⟩ := hD.exists_pos_forall_mul_norm_sq_le
    (b := fun p ↦ ((ContinuousLinearMap.compL ℝ V V ℝ).flip (Jc p)).comp
      ω.toBilinForm.toContinuousBilinearMap)
    (((ContinuousLinearMap.compL ℝ V V ℝ).flip.continuous.comp_continuousOn hJD).clm_comp
      continuousOn_const)
    (fun p hp v hv ↦ by simpa [Jc] using hJt p.1 p.2 hp.2 v hv)
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn hJD
  refine ⟨c, hc, M, fun t x hx v ↦ ?_⟩
  have hp : (Int.fract t, x) ∈ Icc (0 : ℝ) 1 ×ˢ K :=
    ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, hx⟩
  rw [← hJper.apply_fract t]
  exact ⟨by simpa [Jc] using hJc _ hp v, by simpa [Jc] using (Jc _).le_of_opNorm_le (hM _ hp) v⟩

/-- With `1`-periodic data, the Floer equation over one period `(a, ∞) × [0, 1]` of a
half-cylinder holds on the whole half-plane `s > a`. -/
private theorem isComplexLinearMap_perturbedFDeriv_of_periodic (hHper : Periodic H 1)
    (hJper : Periodic J 1) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {z : ℝ × ℝ} (hz : z ∈ Ioi a ×ˢ univ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V) := by
  -- Translate `z` into the first period by `w = (0, -⌊t⌋)`.
  set w : ℝ × ℝ := (0, -⌊z.2⌋)
  have hw (y : ℝ × ℝ) : y + w = (y.1, y.2 - ⌊z.2⌋) := by ext <;> simp [w, sub_eq_add_neg]
  have hu (y : ℝ × ℝ) (hy : a < y.1) : u (y + w) = u y := by
    simpa [hw] using (hper y.1 hy).sub_int_mul_eq (x := y.2) ⌊z.2⌋
  have hloc : u =ᶠ[𝓝 z] fun y ↦ u (y + w) := by
    filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhds hz] with y hy
    exact (hu y hy.1).symm
  have hKt : (fun y : ℝ × ℝ ↦ H (y + w).2) = fun y ↦ H y.2 := funext fun y ↦ by
    simpa [hw] using hHper.sub_int_mul_eq (x := y.2) ⌊z.2⌋
  have hJz : J (z + w).2 = J z.2 := by
    simpa [hw] using hJper.sub_int_mul_eq (x := z.2) ⌊z.2⌋
  have hzw : z + w ∈ Ioi a ×ˢ Icc (0 : ℝ) 1 := by
    rw [hw, Int.self_sub_floor]
    exact ⟨hz.1, Int.fract_nonneg z.2, (Int.fract_lt_one z.2).le⟩
  have h := hfloer (z + w) hzw
  rw [hJz, hu z hz.1, ← ω.perturbedFDeriv_comp_add_right, hKt] at h
  rwa [ω.perturbedFDeriv_congr_of_eventuallyEq _ _ hloc]

/-- On a finite-energy Floer half-cylinder for a family `J_t(x)` tamed uniformly on `ℝ × K`, the
energy `∫ ‖∂ₛu‖²` over `(a, ∞) × [0, 1]` is finite. -/
private theorem setLIntegral_enorm_fderiv_stdComplexLineReal_sq_ne_top (hK : IsCompact K)
    (hJ : ContinuousOn (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (univ ×ˢ K))
    (hJper : Periodic J 1) (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ u z stdComplexLineReal‖ₑ ^ 2 ≠ ⊤ := by
  obtain ⟨c, hc, _, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK hJ hJper hJt
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 / c)) hE) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Icc) fun z hz ↦ ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- The `ds`-component of the perturbation vanishes, so `‖∂ₛu‖² ≤ (2 / c) e`.
  simpa [hamiltonianVectorField_const] using ω.norm_fderiv_stdComplexLineReal_sq_le hc
    (fun w ↦ (hcM z.2 _ (huK z.1 hz.1 z.2) w).1) (hfloer z hz)

/-- In the complex coordinate `e = equivRealProdCLM`, the cylindrical datum `K = H_t dt` of a `C³`
`1`-periodic Hamiltonian gives the `C²` coefficient `X(z, x) = X_K(e z, x) ∘ e`, periodic under
`z ↦ z + 1` and `z ↦ z + i`. -/
private theorem contDiff_hamiltonianOneForm_comp_equivRealProdCLM (hH : ContDiff ℝ 3 (uncurry H))
    (hHper : Periodic H 1) :
    ContDiff ℝ 2 (fun q : ℂ × V ↦ (ω.hamiltonianOneForm (fun _ _ ↦ 0) (fun w ↦ H w.2)
      (equivRealProdCLM q.1) q.2).comp (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)) ∧
    (∀ x, Periodic (fun z ↦ (ω.hamiltonianOneForm (fun _ _ ↦ 0) (fun w ↦ H w.2)
      (equivRealProdCLM z) x).comp (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)) 1) ∧
    ∀ x, Periodic (fun z ↦ (ω.hamiltonianOneForm (fun _ _ ↦ 0) (fun w ↦ H w.2)
      (equivRealProdCLM z) x).comp (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)) I := by
  have h := ω.contDiffOn_hamiltonianOneForm (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) (n := 2)
    isOpen_univ (contDiff_const (c := (0 : ℝ))).contDiffOn
    (contDiff_uncurry_cylindrical hH).contDiffOn
  rw [contDiffOn_univ] at h
  refine ⟨(h.comp ((equivRealProdCLM.contDiff.comp contDiff_fst).prodMk contDiff_snd)).clm_comp
    contDiff_const, fun x z ↦ ?_, fun x z ↦ ?_⟩ <;> ext w <;> simp [hHper z.im]

/-- **Finite-energy Floer half-cylinders have bounded derivatives.** Let `H` be a `C³`,
`1`-periodic Hamiltonian and `J_t(x)` a `1`-periodic family of almost complex structures, `C²` on
an open set `W ⊆ ℝ × V` containing `ℝ × K` for a compact `K ⊆ V`, and tamed by `ω` on `ℝ × K`.
Let `u` be `C³` on the half-plane `s > a`, with `1`-periodic loops `t ↦ u(s, t)` in `K`, solving
the Floer equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on `(a, ∞) × [0, 1]` with finite
energy there. Then `du` is bounded on the half-plane `s ≥ b` for every `b > a`. -/
theorem exists_forall_norm_fderiv_le_of_floer (hH : ContDiff ℝ 3 (uncurry H))
    (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {b : ℝ} (hab : a < b) :
    ∃ M, ∀ z : ℝ × ℝ, b ≤ z.1 → ‖fderiv ℝ u z‖ ≤ M := by
  have hfloer' (z : ℝ × ℝ) (hz : z ∈ Ioi a ×ˢ univ) :=
    isComplexLinearMap_perturbedFDeriv_of_periodic hHper hJper hper hfloer hz
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  have heapp (z : ℂ) : e z = (z.re, z.im) := by simp [he]
  -- The solution in the complex coordinate, extended `i`-periodically past the end.
  set v : ℂ → V := fun z ↦ u (z.re, Int.fract z.im) with hv_def
  set S : Set ℂ := {z | a < z.re}
  have hS : IsOpen S := isOpen_lt continuous_const continuous_re
  have hmaps : MapsTo e S (Ioi a ×ˢ univ) := fun z hz ↦ ⟨by rw [heapp]; exact hz, mem_univ _⟩
  have heq : EqOn v (u ∘ e) S := fun z hz ↦ by
    simp only [hv_def, comp_apply, heapp, (hper z.re hz).apply_fract]
  have hderiv (z : ℂ) (hz : z ∈ S) : fderiv ℝ v z = fderiv ℝ (u ∘ e) z :=
    (heq.eventuallyEq_of_mem (hS.mem_nhds hz)).fderiv_eq
  -- The coordinate data `J(z, x) = J_(im z)(x)` and `X(z, x) = X_K(e z, x) ∘ e`.
  set Jc : ℂ × V → V →L[ℝ] V := fun q ↦ (J q.1.im q.2).toLinearMap.toContinuousLinearMap
  set g : ℂ × V → ℝ × V := fun q ↦ (q.1.im, q.2)
  have hg : ContDiff ℝ 2 g := (imCLM.contDiff.comp contDiff_fst).prodMk contDiff_snd
  obtain ⟨hX, hX1, hXI⟩ := contDiff_hamiltonianOneForm_comp_equivRealProdCLM (ω := ω) hH hHper
  -- The energy `∫ ‖∂ₛv‖²` is the energy `∫ ‖∂ₛu‖²`, since `e` preserves volume.
  have hfin : ∫⁻ z in Ioi a ×ℂ Icc 0 1, ‖fderiv ℝ v z 1‖ₑ ^ 2 ≠ ∞ := by
    have hcongr : ∫⁻ z in Ioi a ×ℂ Icc 0 1, ‖fderiv ℝ v z 1‖ₑ ^ 2 =
        ∫⁻ z in measurableEquivRealProd ⁻¹' (Ioi a ×ˢ Icc 0 1),
          ‖fderiv ℝ u (measurableEquivRealProd z) stdComplexLineReal‖ₑ ^ 2 :=
      setLIntegral_congr_fun (measurableSet_Ioi.reProdIm measurableSet_Icc) fun z hz ↦ by
        rw [hderiv z hz.1, fderiv_comp_equivRealProdCLM_one, measurableEquivRealProd_apply, ←
          he, heapp]
    rw [hcongr, Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      measurableEquivRealProd.measurableEmbedding
      (fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ₑ ^ 2)]
    exact setLIntegral_enorm_fderiv_stdComplexLineReal_sq_ne_top hK (hJ.continuousOn.mono hKW)
      hJper hJt huK hfloer hE
  -- The coordinate bound, read back through `e`.
  obtain ⟨M, hM⟩ := Floer.exists_forall_norm_fderiv_le_of_lintegral_ne_top (J := Jc) (W := g ⁻¹' W)
    (hW.preimage hg.continuous) (hJ.comp hg.contDiffOn (mapsTo_preimage g W)) hX.contDiffOn hK
    (fun q hq ↦ hKW ⟨mem_univ _, hq.2⟩) (fun z x _ w ↦ by simp [Jc]) (fun x z ↦ by simp [Jc])
    (fun x z ↦ by simp only [Jc, add_im, I_im, hJper z.im]) hX1 hXI hab
    ((hu.comp e.contDiff.contDiffOn hmaps).congr heq)
    (fun z ↦ by simp [hv_def, Int.fract_add_one])
    (fun z hz ↦ by
      rw [hderiv z hz, heq hz]
      simpa [Jc, heapp] using ω.fderiv_comp_equivRealProdCLM_I_sub (J := fun w x ↦ J w.2 x)
        (hfloer' (e z) (hmaps hz)))
    (fun z hz ↦ by simpa [heq hz, heapp] using huK _ hz z.im) hfin
  refine ⟨M * ‖(e.symm : ℝ × ℝ →L[ℝ] ℂ)‖, fun z hz ↦ ?_⟩
  have hza : z ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨hab.trans_le hz, mem_univ _⟩
  have hre (y : ℝ × ℝ) : (e.symm y).re = y.1 := by simp [he]
  have hev : u =ᶠ[𝓝 z] v ∘ e.symm := by
    filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhds hza] with y hy
    simpa using (heq (x := e.symm y) (by simpa [S, hre] using hy.1)).symm
  rw [hev.fderiv_eq, e.symm.comp_right_fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
    (hM _ (by rwa [hre])) (norm_nonneg _))

/-- **Finite-energy Floer half-cylinders are Lipschitz.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`, the solution `u` is Lipschitz on
the half-plane `s ≥ b` for every `b > a`. -/
theorem exists_lipschitzOnWith_of_floer (hH : ContDiff ℝ 3 (uncurry H))
    (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {b : ℝ} (hab : a < b) :
    ∃ L : ℝ≥0, LipschitzOnWith L u (Ici b ×ˢ univ) := by
  obtain ⟨M, hM⟩ := exists_forall_norm_fderiv_le_of_floer hH hHper hW hJ hJper hK hKW hJt hu hper
    huK hfloer hE hab
  refine ⟨Real.toNNReal M, ((convex_Ici b).prod convex_univ).lipschitzOnWith_of_nnnorm_fderiv_le
    (𝕜 := ℝ) (fun z hz ↦ ?_) (fun z hz ↦ ?_)⟩
  · have hz' : z ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨hab.trans_le hz.1, mem_univ _⟩
    exact (hu.differentiableOn (by norm_num) z hz').differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hz')
  · rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hM z hz.1).trans (Real.le_coe_toNNReal M)

/-- **A finite-energy Floer half-cylinder breaks off an orbit along every sequence.** Under the
hypotheses of `TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`, let `σ_n → ∞`.
There are a subsequence `σ_(φ n)` and a `1`-periodic orbit `x` of the Hamiltonian vector field,
`x' = X_{H_t}(x)`, such that the translates `(s, t) ↦ u(s + σ_(φ n), t)` converge to the
stationary cylinder `(s, t) ↦ x(t)` locally uniformly on `ℝ × ℝ`. -/
theorem exists_subseq_periodic_hasDerivAt_tendstoLocallyUniformly_of_floer
    (hH : ContDiff ℝ 3 (uncurry H))
    (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {σ : ℕ → ℝ} (hσ : Tendsto σ atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℝ → V, Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoLocallyUniformly (fun n z ↦ u (z + (σ (φ n), 0))) (fun z ↦ x z.2) atTop := by
  have hab : a < a + 1 := lt_add_one a
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_of_floer hH hHper hW hJ hJper hK hKW hJt hu hper huK
    hfloer hE hab
  obtain ⟨φ, hφ, g, htr⟩ := exists_subseq_tendstoLocallyUniformly_comp_add hK hL
    (fun z hz ↦ huK _ (hab.trans_le hz.1) _) hσ
  have hσφ : Tendsto (fun n ↦ σ (φ n)) atTop atTop := hσ.comp hφ.tendsto_atTop
  -- The limit is periodic in `t`, since the translates eventually are at each point.
  have hgper (z : ℝ × ℝ) : g (z.1, z.2 + 1) = g z := by
    refine tendsto_nhds_unique ?_ (htr.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))
    refine (htr.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (z.1, z.2 + 1))).congr' ?_
    filter_upwards [hσφ.eventually_gt_atTop (a - z.1)] with n hn
    have hz (y : ℝ × ℝ) : y + (σ (φ n), 0) = (y.1 + σ (φ n), y.2) := by ext <;> simp
    rw [hz, hz]
    exact hper (z.1 + σ (φ n)) (by linarith) z.2
  -- The limit is a stationary cylinder over a Hamiltonian orbit.
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJ.continuousOn.mono hKW) hJper hJt
  have hEU : Ioi a ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ univ := prod_mono le_rfl (subset_univ _)
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hu1 : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ) := hu.of_le (by norm_num)
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  have hJc : ∀ z ∈ Ioi a ×ˢ Icc (0 : ℝ) 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z.2 (u z) v) :=
    fun z hz v ↦ (hcM z.2 _ (huK z.1 hz.1 z.2) v).1
  have hJM : ∀ z ∈ Ioi a ×ˢ Icc (0 : ℝ) 1, ∀ v, ‖J z.2 (u z) v‖ ≤ M * ‖v‖ :=
    fun z hz v ↦ (hcM z.2 _ (huK z.1 hz.1 z.2) v).2
  have hs : Tendsto (fun n ↦ σ (φ n)) atTop (cocompact ℝ) := hσφ.mono_right atTop_le_cocompact
  have hwin (α β : ℝ) : ∀ᶠ n in atTop,
      Icc (α + σ (φ n)) (β + σ (φ n)) ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ Icc 0 1 := by
    filter_upwards [hσφ.eventually_gt_atTop (a - α)] with n hn z hz
    exact ⟨mem_Ioi.2 (by linarith [hz.1.1]), hz.2⟩
  have hv := htr.tendstoLocallyUniformlyOn (s := univ ×ˢ Icc 0 1)
  have hstat := eq_of_tendstoLocallyUniformlyOn_comp_add hU hu1 hEU hc hJc hJM
    hfloer hE hs hwin hv
  have hder := hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add hH1 hU hu1 hEU hc hJc hJM
    hfloer hE hs hwin hv
  set x : ℝ → V := fun t ↦ g (0, t)
  have hxper : Periodic x 1 := fun t ↦ hgper (0, t)
  have hxc : Continuous x := g.continuous.comp (continuous_const.prodMk continuous_id)
  have hgx : (g : ℝ × ℝ → V) = fun z ↦ x z.2 := funext fun z ↦
    calc g z = g (z.1, Int.fract z.2) :=
          (Periodic.apply_fract (f := fun t ↦ g (z.1, t)) (fun t ↦ hgper (z.1, t)) z.2).symm
      _ = x (Int.fract z.2) := hstat z.1 _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
      _ = x z.2 := hxper.apply_fract z.2
  -- `x' = X_{H_t}(x)` on `[0, 1]` and periodicity give the equation on all of `ℝ`.
  set Y : ℝ → V := fun t ↦ ω.hamiltonianVectorField (H t) (x t)
  have hY : Continuous Y :=
    (ω.continuous_uncurry_hamiltonianVectorField hH1).comp (continuous_id.prodMk hxc)
  have hYper : Periodic Y 1 := fun t ↦ by simp only [Y, hHper t, hxper t]
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, x t - x 0 = ∫ τ in 0..t, Y τ := fun t ht ↦
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hxc.continuousOn
      (fun τ hτ ↦ (hder τ ⟨hτ.1.le, hτ.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hτ.1 (hτ.2.trans_le ht.2))) (hY.intervalIntegrable _ _)).symm
  exact ⟨φ, hφ, x, hxper, hasDerivAt_of_periodic_of_sub_eq_integral one_pos hxper hY hYper hint,
    hgx ▸ htr⟩

end TauCeti.SymplecticForm
