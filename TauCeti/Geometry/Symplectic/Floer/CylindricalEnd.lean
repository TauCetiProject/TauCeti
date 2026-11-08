/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
import Mathlib.Analysis.Complex.Convex
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Complex.ReProdIm
import TauCeti.MeasureTheory.Integral.Lebesgue.ReProdIm

/-!
# Bounded derivatives of finite-energy Floer solutions on cylindrical ends

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

The uniform Lipschitz bound makes the translates `u(· + σ)`, `σ → ∞`, equicontinuous with values in
`K`. This is the input from which the Arzelà–Ascoli theorem produces the locally uniformly
convergent translates whose limits `TauCeti.Geometry.Symplectic.Floer.Breaking` identifies as
Hamiltonian orbits. That extraction, and any decay of `∂ₛu` along the end, are not carried out
here.

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
