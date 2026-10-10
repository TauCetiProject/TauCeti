/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

/-!
# Small-energy interior compactness for pseudoholomorphic curves

For a `C²` almost complex structure on a neighbourhood of a compact set `K`, curves with image
in `K` and sufficiently small energy have a common Lipschitz bound on the concentric half disk.
Consequently every sequence of such curves has a uniformly convergent subsequence there. The
limit takes values in `K` and is Lipschitz. No differentiability or pseudoholomorphicity of the
limit is asserted: these require elliptic regularity.

The energy used here is `∫ ‖∂ₛu‖²`, with `∂ₛu = fderiv ℝ u z 1`. The equation
`∂ₜu = J(u) ∂ₛu` controls the other derivative. Integrability on the outer open disk is explicit,
so a nonintegrable energy density cannot acquire the Bochner integral's junk value zero.
The energy threshold is independent of the disk's centre and radius. The common Lipschitz
constant may depend on the radius but not on the centre or the curve.

This is the local compactness input away from energy concentration in bubbling arguments.
It combines the energy-density mean-value estimate in
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue` with Mathlib's Arzelà–Ascoli theorem.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Sections 4.3 and 4.6.
-/

public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology
open scoped NNReal BoundedContinuousFunction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {J : V → V →L[ℝ] V} {W K : Set V}

/-- Small-energy pseudoholomorphic curves with image in a fixed compact set share a Lipschitz
bound on the concentric half disk. The energy threshold is uniform in the centre and radius;
the Lipschitz constant is uniform in the centre and may depend on the radius. -/
theorem exists_pos_forall_lipschitzOnWith_of_small_energy
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ (r : ℝ), 0 < r → ∃ C : ℝ≥0, ∀ (z₀ : ℂ) (u : ℂ → V),
      ContDiffOn ℝ 3 u (ball z₀ r) →
      (∀ z ∈ ball z₀ r, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) →
      MapsTo u (ball z₀ r) K →
      IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ r) →
      (∫ z in ball z₀ r, ‖fderiv ℝ u z 1‖ ^ 2) < δ →
      LipschitzOnWith C u (closedBall z₀ (r / 2)) := by
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
      hW hJ hK hKW hJsq
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  refine ⟨δ, hδ, fun r hr ↦ ?_⟩
  let B := 1 + 8 * δ / (Real.pi * (r / 4) ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C : ℝ≥0 := ⟨(1 + max a 0) * B, by positivity⟩
  have hCcoe : (C : ℝ) = (1 + max a 0) * B := rfl
  refine ⟨C, fun z₀ u hu hCR huK hInt hE ↦ ?_⟩
  have hinner : closedBall z₀ (r / 2) ⊆ ball z₀ r :=
    closedBall_subset_ball (by linarith)
  have hDu : ContinuousOn (fderiv ℝ u) (ball z₀ r) :=
    (hu.fderiv_of_isOpen isOpen_ball (m := 2) (by norm_num)).continuousOn
  -- Apply the mean-value estimate on disks of radius `r / 4` around each interior point.
  -- Their energy is bounded by the outer disk's energy, using integrability and nonnegativity.
  have hbound : ∀ z ∈ closedBall z₀ (r / 2), ‖fderiv ℝ u z 1‖ ≤ B := by
    intro z hz
    have hsub : closedBall z (r / 4) ⊆ ball z₀ r :=
      closedBall_subset_ball' (by
        have := mem_closedBall.mp hz
        linarith)
    have hsub' : ball z (r / 4) ⊆ ball z₀ r := ball_subset_closedBall.trans hsub
    have hmono := setIntegral_mono_set hInt
      (Eventually.of_forall (fun z ↦ sq_nonneg ‖fderiv ℝ u z 1‖))
      (Eventually.of_forall hsub')
    have h := hmean (by positivity : 0 ≤ r / 4) (hu.mono hsub')
      ((hDu.mono hsub).clm_apply continuousOn_const) (fun y hy ↦ hCR y (hsub' hy))
      (fun y hy ↦ huK (hsub' hy)) (hmono.trans_lt hE)
    have hp : 0 < Real.pi * (r / 4) ^ 2 := by positivity
    have hsq : ‖fderiv ℝ u z 1‖ ^ 2 ≤ 8 * δ / (Real.pi * (r / 4) ^ 2) := by
      rw [le_div_iff₀ hp]
      nlinarith
    have hq : 0 ≤ 8 * δ / (Real.pi * (r / 4) ^ 2) := by positivity
    dsimp [B]
    nlinarith [sq_nonneg (‖fderiv ℝ u z 1‖ - 1)]
  -- The Cauchy--Riemann equation converts the real-direction estimate into an operator bound.
  have hop : ∀ z ∈ closedBall z₀ (r / 2), ‖fderiv ℝ u z‖ ≤ (C : ℝ) := by
    intro z hz
    have hreal := hbound z hz
    have himag : ‖fderiv ℝ u z I‖ ≤ max a 0 * B := by
      rw [hCR z (hinner hz)]
      exact ((J (u z)).le_opNorm _).trans (by
        gcongr
        exact (ha _ (huK (hinner hz))).trans (le_max_left _ _))
    refine ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg fun w ↦ ?_
    have hw : w = w.re • (1 : ℂ) + w.im • I := by simp [Complex.real_smul, Complex.re_add_im]
    calc
      ‖fderiv ℝ u z w‖ = ‖w.re • fderiv ℝ u z 1 + w.im • fderiv ℝ u z I‖ := by
        conv_lhs => rw [hw]
        rw [map_add, map_smul, map_smul]
      _ ≤ |w.re| * ‖fderiv ℝ u z 1‖ + |w.im| * ‖fderiv ℝ u z I‖ := by
        simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
          (w.re • fderiv ℝ u z 1) (w.im • fderiv ℝ u z I)
      _ ≤ ‖w‖ * B + ‖w‖ * (max a 0 * B) := by
        gcongr
        · exact Complex.abs_re_le_norm w
        · exact Complex.abs_im_le_norm w
      _ = (C : ℝ) * ‖w‖ := by rw [hCcoe]; ring
  exact (convex_closedBall z₀ (r / 2)).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun z hz ↦ (hu.contDiffAt (isOpen_ball.mem_nhds (hinner hz))).differentiableAt
      (by norm_num))
    (fun z hz ↦ by exact_mod_cast hop z hz)

/-- Every sequence of small-energy pseudoholomorphic curves with image in a compact set has a
subsequence converging uniformly on the concentric half disk to a Lipschitz map into that set.
The energy threshold is uniform in the centre and radius; the limit's Lipschitz constant is
uniform in the centre and sequence and may depend on the radius. The almost complex structure
may vary with the target point. -/
theorem exists_pos_forall_tendstoUniformlyOn_subseq_of_small_energy
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ (r : ℝ), 0 < r → ∃ C : ℝ≥0, ∀ (z₀ : ℂ) (u : ℕ → ℂ → V),
      (∀ n, ContDiffOn ℝ 3 (u n) (ball z₀ r)) →
      (∀ n z, z ∈ ball z₀ r → fderiv ℝ (u n) z I = J (u n z) (fderiv ℝ (u n) z 1)) →
      (∀ n, MapsTo (u n) (ball z₀ r) K) →
      (∀ n, IntegrableOn (fun z ↦ ‖fderiv ℝ (u n) z 1‖ ^ 2) (ball z₀ r)) →
      (∀ n, (∫ z in ball z₀ r, ‖fderiv ℝ (u n) z 1‖ ^ 2) < δ) →
      ∃ (v : ℂ → V) (φ : ℕ → ℕ), StrictMono φ ∧
        LipschitzOnWith C v (closedBall z₀ (r / 2)) ∧
        MapsTo v (closedBall z₀ (r / 2)) K ∧
        TendstoUniformlyOn (fun n ↦ u (φ n)) v atTop (closedBall z₀ (r / 2)) := by
  classical
  obtain ⟨δ, hδ, hLip⟩ := exists_pos_forall_lipschitzOnWith_of_small_energy hW hJ hK hKW hJsq
  refine ⟨δ, hδ, fun r hr ↦ ?_⟩
  obtain ⟨C, hC⟩ := hLip r hr
  refine ⟨C, fun z₀ u hu hCR huK hInt hE ↦ ?_⟩
  let D := closedBall z₀ (r / 2)
  have hD : D ⊆ ball z₀ r := closedBall_subset_ball (by linarith)
  have hL : ∀ n, LipschitzOnWith C (u n) D :=
    fun n ↦ hC z₀ (u n) (hu n) (hCR n) (huK n) (hInt n) (hE n)
  let U : ℕ → D →ᵇ V := fun n ↦ BoundedContinuousFunction.mkOfCompact
    ⟨D.domRestrict (u n), (hL n).continuousOn.domRestrict⟩
  let A : Set (D →ᵇ V) := {f | LipschitzWith C f ∧ ∀ z, f z ∈ K}
  have hclosed : IsClosed A := by
    have h₁ : IsClosed {f : D →ᵇ V | LipschitzWith C (f : D → V)} :=
      (isClosed_setOfPred_lipschitzWith (α := D) (β := V) C).preimage
        BoundedContinuousFunction.continuous_coe
    have h₂ : IsClosed {f : D →ᵇ V | ∀ z, f z ∈ K} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun z ↦ hK.isClosed.preimage
        ((continuous_apply z).comp BoundedContinuousFunction.continuous_coe)
    exact h₁.inter h₂
  have hcompact : IsCompact A := BoundedContinuousFunction.arzela_ascoli₂ K hK A hclosed
    (fun f z hf ↦ hf.2 z)
    ((LipschitzWith.uniformEquicontinuous (fun f : A ↦ (f.1 : D → V)) C
      (fun f ↦ f.2.1)).equicontinuous)
  obtain ⟨v, hv, φ, hφ, hconv⟩ := hcompact.tendsto_subseq (x := U)
    (fun n ↦ ⟨(lipschitzOnWith_iff_restrict.mp (hL n)), fun z ↦ huK n (hD z.2)⟩)
  -- Extend the limit off the disk only to express uniform convergence on a subset of `ℂ`.
  let v' : ℂ → V := fun z ↦ if hz : z ∈ D then v ⟨z, hz⟩ else 0
  have hv' : D.domRestrict v' = v := by funext z; simp [v', Set.domRestrict]
  refine ⟨v', φ, hφ, ?_, ?_, ?_⟩
  · rw [lipschitzOnWith_iff_restrict, hv']
    exact hv.1
  · intro z hz
    have hzD : z ∈ D := hz
    simpa only [v', dite_eq_left hzD] using hv.2 ⟨z, hzD⟩
  · rw [tendstoUniformlyOn_iff_restrict, hv']
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv

end TauCeti
