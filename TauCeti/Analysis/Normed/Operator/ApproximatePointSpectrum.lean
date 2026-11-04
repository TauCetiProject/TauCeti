/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Approximate-point spectrum of bounded operators

The approximate-point spectrum consists of scalars admitting a sequence of unit vectors
whose eigenvector residuals tend to zero. Equivalently, the shifted operator has no positive
norm lower bound. This distinguishes being bounded below from being surjective, and is useful
for spectral computations on sequence spaces, where approximate eigenvectors need not converge.

We work over either real or complex scalars. No completeness is needed for the definition,
the lower-bound characterization, or the inclusions of eigenvalues and into the spectrum.
Completeness is used for the inclusion of the boundary of the spectrum.

## References

* J. B. Conway, *A Course in Functional Analysis*, second edition, Chapter VII,
  approximate-point spectrum.
-/

public section

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The approximate-point spectrum of a bounded operator: eigenvector residuals tend to zero
along a sequence of unit vectors. In the zero space this set is empty. -/
def approximatePointSpectrum (T : E →L[𝕜] E) : Set 𝕜 :=
  {z | ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
    Tendsto (fun n ↦ T (x n) - z • x n) atTop (𝓝 0)}

/-- Membership expressed by a sequence of unit approximate eigenvectors. -/
theorem mem_approximatePointSpectrum_iff (T : E →L[𝕜] E) (z : 𝕜) :
    z ∈ T.approximatePointSpectrum ↔
      ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
        Tendsto (fun n ↦ T (x n) - z • x n) atTop (𝓝 0) := Iff.rfl

/-- Unit approximate eigenvectors can equivalently be chosen to any prescribed accuracy. -/
theorem mem_approximatePointSpectrum_iff_forall_pos (T : E →L[𝕜] E) (z : 𝕜) :
    z ∈ T.approximatePointSpectrum ↔
      ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖x‖ = 1 ∧ ‖T x - z • x‖ < ε := by
  constructor
  · rintro ⟨x, hx, hlim⟩ ε hε
    have he := (tendsto_order.mp (hlim.norm)).2 ε (by simpa using hε)
    obtain ⟨n, hn⟩ := he.exists
    exact ⟨x n, hx n, by simpa using hn⟩
  · intro h
    choose x hx hres using fun n : ℕ ↦
      h (1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨x, hx, tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
    exact squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (hres n).le)
      (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Outside the approximate-point spectrum, the shifted operator is bounded below.
There is no assertion of surjectivity. -/
theorem not_mem_approximatePointSpectrum_iff (T : E →L[𝕜] E) (z : 𝕜) :
    z ∉ T.approximatePointSpectrum ↔
      ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * ‖x‖ ≤ ‖T x - z • x‖ := by
  rw [mem_approximatePointSpectrum_iff_forall_pos]
  push Not
  constructor
  · rintro ⟨c, hc, hbound⟩
    refine ⟨c, hc, fun x ↦ ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have h := hbound ((‖x‖⁻¹ : 𝕜) • x) (norm_smul_inv_norm hx)
      have hres : ‖T ((‖x‖⁻¹ : 𝕜) • x) - z • ((‖x‖⁻¹ : 𝕜) • x)‖ =
          ‖x‖⁻¹ * ‖T x - z • x‖ := by
        rw [map_smul, smul_comm z, ← smul_sub, norm_smul]
        simp
      rw [hres] at h
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      calc c * ‖x‖ ≤ (‖x‖⁻¹ * ‖T x - z • x‖) * ‖x‖ :=
            mul_le_mul_of_nonneg_right h hxpos.le
        _ = ‖T x - z • x‖ := by field_simp
  · rintro ⟨c, hc, hbound⟩
    exact ⟨c, hc, fun x hx ↦ by simpa only [hx, mul_one] using hbound x⟩

/-- An eigenvalue belongs to the approximate-point spectrum, using the normalized eigenvector
as a constant sequence. -/
theorem mem_approximatePointSpectrum_of_hasEigenvalue (T : E →L[𝕜] E) {z : 𝕜}
    (hz : Module.End.HasEigenvalue T.toLinearMap z) : z ∈ T.approximatePointSpectrum := by
  obtain ⟨x, hx, hx0⟩ := hz.exists_hasEigenvector
  have heig : T x = z • x := (Module.End.mem_eigenspace_iff.mp hx)
  rw [mem_approximatePointSpectrum_iff_forall_pos]
  intro ε hε
  refine ⟨(‖x‖⁻¹ : 𝕜) • x, norm_smul_inv_norm hx0, ?_⟩
  have hres : T ((‖x‖⁻¹ : 𝕜) • x) - z • ((‖x‖⁻¹ : 𝕜) • x) = 0 := by
    rw [map_smul, heig, smul_comm z, sub_self]
  simpa only [hres, norm_zero] using hε

/-- Unit approximate eigenvectors obstruct a bounded inverse. -/
theorem approximatePointSpectrum_subset_spectrum (T : E →L[𝕜] E) :
    T.approximatePointSpectrum ⊆ spectrum 𝕜 T := by
  intro z hz
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  obtain ⟨x, hx, hlim⟩ := hz
  have hleft (y : E) : (↑u⁻¹ : E →L[𝕜] E) ((algebraMap 𝕜 _ z - T) y) = y := by
    rw [← hu, ← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  have hbound (n : ℕ) : 1 ≤ ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖T (x n) - z • x n‖ := by
    have h := (↑u⁻¹ : E →L[𝕜] E).le_opNorm ((algebraMap 𝕜 _ z - T) (x n))
    rw [hleft, hx, sub_apply, algebraMap_apply, norm_sub_rev] at h
    exact h
  have hzero : Tendsto (fun n ↦ ‖(↑u⁻¹ : E →L[𝕜] E)‖ *
      ‖T (x n) - z • x n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul hlim.norm
  have hcontra : (1 : ℝ) ≤ 0 := ge_of_tendsto hzero (Eventually.of_forall hbound)
  norm_num at hcontra

/-- The approximate-point spectrum of an operator on the zero space is empty. -/
@[simp]
theorem approximatePointSpectrum_eq_empty_of_subsingleton [Subsingleton E] (T : E →L[𝕜] E) :
    T.approximatePointSpectrum = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨x, hx, -⟩
  have hzero : x 0 = 0 := Subsingleton.elim _ _
  have h := hx 0
  simp only [hzero, norm_zero, zero_ne_one] at h

/-- The approximate-point spectrum is closed, even for an incomplete space. -/
theorem isClosed_approximatePointSpectrum (T : E →L[𝕜] E) :
    IsClosed T.approximatePointSpectrum := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  rw [mem_approximatePointSpectrum_iff_forall_pos]
  intro ε hε
  obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp hz (ε / 2) (by positivity)
  obtain ⟨x, hx, hres⟩ :=
    (mem_approximatePointSpectrum_iff_forall_pos T w).mp hw (ε / 2) (by positivity)
  refine ⟨x, hx, ?_⟩
  have h := norm_sub_le_norm_sub_add_norm_sub (T x) (w • x) (z • x)
  rw [← sub_smul, norm_smul, norm_sub_rev w z, hx, mul_one] at h
  rw [dist_eq_norm] at hzw
  linarith

/-- Every boundary point of the spectrum admits unit approximate eigenvectors. -/
theorem frontier_spectrum_subset_approximatePointSpectrum [CompleteSpace E]
    (T : E →L[𝕜] E) : frontier (spectrum 𝕜 T) ⊆ T.approximatePointSpectrum := by
  intro z hz
  by_contra hnot
  obtain ⟨c, hc, hbound⟩ := (T.not_mem_approximatePointSpectrum_iff z).mp hnot
  have hzcl : z ∈ closure (spectrum 𝕜 T)ᶜ := by
    rw [closure_compl]
    exact hz.2
  obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp hzcl (c / 4) (by positivity)
  have huw : IsUnit (algebraMap 𝕜 (E →L[𝕜] E) w - T) := by
    have hnotw : w ∉ spectrum 𝕜 T := hw
    simpa only [spectrum.mem_iff, not_not] using hnotw
  obtain ⟨u, hu⟩ := huw
  rw [dist_eq_norm] at hzw
  -- The lower bound at `z` remains at least `c / 2` at the nearby resolvent point `w`.
  have hlow (x : E) : c / 2 * ‖x‖ ≤ ‖(u : E →L[𝕜] E) x‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub (T x) (w • x) (z • x)
    rw [← sub_smul, norm_smul, norm_sub_rev w z] at h
    have hdist := mul_le_mul_of_nonneg_right hzw.le (norm_nonneg x)
    have heq : ‖T x - w • x‖ = ‖(u : E →L[𝕜] E) x‖ := by
      rw [hu, sub_apply, algebraMap_apply, norm_sub_rev]
    rw [heq] at h
    have hb := hbound x
    nlinarith
  have hinv : ‖(↑u⁻¹ : E →L[𝕜] E)‖ ≤ 2 / c := by
    apply opNorm_le_bound _ (by positivity)
    intro y
    have h := hlow ((↑u⁻¹ : E →L[𝕜] E) y)
    have hright : (u : E →L[𝕜] E) ((↑u⁻¹ : E →L[𝕜] E) y) = y := by
      rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
    rw [hright] at h
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith
  -- A Neumann-series perturbation now makes `z` a resolvent point as well.
  let v : E →L[𝕜] E := (u : E →L[𝕜] E) - (algebraMap 𝕜 _ z - T)
  have hv : ‖v‖ ≤ ‖z - w‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    have heq : v x = (w - z) • x := by
      simp only [v, hu, sub_apply, algebraMap_apply, sub_smul]
      abel
    rw [heq, norm_smul, norm_sub_rev]
  have hsmall : ‖(↑u⁻¹ : E →L[𝕜] E) * v‖ < 1 := by
    calc ‖(↑u⁻¹ : E →L[𝕜] E) * v‖ ≤ ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖v‖ := norm_mul_le _ _
      _ ≤ (2 / c) * ‖z - w‖ := mul_le_mul hinv hv (norm_nonneg _) (by positivity)
      _ < 1 := by
        have hpos : 0 < 2 / c := by positivity
        have h := mul_lt_mul_of_pos_left hzw hpos
        have heq : (2 / c) * (c / 4) = 1 / 2 := by field_simp; norm_num
        rw [heq] at h
        linarith
  have hzunit := u.isUnit.mul (isUnit_one_sub_of_norm_lt_one hsmall)
  have heq : (u : E →L[𝕜] E) * (1 - (↑u⁻¹ : E →L[𝕜] E) * v) =
      algebraMap 𝕜 _ z - T := by
    rw [mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
    exact sub_sub_cancel _ _
  rw [heq] at hzunit
  exact (spectrum.mem_iff.mp ((spectrum.isClosed T).frontier_subset hz)) hzunit

end ContinuousLinearMap
