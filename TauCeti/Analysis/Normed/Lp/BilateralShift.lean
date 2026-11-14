/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Spectrum
public import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# The bilateral shift on `ℓᵖ(ℤ, G)` and its spectrum

The **bilateral shift** `lp.bilateralShift p 𝕜 G` on `ℓᵖ(ℤ, G)` (`1 ≤ p ≤ ∞`) is the linear
isometric equivalence induced by `n ↦ n + 1` on `ℤ`: it shifts single-coordinate vectors forward,
`e_n ↦ e_{n + 1}`, and acts on sequences by `(S f)_n = f_{n - 1}`.

Over any nontrivially normed field `𝕜` and any nontrivial Banach space `G` over `𝕜`, the spectrum
of the bilateral shift as a bounded linear operator on `ℓᵖ(ℤ, G)` is the full unit sphere
`Metric.sphere 0 1` (`lp.spectrum_bilateralShift`):

* Since both `S` and `S⁻¹` have operator norm at most `1`, every spectral value `z` satisfies
  `‖z‖ ≤ 1` and `‖z⁻¹‖ ≤ 1`, hence `‖z‖ = 1`.
* Conversely, let `‖z‖ = 1` and choose a nonzero vector `v ∈ G`. For `p = ∞`, the bounded sequence
  `n ↦ z ^ (-n) • v` is an eigenvector of `S` with eigenvalue `z`. For `1 ≤ p < ∞`, the truncated
  Weyl sums `w_N = ∑_{0 ≤ k ≤ N} e_k(z ^ (-k) • v)` satisfy `‖w_N‖ ^ p = (N + 1) ‖v‖ ^ p` while
  `(z • 1 - S) w_N` telescopes to two boundary terms of bounded norm `≤ 2 ‖v‖`, obstructing a
  bounded inverse of `z • 1 - S`.

For `p = 2` and `𝕜 = ℂ`, this exhibits a unitary operator on `ℓ²(ℤ, G)` whose spectrum is the
entire complex unit circle, so no branch cut in `ℂ` avoids its spectrum.

## References

* J. B. Conway, *A Course in Functional Analysis*, second edition, Chapter VII, Example 3.5.
-/

public section

open ContinuousLinearMap Metric
open scoped ENNReal

namespace lp

section Definition

variable (p : ℝ≥0∞) (𝕜 G : Type*) [NormedRing 𝕜] [NormedAddCommGroup G] [Module 𝕜 G]
  [IsBoundedSMul 𝕜 G] [Fact (1 ≤ p)]

/-- The **bilateral shift** on `ℓᵖ(ℤ, G)`, defined by reindexing along `n ↦ n + 1`: it sends a
single-coordinate vector at `n` to `n + 1` and evaluates as `(S f) n = f (n - 1)`. -/
def bilateralShift : lp (fun _ : ℤ ↦ G) p ≃ₗᵢ[𝕜] lp (fun _ : ℤ ↦ G) p :=
  lp.congrLeft p 𝕜 G (Equiv.addRight (1 : ℤ))

variable {p 𝕜 G}

/-- Evaluating the bilateral shift at `n` reads the coordinate `n - 1`. -/
@[simp]
theorem bilateralShift_apply (f : lp (fun _ : ℤ ↦ G) p) (n : ℤ) :
    bilateralShift p 𝕜 G f n = f (n - 1) := by
  simp [bilateralShift, sub_eq_add_neg]

/-- Evaluating the inverse bilateral shift at `n` reads the coordinate `n + 1`. -/
@[simp]
theorem bilateralShift_symm_apply (f : lp (fun _ : ℤ ↦ G) p) (n : ℤ) :
    (bilateralShift p 𝕜 G).symm f n = f (n + 1) := by
  simp [bilateralShift]

/-- The bilateral shift moves a single-coordinate vector from `n` to `n + 1`. -/
@[simp]
theorem bilateralShift_single (n : ℤ) (v : G) :
    bilateralShift p 𝕜 G (lp.single p n v) = lp.single p (n + 1) v :=
  lp.congrLeft_single (Equiv.addRight (1 : ℤ)) n v

/-- The inverse bilateral shift moves a single-coordinate vector from `n` to `n - 1`. -/
@[simp]
theorem bilateralShift_symm_single (n : ℤ) (v : G) :
    (bilateralShift p 𝕜 G).symm (lp.single p n v) = lp.single p (n - 1) v := by
  rw [bilateralShift, lp.congrLeft_symm]
  exact lp.congrLeft_single (Equiv.addRight (1 : ℤ)).symm n v

end Definition

section Spectrum

variable {p : ℝ≥0∞} {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- On a subsingleton fiber `G`, the spectrum of the bilateral shift is empty. -/
@[simp]
theorem spectrum_bilateralShift_of_subsingleton [Subsingleton G] [Fact (1 ≤ p)] :
    spectrum 𝕜 (bilateralShift p 𝕜 G : lp (fun _ : ℤ ↦ G) p →L[𝕜] lp (fun _ : ℤ ↦ G) p) = ∅ := by
  have : Subsingleton (lp (fun _ : ℤ ↦ G) p) :=
    ⟨fun f g ↦ lp.ext <| funext fun n ↦ Subsingleton.elim (f n) (g n)⟩
  exact spectrum.of_subsingleton _

private theorem not_isUnit_sub_bilateralShift_top [Nontrivial G] {z : 𝕜} (hz : ‖z‖ = 1) :
    ¬ IsUnit (z • (1 : lp (fun _ : ℤ ↦ G) ∞ →L[𝕜] lp (fun _ : ℤ ↦ G) ∞) -
      bilateralShift ∞ 𝕜 G) := by
  let S : lp (fun _ : ℤ ↦ G) ∞ →L[𝕜] lp (fun _ : ℤ ↦ G) ∞ := bilateralShift ∞ 𝕜 G
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (by simp [hz])
  obtain ⟨v, hv⟩ := exists_ne (0 : G)
  rintro ⟨u, hu⟩
  let Uinv : lp (fun _ : ℤ ↦ G) ∞ →L[𝕜] lp (fun _ : ℤ ↦ G) ∞ := ↑u⁻¹
  have hmem : Memℓp (fun n : ℤ ↦ (z ^ (-n)) • v) ∞ :=
    memℓp_infty ⟨‖v‖, by rintro _ ⟨n, rfl⟩; simp [norm_smul, hz]⟩
  let x : lp (fun _ : ℤ ↦ G) ∞ := ⟨fun n ↦ (z ^ (-n)) • v, hmem⟩
  have hsub : (z • 1 - S) x = 0 := by
    ext n
    simp only [S, sub_apply, smul_apply, one_apply_eq_self, LinearIsometryEquiv.coe_coe'',
      bilateralShift_apply, lp.coeFn_sub, lp.coeFn_smul, lp.coeFn_zero, Pi.sub_apply,
      Pi.smul_apply, Pi.zero_apply, x, smul_smul]
    have hpow : z * z ^ (-n) = z ^ (-(n - 1)) := by
      rw [← zpow_one_add₀ hz0]
      congr 1
      ring
    rw [hpow, sub_self]
  have hx0 : x = 0 := by
    have hmul : Uinv * u.val = 1 := u.inv_val
    calc x = (Uinv * u.val) x := by rw [hmul, one_apply_eq_self]
      _ = Uinv ((z • 1 - S) x) := by rw [hu]; rfl
      _ = 0 := by rw [hsub, map_zero]
  exact hv (by simpa [x] using congr($hx0 0))

private theorem not_isUnit_sub_bilateralShift_of_ne_top [Nontrivial G] [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {z : 𝕜} (hz : ‖z‖ = 1) :
    ¬ IsUnit (z • (1 : lp (fun _ : ℤ ↦ G) p →L[𝕜] lp (fun _ : ℤ ↦ G) p) -
      bilateralShift p 𝕜 G) := by
  let S : lp (fun _ : ℤ ↦ G) p →L[𝕜] lp (fun _ : ℤ ↦ G) p := bilateralShift p 𝕜 G
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (by simp [hz])
  have hp_pos : 0 < p := zero_lt_one.trans_le Fact.out
  have hp_real : 0 < p.toReal := ENNReal.toReal_pos hp_pos.ne' hp_top
  obtain ⟨v, hv⟩ := exists_ne (0 : G)
  let f : ℕ → lp (fun _ : ℤ ↦ G) p := fun k ↦ lp.single p (k : ℤ) ((z ^ (-(k : ℤ))) • v)
  have hf_norm (k : ℕ) : ‖f k‖ = ‖v‖ := by simp [f, lp.norm_single hp_pos, norm_smul, hz]
  have hf_step (k : ℕ) : (z • 1 - S) (f k) = z • (f k - f (k + 1)) := by
    have hS : S (f k) = lp.single p ((k : ℤ) + 1) ((z ^ (-(k : ℤ))) • v) :=
      bilateralShift_single (k : ℤ) _
    have hzf : z • f (k + 1) = S (f k) := by
      rw [hS]
      ext n
      simp only [f, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_ite,
        smul_zero, smul_smul, Nat.cast_add, Nat.cast_one]
      have hpow : z * z ^ (-((k : ℤ) + 1)) = z ^ (-(k : ℤ)) := by
        rw [← zpow_one_add₀ hz0]
        congr 1
        ring
      rw [hpow]
    rw [sub_apply, smul_apply, one_apply_eq_self, smul_sub, hzf]
  rintro ⟨u, hu⟩
  let Uinv : lp (fun _ : ℤ ↦ G) p →L[𝕜] lp (fun _ : ℤ ↦ G) p := ↑u⁻¹
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖Uinv‖ * (2 * ‖v‖)) ^ p.toReal / ‖v‖ ^ p.toReal)
  let w : lp (fun _ : ℤ ↦ G) p := ∑ k ∈ Finset.range (N + 1), f k
  have hw_norm : ‖w‖ ^ p.toReal = (N + 1 : ℝ) * ‖v‖ ^ p.toReal := by
    have hw_eq : w = ∑ m ∈ (Finset.range (N + 1)).map ⟨Int.ofNat, Nat.cast_injective⟩,
        lp.single p m ((z ^ (-m)) • v) := by simp [w, f]
    rw [hw_eq, lp.norm_sum_single hp_real, Finset.sum_map]
    simp [norm_smul, hz]
  have hres : ‖(z • 1 - S) w‖ ≤ 2 * ‖v‖ := by
    have htele : (z • 1 - S) w = z • (f 0 - f (N + 1)) := by
      simp only [w, map_sum, hf_step, ← Finset.smul_sum, Finset.sum_range_sub']
    rw [htele, norm_smul, hz, one_mul]
    exact (norm_sub_le _ _).trans_eq (by rw [hf_norm, hf_norm]; ring)
  have hw_le : ‖w‖ ≤ ‖Uinv‖ * (2 * ‖v‖) := by
    have hUinv : Uinv ((z • 1 - S) w) = w := by
      have hmul : Uinv * u.val = 1 := u.inv_val
      calc Uinv ((z • 1 - S) w) = (Uinv * u.val) w := by rw [hu]; rfl
        _ = w := by rw [hmul, one_apply_eq_self]
    exact (congrArg norm hUinv).symm.trans_le ((Uinv.le_opNorm _).trans (by gcongr))
  have hle : (N + 1 : ℝ) * ‖v‖ ^ p.toReal ≤ (‖Uinv‖ * (2 * ‖v‖)) ^ p.toReal :=
    hw_norm ▸ Real.rpow_le_rpow (norm_nonneg w) hw_le hp_real.le
  exact hN.not_ge <| (by linarith : (N : ℝ) ≤ N + 1).trans <|
    (le_div_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.2 hv) _)).2 hle

/-- **Spectrum of the bilateral shift.** For `1 ≤ p ≤ ∞` and any nontrivial Banach space `G` over a
nontrivially normed field `𝕜`, the spectrum of `lp.bilateralShift p 𝕜 G` on `ℓᵖ(ℤ, G)` is the unit
sphere `Metric.sphere 0 1`. -/
theorem spectrum_bilateralShift [CompleteSpace G] [Nontrivial G] [Fact (1 ≤ p)] :
    spectrum 𝕜 (bilateralShift p 𝕜 G : lp (fun _ : ℤ ↦ G) p →L[𝕜] lp (fun _ : ℤ ↦ G) p) =
      Metric.sphere 0 1 := by
  refine Set.Subset.antisymm (bilateralShift p 𝕜 G).spectrum_subset_sphere fun z hz ↦ ?_
  rw [mem_sphere_zero_iff_norm] at hz
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  rcases eq_or_ne p ∞ with rfl | hp_top
  · exact not_isUnit_sub_bilateralShift_top hz
  · exact not_isUnit_sub_bilateralShift_of_ne_top hp_top hz

end Spectrum

end lp
