/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.Analysis.Normed.Lp.Diagonal

/-!
# The spectrum of a bounded diagonal operator

A bounded coefficient family `d` on a sequence space defines the diagonal operator
`lp.diagonalCLM d` on `ℓ^p(ι, 𝕜)`. Its spectrum is the closure of the range of `d`: the
spectral values of a diagonal operator are the coefficients themselves together with their
limit points.

Consequently every nonempty compact subset `K` of `ℂ` is the spectrum of a bounded operator on
`ℓ²(ℕ, ℂ)`, namely the diagonal operator attached to a sequence dense in `K`.

* `lp.spectrum_diagonalCLM`: the spectrum of `lp.diagonalCLM d` is `closure (Set.range d)`.
* `lp.mem_spectrum_diagonalCLM_iff`: the membership form of that statement.
* `TauCeti.exists_spectrum_diagonalCLM_eq_of_isCompact`: every nonempty compact subset of `ℂ`
  is the spectrum of a bounded diagonal operator on `ℓ²(ℕ, ℂ)`.

## References

* The diagonal-operator spectrum is the standard worked example of a resolvent: at a scalar
  outside the coefficient range the inverse is the diagonal operator of the reciprocal
  coefficients.
* The compact-realisation step chooses its dense sequence with Mathlib's
  `IsCompact.exists_countable_dense_subset` and `Set.Countable.exists_eq_range`, and uses
  `lp.diagonalCLM` from `TauCeti.Analysis.Normed.Lp.Diagonal`.
-/

public section

open scoped lp ENNReal NNReal Topology
open Filter

namespace lp

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The pointwise action of `algebraMap 𝕜 _ c - diagonalCLM d` multiplies the `j`-th coordinate
by `c - d j`. -/
private lemma sub_algebraMap_diagonalCLM_apply (d : ℓ^∞(ι, 𝕜)) (c : 𝕜) (y : ℓ^p(ι, 𝕜))
    (j : ι) :
    ((algebraMap 𝕜 (ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜)) c - diagonalCLM (p := p) d) y) j =
      (c - d j) * y j := by
  simp only [sub_apply, ContinuousLinearMap.algebraMap_apply, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, diagonalCLM_apply]
  ring

/-- A scalar outside the closure of the coefficient range has positive distance to it, so the
reciprocal coefficients are bounded and give a two-sided inverse of
`algebraMap 𝕜 _ c - diagonalCLM d`. -/
private lemma isUnit_algebraMap_sub_diagonalCLM (d : ℓ^∞(ι, 𝕜)) {c : 𝕜}
    (hc : c ∉ closure (Set.range d)) :
    IsUnit (algebraMap 𝕜 (ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜)) c - diagonalCLM (p := p) d) := by
  classical
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ ‖c - d i‖ := by
    obtain ⟨δ, hδ0, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl c hc
    refine ⟨δ, hδ0, fun i => ?_⟩
    have hmem : d i ∈ closure (Set.range d) := subset_closure ⟨i, rfl⟩
    have hgt : ¬ dist (d i) c < δ := fun h => hball h hmem
    rw [dist_eq_norm, norm_sub_rev] at hgt
    exact not_lt.mp hgt
  have hne : ∀ i, c - d i ≠ 0 := fun i h => by
    have h2 : δ ≤ 0 := by simpa [h] using hδ i
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℓ^∞(ι, 𝕜), ∀ i, e i = (c - d i)⁻¹ := by
    refine ⟨⟨fun i => (c - d i)⁻¹, memℓp_infty ⟨δ⁻¹, ?_⟩⟩, fun i => rfl⟩
    rintro - ⟨i, rfl⟩
    simp only [norm_inv]
    exact inv_anti₀ hδ0 (hδ i)
  refine isUnit_iff_exists.mpr ⟨diagonalCLM e, ?_, ?_⟩
  · ext x j
    simp only [mul_apply_eq_comp, one_apply_eq_self, sub_algebraMap_diagonalCLM_apply,
      diagonalCLM_apply, he j]
    rw [← mul_assoc, mul_inv_cancel₀ (hne j), one_mul]
  · ext x j
    simp only [mul_apply_eq_comp, one_apply_eq_self, sub_algebraMap_diagonalCLM_apply,
      diagonalCLM_apply, he j]
    rw [← mul_assoc, inv_mul_cancel₀ (hne j), one_mul]

/-- A scalar in the closure of the coefficient range is not a unit of the algebra after
subtracting the diagonal operator: an attained coefficient gives an eigenvector, and an
unattained one gives unit approximate eigenvectors, so `algebraMap 𝕜 _ c - diagonalCLM d` has no
left inverse. -/
private lemma not_isUnit_algebraMap_sub_diagonalCLM_of_mem_closure (d : ℓ^∞(ι, 𝕜)) {c : 𝕜}
    (hc : c ∈ closure (Set.range d)) :
    ¬ IsUnit (algebraMap 𝕜 (ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜)) c - diagonalCLM (p := p) d) := by
  classical
  have hp : 0 < p := zero_lt_one.trans_le (Fact.out : 1 ≤ p)
  intro h
  obtain ⟨g, hg⟩ := h.exists_left_inv
  have hgu : ∀ y, g ((algebraMap 𝕜 (ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜)) c -
      diagonalCLM (p := p) d) y) = y := by
    intro y
    rw [← mul_apply_eq_comp, hg, one_apply_eq_self]
  by_cases hmem : c ∈ Set.range d
  · -- an attained coefficient gives a nontrivial kernel vector
    obtain ⟨i, hi⟩ := hmem
    have hker : (algebraMap 𝕜 (ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜)) c -
        diagonalCLM (p := p) d) (lp.single (E := fun _ : ι => 𝕜) p i 1) = 0 := by
      ext j
      rw [sub_algebraMap_diagonalCLM_apply, lp.single_apply]
      by_cases hj : j = i
      · subst hj
        simp [hi]
      · simp [hj]
    have hsingle : lp.single (E := fun _ : ι => 𝕜) p i (1 : 𝕜) ≠ 0 := by
      intro h0
      have h1 : ‖lp.single (E := fun _ : ι => 𝕜) p i (1 : 𝕜)‖ = 1 := by
        rw [lp.norm_single hp, norm_one]
      rw [h0] at h1
      simp at h1
    have hzero : lp.single (E := fun _ : ι => 𝕜) p i (1 : 𝕜) = 0 := by
      have h := hgu (lp.single (E := fun _ : ι => 𝕜) p i 1)
      rw [hker, g.map_zero] at h
      exact h.symm
    exact hsingle hzero
  · -- an unattained point of the closure is a limit of unit approximate eigenvectors
    have hlim : ∀ k : ℕ, ∃ i, ‖c - d i‖ < 1 / ((k : ℝ) + 1) := by
      intro k
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc (1 / ((k : ℝ) + 1)) hpos
      obtain ⟨i, hi⟩ := hy
      exact ⟨i, by rw [hi, ← dist_eq_norm]; exact hdist⟩
    choose n hn using hlim
    have hnorm : Tendsto (fun k => ‖c - d (n k)‖) atTop (𝓝 0) := by
      refine squeeze_zero (f := fun k => ‖c - d (n k)‖)
        (g := fun k => 1 / ((k : ℝ) + 1)) (fun k => norm_nonneg _) (fun k => (hn k).le) ?_
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hxe : ∀ k, (algebraMap 𝕜 (ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜)) c -
        diagonalCLM (p := p) d) (lp.single (E := fun _ : ι => 𝕜) p (n k) 1) =
          lp.single (E := fun _ : ι => 𝕜) p (n k) (c - d (n k)) := by
      intro k
      ext j
      rw [sub_algebraMap_diagonalCLM_apply, lp.single_apply, lp.single_apply]
      by_cases hj : j = n k
      · subst hj
        simp
      · simp [hj]
    have hbound : ∀ k, (1 : ℝ) ≤ ‖g‖ * ‖c - d (n k)‖ := by
      intro k
      have hle := g.le_opNorm ((algebraMap 𝕜 (ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜)) c -
        diagonalCLM (p := p) d) (lp.single (E := fun _ : ι => 𝕜) p (n k) 1))
      rw [hgu (lp.single (E := fun _ : ι => 𝕜) p (n k) 1), hxe k, lp.norm_single hp,
        lp.norm_single hp, norm_one] at hle
      exact hle
    have hcontra : (1 : ℝ) ≤ 0 := by
      refine ge_of_tendsto (x := atTop) ?_ (Eventually.of_forall hbound)
      simpa using tendsto_const_nhds.mul hnorm
    linarith

/-- A scalar lies in the spectrum of a bounded diagonal operator exactly when it lies in the
closure of the set of coefficients. -/
theorem mem_spectrum_diagonalCLM_iff (d : ℓ^∞(ι, 𝕜)) (c : 𝕜) :
    c ∈ spectrum 𝕜 (diagonalCLM (p := p) d) ↔ c ∈ closure (Set.range d) := by
  rw [spectrum.mem_iff]
  exact ⟨fun h => by_contra fun hc => h (isUnit_algebraMap_sub_diagonalCLM d hc),
    not_isUnit_algebraMap_sub_diagonalCLM_of_mem_closure d⟩

/-- The spectrum of a bounded diagonal operator is the closure of its coefficient range. -/
@[simp]
theorem spectrum_diagonalCLM (d : ℓ^∞(ι, 𝕜)) :
    spectrum 𝕜 (diagonalCLM (p := p) d) = closure (Set.range d) :=
  Set.ext fun _ => mem_spectrum_diagonalCLM_iff d _

end lp

namespace TauCeti

/-- Every nonempty compact subset of `ℂ` is the spectrum of a bounded diagonal operator on
`ℓ²(ℕ, ℂ)`. -/
theorem exists_spectrum_diagonalCLM_eq_of_isCompact {K : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) :
    ∃ d : ℓ^∞(ℕ, ℂ), spectrum ℂ (lp.diagonalCLM (p := 2) d) = K := by
  classical
  -- a countable set dense in `K`
  obtain ⟨t, htK, htc, hKt⟩ := hK.exists_countable_dense_subset
  have htne : t.Nonempty := by
    rcases Set.eq_empty_or_nonempty t with h | h
    · rw [h] at hKt
      simp only [closure_empty, Set.subset_empty_iff] at hKt
      exact (hne.ne_empty hKt).elim
    · exact h
  obtain ⟨f, rfl⟩ := htc.exists_eq_range htne
  have hcl : closure (Set.range f) = K := by
    refine le_antisymm ?_ hKt
    rw [← hK.isClosed.closure_eq]
    exact closure_mono htK
  -- the dense sequence is bounded, so it is an element of `ℓ^∞`
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hmem : Memℓp f ∞ := memℓp_infty ⟨r, fun y hy => by
    obtain ⟨k, rfl⟩ := hy
    simpa [dist_eq_norm] using hr (htK ⟨k, rfl⟩)⟩
  refine ⟨⟨f, hmem⟩, ?_⟩
  rw [lp.spectrum_diagonalCLM]
  exact hcl

end TauCeti
