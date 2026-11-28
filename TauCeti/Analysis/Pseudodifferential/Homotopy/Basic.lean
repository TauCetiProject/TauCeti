/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Elliptic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Geometry.Manifold.SmoothApprox
import TauCeti.Analysis.Calculus.ContDiff.Homogeneous
import TauCeti.Topology.MetricSpace.ContinuousRadius

/-!
# Smooth homotopies of elliptic homogeneous symbols

This file smooths homotopies of elliptic symbols. Index arguments produce homotopies
`t ↦ a t` of principal symbols that are only continuous, for instance straight lines through
merely continuous symbols, or the coefficient homotopies of cut-off external products. If such a
homotopy is invertible on the unit sphere for `t ∈ [0, 1]` and joins two smooth homogeneous
symbols `a₀` and `a₁`, then there is a family `b t` of elliptic homogeneous symbols of the same
degree with `b t = a₀` for `t ≤ 0` and `b t = a₁` for `1 ≤ t`, whose coefficient
`(t, x, ξ) ↦ b t (x, ξ)` is jointly smooth at nonzero frequencies and, on the unit sphere, within
any prescribed continuous positive precision of `a (σ t)` for a time change `σ` fixing the ends
(`HomogeneousSymbol.exists_contDiffOn_isElliptic_homotopy`). Joint smoothness is the form in
which such a homotopy can be quantized: every position and frequency derivative of `b t` is
continuous in `(t, x, ξ)` at nonzero frequencies. On `ℝⁿ` this makes `t ↦ b t` a continuous path
in every seminorm of the homogeneous symbols (`HomogeneousSymbol.continuous_of_contDiffOn`).

The proof is a relative Whitney approximation in the open set of invertible operators. After a
reparametrization `σ` that is constant near `t = 0` and `t = 1`, the map
`(t, x, ξ) ↦ χ(2ξ) • a (σ t) (x, ‖ξ‖⁻¹ • ξ)`, where the rescaled frequency cutoff `χ(2ξ)`
vanishes for `‖ξ‖ ≤ 1 / 2` and equals `1` for `‖ξ‖ ≥ 1`, in particular on the unit sphere, is
continuous on the whole space and smooth for `t` near the ends. Mathlib's
`Continuous.exists_contDiff_approx_and_eqOn` (A. Dedecker and P. Massot) approximates it by a
smooth map `g` that is unchanged near the ends, within a continuous positive precision that keeps
`g` invertible on the unit sphere and within the prescribed precision: the minimum of that
precision and of the margin of invertibility (`IsOpen.exists_continuous_forall_dist_lt`
for the open set of invertible operators) plus the distance to the unit sphere. The
homogeneous extensions `b t = HomogeneousSymbol.ofSphere m (g t)` are the required symbols, and
they are elliptic by `HomogeneousSymbol.isElliptic_ofSphere_iff`. No compactness of the positions
is needed, since the precision is allowed to vary from point to point.

## Main declaration

* `TauCeti.HomogeneousSymbol.exists_contDiffOn_isElliptic_homotopy`: a continuous homotopy
  through invertible maps between two smooth homogeneous symbols can be approximated, after a
  time change fixing the ends, by a jointly smooth homotopy of elliptic homogeneous symbols with
  the same endpoints.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 6.21
  (Whitney approximation for functions, relative to a closed set).
* Mathlib, `Mathlib/Geometry/Manifold/SmoothApprox.lean`: the relative approximation theorem with
  a variable precision, used here as the smoothing step.
-/

public section

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Topology

namespace TauCeti

namespace HomogeneousSymbol

variable {X E V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- The continuous map approximated in `exists_contDiffOn_isElliptic_homotopy`: the homotopy `a`,
read on the unit sphere after a time change `σ`, extended to all frequencies by the cutoff
`χ(2ξ)`, which vanishes near the zero frequency. -/
private theorem continuous_cutoff_smul_comp_normalize (χ : FrequencyCutoff E) {σ : ℝ → ℝ}
    (hσ : Continuous σ) (hσ_mem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) {a : ℝ → X × E → V →L[ℂ] W}
    (ha : ContinuousOn (uncurry a) (Icc 0 1 ×ˢ {q : X × E | ‖q.2‖ = 1})) :
    Continuous fun q : (ℝ × X) × E ↦
      χ ((1 / 2 : ℝ)⁻¹ • q.2) • a (σ q.1.1) (q.1.2, ‖q.2‖⁻¹ • q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hq : ‖(1 / 2 : ℝ)⁻¹ • q.2‖ < 1
  · -- Near small frequencies the cutoff vanishes identically.
    exact (continuousAt_const (y := (0 : V →L[ℂ] W))).congr
      (χ.comp_inv_smul_snd_smul_eventuallyEq_zero (1 / 2) _ hq).symm
  · -- Away from the zero frequency, compose `a` with the radial projection and the time change.
    have hq0 : q.2 ≠ 0 := by rintro h; simp [h] at hq
    have hΦ : ContinuousOn (fun q : (ℝ × X) × E ↦ (σ q.1.1, (q.1.2, ‖q.2‖⁻¹ • q.2)))
        {q | q.2 ≠ 0} :=
      ((hσ.comp (continuous_fst.comp continuous_fst)).continuousOn).prodMk
        ((continuous_snd.comp continuous_fst).continuousOn.prodMk
          ((continuous_snd.norm.continuousOn.inv₀ fun q hq ↦ norm_ne_zero_iff.mpr hq).smul
            continuous_snd.continuousOn))
    have hmaps : MapsTo (fun q : (ℝ × X) × E ↦ (σ q.1.1, (q.1.2, ‖q.2‖⁻¹ • q.2)))
        {q | q.2 ≠ 0} (Icc 0 1 ×ˢ {q : X × E | ‖q.2‖ = 1}) := fun q hq ↦
      ⟨hσ_mem _, by simpa using norm_smul_inv_norm (𝕜 := ℝ) (show q.2 ≠ 0 from hq)⟩
    exact ((χ.contDiff_comp_inv_smul_snd (1 / 2)).continuous.continuousAt).smul
      ((ha.comp hΦ hmaps).continuousAt
        ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hq0))

/-- A time change `σ : ℝ → [0, 1]`, equal to `0` before `1 / 3` and to `1` after `2 / 3`. -/
private theorem exists_timeChange : ∃ σ : ℝ → ℝ, Continuous σ ∧ (∀ t, σ t ∈ Icc (0 : ℝ) 1) ∧
    (∀ t < 1 / 3, σ t = 0) ∧ ∀ t, 2 / 3 < t → σ t = 1 :=
  ⟨fun t ↦ projIcc (0 : ℝ) 1 zero_le_one (3 * t - 1),
    continuous_subtypeVal.comp (continuous_projIcc.comp (by fun_prop)), fun _ ↦ Subtype.prop _,
    fun t ht ↦ by simp [projIcc_of_le_left _ (show 3 * t - 1 ≤ 0 by linarith)],
    fun t ht ↦ by simp [projIcc_of_right_le _ (show 1 ≤ 3 * t - 1 by linarith)]⟩

/-- If the time change `σ` is `0` before `1 / 3` and `1` after `2 / 3`, and `a 0`, `a 1` agree on
the unit sphere with homogeneous symbols `a₀`, `a₁`, then the map of
`continuous_cutoff_smul_comp_normalize` is smooth at times before `1 / 3` and after `2 / 3`. -/
private theorem contDiffOn_cutoff_smul_comp_normalize (χ : FrequencyCutoff E) {σ : ℝ → ℝ}
    (hσ₀ : ∀ t < 1 / 3, σ t = 0) (hσ₁ : ∀ t, 2 / 3 < t → σ t = 1) {a : ℝ → X × E → V →L[ℂ] W}
    (a₀ a₁ : HomogeneousSymbol X E V W m)
    (ha₀ : ∀ x ξ, ‖ξ‖ = 1 → a 0 (x, ξ) = a₀.coefficient (x, ξ))
    (ha₁ : ∀ x ξ, ‖ξ‖ = 1 → a 1 (x, ξ) = a₁.coefficient (x, ξ)) :
    ContDiffOn ℝ ∞ (fun q : (ℝ × X) × E ↦
      χ ((1 / 2 : ℝ)⁻¹ • q.2) • a (σ q.1.1) (q.1.2, ‖q.2‖⁻¹ • q.2))
      ({q | q.1.1 < 1 / 3} ∪ {q | 2 / 3 < q.1.1}) := by
  -- Where `σ = s` and `a s = c` on the sphere, the map is the cut-off term of the degree `0`
  -- symbol `(t, x, ξ) ↦ c (x, ‖ξ‖⁻¹ • ξ)`, which is smooth.
  have key (c : HomogeneousSymbol X E V W m) (s : ℝ)
      (hs : ∀ x ξ, ‖ξ‖ = 1 → a s (x, ξ) = c.coefficient (x, ξ)) {T : Set ((ℝ × X) × E)}
      (hT : ∀ q ∈ T, σ q.1.1 = s) (hTo : IsOpen T) {q} (hq : q ∈ T) :
      ContDiffWithinAt ℝ ∞ (fun q : (ℝ × X) × E ↦
        χ ((1 / 2 : ℝ)⁻¹ • q.2) • a (σ q.1.1) (q.1.2, ‖q.2‖⁻¹ • q.2))
        ({q | q.1.1 < 1 / 3} ∪ {q | 2 / 3 < q.1.1}) q := by
    set c' := (ofSphere 0 c.coefficient c.contDiffOn_coefficient).compPosition
      (Prod.snd : ℝ × X → X) contDiff_snd
    have hEq : EqOn (fun q : (ℝ × X) × E ↦
        χ ((1 / 2 : ℝ)⁻¹ • q.2) • a (σ q.1.1) (q.1.2, ‖q.2‖⁻¹ • q.2))
        (fun q ↦ χ ((1 / 2 : ℝ)⁻¹ • q.2) • c'.coefficient q) T := fun q hq ↦ by
      rcases eq_or_ne q.2 0 with h0 | h0
      · simp [h0, χ.apply_zero]
      · simp only [hT q hq, hs _ _ (by simpa using norm_smul_inv_norm (𝕜 := ℝ) h0), c',
          coefficient_compPosition, coefficient_ofSphere_of_ne_zero _ _ h0, Real.rpow_zero,
          one_smul]
    exact ((c'.contDiff_comp_inv_smul_snd_smul_coefficient χ (1 / 2)).contDiffAt
      |>.congr_of_eventuallyEq (eventuallyEq_of_mem (hTo.mem_nhds hq) hEq)).contDiffWithinAt
  rintro q (hq | hq)
  · exact key a₀ 0 ha₀ (fun q hq ↦ hσ₀ _ hq)
      (isOpen_lt (continuous_fst.comp continuous_fst) continuous_const) hq
  · exact key a₁ 1 ha₁ (fun q hq ↦ hσ₁ _ hq)
      (isOpen_lt continuous_const (continuous_fst.comp continuous_fst)) hq

/-- The two ends `{t ≤ 1 / 4} ∪ {3 / 4 ≤ t}` of the time interval, where the approximation in
`exists_contDiffOn_isElliptic_homotopy` is unchanged, form a closed set, and the set
`{t < 1 / 3} ∪ {2 / 3 < t}` where the time change of `exists_timeChange` is constant is a
neighbourhood of it. -/
private theorem isClosed_ends_and_mem_nhdsSet {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] :
    IsClosed ({q : (ℝ × Y) × Z | q.1.1 ≤ 1 / 4} ∪ {q | 3 / 4 ≤ q.1.1}) ∧
      {q : (ℝ × Y) × Z | q.1.1 < 1 / 3} ∪ {q | 2 / 3 < q.1.1} ∈
        𝓝ˢ ({q : (ℝ × Y) × Z | q.1.1 ≤ 1 / 4} ∪ {q | 3 / 4 ≤ q.1.1}) :=
  ⟨(isClosed_le (continuous_fst.comp continuous_fst) continuous_const).union
      (isClosed_le continuous_const (continuous_fst.comp continuous_fst)),
    ((isOpen_lt (continuous_fst.comp continuous_fst) continuous_const).union
      (isOpen_lt continuous_const (continuous_fst.comp continuous_fst))).mem_nhdsSet.mpr
      (union_subset_union (fun q (hq : q.1.1 ≤ 1 / 4) ↦ (show q.1.1 < 1 / 3 by linarith))
        fun q (hq : 3 / 4 ≤ q.1.1) ↦ (show 2 / 3 < q.1.1 by linarith))⟩

/-- **Smoothing a homotopy of elliptic symbols.** Let `a t`, `t ∈ [0, 1]`, be maps that depend
continuously on `(t, x, ξ)` and are invertible on the unit sphere of frequencies, joining two
homogeneous symbols `a₀` and `a₁` of degree `m` there, and let `δ` be a continuous positive
precision. Then there are a continuous time change `σ : ℝ → [0, 1]`, equal to `0` for `t ≤ 0` and to
`1` for `1 ≤ t`, and elliptic homogeneous symbols `b t` of degree `m` for all `t`, with `b t = a₀`
for `t ≤ 0` and `b t = a₁` for `1 ≤ t`, whose coefficient is jointly smooth in `(t, x, ξ)` at
nonzero frequencies and is within `δ (t, x, ξ)` of `a (σ t) (x, ξ)` on the unit sphere.

Only the values of `a t` on the unit sphere are used, so homotopies of homogeneous maps need only be
checked there. Continuity is required on `[0, 1]` only, and the endpoints are matched exactly. -/
theorem exists_contDiffOn_isElliptic_homotopy [FiniteDimensional ℝ X] [FiniteDimensional ℝ E]
    [CompleteSpace V] (a₀ a₁ : HomogeneousSymbol X E V W m) {a : ℝ → X × E → V →L[ℂ] W}
    (ha : ContinuousOn (uncurry a) (Icc 0 1 ×ˢ {q : X × E | ‖q.2‖ = 1}))
    (ha_inv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ξ, ‖ξ‖ = 1 → (a t (x, ξ)).IsInvertible)
    (ha₀ : ∀ x ξ, ‖ξ‖ = 1 → a 0 (x, ξ) = a₀.coefficient (x, ξ))
    (ha₁ : ∀ x ξ, ‖ξ‖ = 1 → a 1 (x, ξ) = a₁.coefficient (x, ξ)) {δ : ℝ × X × E → ℝ}
    (hδ : Continuous δ) (hδ_pos : ∀ p, 0 < δ p) :
    ∃ (σ : ℝ → ℝ) (b : ℝ → HomogeneousSymbol X E V W m),
      Continuous σ ∧ (∀ t, σ t ∈ Icc (0 : ℝ) 1) ∧ (∀ t ≤ 0, σ t = 0) ∧ (∀ t, 1 ≤ t → σ t = 1) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × X × E ↦ (b p.1).coefficient p.2) {p | p.2.2 ≠ 0} ∧
      (∀ t, (b t).IsElliptic) ∧ (∀ t ≤ 0, b t = a₀) ∧ (∀ t, 1 ≤ t → b t = a₁) ∧
      ∀ t x ξ, ‖ξ‖ = 1 → dist ((b t).coefficient (x, ξ)) (a (σ t) (x, ξ)) < δ (t, x, ξ) := by
  -- A time change `σ`, constant near `0` and near `1`, and a frequency cutoff `χ`, with `χ(2ξ)`
  -- vanishing for `‖ξ‖ ≤ 1 / 2` and equal to `1` on the unit sphere.
  obtain ⟨σ, hσ_cont, hσ_mem, hσ₀, hσ₁⟩ := exists_timeChange
  let χ : FrequencyCutoff E := .ofContDiffBump ⟨1, 2, one_pos, one_lt_two⟩ le_rfl le_rfl
  -- The continuous map `G` to approximate, on `(ℝ × X) × E`; on the unit sphere it is `a (σ t)`.
  set G : (ℝ × X) × E → V →L[ℂ] W :=
    fun q ↦ χ ((1 / 2 : ℝ)⁻¹ • q.2) • a (σ q.1.1) (q.1.2, ‖q.2‖⁻¹ • q.2) with hG_def
  have hG_cont : Continuous G := continuous_cutoff_smul_comp_normalize χ hσ_cont hσ_mem ha
  have hG_sphere {q : (ℝ × X) × E} (hq : ‖q.2‖ = 1) : G q = a (σ q.1.1) (q.1.2, q.2) := by
    simp only [hG_def, χ.apply_inv_smul_eq_one (t := 1 / 2) (by norm_num) (by rw [hq]; norm_num),
      hq, inv_one, one_smul]
  -- `G` is smooth near the two ends `S` of the time interval, where `σ` is constant.
  obtain ⟨hS, hSU⟩ := isClosed_ends_and_mem_nhdsSet (Y := X) (Z := E)
  -- Approximate `G`, unchanged on `S`, within a precision keeping it invertible on the sphere:
  -- the margin of invertibility of `G`, plus the distance to the sphere to make it positive,
  -- and at most `δ`.
  obtain ⟨ε, hε_cont, hε₀, hε_pos, hε_inv⟩ :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.exists_continuous_forall_dist_lt hG_cont
  obtain ⟨g, hg, hgG, hgS, -⟩ := hG_cont.exists_contDiff_approx_and_eqOn ⊤
    ((hε_cont.add (continuous_snd.norm.sub continuous_const).abs).min
      (hδ.comp (by fun_prop : Continuous fun q : (ℝ × X) × E ↦ (q.1.1, q.1.2, q.2))))
    (fun q ↦ lt_min (by
      rcases eq_or_ne ‖q.2‖ 1 with hq | hq
      · exact add_pos_of_pos_of_nonneg (hε_pos q (show (G q).IsInvertible by
          simpa only [hG_sphere hq] using ha_inv _ (hσ_mem _) _ _ hq)) (abs_nonneg _)
      · exact add_pos_of_nonneg_of_pos (hε₀ q) (abs_pos.mpr (sub_ne_zero.mpr hq))) (hδ_pos _))
    hS hSU (contDiffOn_cutoff_smul_comp_normalize χ hσ₀ hσ₁ a₀ a₁ ha₀ ha₁)
  -- The homogeneous extensions of the time slices of `g`.
  have hg_slice (t : ℝ) : ContDiffOn ℝ ∞ (fun p : X × E ↦ g ((t, p.1), p.2)) {p | p.2 ≠ 0} :=
    (hg.comp (by fun_prop : ContDiff ℝ ∞ fun p : X × E ↦ ((t, p.1), p.2))).contDiffOn
  refine ⟨σ, fun t ↦ ofSphere m (fun p ↦ g ((t, p.1), p.2)) (hg_slice t), hσ_cont, hσ_mem,
    fun t ht ↦ hσ₀ t (by linarith), fun t ht ↦ hσ₁ t (by linarith), ?_, fun t ↦ ?_,
    fun t ht ↦ ?_, fun t ht ↦ ?_, fun t x ξ hξ ↦ ?_⟩
  · -- Joint smoothness, transported from `(ℝ × X) × E` along the reassociation.
    refine ((hg.contDiffOn.norm_rpow_smul_comp_normalize m).comp_continuousLinearMap
      (ContinuousLinearEquiv.prodAssoc ℝ ℝ X E).symm.toContinuousLinearMap).congr ?_
    rintro ⟨t, x, ξ⟩ (hξ : ξ ≠ 0)
    simp [coefficient_ofSphere_of_ne_zero _ _ hξ, ContinuousLinearEquiv.prodAssoc_symm_apply]
  · exact (isElliptic_ofSphere_iff _).mpr fun x ξ hξ ↦
      hε_inv ((t, x), ξ) _ (by simpa [hξ] using (lt_min_iff.mp (hgG ((t, x), ξ))).1)
  · refine (ofSphere_congr _ _ fun x ξ hξ ↦ ?_).trans (ofSphere_coefficient a₀)
    rw [hgS (Or.inl (show t ≤ 1 / 4 by linarith)), hG_sphere (q := ((t, x), ξ)) hξ,
      hσ₀ _ (by linarith), ha₀ x ξ hξ]
  · refine (ofSphere_congr _ _ fun x ξ hξ ↦ ?_).trans (ofSphere_coefficient a₁)
    rw [hgS (Or.inr (show 3 / 4 ≤ t by linarith)), hG_sphere (q := ((t, x), ξ)) hξ,
      hσ₁ _ (by linarith), ha₁ x ξ hξ]
  · -- On the unit sphere `b t` is the time slice of `g`, and `G` is `a (σ t)`.
    have h := (lt_min_iff.mp (hgG ((t, x), ξ))).2
    rwa [hG_sphere (q := ((t, x), ξ)) hξ, ← coefficient_ofSphere_of_norm_eq_one (m := m) _
      (hg_slice t) hξ] at h

end HomogeneousSymbol

end TauCeti
