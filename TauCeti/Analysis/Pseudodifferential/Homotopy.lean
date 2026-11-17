/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Elliptic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Smooth homotopies of elliptic homogeneous symbols

A homogeneous symbol of degree `m` is determined by its values on the unit sphere of
frequencies. Conversely, every map `g` smooth off the zero frequency extends from the sphere to
the homogeneous symbol `HomogeneousSymbol.ofSphere m g`, equal to `‖ξ‖ ^ m • g (x, ‖ξ‖⁻¹ • ξ)` at
`ξ ≠ 0`. It is elliptic exactly when `g` is invertible on the sphere
(`HomogeneousSymbol.isElliptic_ofSphere_iff`), and every homogeneous symbol is the extension of
its own coefficient (`HomogeneousSymbol.ofSphere_coefficient`).

The main result smooths homotopies of elliptic symbols. Index arguments produce homotopies
`t ↦ a t` of principal symbols that are only continuous, for instance straight lines through
merely continuous symbols, or the coefficient homotopies of cut-off external products. If such a
homotopy is invertible on the unit sphere for `t ∈ [0, 1]` and joins two smooth homogeneous
symbols `a₀` and `a₁`, then there is a family `b t` of elliptic homogeneous symbols of the same
degree with `b t = a₀` for `t ≤ 0` and `b t = a₁` for `1 ≤ t`, whose coefficient
`(t, x, ξ) ↦ b t (x, ξ)` is jointly smooth at nonzero frequencies
(`HomogeneousSymbol.exists_contDiffOn_isElliptic_homotopy`). Joint smoothness is the form in
which such a homotopy can be quantized: every position and frequency derivative of `b t` is
continuous in `(t, x, ξ)` at nonzero frequencies.

The proof is a relative Whitney approximation in the open set of invertible operators. After a
reparametrization `σ` that is constant near `t = 0` and `t = 1`, the map
`(t, x, ξ) ↦ χ(2ξ) • a (σ t) (x, ‖ξ‖⁻¹ • ξ)`, with a frequency cutoff `χ` vanishing near `ξ = 0`
and equal to `1` on the unit sphere, is continuous on the whole space and smooth for `t` near the
ends. Mathlib's `Continuous.exists_contDiff_approx_and_eqOn` (A. Dedecker and P. Massot)
approximates it by a smooth map `g` that is unchanged near the ends, within a continuous positive
precision that keeps `g` invertible on the unit sphere: the distance from the value to the closed
set of non-invertible operators. The homogeneous extensions `b t = ofSphere m (g t)` are the
required symbols. No compactness of the positions is needed, since the precision is allowed to
vary from point to point.

## Main declarations

* `TauCeti.HomogeneousSymbol.contDiffOn_norm_rpow_smul_comp_normalize`: the formula of the
  homogeneous extension is smooth off the zero frequency.
* `TauCeti.HomogeneousSymbol.ofSphere`: the homogeneous symbol of degree `m` extending a map from
  the unit sphere of frequencies, with `coefficient_ofSphere`,
  `coefficient_ofSphere_of_norm_eq_one`, `ofSphere_congr` and `ofSphere_coefficient`.
* `TauCeti.HomogeneousSymbol.isElliptic_ofSphere_iff`: the extension is elliptic exactly when the
  map is invertible on the unit sphere.
* `TauCeti.HomogeneousSymbol.exists_contDiffOn_isElliptic_homotopy`: a continuous homotopy
  through invertible maps between two smooth homogeneous symbols can be replaced by a jointly
  smooth homotopy of elliptic homogeneous symbols with the same endpoints.

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

/-! ### Homogeneous extension from the unit sphere -/

section Extension

variable {Y F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The formula `(y, ξ) ↦ ‖ξ‖ ^ m • g (y, ‖ξ‖⁻¹ • ξ)` of the homogeneous extension of degree `m`
from the unit sphere of frequencies is smooth off the zero frequency when `g` is. -/
theorem contDiffOn_norm_rpow_smul_comp_normalize {g : Y × E → F}
    (hg : ContDiffOn ℝ ∞ g {q | q.2 ≠ 0}) (m : ℝ) :
    ContDiffOn ℝ ∞ (fun q : Y × E ↦ ‖q.2‖ ^ m • g (q.1, ‖q.2‖⁻¹ • q.2)) {q | q.2 ≠ 0} := by
  intro q hq
  have hq' : q.2 ≠ 0 := hq
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq'
  have hnorm : ContDiffAt ℝ ∞ (fun q : Y × E ↦ ‖q.2‖) q :=
    (contDiffAt_norm ℝ hq').comp q contDiffAt_snd
  -- The radial projection stays off the zero frequency, where `g` is smooth.
  have hmem : (q.1, ‖q.2‖⁻¹ • q.2) ∈ {q : Y × E | q.2 ≠ 0} := smul_ne_zero (inv_ne_zero hn) hq'
  have hg' := (hg.contDiffAt ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hmem)).comp
    q (contDiffAt_fst.prodMk ((hnorm.inv hn).smul contDiffAt_snd))
  exact ((hnorm.rpow_const_of_ne (p := m) hn).smul hg').contDiffWithinAt

end Extension

variable (m) in
/-- The homogeneous symbol of degree `m` that agrees with `g` on the unit sphere of frequencies:
its value at `ξ ≠ 0` is `‖ξ‖ ^ m • g (x, ‖ξ‖⁻¹ • ξ)`. Only the values of `g` on the unit sphere
matter (`HomogeneousSymbol.ofSphere_congr`); smoothness off the zero frequency is assumed so that
the extension is smooth. -/
def ofSphere (g : X × E → V →L[ℂ] W) (hg : ContDiffOn ℝ ∞ g {p | p.2 ≠ 0}) :
    HomogeneousSymbol X E V W m :=
  mk' (fun p ↦ ‖p.2‖ ^ m • g (p.1, ‖p.2‖⁻¹ • p.2)) (contDiffOn_norm_rpow_smul_comp_normalize hg m)
    fun x ξ _ t ht ↦ by
      have hdir : (t * ‖ξ‖)⁻¹ • (t • ξ) = ‖ξ‖⁻¹ • ξ := by
        rw [smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
      simp only [norm_smul, Real.norm_of_nonneg ht.le, hdir, Real.mul_rpow ht.le (norm_nonneg ξ),
        mul_smul]

@[simp]
theorem coefficient_ofSphere (g : X × E → V →L[ℂ] W) (hg : ContDiffOn ℝ ∞ g {p | p.2 ≠ 0})
    {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (ofSphere m g hg).coefficient (x, ξ) = ‖ξ‖ ^ m • g (x, ‖ξ‖⁻¹ • ξ) :=
  coefficient_mk'_of_ne_zero _ _ _ hξ

/-- On the unit sphere of frequencies the homogeneous extension of `g` is `g`. -/
theorem coefficient_ofSphere_of_norm_eq_one (g : X × E → V →L[ℂ] W)
    (hg : ContDiffOn ℝ ∞ g {p | p.2 ≠ 0}) {x : X} {ξ : E} (hξ : ‖ξ‖ = 1) :
    (ofSphere m g hg).coefficient (x, ξ) = g (x, ξ) := by
  rw [coefficient_ofSphere g hg (norm_ne_zero_iff.mp (hξ ▸ one_ne_zero)), hξ]
  simp

/-- The homogeneous extension only depends on the values on the unit sphere. -/
theorem ofSphere_congr {g g' : X × E → V →L[ℂ] W} (hg : ContDiffOn ℝ ∞ g {p | p.2 ≠ 0})
    (hg' : ContDiffOn ℝ ∞ g' {p | p.2 ≠ 0}) (h : ∀ x ξ, ‖ξ‖ = 1 → g (x, ξ) = g' (x, ξ)) :
    ofSphere m g hg = ofSphere m g' hg' :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [coefficient_ofSphere g hg hξ, coefficient_ofSphere g' hg' hξ,
      h x _ (by simpa using norm_smul_inv_norm (𝕜 := ℝ) hξ)]

/-- A homogeneous symbol is the homogeneous extension of its values on the unit sphere. -/
@[simp]
theorem ofSphere_coefficient (a : HomogeneousSymbol X E V W m) :
    ofSphere m a.coefficient a.contDiffOn_coefficient = a :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    rw [coefficient_ofSphere _ _ hξ, a.homogeneous x ξ _ (inv_pos.mpr hn), smul_smul,
      ← Real.mul_rpow hn.le (inv_pos.mpr hn).le, mul_inv_cancel₀ hn.ne', Real.one_rpow, one_smul]

/-- The homogeneous extension of `g` is elliptic exactly when `g` is invertible on the unit sphere
of frequencies. -/
theorem isElliptic_ofSphere_iff {g : X × E → V →L[ℂ] W} (hg : ContDiffOn ℝ ∞ g {p | p.2 ≠ 0}) :
    (ofSphere m g hg).IsElliptic ↔ ∀ x ξ, ‖ξ‖ = 1 → (g (x, ξ)).IsInvertible := by
  rw [isElliptic_iff]
  refine ⟨fun h x ξ hξ ↦ ?_, fun h x ξ hξ ↦ ?_⟩
  · simpa [coefficient_ofSphere_of_norm_eq_one g hg hξ] using
      h x ξ (norm_ne_zero_iff.mp (hξ ▸ one_ne_zero))
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    rw [coefficient_ofSphere g hg hξ, ← Complex.coe_smul,
      ContinuousLinearMap.isInvertible_smul_iff (by exact_mod_cast (Real.rpow_pos_of_pos hn m).ne')]
    exact h x _ (by simpa using norm_smul_inv_norm (𝕜 := ℝ) hξ)

/-! ### Smoothing homotopies of elliptic symbols -/

section Homotopy

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
    continuous_subtype_val.comp (continuous_projIcc.comp (by fun_prop)), fun _ ↦ Subtype.prop _,
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
          coefficient_compPosition, coefficient_ofSphere _ _ h0, Real.rpow_zero, one_smul]
    exact ((c'.contDiff_comp_inv_smul_snd_smul_coefficient χ (1 / 2)).contDiffAt
      |>.congr_of_eventuallyEq (eventuallyEq_of_mem (hTo.mem_nhds hq) hEq)).contDiffWithinAt
  rintro q (hq | hq)
  · exact key a₀ 0 ha₀ (fun q hq ↦ hσ₀ _ hq)
      (isOpen_lt (continuous_fst.comp continuous_fst) continuous_const) hq
  · exact key a₁ 1 ha₁ (fun q hq ↦ hσ₁ _ hq)
      (isOpen_lt continuous_const (continuous_fst.comp continuous_fst)) hq

omit [InnerProductSpace ℝ E] in
/-- A continuous map into the operators that is invertible on the unit sphere of frequencies has a
continuous positive precision `ε`: every operator within `ε` of it at a point of the unit sphere
is invertible. -/
private theorem exists_continuous_pos_isInvertible_of_dist_lt [CompleteSpace V] {Z : Type*}
    [TopologicalSpace Z] {G : Z × E → V →L[ℂ] W} (hG : Continuous G)
    (hinv : ∀ q : Z × E, ‖q.2‖ = 1 → (G q).IsInvertible) :
    ∃ ε : Z × E → ℝ, Continuous ε ∧ (∀ q, 0 < ε q) ∧
      ∀ q : Z × E, ‖q.2‖ = 1 → ∀ T : V →L[ℂ] W, dist T (G q) < ε q → T.IsInvertible := by
  classical
  -- The distance to the closed set of non-invertible operators, plus the distance to the sphere.
  set N : Set (V →L[ℂ] W) := {T | ¬T.IsInvertible}
  have hN : IsClosed N := ContinuousLinearMap.isOpen_setOfPred_isInvertible.isClosed_compl
  refine ⟨fun q ↦ (if N.Nonempty then infDist (G q) N else 1) + |‖q.2‖ - 1|, ?_, fun q ↦ ?_,
    fun q hq T hT ↦ ?_⟩
  · refine Continuous.add ?_ (continuous_snd.norm.sub continuous_const).abs
    split_ifs
    · exact (continuous_infDist_pt N).comp hG
    · exact continuous_const
  · rcases eq_or_ne ‖q.2‖ 1 with hq | hq
    · have h1 : 0 < if N.Nonempty then infDist (G q) N else 1 := by
        split_ifs with hne
        · exact (hN.notMem_iff_infDist_pos hne).mp fun h ↦ h (hinv q hq)
        · exact one_pos
      simpa [hq] using h1
    · have h1 : 0 ≤ if N.Nonempty then infDist (G q) N else 1 := by
        split_ifs
        · exact infDist_nonneg
        · exact zero_le_one
      exact add_pos_of_nonneg_of_pos h1 (abs_pos.mpr (sub_ne_zero.mpr hq))
  · by_contra hTN
    have hne : N.Nonempty := ⟨T, hTN⟩
    have hlt : dist T (G q) < infDist (G q) N := by simpa [hne, hq] using hT
    exact (infDist_le_dist_of_mem hTN).not_gt (by rwa [dist_comm] at hlt)

/-- **Smoothing a homotopy of elliptic symbols.** Let `a t`, `t ∈ [0, 1]`, be maps that depend
continuously on `(t, x, ξ)` and are invertible on the unit sphere of frequencies, joining two
homogeneous symbols `a₀` and `a₁` of degree `m` there. Then there are elliptic homogeneous symbols
`b t` of degree `m` for all `t`, with `b t = a₀` for `t ≤ 0` and `b t = a₁` for `1 ≤ t`, whose
coefficient is jointly smooth in `(t, x, ξ)` at nonzero frequencies.

Only the values of `a t` on the unit sphere are used, so homotopies of homogeneous maps need only be
checked there. Continuity is required on `[0, 1]` only, and the endpoints are matched exactly. -/
theorem exists_contDiffOn_isElliptic_homotopy [FiniteDimensional ℝ X] [FiniteDimensional ℝ E]
    [CompleteSpace V] (a₀ a₁ : HomogeneousSymbol X E V W m) {a : ℝ → X × E → V →L[ℂ] W}
    (ha : ContinuousOn (uncurry a) (Icc 0 1 ×ˢ {q : X × E | ‖q.2‖ = 1}))
    (ha_inv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ξ, ‖ξ‖ = 1 → (a t (x, ξ)).IsInvertible)
    (ha₀ : ∀ x ξ, ‖ξ‖ = 1 → a 0 (x, ξ) = a₀.coefficient (x, ξ))
    (ha₁ : ∀ x ξ, ‖ξ‖ = 1 → a 1 (x, ξ) = a₁.coefficient (x, ξ)) :
    ∃ b : ℝ → HomogeneousSymbol X E V W m,
      ContDiffOn ℝ ∞ (fun p : ℝ × X × E ↦ (b p.1).coefficient p.2) {p | p.2.2 ≠ 0} ∧
      (∀ t, (b t).IsElliptic) ∧ (∀ t ≤ 0, b t = a₀) ∧ ∀ t, 1 ≤ t → b t = a₁ := by
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
  set S : Set ((ℝ × X) × E) := {q | q.1.1 ≤ 1 / 4} ∪ {q | 3 / 4 ≤ q.1.1}
  have hS : IsClosed S :=
    (isClosed_le (continuous_fst.comp continuous_fst) continuous_const).union
      (isClosed_le continuous_const (continuous_fst.comp continuous_fst))
  have hSU : {q : (ℝ × X) × E | q.1.1 < 1 / 3} ∪ {q | 2 / 3 < q.1.1} ∈ 𝓝ˢ S :=
    ((isOpen_lt (continuous_fst.comp continuous_fst) continuous_const).union
      (isOpen_lt continuous_const (continuous_fst.comp continuous_fst))).mem_nhdsSet.mpr
      (union_subset_union (fun q (hq : q.1.1 ≤ 1 / 4) ↦ (show q.1.1 < 1 / 3 by linarith))
        fun q (hq : 3 / 4 ≤ q.1.1) ↦ (show 2 / 3 < q.1.1 by linarith))
  -- Approximate `G`, unchanged on `S`, within a precision keeping it invertible on the sphere.
  obtain ⟨ε, hε_cont, hε_pos, hε_inv⟩ := exists_continuous_pos_isInvertible_of_dist_lt hG_cont
    fun q hq ↦ by simpa only [hG_sphere hq] using ha_inv _ (hσ_mem _) _ _ hq
  obtain ⟨g, hg, hgG, hgS, -⟩ := hG_cont.exists_contDiff_approx_and_eqOn ⊤ hε_cont hε_pos hS hSU
    (contDiffOn_cutoff_smul_comp_normalize χ hσ₀ hσ₁ a₀ a₁ ha₀ ha₁)
  -- The homogeneous extensions of the time slices of `g`.
  have hg_slice (t : ℝ) : ContDiffOn ℝ ∞ (fun p : X × E ↦ g ((t, p.1), p.2)) {p | p.2 ≠ 0} :=
    (hg.comp (by fun_prop : ContDiff ℝ ∞ fun p : X × E ↦ ((t, p.1), p.2))).contDiffOn
  refine ⟨fun t ↦ ofSphere m (fun p ↦ g ((t, p.1), p.2)) (hg_slice t), ?_, fun t ↦ ?_,
    fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · -- Joint smoothness, transported from `(ℝ × X) × E` along the reassociation.
    have h := (contDiffOn_norm_rpow_smul_comp_normalize hg.contDiffOn m).comp_continuousLinearMap
      (ContinuousLinearEquiv.prodAssoc ℝ ℝ X E).symm.toContinuousLinearMap
    refine h.congr fun p (hp : p.2.2 ≠ 0) ↦ ?_
    simp only [coefficient_ofSphere _ _ hp]
    rfl
  · rw [isElliptic_ofSphere_iff]
    intro x ξ hξ
    exact hε_inv ((t, x), ξ) hξ _ (hgG _)
  · rw [← ofSphere_coefficient a₀]
    refine ofSphere_congr _ _ fun x ξ hξ ↦ ?_
    rw [hgS (Or.inl (show t ≤ 1 / 4 by linarith)), hG_sphere (q := ((t, x), ξ)) hξ,
      hσ₀ _ (by linarith), ha₀ x ξ hξ]
  · rw [← ofSphere_coefficient a₁]
    refine ofSphere_congr _ _ fun x ξ hξ ↦ ?_
    rw [hgS (Or.inr (show 3 / 4 ≤ t by linarith)), hG_sphere (q := ((t, x), ξ)) hξ,
      hσ₁ _ (by linarith), ha₁ x ξ hξ]

end Homotopy

end HomogeneousSymbol

end TauCeti
