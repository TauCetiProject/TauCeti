/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quasiregular.Euclidean
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.InnerProductSpace.Radial.Stretch
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow

/-!
# Quasiregularity of the radial stretch

Let `E` be a finite-dimensional real inner product space of dimension `n`. For `a > 0` the
**radial stretch** `x ↦ ‖x‖ ^ (a - 1) • x` is continuous, smooth away from the origin, and its
classical derivative, taken away from the origin, is a weak derivative on every open set
(`TauCeti.hasWeakFDerivOn_norm_rpow_smul_self`), with `‖Du‖ⁿ = O(‖x‖ ^ (n (a - 1)))` locally
integrable since `n (a - 1) > -n`. With the pointwise distortion of the radial stretch
(`TauCeti/Analysis/InnerProductSpace/Radial/Stretch.lean`), it is a Euclidean quasiregular map of
every open set (`TauCeti.IsQuasiregularOn`), with sharp constant:

* for `a ≥ 1` it is `a ^ (n - 1)`-quasiregular
  (`TauCeti.isQuasiregularOn_norm_rpow_smul_self_of_one_le`), and on a nonempty open set for no
  smaller constant (`TauCeti.pow_le_of_isQuasiregularOn_norm_rpow_smul_self`);
* for `0 < a ≤ 1` it is `a⁻¹`-quasiregular
  (`TauCeti.isQuasiregularOn_norm_rpow_smul_self_of_le_one`), and when `n ≥ 2`, on a nonempty open
  set, for no smaller constant (`TauCeti.inv_le_of_isQuasiregularOn_norm_rpow_smul_self`). In
  dimension one the derivative `a |t| ^ (a - 1)` is its own determinant, so the map is
  `1`-quasiregular for every `a > 0`
  (`TauCeti.isQuasiregularOn_norm_rpow_smul_self_of_finrank_eq_one`).

For `a = 0` the map `x ↦ ‖x‖⁻¹ • x` is not continuous at the origin, so it is not quasiregular on
any open set containing it (`TauCeti.not_isQuasiregularOn_norm_inv_smul_self`).

## Checks

In `ℝ³`, the radial stretch with `a = 1/2` is `2`-quasiregular, and on a nonempty open set not
`K`-quasiregular for `K < 2` (`TauCeti.isQuasiregularOn_norm_rpow_smul_self_half_fin_three`,
`TauCeti.two_le_of_isQuasiregularOn_norm_rpow_smul_self_half_fin_three`), and the one with `a = 2`
is `4`-quasiregular, and on a nonempty open set not `K`-quasiregular for `K < 4`
(`TauCeti.isQuasiregularOn_norm_rpow_smul_self_two_fin_three`,
`TauCeti.four_le_of_isQuasiregularOn_norm_rpow_smul_self_two_fin_three`).
-/

public section

open MeasureTheory Module Set TopologicalSpace
open scoped RealInnerProductSpace Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Quasiregularity of the radial stretch from the pointwise inequality.** For `a > 0` and
`1 ≤ K`, if the derivative `D` of the radial stretch `x ↦ ‖x‖ ^ (a - 1) • x` satisfies
`‖D‖ⁿ ≤ K det D` at every point other than the origin, then the radial stretch is
`K`-quasiregular on every open set. -/
theorem isQuasiregularOn_norm_rpow_smul_self_of_forall_ne {a K : ℝ} (ha : 0 < a) (hK : 1 ≤ K)
    (h : ∀ x : E, x ≠ 0 →
      ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ ^ finrank ℝ E ≤
        K * LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E))
    (Ω : Opens E) : IsQuasiregularOn K Ω (fun x : E ↦ ‖x‖ ^ (a - 1) • x) := by
  have hp : -1 < a - 1 := by linarith
  have hDu := hasWeakFDerivOn_norm_rpow_smul_self (μ := volume) hp Ω
  refine (isQuasiregularOn_iff hDu).2
    ⟨hK, (continuous_norm_rpow_smul_self hp).continuousOn, ?_, ?_⟩
  · exact (locallyIntegrable_norm_rpow_smul_id_add_smulRight_pow hp).locallyIntegrableOn _
  · rcases Nat.eq_zero_or_pos (finrank ℝ E) with hd | hd
    · refine ae_of_all _ fun x ↦ ?_
      rw [hd, pow_zero, LinearMap.det_eq_one_of_finrank_eq_zero hd, mul_one]
      exact hK
    have : Nontrivial E := Module.nontrivial_of_finrank_pos hd
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx
    rw [← fderiv_norm_rpow_smul_self_of_ne (a - 1) hx]
    exact h x hx

/-- **The radial stretch with `a ≥ 1` is `a ^ (n - 1)`-quasiregular** on every open set of an
`n`-dimensional space: off the origin `‖D‖ⁿ = a ^ (n - 1) det D`. -/
theorem isQuasiregularOn_norm_rpow_smul_self_of_one_le {a : ℝ} (ha : 1 ≤ a) (Ω : Opens E) :
    IsQuasiregularOn (a ^ (finrank ℝ E - 1)) Ω (fun x : E ↦ ‖x‖ ^ (a - 1) • x) :=
  isQuasiregularOn_norm_rpow_smul_self_of_forall_ne (by linarith) (one_le_pow₀ ha)
    (fun _ hx ↦ (norm_fderiv_norm_rpow_smul_self_pow_eq_of_one_le ha hx).le) Ω

/-- **The radial stretch with `0 < a ≤ 1` is `a⁻¹`-quasiregular** on every open set: off the
origin `‖D‖ ≤ ‖x‖ ^ (a - 1)` and `det D = a (‖x‖ ^ (a - 1))ⁿ`. -/
theorem isQuasiregularOn_norm_rpow_smul_self_of_le_one {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    (Ω : Opens E) : IsQuasiregularOn a⁻¹ Ω (fun x : E ↦ ‖x‖ ^ (a - 1) • x) := by
  refine isQuasiregularOn_norm_rpow_smul_self_of_forall_ne ha ((one_le_inv₀ ha).2 ha₁)
    (fun x hx ↦ ?_) Ω
  have hb : ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ ≤ ‖x‖ ^ (a - 1) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ by
      simpa [abs_of_pos ha, max_eq_right ha₁] using
        (norm_fderiv_norm_rpow_smul_self_apply_mem_Icc a hx v).2
  rw [det_fderiv_norm_rpow_smul_self a hx, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) hb _

/-- **In dimension one the radial stretch is `1`-quasiregular** for every `a > 0`: its derivative
off the origin is multiplication by `a |t| ^ (a - 1) > 0`, its own determinant. -/
theorem isQuasiregularOn_norm_rpow_smul_self_of_finrank_eq_one (hE : finrank ℝ E = 1) {a : ℝ}
    (ha : 0 < a) (Ω : Opens E) : IsQuasiregularOn 1 Ω (fun x : E ↦ ‖x‖ ^ (a - 1) • x) := by
  refine isQuasiregularOn_norm_rpow_smul_self_of_forall_ne ha le_rfl (fun x hx ↦ ?_) Ω
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  have hn : ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ ≤ |a| * ‖x‖ ^ (a - 1) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
    -- In dimension one every vector is a multiple of `x`.
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' x hx).1 hE v
    rw [map_smul, norm_smul, norm_smul, norm_fderiv_norm_rpow_smul_self_apply_self a hx]
    exact le_of_eq (by ring)
  rw [hE, pow_one, one_mul, det_fderiv_norm_rpow_smul_self a hx, hE, pow_one]
  rwa [abs_of_pos ha] at hn

/-- Lower bound for the constant of a quasiregular radial stretch: if off the origin
`‖D‖ⁿ = c det D`, and the radial stretch is `K`-quasiregular on a nonempty open set, then `c ≤ K`.
-/
private theorem le_of_isQuasiregularOn_norm_rpow_smul_self [Nontrivial E] {a c K : ℝ}
    (ha : 0 < a) {Ω : Opens E} (hΩ : (Ω : Set E).Nonempty)
    (hf : IsQuasiregularOn K Ω (fun x : E ↦ ‖x‖ ^ (a - 1) • x))
    (hc : ∀ x : E, x ≠ 0 →
      ‖fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x‖ ^ finrank ℝ E =
        c * LinearMap.det (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E)) :
    c ≤ K := by
  have hDu := hasWeakFDerivOn_norm_rpow_smul_self (μ := volume) (by linarith : -1 < a - 1) Ω
  have hmain : ∀ᵐ _ ∂volume.restrict (Ω : Set E), c ≤ K := by
    filter_upwards [hf.ae_norm_pow_le_mul_det hDu,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hle hx
    rw [← fderiv_norm_rpow_smul_self_of_ne (a - 1) hx, hc x hx] at hle
    have hdet : 0 < LinearMap.det
        (fderiv ℝ (fun y : E ↦ ‖y‖ ^ (a - 1) • y) x : E →ₗ[ℝ] E) := by
      rw [det_fderiv_norm_rpow_smul_self a hx]
      have := norm_pos_iff.mpr hx
      positivity
    exact le_of_mul_le_mul_right hle hdet
  have := ae_restrict_neBot.2 (Ω.isOpen.measure_pos volume hΩ).ne'
  exact hmain.exists.choose_spec

/-- **Sharpness for `a ≥ 1`.** If the radial stretch with `a ≥ 1` is `K`-quasiregular on a
nonempty open set, then `a ^ (n - 1) ≤ K`. -/
theorem pow_le_of_isQuasiregularOn_norm_rpow_smul_self {a K : ℝ} (ha : 1 ≤ a) {Ω : Opens E}
    (hΩ : (Ω : Set E).Nonempty) (hf : IsQuasiregularOn K Ω (fun x : E ↦ ‖x‖ ^ (a - 1) • x)) :
    a ^ (finrank ℝ E - 1) ≤ K := by
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hd | hd
  · simpa [hd] using hf.one_le
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hd
  exact le_of_isQuasiregularOn_norm_rpow_smul_self (by linarith) hΩ hf
    fun _ hx ↦ norm_fderiv_norm_rpow_smul_self_pow_eq_of_one_le ha hx

/-- **Sharpness for `0 < a ≤ 1`.** If `n ≥ 2` and the radial stretch with `0 < a ≤ 1` is
`K`-quasiregular on a nonempty open set, then `a⁻¹ ≤ K`. In dimension one it is `1`-quasiregular
(`TauCeti.isQuasiregularOn_norm_rpow_smul_self_of_finrank_eq_one`). -/
theorem inv_le_of_isQuasiregularOn_norm_rpow_smul_self (hE : 2 ≤ finrank ℝ E) {a K : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) {Ω : Opens E} (hΩ : (Ω : Set E).Nonempty)
    (hf : IsQuasiregularOn K Ω (fun x : E ↦ ‖x‖ ^ (a - 1) • x)) : a⁻¹ ≤ K := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  refine le_of_isQuasiregularOn_norm_rpow_smul_self ha hΩ hf fun x hx ↦ ?_
  rw [← mul_norm_fderiv_norm_rpow_smul_self_pow_eq_of_le_one hE ha ha₁ hx, ← mul_assoc,
    inv_mul_cancel₀ ha.ne', one_mul]

/-- **The case `a = 0` is excluded.** In a nontrivial space, `x ↦ ‖x‖⁻¹ • x` is not
`K`-quasiregular, for any `K`, on any open set containing the origin: it is not continuous at
the origin, where it vanishes while it has norm `1` everywhere else. -/
theorem not_isQuasiregularOn_norm_inv_smul_self [Nontrivial E] {K : ℝ} {Ω : Opens E}
    (h0 : (0 : E) ∈ Ω) : ¬ IsQuasiregularOn K Ω (fun x : E ↦ ‖x‖⁻¹ • x) := by
  intro hf
  have hc : ContinuousAt (fun x : E ↦ ‖x‖⁻¹ • x) 0 :=
    hf.continuousOn.continuousAt (Ω.isOpen.mem_nhds h0)
  have ht : Filter.Tendsto (fun x : E ↦ ‖‖x‖⁻¹ • x‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (hc.tendsto.mono_left nhdsWithin_le_nhds).norm
  have h1 : (fun x : E ↦ ‖‖x‖⁻¹ • x‖) =ᶠ[𝓝[≠] 0] fun _ ↦ 1 :=
    eventually_nhdsWithin_of_forall fun x hx ↦ by
      dsimp only
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  have := Module.punctured_nhds_neBot ℝ E 0
  exact one_ne_zero (tendsto_nhds_unique (ht.congr' h1) tendsto_const_nhds).symm

/-! ### Checks in `ℝ³` -/

/-- **Check.** In `ℝ³` the radial stretch with `a = 1/2` is `2`-quasiregular on every open set. -/
theorem isQuasiregularOn_norm_rpow_smul_self_half_fin_three (Ω : Opens (EuclideanSpace ℝ (Fin 3))) :
    IsQuasiregularOn 2 Ω (fun x : EuclideanSpace ℝ (Fin 3) ↦ ‖x‖ ^ ((1 / 2 : ℝ) - 1) • x) := by
  simpa using isQuasiregularOn_norm_rpow_smul_self_of_le_one (E := EuclideanSpace ℝ (Fin 3))
    (a := 1 / 2) (by norm_num) (by norm_num) Ω

/-- **Check.** In `ℝ³` the radial stretch with `a = 1/2` is not `K`-quasiregular on a nonempty
open set for any `K < 2`. -/
theorem two_le_of_isQuasiregularOn_norm_rpow_smul_self_half_fin_three {K : ℝ}
    {Ω : Opens (EuclideanSpace ℝ (Fin 3))} (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin 3))).Nonempty)
    (hf : IsQuasiregularOn K Ω
      (fun x : EuclideanSpace ℝ (Fin 3) ↦ ‖x‖ ^ ((1 / 2 : ℝ) - 1) • x)) : 2 ≤ K := by
  simpa using inv_le_of_isQuasiregularOn_norm_rpow_smul_self (by simp) (by norm_num)
    (by norm_num) hΩ hf

/-- **Check.** In `ℝ³` the radial stretch with `a = 2` is `4`-quasiregular on every open set. -/
theorem isQuasiregularOn_norm_rpow_smul_self_two_fin_three (Ω : Opens (EuclideanSpace ℝ (Fin 3))) :
    IsQuasiregularOn 4 Ω (fun x : EuclideanSpace ℝ (Fin 3) ↦ ‖x‖ ^ ((2 : ℝ) - 1) • x) := by
  have h := isQuasiregularOn_norm_rpow_smul_self_of_one_le (E := EuclideanSpace ℝ (Fin 3))
    (a := 2) one_le_two Ω
  rwa [finrank_euclideanSpace_fin, show (2 : ℝ) ^ (3 - 1) = 4 by norm_num] at h

/-- **Check.** In `ℝ³` the radial stretch with `a = 2` is not `K`-quasiregular on a nonempty
open set for any `K < 4`. -/
theorem four_le_of_isQuasiregularOn_norm_rpow_smul_self_two_fin_three {K : ℝ}
    {Ω : Opens (EuclideanSpace ℝ (Fin 3))} (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin 3))).Nonempty)
    (hf : IsQuasiregularOn K Ω
      (fun x : EuclideanSpace ℝ (Fin 3) ↦ ‖x‖ ^ ((2 : ℝ) - 1) • x)) : 4 ≤ K := by
  have h := pow_le_of_isQuasiregularOn_norm_rpow_smul_self one_le_two hΩ hf
  rw [finrank_euclideanSpace_fin] at h
  norm_num at h
  exact h

end TauCeti
