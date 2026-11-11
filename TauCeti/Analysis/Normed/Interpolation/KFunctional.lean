/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple

/-!
# The `K`-functional of a compatible couple

For a compatible couple `(X₀, X₁)` and `t ≥ 0`, Peetre's `K`-functional on the sum space is
`K(t, u) = inf {‖x₀‖ + t ‖x₁‖ | u = x₀ + x₁}`. It is the building block of the real
interpolation method: the space `(X₀, X₁)_{θ,q}` consists of the `u` for which
`t ↦ t^(-θ) K(t, u)` lies in `L^q(dt / t)`.

We prove the basic properties of `K` from Bergh–Löfström, §3.1:

* `K(1, ·)` is the sum norm (`kFunctional_one`);
* for fixed `t ≥ 0`, `K(t, ·)` is a seminorm (`kFunctional_add_le`, `kFunctional_smul`),
  and for `t > 0` a norm equivalent to the sum norm, with
  `min 1 t * ‖u‖ ≤ K(t, u) ≤ max 1 t * ‖u‖`; it is `max 1 t`-Lipschitz
  (`lipschitzWith_kFunctional`);
* for fixed `u`, `t ↦ K(t, u)` is nonnegative, monotone and concave on `[0, ∞)`, hence continuous
  on `(0, ∞)` (`continuousOn_kFunctional`), and `K(t, u) ≤ max 1 (t / s) * K(s, u)` for `s > 0`;
* elements of `X₀`, `X₁` and the intersection satisfy `K(t, x₀) ≤ ‖x₀‖`, `K(t, x₁) ≤ t ‖x₁‖`
  and `K(t, x) ≤ min 1 t * ‖x‖`;
* a linear map of sum spaces restricting to maps `X₀ → Y₀`, `X₁ → Y₁` bounded by `M₀ > 0`
  and `M₁` satisfies `K(t, T u) ≤ M₀ K(t M₁ / M₀, u)` (`kFunctional_map_le`);
* for the couple `(X, X)`, `K(t, u) = min 1 t * ‖u‖` (`kFunctional_refl`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §3.1.
-/

public noncomputable section

namespace TauCeti

namespace CompatibleCouple

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-- Peetre's `K`-functional `K(t, u) = inf {‖x₀‖ + t ‖x₁‖ | u = x₀ + x₁}` on the sum space of a
compatible couple. It is meaningful for `t ≥ 0`, which the lemmas below assume where needed.
Negative parameters are outside the intended API: for `t < 0` the infimum need not be bounded
below, and no property of the value is claimed. -/
def kFunctional (t : ℝ) (u : C.SumSpace) : ℝ :=
  ⨅ x : {x : X₀ × X₁ // C.fstToSum x.1 + C.sndToSum x.2 = u}, ‖x.1.1‖ + t * ‖x.1.2‖

variable {C} {s t : ℝ} {u v : C.SumSpace}

private lemma nonempty_decomposition (u : C.SumSpace) :
    Nonempty {x : X₀ × X₁ // C.fstToSum x.1 + C.sndToSum x.2 = u} :=
  let ⟨x₀, x₁, h⟩ := C.exists_fstToSum_add_sndToSum_eq u
  ⟨⟨(x₀, x₁), h⟩⟩

/-- Each decomposition `u = x₀ + x₁` bounds `K(t, u)` by `‖x₀‖ + t ‖x₁‖`. -/
theorem kFunctional_le (ht : 0 ≤ t) {x₀ : X₀} {x₁ : X₁}
    (h : C.fstToSum x₀ + C.sndToSum x₁ = u) : C.kFunctional t u ≤ ‖x₀‖ + t * ‖x₁‖ := by
  rw [kFunctional]
  exact ciInf_le (f := fun x : {x : X₀ × X₁ // C.fstToSum x.1 + C.sndToSum x.2 = u} =>
    ‖x.1.1‖ + t * ‖x.1.2‖) ⟨0, by rintro _ ⟨x, rfl⟩; positivity⟩ ⟨(x₀, x₁), h⟩

/-- `K(t, u)` is the largest lower bound of `‖x₀‖ + t ‖x₁‖` over the decompositions
`u = x₀ + x₁`. -/
theorem le_kFunctional_iff (ht : 0 ≤ t) {r : ℝ} :
    r ≤ C.kFunctional t u ↔
      ∀ x₀ x₁, C.fstToSum x₀ + C.sndToSum x₁ = u → r ≤ ‖x₀‖ + t * ‖x₁‖ := by
  refine ⟨fun hr x₀ x₁ h => hr.trans (kFunctional_le ht h), fun H => ?_⟩
  have := nonempty_decomposition u
  exact le_ciInf fun x => H x.1.1 x.1.2 x.2

theorem kFunctional_lt_iff (ht : 0 ≤ t) {r : ℝ} :
    C.kFunctional t u < r ↔
      ∃ x₀ x₁, C.fstToSum x₀ + C.sndToSum x₁ = u ∧ ‖x₀‖ + t * ‖x₁‖ < r := by
  simp only [← not_le, le_kFunctional_iff ht, not_forall, exists_prop]

theorem kFunctional_nonneg (ht : 0 ≤ t) : 0 ≤ C.kFunctional t u :=
  (le_kFunctional_iff ht).2 fun _ _ _ => by positivity

@[simp]
theorem kFunctional_zero (ht : 0 ≤ t) : C.kFunctional t 0 = 0 :=
  le_antisymm ((kFunctional_le ht (x₀ := 0) (x₁ := 0) (by simp)).trans_eq (by simp))
    (kFunctional_nonneg ht)

/-- At `t = 1` the `K`-functional is the norm of the sum space. -/
@[simp]
theorem kFunctional_one (u : C.SumSpace) : C.kFunctional 1 u = ‖u‖ := by
  refine le_antisymm (le_of_forall_gt fun r hr => ?_) ((le_kFunctional_iff zero_le_one).2 ?_)
  · obtain ⟨x₀, x₁, h, hr⟩ := C.norm_sumSpace_lt_iff.1 hr
    exact (kFunctional_lt_iff zero_le_one).2 ⟨x₀, x₁, h, by simpa using hr⟩
  · rintro x₀ x₁ rfl
    simpa using C.norm_fstToSum_add_sndToSum_le x₀ x₁

variable (C) in
theorem kFunctional_fstToSum_le (ht : 0 ≤ t) (x : X₀) : C.kFunctional t (C.fstToSum x) ≤ ‖x‖ :=
  (kFunctional_le ht (x₀ := x) (x₁ := 0) (by simp)).trans_eq (by simp)

variable (C) in
theorem kFunctional_sndToSum_le (ht : 0 ≤ t) (x : X₁) :
    C.kFunctional t (C.sndToSum x) ≤ t * ‖x‖ :=
  (kFunctional_le ht (x₀ := 0) (x₁ := x) (by simp)).trans_eq (by simp)

/-- On the intersection, `K(t, x) ≤ min 1 t * ‖x‖`. -/
theorem kFunctional_fstToSum_interFst_le (ht : 0 ≤ t) (x : C.inter) :
    C.kFunctional t (C.fstToSum (C.interFst x)) ≤ min 1 t * ‖x‖ := by
  rcases le_total 1 t with h | h
  · rw [min_eq_left h, one_mul]
    exact (C.kFunctional_fstToSum_le ht _).trans (C.norm_interFst_le x)
  · rw [min_eq_right h, C.fstToSum_interFst]
    exact (C.kFunctional_sndToSum_le ht _).trans (by gcongr; exact C.norm_interSnd_le x)

/-- `t ↦ K(t, u)` is monotone on `[0, ∞)`. -/
theorem kFunctional_mono (hs : 0 ≤ s) (hst : s ≤ t) (u : C.SumSpace) :
    C.kFunctional s u ≤ C.kFunctional t u :=
  (le_kFunctional_iff (hs.trans hst)).2 fun _ _ h =>
    (kFunctional_le hs h).trans (by gcongr)

/-- `t ↦ K(t, u)` is concave on `[0, ∞)`, being an infimum of affine functions of `t`. -/
theorem concaveOn_kFunctional (u : C.SumSpace) :
    ConcaveOn ℝ (Set.Ici 0) (C.kFunctional · u) := by
  refine ⟨convex_Ici 0, fun s hs t ht a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hs ht
  simp only [smul_eq_mul]
  refine (le_kFunctional_iff (by positivity)).2 fun x₀ x₁ h => ?_
  calc a * C.kFunctional s u + b * C.kFunctional t u
      ≤ a * (‖x₀‖ + s * ‖x₁‖) + b * (‖x₀‖ + t * ‖x₁‖) := by
        gcongr
        · exact kFunctional_le hs h
        · exact kFunctional_le ht h
    _ = ‖x₀‖ + (a * s + b * t) * ‖x₁‖ := by linear_combination ‖x₀‖ * hab

/-- Changing the parameter from `s` to `t` multiplies `K` by at most `max 1 (t / s)`. -/
theorem kFunctional_le_max_mul (hs : 0 < s) (ht : 0 ≤ t) (u : C.SumSpace) :
    C.kFunctional t u ≤ max 1 (t / s) * C.kFunctional s u := by
  conv_rhs => rw [kFunctional, Real.mul_iInf_of_nonneg (by positivity)]
  have := nonempty_decomposition u
  refine le_ciInf fun ⟨⟨x₀, x₁⟩, h⟩ => (kFunctional_le ht h).trans ?_
  have h₁ : 1 ≤ max 1 (t / s) := le_max_left _ _
  have h₂ : t / s ≤ max 1 (t / s) := le_max_right _ _
  calc ‖x₀‖ + t * ‖x₁‖ = 1 * ‖x₀‖ + t / s * (s * ‖x₁‖) := by field_simp
    _ ≤ max 1 (t / s) * ‖x₀‖ + max 1 (t / s) * (s * ‖x₁‖) := by gcongr
    _ = max 1 (t / s) * (‖x₀‖ + s * ‖x₁‖) := by ring

/-- Changing the parameter from `s` to `t` multiplies `K` by at least `min 1 (t / s)`. -/
theorem min_mul_kFunctional_le (hs : 0 < s) (ht : 0 ≤ t) (u : C.SumSpace) :
    min 1 (t / s) * C.kFunctional s u ≤ C.kFunctional t u := by
  refine (le_kFunctional_iff ht).2 fun x₀ x₁ h => ?_
  have h₀ : 0 ≤ min 1 (t / s) := le_min zero_le_one (by positivity)
  have h₁ : min 1 (t / s) ≤ 1 := min_le_left _ _
  have h₂ : min 1 (t / s) ≤ t / s := min_le_right _ _
  calc min 1 (t / s) * C.kFunctional s u ≤ min 1 (t / s) * (‖x₀‖ + s * ‖x₁‖) := by
        gcongr
        exact kFunctional_le hs.le h
    _ = min 1 (t / s) * ‖x₀‖ + min 1 (t / s) * (s * ‖x₁‖) := by ring
    _ ≤ 1 * ‖x₀‖ + t / s * (s * ‖x₁‖) := by gcongr
    _ = ‖x₀‖ + t * ‖x₁‖ := by field_simp

/-- For `t ≥ 0`, `K(t, u)` is at most `max 1 t` times the sum norm of `u`. -/
theorem kFunctional_le_max_one_mul_norm (ht : 0 ≤ t) (u : C.SumSpace) :
    C.kFunctional t u ≤ max 1 t * ‖u‖ := by
  simpa using kFunctional_le_max_mul zero_lt_one ht u

/-- For `t ≥ 0`, `K(t, u)` is at least `min 1 t` times the sum norm of `u`; with the upper bound
`kFunctional_le_max_one_mul_norm`, `K(t, ·)` is equivalent to the sum norm for `t > 0`. -/
theorem min_one_mul_norm_le_kFunctional (ht : 0 ≤ t) (u : C.SumSpace) :
    min 1 t * ‖u‖ ≤ C.kFunctional t u := by
  simpa using min_mul_kFunctional_le zero_lt_one ht u

/-- For `t > 0`, `K(t, ·)` vanishes only at zero. -/
theorem kFunctional_eq_zero_iff [T1Space V] (ht : 0 < t) :
    C.kFunctional t u = 0 ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ kFunctional_zero ht.le⟩
  have h' := min_one_mul_norm_le_kFunctional ht.le u
  rw [h] at h'
  have hu : ‖u‖ ≤ 0 := nonpos_of_mul_nonpos_right h' (lt_min zero_lt_one ht)
  exact norm_le_zero_iff.1 hu

/-- For `t ≥ 0`, `K(t, ·)` is subadditive: `K(t, u + v) ≤ K(t, u) + K(t, v)`. -/
theorem kFunctional_add_le (ht : 0 ≤ t) (u v : C.SumSpace) :
    C.kFunctional t (u + v) ≤ C.kFunctional t u + C.kFunctional t v := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨x₀, x₁, hx, hxε⟩ :=
    (kFunctional_lt_iff ht).1 (lt_add_of_pos_right (C.kFunctional t u) (half_pos hε))
  obtain ⟨y₀, y₁, hy, hyε⟩ :=
    (kFunctional_lt_iff ht).1 (lt_add_of_pos_right (C.kFunctional t v) (half_pos hε))
  refine (kFunctional_le ht (x₀ := x₀ + y₀) (x₁ := x₁ + y₁) ?_).trans_lt ?_
  · rw [← hx, ← hy, map_add, map_add]
    abel
  · have := mul_le_mul_of_nonneg_left (norm_add_le x₁ y₁) ht
    linarith [norm_add_le x₀ y₀]

private lemma kFunctional_smul_le (ht : 0 ≤ t) (c : 𝕜) (u : C.SumSpace) :
    C.kFunctional t (c • u) ≤ ‖c‖ * C.kFunctional t u := by
  conv_rhs => rw [kFunctional, Real.mul_iInf_of_nonneg (norm_nonneg c)]
  have := nonempty_decomposition u
  refine le_ciInf fun ⟨⟨x₀, x₁⟩, h⟩ =>
    (kFunctional_le ht (x₀ := c • x₀) (x₁ := c • x₁) ?_).trans_eq ?_
  · rw [map_smul, map_smul, ← smul_add, h]
  · simp only [norm_smul]
    ring

/-- For `t ≥ 0`, `K(t, ·)` is absolutely homogeneous: `K(t, c • u) = ‖c‖ * K(t, u)`. -/
theorem kFunctional_smul (ht : 0 ≤ t) (c : 𝕜) (u : C.SumSpace) :
    C.kFunctional t (c • u) = ‖c‖ * C.kFunctional t u := by
  refine le_antisymm (kFunctional_smul_le ht c u) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp [kFunctional_zero ht]
  · calc ‖c‖ * C.kFunctional t u = ‖c‖ * C.kFunctional t (c⁻¹ • c • u) := by
          rw [inv_smul_smul₀ hc]
      _ ≤ ‖c‖ * (‖c⁻¹‖ * C.kFunctional t (c • u)) := by
          gcongr
          exact kFunctional_smul_le ht _ _
      _ = C.kFunctional t (c • u) := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc), one_mul]

/-- For `t ≥ 0`, `K(t, ·)` is Lipschitz for the sum norm, with constant `max 1 t`. -/
theorem lipschitzWith_kFunctional (ht : 0 ≤ t) :
    LipschitzWith (max 1 t).toNNReal (C.kFunctional t) :=
  LipschitzWith.of_le_add_mul' _ fun u v =>
    calc C.kFunctional t u = C.kFunctional t (v + (u - v)) := by rw [add_sub_cancel]
      _ ≤ C.kFunctional t v + C.kFunctional t (u - v) := kFunctional_add_le ht _ _
      _ ≤ C.kFunctional t v + max 1 t * dist u v := by
        rw [dist_eq_norm]
        gcongr
        exact kFunctional_le_max_one_mul_norm ht _

theorem continuous_kFunctional (ht : 0 ≤ t) : Continuous (C.kFunctional t) :=
  (lipschitzWith_kFunctional ht).continuous

/-- For fixed `u`, `t ↦ K(t, u)` is continuous on `(0, ∞)`, the interior of the half-line on
which it is concave. -/
theorem continuousOn_kFunctional (u : C.SumSpace) :
    ContinuousOn (C.kFunctional · u) (Set.Ioi 0) := by
  simpa using (concaveOn_kFunctional u).continuousOn_interior

section Map

variable {Y₀ Y₁ W : Type*} [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀] [NormedAddCommGroup Y₁]
  [NormedSpace 𝕜 Y₁] [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [ContinuousAdd W]
  {D : CompatibleCouple 𝕜 Y₀ Y₁ W}

/-- A linear map `T` between the sum spaces of two couples that restricts to maps
`T₀ : X₀ → Y₀` and `T₁ : X₁ → Y₁` with `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖`, where `M₀ > 0`,
satisfies `K(t, T u) ≤ M₀ K(t M₁ / M₀, u)`. -/
theorem kFunctional_map_le (T : C.SumSpace →ₗ[𝕜] D.SumSpace) {T₀ : X₀ → Y₀} {T₁ : X₁ → Y₁}
    (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (ht : 0 ≤ t)
    (u : C.SumSpace) : D.kFunctional t (T u) ≤ M₀ * C.kFunctional (t * M₁ / M₀) u := by
  conv_rhs => rw [kFunctional, Real.mul_iInf_of_nonneg hM₀.le]
  have := nonempty_decomposition u
  refine le_ciInf fun ⟨⟨x₀, x₁⟩, h⟩ => (kFunctional_le ht (x₀ := T₀ x₀) (x₁ := T₁ x₁) ?_).trans ?_
  · rw [← h, map_add, hT₀, hT₁]
  · calc ‖T₀ x₀‖ + t * ‖T₁ x₁‖ ≤ M₀ * ‖x₀‖ + t * (M₁ * ‖x₁‖) := by
          gcongr
          · exact h₀ x₀
          · exact h₁ x₁
      _ = M₀ * (‖x₀‖ + t * M₁ / M₀ * ‖x₁‖) := by field_simp

end Map

section Refl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- For the couple `(X, X)`, `K(t, u) = min 1 t * ‖u‖`. -/
theorem kFunctional_refl (ht : 0 ≤ t) (u : (refl 𝕜 X).SumSpace) :
    (refl 𝕜 X).kFunctional t u = min 1 t * ‖u‖ := by
  refine le_antisymm ?_ (min_one_mul_norm_le_kFunctional ht u)
  rw [← norm_refl_sumSpaceEmbed u]
  rcases le_total 1 t with h | h
  · simpa [min_eq_left h] using (refl 𝕜 X).kFunctional_fstToSum_le ht ((refl 𝕜 X).sumSpaceEmbed u)
  · simpa [min_eq_right h] using (refl 𝕜 X).kFunctional_sndToSum_le ht ((refl 𝕜 X).sumSpaceEmbed u)

end Refl

end CompatibleCouple

end TauCeti
