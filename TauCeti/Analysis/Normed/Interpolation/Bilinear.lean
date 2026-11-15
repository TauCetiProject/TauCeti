/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.RealMethod
import TauCeti.Analysis.Normed.Interpolation.Exponent
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Bilinear real interpolation

Let `(A₀, A₁)`, `(B₀, B₁)` and `(C₀, C₁)` be compatible couples, and let `T` be a bilinear map
from `A₀ ∩ A₁` and `B₀ ∩ B₁` to the sum space `C₀ + C₁` with the three endpoint bounds

`T : A₀ × B₀ → C₀`, `T : A₀ × B₁ → C₁`, `T : A₁ × B₀ → C₁`,

of norms `M₀`, `M₁`, `M₁`. No bound is assumed on `A₁ × B₁`. The bilinear real interpolation
theorem (Bergh–Löfström, Exercise 3.13.5(b)) says that for `θ₀, θ₁ > 0` with `θ₀ + θ₁ < 1` and
`1 / p + 1 / q ≥ 1`,

`‖T a b‖_{(C₀, C₁)_{θ₀ + θ₁, 1}} ≤ K ‖a‖_{(A₀, A₁)_{θ₀, p}} ‖b‖_{(B₀, B₁)_{θ₁, q}}`,

with `K` depending only on `θ₀`, `θ₁`, `q`, `M₀` and `M₁`. Keel and Tao use this theorem, with
weighted sequence spaces as the target couple, to sum the dyadic pieces of the bilinear form in
their proof of the endpoint Strichartz estimate.

## Main results

* `TauCeti.CompatibleCouple.kMethodENorm_apply_apply_le`: the estimate for Hölder conjugate `p`
  and `q`, with `K = 48 c_{θ,1} M₀ ^ (1 - θ) M₁ ^ θ (θ₀⁻¹ + θ₁⁻¹) / (log 2)²`, `θ = θ₀ + θ₁`,
  where `c_{θ,1}` is `TauCeti.CompatibleCouple.kMethodConst θ 1`, finite for `0 < θ < 1`.
* `TauCeti.CompatibleCouple.kMethodENorm_apply_apply_le_of_le`: the estimate for every `q` with
  `1 / p + 1 / q ≥ 1`, through the secondary-exponent embedding.

## The argument

Every `a ∈ A₀ ∩ A₁` has a dyadic decomposition `a = ∑ⱼ uⱼ`, `j ∈ ℤ`, in the intersection with
`‖uⱼ‖_{A₀} ≤ 4 K(2 ^ j, a)` and `2 ^ j ‖uⱼ‖_{A₁} ≤ 6 K(2 ^ j, a)`
(`TauCeti.CompatibleCouple.nonempty_dyadicDecomposition`): take near-optimal
decompositions `a = a⁰ⱼ + a¹ⱼ` for `K(2 ^ j, a)`, which lie in the intersection
(`TauCeti.CompatibleCouple.exists_add_eq_and_norm_interFst_add_mul_norm_interSnd_lt`), and put
`uⱼ = a⁰ⱼ - a⁰ⱼ₋₁`. With `b = ∑ₖ vₖ` likewise, the endpoint bounds give

`K(t, T uⱼ vₖ) ≤ C K(s, a) K(r, b) min M₀ (t M₁ min s⁻¹ r⁻¹)`

for `s ∈ [2 ^ j, 2 ^ (j + 1))` and `r ∈ [2 ^ k, 2 ^ (k + 1))`. Integrating against
`t ^ (-θ) dt / t` and summing over the dyadic squares bounds `‖T a b‖_{θ,1}` by a multiple of

`∫∫ f(s) κ(s, r) g(r) ds / s dr / r`, `f(s) = s ^ (-θ₀) K(s, a)`, `g(r) = r ^ (-θ₁) K(r, b)`,

with the kernel `κ(s, r) = s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)`. It depends only on `s / r`
and has integral `θ₀⁻¹ + θ₁⁻¹` in each variable
(`TauCeti.lintegral_multHaar_rpow_mul_rpow_mul_min_inv_rpow_right` and `_left`), so Schur's test
and Hölder's inequality (`TauCeti.lintegral_lintegral_mul_mul_le`) bound the double integral by
`(θ₀⁻¹ + θ₁⁻¹) ‖f‖_{L^p(ds / s)} ‖g‖_{L^q(dr / r)}`, which are the two `K`-method norms.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §3.13, Exercise 5(b).
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. **120** (1998), 955–980,
  the proof of Theorem 1.2 at the endpoint.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TauCeti

namespace CompatibleCouple

section Weighted

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  {C : CompatibleCouple 𝕜 X₀ X₁ V}

/-- The weighted `K`-functional `s ↦ s ^ (-θ) K(max s 0, x)` is measurable, being a power times a
monotone function, and its `L^p(ds / s)` norm is the `K`-method norm of `x`. -/
private theorem measurable_and_eLpNorm_eq (θ : ℝ) (p : ℝ≥0∞) (x : C.SumSpace) :
    Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (-θ) * C.kFunctional (max s 0) x)) ∧
      eLpNorm (fun s : ℝ => ENNReal.ofReal (s ^ (-θ) * C.kFunctional (max s 0) x)) p multHaar =
        C.kMethodENorm θ p x := by
  have hmono : Monotone fun s : ℝ => C.kFunctional (max s 0) x := fun s s' h =>
    kFunctional_mono (le_max_right _ _) (max_le_max h le_rfl) x
  have hm : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (-θ) * C.kFunctional (max s 0) x) :=
    (((measurable_id (α := ℝ)).pow_const _).mul hmono.measurable).ennreal_ofReal
  refine ⟨hm, ?_⟩
  rw [kMethodENorm_def]
  refine eLpNorm_congr_eNorm_ae hm.aestronglyMeasurable
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ x) ?_
  filter_upwards [ae_pos_multHaar] with s hs
  rw [max_eq_left hs.le, Real.eNorm_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hs.le _) (kFunctional_nonneg hs.le)), eNorm_eq_self]

end Weighted

section Bilinear

variable {𝕜 X₀ X₁ V Y₀ Y₁ W Z₀ Z₁ U : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀] [NormedAddCommGroup Y₁] [NormedSpace 𝕜 Y₁]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [ContinuousAdd W]
  [NormedAddCommGroup Z₀] [NormedSpace 𝕜 Z₀] [NormedAddCommGroup Z₁] [NormedSpace 𝕜 Z₁]
  [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U] [ContinuousAdd U]
  {A : CompatibleCouple 𝕜 X₀ X₁ V} {B : CompatibleCouple 𝕜 Y₀ Y₁ W}
  {C : CompatibleCouple 𝕜 Z₀ Z₁ U} (T : A.inter →ₗ[𝕜] B.inter →ₗ[𝕜] C.SumSpace) {M₀ M₁ : ℝ}

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The three endpoint bounds of `T`, read through the `K`-functional of `C`: for `t ≥ 0`,
`K(t, T a b)` is at most `M₀ ‖a‖_{X₀} ‖b‖_{Y₀}`, `t M₁ ‖a‖_{X₀} ‖b‖_{Y₁}` and
`t M₁ ‖a‖_{X₁} ‖b‖_{Y₀}`. -/
private def EndpointBounds (M₀ M₁ : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ (a : A.inter) (b : B.inter),
    C.kFunctional t (T a b) ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖ ∧
    C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖) ∧
    C.kFunctional t (T a b) ≤ t * (M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖)

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The three endpoint bounds of `T`, read through the `K`-functional of `C`. -/
private theorem endpointBounds
    (h₀₀ : ∀ a b, ∃ z : Z₀, T a b = C.fstToSum z ∧ ‖z‖ ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖)
    (h₀₁ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖)
    (h₁₀ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖) :
    EndpointBounds T M₀ M₁ := by
  intro t ht a b
  obtain ⟨z₀, hz₀, hz₀le⟩ := h₀₀ a b
  obtain ⟨z₁, hz₁, hz₁le⟩ := h₀₁ a b
  obtain ⟨z₂, hz₂, hz₂le⟩ := h₁₀ a b
  refine ⟨?_, ?_, ?_⟩
  · rw [hz₀]
    exact (C.kFunctional_fstToSum_le ht z₀).trans hz₀le
  · rw [hz₁]
    exact (C.kFunctional_sndToSum_le ht z₁).trans (mul_le_mul_of_nonneg_left hz₁le ht)
  · rw [hz₂]
    exact (C.kFunctional_sndToSum_le ht z₂).trans (mul_le_mul_of_nonneg_left hz₂le ht)

variable {T}

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The remainder terms of the dyadic partial sums: if `‖S‖_{X₀} ≤ 4 ‖a‖_{X₀}`, `y, y'` are
`O(2 ^ (-N))` in the first spaces and `z, z'` in the second spaces, then the `K`-functional at `t`
of `T S y' + T S z' + T y b + T z b` is `O(2 ^ (-N))`. -/
private theorem kFunctional_remainder_le
    (hK : EndpointBounds T M₀ M₁)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) {t : ℝ} (ht : 0 ≤ t) {N : ℕ} {a S y z : A.inter}
    {b y' z' : B.inter} (hS : ‖A.interFst S‖ ≤ 4 * ‖A.interFst a‖)
    (hy : ‖A.interFst y‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interSnd a‖)
    (hz : ‖A.interSnd z‖ ≤ 2 * 2⁻¹ ^ N * ‖A.interFst a‖)
    (hy' : ‖B.interFst y'‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interSnd b‖)
    (hz' : ‖B.interSnd z'‖ ≤ 2 * 2⁻¹ ^ N * ‖B.interFst b‖) :
    C.kFunctional t (T S y' + T S z' + T y b + T z b) ≤ 2⁻¹ ^ N *
      (8 * M₀ * ‖A.interFst a‖ * ‖B.interSnd b‖ + 10 * t * M₁ * ‖A.interFst a‖ * ‖B.interFst b‖ +
        2 * M₀ * ‖A.interSnd a‖ * ‖B.interFst b‖) := by
  have e1 := (hK t ht S y').1
  have e2 := (hK t ht S z').2.1
  have e3 := (hK t ht y b).1
  have e4 := (hK t ht z b).2.2
  have f1 : M₀ * ‖A.interFst S‖ * ‖B.interFst y'‖ ≤
      M₀ * (4 * ‖A.interFst a‖) * (2 * 2⁻¹ ^ N * ‖B.interSnd b‖) := by gcongr
  have f2 : t * (M₁ * ‖A.interFst S‖ * ‖B.interSnd z'‖) ≤
      t * (M₁ * (4 * ‖A.interFst a‖) * (2 * 2⁻¹ ^ N * ‖B.interFst b‖)) := by gcongr
  have f3 : M₀ * ‖A.interFst y‖ * ‖B.interFst b‖ ≤
      M₀ * (2 * 2⁻¹ ^ N * ‖A.interSnd a‖) * ‖B.interFst b‖ := by gcongr
  have f4 : t * (M₁ * ‖A.interSnd z‖ * ‖B.interFst b‖) ≤
      t * (M₁ * (2 * 2⁻¹ ^ N * ‖A.interFst a‖) * ‖B.interFst b‖) := by gcongr
  calc _ ≤ C.kFunctional t (T S y') + C.kFunctional t (T S z') +
        C.kFunctional t (T y b) + C.kFunctional t (T z b) := by
        refine (kFunctional_add_le ht _ _).trans ?_
        gcongr
        refine (kFunctional_add_le ht _ _).trans ?_
        gcongr
        exact kFunctional_add_le ht _ _
    _ ≤ _ := by linarith

/-- The `K`-functional of `T a b` at `t` is at most the sum over the dyadic pieces of the partial
sums of `a` and `b` up to `N`, plus an `O(2 ^ (-N))` remainder. -/
private theorem kFunctional_le_sum_sum_add
    (hK : EndpointBounds T M₀ M₁)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) {t : ℝ} (ht : 0 ≤ t) {a : A.inter} {b : B.inter}
    (da : A.DyadicDecomposition a) (db : B.DyadicDecomposition b) (N : ℕ) :
    C.kFunctional t (T a b) ≤ ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
        C.kFunctional t (T (da.u ((i : ℤ) + 1 - N)) (db.u ((i' : ℤ) + 1 - N))) + 2⁻¹ ^ N *
      (8 * M₀ * ‖A.interFst a‖ * ‖B.interSnd b‖ + 10 * t * M₁ * ‖A.interFst a‖ * ‖B.interFst b‖ +
        2 * M₀ * ‖A.interSnd a‖ * ‖B.interFst b‖) := by
  set Sa := ∑ i ∈ Finset.range (2 * N), da.u ((i : ℤ) + 1 - N)
  have e1 : T a b = T Sa b + T (da.y N) b + T (da.z N) b := by
    conv_lhs => rw [← da.sum_add_add_eq N]
    simp only [Sa, map_add, LinearMap.add_apply]
  have e2 : T Sa b = ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
      T (da.u ((i : ℤ) + 1 - N)) (db.u ((i' : ℤ) + 1 - N)) + T Sa (db.y N) + T Sa (db.z N) := by
    conv_lhs => rw [← db.sum_add_add_eq N]
    simp only [Sa, map_add, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
  have hsplit : T a b = ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
      T (da.u ((i : ℤ) + 1 - N)) (db.u ((i' : ℤ) + 1 - N)) +
        (T Sa (db.y N) + T Sa (db.z N) + T (da.y N) b + T (da.z N) b) := by
    rw [e1, e2]
    abel
  rw [hsplit]
  refine (kFunctional_add_le ht _ _).trans (add_le_add ?_
    (kFunctional_remainder_le hK hM₀ hM₁ ht (da.norm_interFst_sum_le N) (da.norm_interFst_y_le N)
      (da.norm_interSnd_z_le N) (db.norm_interFst_y_le N) (db.norm_interSnd_z_le N)))
  exact (kFunctional_sum_le ht _ _).trans (Finset.sum_le_sum fun i _ => kFunctional_sum_le ht _ _)

/-- The pointwise step of the bilinear estimate: at each `t > 0`, `t ^ (-θ) K(t, T a b)` is at
most the double series of `t ^ (-θ) K(t, T uⱼ vₖ)` over dyadic decompositions `a = ∑ⱼ uⱼ` and
`b = ∑ₖ vₖ`, since the remainders of the partial sums are `O(2 ^ (-N))`. -/
private theorem ofReal_rpow_mul_kFunctional_le_tsum_tsum (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hK : EndpointBounds T M₀ M₁)
    {θ t : ℝ} (ht : 0 < t) {a : A.inter} {b : B.inter} (da : A.DyadicDecomposition a)
    (db : B.DyadicDecomposition b) :
    ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T a b)) ≤
      ∑' j, ∑' k, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (da.u j) (db.u k))) := by
  set u := da.u
  set v := db.u
  set R := 8 * M₀ * ‖A.interFst a‖ * ‖B.interSnd b‖ +
    10 * t * M₁ * ‖A.interFst a‖ * ‖B.interFst b‖ + 2 * M₀ * ‖A.interSnd a‖ * ‖B.interFst b‖
  set Q := t ^ (-θ) * R
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (div_pos (NNReal.coe_pos.2 hε) (by positivity : (0 : ℝ) < Q + 1)) (by norm_num : (2⁻¹ : ℝ) < 1)
  have hNε : 2⁻¹ ^ N * Q < (ε : ℝ) := by
    rw [lt_div_iff₀ (by positivity)] at hN
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) N]
  have hreal : t ^ (-θ) * C.kFunctional t (T a b) ≤
      ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
        t ^ (-θ) * C.kFunctional t (T (u ((i : ℤ) + 1 - N)) (v ((i' : ℤ) + 1 - N))) +
        2⁻¹ ^ N * Q := by
    simp only [← Finset.mul_sum]
    rw [show 2⁻¹ ^ N * Q = t ^ (-θ) * (2⁻¹ ^ N * R) by ring, ← mul_add]
    exact mul_le_mul_of_nonneg_left (kFunctional_le_sum_sum_add hK hM₀ hM₁ ht.le da db N)
      (Real.rpow_nonneg ht.le _)
  have hnn (j k : ℤ) : 0 ≤ t ^ (-θ) * C.kFunctional t (T (u j) (v k)) :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)
  calc ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T a b))
      ≤ ∑ i ∈ Finset.range (2 * N), ∑ i' ∈ Finset.range (2 * N),
          ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u ((i : ℤ) + 1 - N))
            (v ((i' : ℤ) + 1 - N)))) + ENNReal.ofReal (2⁻¹ ^ N * Q) := by
        refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ =>
          hnn _ _) (by positivity), ENNReal.ofReal_sum_of_nonneg fun i _ =>
          Finset.sum_nonneg fun i' _ => hnn _ _]
        congr 1
        exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_sum_of_nonneg fun i' _ => hnn _ _
    _ ≤ ∑' j, ∑' k, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u j) (v k))) + ε := by
        gcongr
        · -- the blocks `(i + 1 - N, i' + 1 - N)`, `i, i' < 2 N`, are distinct terms of the series
          let e : ℕ ↪ ℤ := ⟨fun i => (i : ℤ) + 1 - N, fun i i' h => by simpa using h⟩
          have h (c : ℤ → ℝ≥0∞) : ∑ i ∈ Finset.range (2 * N), c ((i : ℤ) + 1 - N) ≤ ∑' j, c j :=
            Finset.sum_map (Finset.range (2 * N)) e c ▸ sum_le_tsum _
          exact (Finset.sum_le_sum fun (i : ℕ) _ => h fun k =>
            ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u ((i : ℤ) + 1 - N)) (v k)))).trans
            (h fun j => ∑' k, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (u j) (v k))))
        · rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top]
          exact hNε.le

omit [ContinuousAdd V] [ContinuousAdd W] in
/-- The contribution of one pair of dyadic pieces. If `‖u‖_{X₀} ≤ 4 α`, `s ‖u‖_{X₁} ≤ 12 α`,
`‖v‖_{Y₀} ≤ 4 β` and `r ‖v‖_{Y₁} ≤ 12 β`, then
`K(t, T u v) ≤ 48 α β min M₀ (t M₁ min s⁻¹ r⁻¹)`, and integrating against `t ^ (-θ) dt / t` gives
`48 α β M₀ ^ (1 - θ) (M₁ min s⁻¹ r⁻¹) ^ θ c_{θ,1}`. -/
private theorem lintegral_rpow_mul_kFunctional_le (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hK : EndpointBounds T M₀ M₁)
    (θ : ℝ) {u : A.inter} {v : B.inter} {α β s r : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : 0 < s)
    (hr : 0 < r) (hu₀ : ‖A.interFst u‖ ≤ 4 * α) (hu₁ : s * ‖A.interSnd u‖ ≤ 12 * α)
    (hv₀ : ‖B.interFst v‖ ≤ 4 * β) (hv₁ : r * ‖B.interSnd v‖ ≤ 12 * β) :
    ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T u v)) ∂multHaar ≤
      ENNReal.ofReal (48 * α * β * (M₀ ^ (1 - θ) * (M₁ * min s⁻¹ r⁻¹) ^ θ)) *
        kMethodConst θ 1 := by
  set c := M₁ * min s⁻¹ r⁻¹ with hc_def
  have hc : 0 < c := mul_pos hM₁ (lt_min (inv_pos.2 hs) (inv_pos.2 hr))
  have h48 : 0 ≤ 48 * α * β := by positivity
  have hu₁' : ‖A.interSnd u‖ ≤ 12 * α * s⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hs]
    linarith
  have hv₁' : ‖B.interSnd v‖ ≤ 12 * β * r⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hr]
    linarith
  have hpt : ∀ t, 0 < t → C.kFunctional t (T u v) ≤ 48 * α * β * min M₀ (t * c) := by
    intro t ht
    obtain ⟨e₀, e₁, e₂⟩ := hK t ht.le u v
    rw [hc_def, ← mul_assoc, mul_min_of_nonneg _ _ (mul_nonneg ht.le hM₁.le),
      mul_min_of_nonneg _ _ h48, mul_min_of_nonneg _ _ h48]
    refine le_min ?_ (le_min ?_ ?_)
    · calc _ ≤ M₀ * (4 * α) * (4 * β) := e₀.trans (by gcongr)
        _ ≤ 48 * α * β * M₀ := by nlinarith [mul_nonneg (mul_nonneg hα hβ) hM₀.le]
    · calc _ ≤ t * (M₁ * (12 * α * s⁻¹) * (4 * β)) := e₂.trans (by gcongr)
        _ = 48 * α * β * (t * M₁ * s⁻¹) := by ring
    · calc _ ≤ t * (M₁ * (4 * α) * (12 * β * r⁻¹)) := e₁.trans (by gcongr)
        _ = 48 * α * β * (t * M₁ * r⁻¹) := by ring
  calc ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T u v)) ∂multHaar
      ≤ ∫⁻ t, ENNReal.ofReal (48 * α * β) * ENNReal.ofReal (t ^ (-θ) * min M₀ (t * c))
          ∂multHaar := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_pos_multHaar] with t ht
        rw [← ENNReal.ofReal_mul h48]
        refine ENNReal.ofReal_le_ofReal ?_
        calc t ^ (-θ) * C.kFunctional t (T u v) ≤ t ^ (-θ) * (48 * α * β * min M₀ (t * c)) :=
              mul_le_mul_of_nonneg_left (hpt t ht) (Real.rpow_nonneg ht.le _)
          _ = 48 * α * β * (t ^ (-θ) * min M₀ (t * c)) := by ring
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rpow_neg_mul_min θ hM₀ hc,
          ← mul_assoc, ← ENNReal.ofReal_mul h48]


/-- The `K`-method norm of exponent `1` of `T a b` is at most the double series over the dyadic
pieces of `a` and `b`. -/
private theorem kMethodENorm_le_tsum_tsum_lintegral (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hK : EndpointBounds T M₀ M₁)
    (θ : ℝ) {a : A.inter} {b : B.inter} (da : A.DyadicDecomposition a)
    (db : B.DyadicDecomposition b) :
    C.kMethodENorm θ 1 (T a b) ≤ ∑' j, ∑' k,
      ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (da.u j) (db.u k))) ∂multHaar := by
  have hmeas (c : C.SumSpace) :
      AEMeasurable (fun t => ENNReal.ofReal (t ^ (-θ) * C.kFunctional t c)) multHaar :=
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ c).aemeasurable.ennreal_ofReal
  rw [kMethodENorm_def, eLpNorm_one_eq_lintegral_eNorm
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ _)]
  calc ∫⁻ t, ‖t ^ (-θ) * C.kFunctional t (T a b)‖ₑ ∂multHaar
      ≤ ∫⁻ t, ∑' j, ∑' k, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (da.u j) (db.u k)))
          ∂multHaar := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_pos_multHaar] with t ht
        rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))]
        exact ofReal_rpow_mul_kFunctional_le_tsum_tsum hM₀ hM₁ hK ht da db
    _ = _ := by
        rw [lintegral_tsum fun j => AEMeasurable.tsum fun k => hmeas _]
        exact tsum_congr fun j => lintegral_tsum fun k => hmeas _

/-- The contribution of the dyadic pieces `u` and `v` at scales `2 ^ j` and `2 ^ k` is controlled
by the integrand `f(s) κ(s, r) g(r)` of the final double integral at every point `(s, r)` of the
dyadic square `[2 ^ j, 2 ^ (j + 1)) × [2 ^ k, 2 ^ (k + 1))`. -/
private theorem lintegral_le_mul_kernel_of_mem_Ico (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hK : EndpointBounds T M₀ M₁)
    {θ₀ θ₁ : ℝ} {a' : A.SumSpace} {b' : B.SumSpace} {u : A.inter} {v : B.inter} {j k : ℤ}
    (hu₀ : ‖A.interFst u‖ ≤ 4 * A.kFunctional (2 ^ j) a')
    (hu₁ : (2 : ℝ) ^ j * ‖A.interSnd u‖ ≤ 6 * A.kFunctional (2 ^ j) a')
    (hv₀ : ‖B.interFst v‖ ≤ 4 * B.kFunctional (2 ^ k) b')
    (hv₁ : (2 : ℝ) ^ k * ‖B.interSnd v‖ ≤ 6 * B.kFunctional (2 ^ k) b') {s r : ℝ}
    (hs : s ∈ Ico ((2 : ℝ) ^ j) (2 ^ (j + 1))) (hr : r ∈ Ico ((2 : ℝ) ^ k) (2 ^ (k + 1))) :
    ∫⁻ t, ENNReal.ofReal (t ^ (-(θ₀ + θ₁)) * C.kFunctional t (T u v)) ∂multHaar ≤
      48 * kMethodConst (θ₀ + θ₁) 1 *
        ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁)) *
        (ENNReal.ofReal (s ^ (-θ₀) * A.kFunctional (max s 0) a') *
          (ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)) *
            ENNReal.ofReal (r ^ (-θ₁) * B.kFunctional (max r 0) b'))) := by
  set θ := θ₀ + θ₁
  have hs0 : 0 < s := (zpow_pos two_pos j).trans_le hs.1
  have hr0 : 0 < r := (zpow_pos two_pos k).trans_le hr.1
  have hα := kFunctional_nonneg (C := A) (u := a') hs0.le
  have hβ := kFunctional_nonneg (C := B) (u := b') hr0.le
  have hKa := kFunctional_mono (zpow_pos two_pos j).le hs.1 a'
  have hKb := kFunctional_mono (zpow_pos two_pos k).le hr.1 b'
  have hs2 : s * ‖A.interSnd u‖ ≤ 2 * (2 ^ j * ‖A.interSnd u‖) := by
    rw [← mul_assoc, ← zpow_one_add₀ two_ne_zero, add_comm]
    exact mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _)
  have hr2 : r * ‖B.interSnd v‖ ≤ 2 * (2 ^ k * ‖B.interSnd v‖) := by
    rw [← mul_assoc, ← zpow_one_add₀ two_ne_zero, add_comm]
    exact mul_le_mul_of_nonneg_right hr.2.le (norm_nonneg _)
  refine (lintegral_rpow_mul_kFunctional_le hM₀ hM₁ hK θ hα hβ hs0 hr0 (hu₀.trans
    (by linarith)) (hs2.trans (by linarith [hu₁])) (hv₀.trans (by linarith))
    (hr2.trans (by linarith [hv₁]))).trans_eq ?_
  have hm0 : 0 ≤ min s⁻¹ r⁻¹ := le_min (inv_nonneg.2 hs0.le) (inv_nonneg.2 hr0.le)
  have e : 48 * A.kFunctional s a' * B.kFunctional r b' * (M₀ ^ (1 - θ) * (M₁ * min s⁻¹ r⁻¹) ^ θ)
      = 48 * (M₀ ^ (1 - θ) * M₁ ^ θ) * (s ^ (-θ₀) * A.kFunctional s a' *
        (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ θ * (r ^ (-θ₁) * B.kFunctional r b'))) := by
    rw [Real.mul_rpow hM₁.le hm0, Real.rpow_neg hs0.le, Real.rpow_neg hr0.le]
    have := (Real.rpow_pos_of_pos hs0 θ₀).ne'
    have := (Real.rpow_pos_of_pos hr0 θ₁).ne'
    field_simp
  simp only [max_eq_left hs0.le, max_eq_left hr0.le]
  have hP : 0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by positivity
  have hκ0 : 0 ≤ s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ θ :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hr0.le _))
      (Real.rpow_nonneg hm0 _)
  rw [e, ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 48) hP),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 48),
    ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs0.le _) hα), ENNReal.ofReal_mul hκ0,
    ENNReal.ofReal_ofNat]
  ring

/-- **Bilinear real interpolation** (Bergh–Löfström, §3.13, Exercise 5(b)). Let `T`
be a bilinear map from the intersections `A₀ ∩ A₁` and `B₀ ∩ B₁` of two compatible couples to the
sum space of a third couple `(C₀, C₁)`, with the three endpoint bounds

* `‖T a b‖_{C₀} ≤ M₀ ‖a‖_{A₀} ‖b‖_{B₀}`,
* `‖T a b‖_{C₁} ≤ M₁ ‖a‖_{A₀} ‖b‖_{B₁}`,
* `‖T a b‖_{C₁} ≤ M₁ ‖a‖_{A₁} ‖b‖_{B₀}`.

Then for `θ₀, θ₁ > 0` and Hölder conjugate exponents `p` and `p'`,

`‖T a b‖_{(C₀, C₁)_{θ₀ + θ₁, 1}} ≤ K ‖a‖_{(A₀, A₁)_{θ₀, p}} ‖b‖_{(B₀, B₁)_{θ₁, p'}}`

with `K = 48 c_{θ,1} M₀ ^ (1 - θ) M₁ ^ θ (θ₀⁻¹ + θ₁⁻¹) / (log 2)²`, `θ = θ₀ + θ₁`, where
`c_{θ,1} = kMethodConst θ 1` is finite for `0 < θ < 1` (`kMethodConst_lt_top`). No bound on
`A₁ × B₁` is assumed, and the target carries the smallest secondary exponent `1`. This is the
interpolation step of Keel and Tao's proof of the endpoint Strichartz estimate. -/
theorem kMethodENorm_apply_apply_le [T1Space V] [T1Space W]
    (T : A.inter →ₗ[𝕜] B.inter →ₗ[𝕜] C.SumSpace) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀₀ : ∀ a b, ∃ z : Z₀, T a b = C.fstToSum z ∧ ‖z‖ ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖)
    (h₀₁ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖)
    (h₁₀ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖)
    {θ₀ θ₁ : ℝ} (hθ₀ : 0 < θ₀) (hθ₁ : 0 < θ₁) {p p' : ℝ≥0∞} [p.HolderConjugate p']
    (a : A.inter) (b : B.inter) :
    C.kMethodENorm (θ₀ + θ₁) 1 (T a b) ≤
      48 * kMethodConst (θ₀ + θ₁) 1 *
        ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁) * (θ₀⁻¹ + θ₁⁻¹) / Real.log 2 ^ 2) *
        A.kMethodENorm θ₀ p (A.fstToSum (A.interFst a)) *
        B.kMethodENorm θ₁ p' (B.fstToSum (B.interFst b)) := by
  -- dyadic decompositions of `a` and `b`, and the integrands `f`, `κ`, `g` of the final bound
  obtain ⟨da⟩ := A.nonempty_dyadicDecomposition a
  obtain ⟨db⟩ := B.nonempty_dyadicDecomposition b
  have hK := endpointBounds T h₀₀ h₀₁ h₁₀
  set θ := θ₀ + θ₁
  set a' := A.fstToSum (A.interFst a)
  set b' := B.fstToSum (B.interFst b)
  set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-θ₀) * A.kFunctional (max s 0) a')
  set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-θ₁) * B.kFunctional (max r 0) b')
  set κ : ℝ → ℝ → ℝ≥0∞ := fun s r => ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ θ)
  obtain ⟨hf, hfn⟩ := measurable_and_eLpNorm_eq θ₀ p a'
  obtain ⟨hg, hgn⟩ := measurable_and_eLpNorm_eq θ₁ p' b'
  set Cst := 48 * kMethodConst θ 1 * ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ)
  set L := ENNReal.ofReal (Real.log 2)
  have hL : L ≠ 0 := by simp [L, Real.log_pos one_lt_two]
  -- the double series over dyadic pieces, the double integral, then Schur and Hölder
  have hmain : L * (L * C.kMethodENorm θ 1 (T a b)) ≤
      Cst * (ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) * eLpNorm f p multHaar * eLpNorm g p' multHaar) := by
    have hκ : Measurable (Function.uncurry κ) := by
      simp only [κ, Function.uncurry_def]
      fun_prop
    have hF : Measurable (Function.uncurry fun s r => f s * (κ s r * g r)) :=
      (hf.comp measurable_fst).mul (hκ.mul (hg.comp measurable_snd))
    calc L * (L * C.kMethodENorm θ 1 (T a b))
        ≤ L * (L * ∑' j, ∑' k,
            ∫⁻ t, ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (T (da.u j) (db.u k))) ∂multHaar) := by
          gcongr
          exact kMethodENorm_le_tsum_tsum_lintegral hM₀.le hM₁.le hK θ da db
      _ ≤ ∫⁻ s, ∫⁻ r, Cst * (f s * (κ s r * g r)) ∂multHaar ∂multHaar := by
          -- the dyadic squares `[2 ^ j, 2 ^ (j + 1)) × [2 ^ k, 2 ^ (k + 1))` tile `(0, ∞)²`
          have hI (j : ℤ) : Ico (1 * (2 : ℝ) ^ ((1 : ℝ) * j)) (1 * 2 ^ ((1 : ℝ) * j + |1|)) =
              Ico (2 ^ j) (2 ^ (j + 1)) := by
            simp only [abs_one, one_mul]
            norm_cast
          rw [show L = ENNReal.ofReal (|1| * Real.log 2) by rw [abs_one, one_mul],
            ← ENNReal.tsum_mul_left]
          exact ofReal_mul_tsum_int_le_lintegral_multHaar one_le_two one_pos fun j s hs =>
            ofReal_mul_tsum_int_le_lintegral_multHaar one_le_two one_pos fun k r hr =>
              lintegral_le_mul_kernel_of_mem_Ico hM₀ hM₁ hK (da.norm_interFst_le j)
                (da.zpow_mul_norm_interSnd_le j) (db.norm_interFst_le k)
                (db.zpow_mul_norm_interSnd_le k) (hI j ▸ hs) (hI k ▸ hr)
      _ = Cst * ∫⁻ s, ∫⁻ r, f s * (κ s r * g r) ∂multHaar ∂multHaar := by
          have hmeas : Measurable fun s => ∫⁻ r, f s * (κ s r * g r) ∂multHaar :=
            hF.lintegral_prod_right'
          rw [← lintegral_const_mul _ hmeas]
          exact lintegral_congr fun s => lintegral_const_mul _ (hF.comp measurable_prodMk_left)
      _ ≤ _ := by
          -- Schur's test: `κ` has integral `θ₀⁻¹ + θ₁⁻¹` in each variable
          gcongr
          set c := ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹)
          have hc0 : c ≠ 0 := by
            simp only [c, ne_eq, ENNReal.ofReal_eq_zero, not_le]
            positivity
          have hrow : ∀ᵐ s ∂multHaar, ∫⁻ r, κ s r ∂multHaar ≤ c := by
            filter_upwards [ae_pos_multHaar] with s hs using
              (lintegral_multHaar_rpow_mul_rpow_mul_min_inv_rpow_right hθ₀ hθ₁ hs).le
          have hcol : ∀ᵐ r ∂multHaar, ∫⁻ s, κ s r ∂multHaar ≤ c := by
            filter_upwards [ae_pos_multHaar] with r hr using
              (lintegral_multHaar_rpow_mul_rpow_mul_min_inv_rpow_left hθ₀ hθ₁ hr).le
          refine (lintegral_lintegral_mul_mul_le (p := p) (q := p') hκ.aemeasurable
            hf.aemeasurable hg.aemeasurable hrow hcol).trans_eq ?_
          rw [← ENNReal.rpow_add _ _ hc0 ENNReal.ofReal_ne_top, sub_add_cancel, ENNReal.rpow_one]
  -- divide by `(log 2)²` and identify the two `L^p(dt / t)` norms as `K`-method norms
  calc C.kMethodENorm θ 1 (T a b) = L⁻¹ * (L⁻¹ * (L * (L * C.kMethodENorm θ 1 (T a b)))) := by
        rw [← mul_assoc L⁻¹ L, ENNReal.inv_mul_cancel hL ENNReal.ofReal_ne_top, one_mul,
          ← mul_assoc, ENNReal.inv_mul_cancel hL ENNReal.ofReal_ne_top, one_mul]
    _ ≤ L⁻¹ * (L⁻¹ * (Cst *
          (ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) * eLpNorm f p multHaar * eLpNorm g p' multHaar))) := by
        gcongr
    _ = _ := by
        have hlog := Real.log_pos one_lt_two
        rw [hfn, hgn, ENNReal.ofReal_div_of_pos (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hlog.le, div_eq_mul_inv,
          ENNReal.inv_pow]
        simp only [Cst, L]
        ring

/-- **Bilinear real interpolation** for secondary exponents with `1 / p + 1 / q ≥ 1`, that is
`q ≤ p'` for the exponent `p'` conjugate to `p`: under the hypotheses of
`kMethodENorm_apply_apply_le`,
`‖T a b‖_{(C₀, C₁)_{θ₀ + θ₁, 1}} ≤ K' ‖a‖_{(A₀, A₁)_{θ₀, p}} ‖b‖_{(B₀, B₁)_{θ₁, q}}`
with `K' = K max 1 c_{θ₁,q}⁻¹`.
This is the form stated by Bergh–Löfström and Keel–Tao; it follows from the conjugate case by the
secondary-exponent embedding `(B₀, B₁)_{θ₁, q} ⊆ (B₀, B₁)_{θ₁, p'}`. -/
theorem kMethodENorm_apply_apply_le_of_le [T1Space V] [T1Space W]
    (T : A.inter →ₗ[𝕜] B.inter →ₗ[𝕜] C.SumSpace) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀₀ : ∀ a b, ∃ z : Z₀, T a b = C.fstToSum z ∧ ‖z‖ ≤ M₀ * ‖A.interFst a‖ * ‖B.interFst b‖)
    (h₀₁ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interFst a‖ * ‖B.interSnd b‖)
    (h₁₀ : ∀ a b, ∃ z : Z₁, T a b = C.sndToSum z ∧ ‖z‖ ≤ M₁ * ‖A.interSnd a‖ * ‖B.interFst b‖)
    {θ₀ θ₁ : ℝ} (hθ₀ : 0 < θ₀) (hθ₁ : 0 < θ₁) {p p' q : ℝ≥0∞} [p.HolderConjugate p']
    [Fact (1 ≤ q)] (hq : q ≤ p') (a : A.inter) (b : B.inter) :
    C.kMethodENorm (θ₀ + θ₁) 1 (T a b) ≤
      48 * kMethodConst (θ₀ + θ₁) 1 *
        ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁) * (θ₀⁻¹ + θ₁⁻¹) / Real.log 2 ^ 2) *
        ENNReal.ofReal (max 1 (kMethodConst θ₁ q).toReal⁻¹) *
        A.kMethodENorm θ₀ p (A.fstToSum (A.interFst a)) *
        B.kMethodENorm θ₁ q (B.fstToSum (B.interFst b)) := by
  calc C.kMethodENorm (θ₀ + θ₁) 1 (T a b)
      ≤ 48 * kMethodConst (θ₀ + θ₁) 1 *
          ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁) * (θ₀⁻¹ + θ₁⁻¹) / Real.log 2 ^ 2) *
          A.kMethodENorm θ₀ p (A.fstToSum (A.interFst a)) *
          B.kMethodENorm θ₁ p' (B.fstToSum (B.interFst b)) :=
        kMethodENorm_apply_apply_le T hM₀ hM₁ h₀₀ h₀₁ h₁₀ hθ₀ hθ₁ a b
    _ ≤ 48 * kMethodConst (θ₀ + θ₁) 1 *
          ENNReal.ofReal (M₀ ^ (1 - (θ₀ + θ₁)) * M₁ ^ (θ₀ + θ₁) * (θ₀⁻¹ + θ₁⁻¹) / Real.log 2 ^ 2) *
          A.kMethodENorm θ₀ p (A.fstToSum (A.interFst a)) *
          (ENNReal.ofReal (max 1 (kMethodConst θ₁ q).toReal⁻¹) *
            B.kMethodENorm θ₁ q (B.fstToSum (B.interFst b))) := by
        gcongr
        exact kMethodENorm_le_ofReal_mul_kMethodENorm hq _
    _ = _ := by ring

end Bilinear

end CompatibleCouple

end TauCeti
