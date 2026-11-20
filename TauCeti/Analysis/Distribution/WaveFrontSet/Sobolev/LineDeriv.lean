/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The Sobolev wave front set of a derivative

A derivative costs at most one order of Sobolev regularity, microlocally as well: for a complex
distribution `T` on an open subset `Ω` of a finite-dimensional real inner product space, a direction
`v` and a real `s`, the `H^(s - 1)` wave front set of `∂_{v} T` lies in the `H^s` wave front set of
`T`. Iterating, an iterated derivative `∂^{m}` of order `n` satisfies
`WF_(s - n)(∂^{m} T) ⊆ WF_s(T)`, and a differential operator `P` of order at most `k` with smooth
coefficients satisfies `WF_(s - k)(P T) ⊆ WF_s(T)`.
This is the differential-operator case of the order shift of `H^s` wave front sets under
pseudodifferential operators (Hörmander, *Lectures on Nonlinear Hyperbolic Differential
Equations*, §11.1).

Projecting to the base gives the corresponding statements for the `H^s` singular support: a
differential operator of order at most `k` maps distributions that are `H^s` near a point to
distributions that are `H^(s - k)` near that point
(`Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`), that is, it maps
`H^s_loc` to `H^(s - k)_loc`.

The proof uses the formula `Distribution.localFourier_lineDerivOp`,

`(∂_{v} T) (φ e_η) = 2 π i ⟪v, η⟫ T (φ e_η) - T ((∂_{v} φ) e_η)`,

for a cutoff `φ` near a point at which `T` is microlocally `H^s`: there, every cutoff has weighted
localized Fourier transform square integrable on a fixed cone
(`Distribution.IsMicrolocallySobolevAt.exists_nhds_cone`), and `∂_{v} φ` is supported near the
point as well. The factor `⟪v, η⟫` is bounded by `‖v‖ ⟨η⟩`, where `⟨η⟩ = (1 + ‖η‖ ^ 2) ^ (1 / 2)`,
which is absorbed by the weight `⟨η⟩ ^ (s - 1) ⟨η⟩ = ⟨η⟩ ^ s`.

## Main results

* `Distribution.IsMicrolocallySobolevAt.lineDerivOp`,
  `Distribution.IsMicrolocallySobolevAt.iteratedLineDerivOp`: if `T` is microlocally `H^s` at
  `(x, ξ)`, then `∂_{v} T` is microlocally `H^(s - 1)` there, and an iterated derivative of order
  `n` is microlocally `H^(s - n)`.
* `Distribution.sobolevWaveFrontSet_lineDerivOp_subset`,
  `Distribution.sobolevWaveFrontSet_iteratedLineDerivOp_subset`: `WF_(s - 1)(∂_{v} T) ⊆ WF_s(T)`
  and `WF_(s - n)(∂^{m} T) ⊆ WF_s(T)`.
* `Distribution.IsMicrolocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`,
  `Distribution.sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: a
  differential operator `P = ∑ i, c i g i ∂^{m i}` of order at most `k`, with smooth real
  coefficients `g i` and complex constants `c i`, maps microlocally `H^s` distributions to
  microlocally `H^(s - k)` ones, so `WF_(s - k)(P T) ⊆ WF_s(T)`.
* `Distribution.IsLocallySobolevAt.lineDerivOp`,
  `Distribution.IsLocallySobolevAt.iteratedLineDerivOp`,
  `Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp` and
  `Distribution.sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: the same
  for local `H^s` regularity and the `H^s` singular support.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and its behaviour under differential operators).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Real Set TopologicalSpace TestFunction LineDeriv
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-- The polynomial factor of `Distribution.localFourier_lineDerivOp` costs one order of the
Sobolev weight: `⟨η⟩ ^ (s - 1) ‖2 π i ⟪v, η⟫‖ ≤ 2 π ‖v‖ ⟨η⟩ ^ s`. -/
private theorem weight_mul_norm_two_mul_pi_mul_I_mul_inner_le (s : ℝ) (v η : E) :
    (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ ≤
      2 * π * ‖v‖ * (1 + ‖η‖ ^ 2) ^ (s / 2) := by
  have hn : ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ = 2 * π * |⟪v, η⟫| := by
    simp [abs_of_pos pi_pos]
  -- `⟨η⟩ ^ (s - 1) ‖η‖ ≤ ⟨η⟩ ^ s`.
  have hw := TauCeti.one_add_norm_sq_rpow_mul_norm_le η (s - 1)
  rw [sub_add_cancel] at hw
  rw [hn]
  calc (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * (2 * π * |⟪v, η⟫|)
      ≤ (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * (2 * π * (‖v‖ * ‖η‖)) := by
        gcongr
        exact abs_real_inner_le_norm v η
    _ = 2 * π * ‖v‖ * ((1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖η‖) := by
        ring
    _ ≤ 2 * π * ‖v‖ * (1 + ‖η‖ ^ 2) ^ (s / 2) := by
        gcongr

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A derivative `∂_{v} T` of a distribution microlocally `H^s` at `(x, ξ)` is microlocally
`H^(s - 1)` there. -/
theorem IsMicrolocallySobolevAt.lineDerivOp {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) (v : E) :
    (∂_{v} T).IsMicrolocallySobolevAt (s - 1) x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySobolevAt_iff.1 h
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hL⟩ := h.exists_nhds_cone
  -- A cutoff supported in `U`; its derivative is supported in `U` as well.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  refine isMicrolocallySobolevAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, ?_⟩
  have h₁ := (hL ψ (hψ.trans inter_subset_left)).norm.const_mul (2 * π * ‖v‖)
  have h₂ := (hL (∂_{v} ψ)
    ((tsupport_lineDerivOp_subset ψ v).trans (hψ.trans inter_subset_left))).norm
  refine (h₁.add h₂).of_le (((Function.hasTemperateGrowth_one_add_norm_sq_rpow E
    ((s - 1) / 2)).1.continuous.smul
      ((∂_{v} T).continuous_localFourier ψ)).aestronglyMeasurable) (.of_forall fun η ↦ ?_)
  have hw : 0 ≤ (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) := by positivity
  have hw' : 0 ≤ (1 + ‖η‖ ^ 2) ^ (s / 2) := by positivity
  have hle : (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) ≤ (1 + ‖η‖ ^ 2) ^ (s / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [norm_nonneg η]) (by linarith)
  have key : ‖(∂_{v} T).localFourier ψ η‖ ≤
      ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ * ‖T.localFourier ψ η‖ + ‖T.localFourier (∂_{v} ψ) η‖ := by
    rw [localFourier_lineDerivOp, ← norm_mul]
    exact norm_sub_le _ _
  simp only [Pi.add_apply, norm_smul, Real.norm_of_nonneg hw, Real.norm_of_nonneg hw']
  rw [Real.norm_of_nonneg (by positivity)]
  calc (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖(∂_{v} T).localFourier ψ η‖
      ≤ (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ * ‖T.localFourier ψ η‖ +
          (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖T.localFourier (∂_{v} ψ) η‖ := by
        rw [mul_assoc, ← mul_add]
        gcongr
    _ ≤ 2 * π * ‖v‖ * (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier ψ η‖ +
          (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier (∂_{v} ψ) η‖ := by
        exact add_le_add (mul_le_mul_of_nonneg_right
          (weight_mul_norm_two_mul_pi_mul_I_mul_inner_le s v η) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hle (norm_nonneg _))
    _ = 2 * π * ‖v‖ * ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier ψ η‖) +
          (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier (∂_{v} ψ) η‖ := by
        ring

/-- An iterated derivative `∂^{m}` of order `n` of a distribution microlocally `H^s` at `(x, ξ)`
is microlocally `H^(s - n)` there. -/
theorem IsMicrolocallySobolevAt.iteratedLineDerivOp {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) {n : ℕ} (m : Fin n → E) :
    (∂^{m} T).IsMicrolocallySobolevAt (s - n) x ξ := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, Nat.cast_succ, ← sub_sub]
    exact (ih _).lineDerivOp _

/-- **A derivative costs one order of microlocal Sobolev regularity**:
`WF_(s - 1)(∂_{v} T) ⊆ WF_s(T)`. -/
theorem sobolevWaveFrontSet_lineDerivOp_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) (v : E) :
    (∂_{v} T).sobolevWaveFrontSet (s - 1) ⊆ T.sobolevWaveFrontSet s := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  exact mem_sobolevWaveFrontSet_iff.2 ⟨hx, hξ, fun h ↦ hT (h.lineDerivOp v)⟩

/-- An iterated derivative of order `n` costs `n` orders of microlocal Sobolev regularity:
`WF_(s - n)(∂^{m} T) ⊆ WF_s(T)`. -/
theorem sobolevWaveFrontSet_iteratedLineDerivOp_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) {n : ℕ}
    (m : Fin n → E) : (∂^{m} T).sobolevWaveFrontSet (s - n) ⊆ T.sobolevWaveFrontSet s := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  exact mem_sobolevWaveFrontSet_iff.2 ⟨hx, hξ, fun h ↦ hT (h.iteratedLineDerivOp m)⟩

/-- A linear differential operator `P = ∑ i ∈ t, c i g i ∂^{m i}` of order at most `k`, with
smooth real coefficient functions `g i`, complex constants `c i` and iterated derivatives
`∂^{m i}` of orders `n i ≤ k`, maps a distribution microlocally `H^s` at `(x, ξ)` to one
microlocally `H^(s - k)` there. -/
theorem IsMicrolocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp {s : ℝ}
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (h : T.IsMicrolocallySobolevAt s x ξ) {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {n : ι → ℕ}
    (m : ∀ i, Fin (n i) → E) {k : ℕ} (hk : ∀ i ∈ t, n i ≤ k) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsMicrolocallySobolevAt
      (s - k) x ξ :=
  Finset.sum_induction _ (fun S : 𝓓'(Ω, ℂ) ↦ S.IsMicrolocallySobolevAt (s - k) x ξ)
    (fun _ _ ↦ IsMicrolocallySobolevAt.add)
    (zero_smul ℂ T ▸ (h.mono (sub_le_self _ k.cast_nonneg)).smul 0)
    fun i hi ↦ (((h.iteratedLineDerivOp (m i)).mono (by gcongr; exact hk i hi)).smulLeftCLM
      (hg i)).smul (c i)

/-- **Differential operators shift the Sobolev wave front set by their order.** A linear
differential operator `P = ∑ i ∈ t, c i g i ∂^{m i}` of order at most `k`, with smooth real
coefficient functions `g i`, complex constants `c i` and iterated derivatives `∂^{m i}` of
orders `n i ≤ k`, satisfies `WF_(s - k)(P T) ⊆ WF_s(T)`. -/
theorem sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset (s : ℝ)
    {ι : Type*} (t : Finset ι) (c : ι → ℂ) {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {n : ι → ℕ} (m : ∀ i, Fin (n i) → E) {k : ℕ} (hk : ∀ i ∈ t, n i ≤ k) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).sobolevWaveFrontSet (s - k) ⊆
      T.sobolevWaveFrontSet s :=
  (sobolevWaveFrontSet_sum_subset _ t _).trans <| iUnion₂_subset fun i hi ↦
    (sobolevWaveFrontSet_smul_subset _ _ _).trans <|
      (sobolevWaveFrontSet_smulLeftCLM_subset _ _ (hg i)).trans <| inter_subset_left.trans <|
        (sobolevWaveFrontSet_mono (by gcongr; exact hk i hi) _).trans
          (sobolevWaveFrontSet_iteratedLineDerivOp_subset s T (m i))

/-! ### Local `H^s` regularity and the `H^s` singular support -/

section Local

variable {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}

/-- A derivative `∂_v T` of a distribution `H^s` near `x` is `H^(s - 1)` near `x`. -/
theorem IsLocallySobolevAt.lineDerivOp (hT : T.IsLocallySobolevAt s x) (v : E) :
    (∂_{v} T).IsLocallySobolevAt (s - 1) x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hT.mem).2 fun ξ _ ↦
    (hT.isMicrolocallySobolevAt ξ).lineDerivOp v

/-- An iterated derivative `∂^m T` of order `n` of a distribution `H^s` near `x` is `H^(s - n)`
near `x`. -/
theorem IsLocallySobolevAt.iteratedLineDerivOp (hT : T.IsLocallySobolevAt s x) {n : ℕ}
    (m : Fin n → E) : (∂^{m} T).IsLocallySobolevAt (s - n) x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hT.mem).2 fun ξ _ ↦
    (hT.isMicrolocallySobolevAt ξ).iteratedLineDerivOp m

/-- The `H^s` singular support of a derivative: `singsupp_(s - 1)(∂_v T) ⊆ singsupp_s(T)`. -/
theorem sobolevSingularSupport_lineDerivOp_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) (v : E) :
    (∂_{v} T).sobolevSingularSupport (s - 1) ⊆ T.sobolevSingularSupport s := fun _ hx ↦
  mem_sobolevSingularSupport_iff.2 ⟨(mem_sobolevSingularSupport_iff.1 hx).1,
    fun hT ↦ (mem_sobolevSingularSupport_iff.1 hx).2 (hT.lineDerivOp v)⟩

/-- The `H^s` singular support of an iterated derivative of order `n`:
`singsupp_(s - n)(∂^m T) ⊆ singsupp_s(T)`. -/
theorem sobolevSingularSupport_iteratedLineDerivOp_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) {n : ℕ}
    (m : Fin n → E) : (∂^{m} T).sobolevSingularSupport (s - n) ⊆ T.sobolevSingularSupport s :=
  fun _ hx ↦ mem_sobolevSingularSupport_iff.2 ⟨(mem_sobolevSingularSupport_iff.1 hx).1,
    fun hT ↦ (mem_sobolevSingularSupport_iff.1 hx).2 (hT.iteratedLineDerivOp m)⟩

/-- **Differential operators shift the `H^s` singular support by their order.** For a differential
operator `P T = ∑ i ∈ t, c i • g i ∂^(m i) T` with smooth coefficients and orders `n i ≤ k`,
`singsupp_(s - k)(P T) ⊆ singsupp_s(T)`. -/
theorem sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset (s : ℝ)
    {ι : Type*} (t : Finset ι) (c : ι → ℂ) {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {n : ι → ℕ} (m : ∀ i, Fin (n i) → E) {k : ℕ} (hk : ∀ i ∈ t, n i ≤ k) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).sobolevSingularSupport (s - k) ⊆
      T.sobolevSingularSupport s := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet]
  exact image_mono (sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset s t c hg
    m hk T)

/-- **Differential operators map `H^s_loc` to `H^(s - k)_loc`.** If `T` is `H^s` near `x`, then
`P T = ∑ i ∈ t, c i • g i ∂^(m i) T`, with smooth coefficients and orders `n i ≤ k`, is
`H^(s - k)` near `x`. -/
theorem IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp (hT : T.IsLocallySobolevAt s x)
    {ι : Type*} (t : Finset ι) (c : ι → ℂ) {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {n : ι → ℕ} (m : ∀ i, Fin (n i) → E) {k : ℕ} (hk : ∀ i ∈ t, n i ≤ k) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt (s - k) x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hT.mem).2 fun ξ _ ↦
    (hT.isMicrolocallySobolevAt ξ).sum_smul_smulLeftCLM_iteratedLineDerivOp t c hg m hk

end Local

end Distribution
