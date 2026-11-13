/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The Sobolev wave front set under differentiation and differential operators

A derivative costs at most one Sobolev order, also microlocally: if a complex distribution `T` is
microlocally `H^s` at `(x, ξ)`, then `∂_v T` is microlocally `H^(s - 1)` there. Hence

`WF_(s - 1)(∂_v T) ⊆ WF_s(T)` and `WF_(s - k)(∂^m T) ⊆ WF_s(T)`

for an iterated derivative of order `k`. Together with the sum and smooth-multiplication rules
`Distribution.sobolevWaveFrontSet_sum_subset` and
`Distribution.sobolevWaveFrontSet_smulLeftCLM_subset`, a differential operator
`P = ∑ c_α a_α ∂^α` of order at most `N` with smooth coefficients satisfies the **order shift**
`WF_(s - N)(P T) ⊆ WF_s(T)`
(`Distribution.sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`). This is the
`H^s` refinement of `Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`,
and the case of differential operators of the order shift `WF_(s - m)(P T) ⊆ WF_s(T)` for
pseudodifferential operators of order `m`.

Projecting to the base gives the corresponding statements for the `H^s` singular support: a
differential operator of order at most `N` maps distributions that are `H^s` near a point to
distributions that are `H^(s - N)` near that point
(`Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`), that is, it maps
`H^s_loc` to `H^(s - N)_loc`.

The proof uses the localized Fourier transform `η ↦ T (φ e_η)` and the product rule

`(∂_v T) (φ e_η) = 2πi ⟪v, η⟫ T (φ e_η) - T ((∂_v φ) e_η)`

(`Distribution.localFourier_lineDerivOp`). The factor `⟪v, η⟫` is bounded by `‖v‖ ⟨η⟩`, where
`⟨η⟩ = (1 + ‖η‖ ^ 2) ^ (1 / 2)`, so it is absorbed by one power of the Sobolev weight
(`TauCeti.one_add_norm_sq_rpow_mul_norm_le`), and the second term is `H^s` on the same cone since
the cutoff `∂_v φ` is supported where `φ` is.

## Main results

* `Distribution.IsMicrolocallySobolevAt.lineDerivOp`,
  `Distribution.IsMicrolocallySobolevAt.iteratedLineDerivOp`: microlocal `H^s` regularity of
  derivatives.
* `Distribution.sobolevWaveFrontSet_lineDerivOp_subset`,
  `Distribution.sobolevWaveFrontSet_iteratedLineDerivOp_subset`: the `H^s` wave front sets of
  derivatives.
* `Distribution.sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: the order
  shift of the `H^s` wave front set under differential operators with smooth coefficients.
* `Distribution.IsLocallySobolevAt.lineDerivOp`,
  `Distribution.IsLocallySobolevAt.iteratedLineDerivOp`,
  `Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp` and
  `Distribution.sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: the same
  for local `H^s` regularity and the `H^s` singular support.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
-/

public section

noncomputable section

open Complex Filter LineDeriv MeasureTheory Real Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}

/-! ### The `H^s` wave front set -/

/-- A derivative `∂_v T` of a distribution microlocally `H^s` at `(x, ξ)` is microlocally
`H^(s - 1)` there. -/
theorem IsMicrolocallySobolevAt.lineDerivOp (hT : T.IsMicrolocallySobolevAt s x ξ) (v : E) :
    (∂_{v} T).IsMicrolocallySobolevAt (s - 1) x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySobolevAt_iff.1 hT
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hL⟩ := hT.exists_nhds_cone
  obtain ⟨φ, hφU, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  have hφU' : tsupport φ ⊆ U := hφU.trans inter_subset_left
  refine isMicrolocallySobolevAt_iff.2 ⟨φ, by simp [hφx], Γ, hΓ, hξ, hcone, ?_⟩
  -- Both terms of `localFourier_lineDerivOp` are `H^s` on `Γ`; the factor `⟪v, η⟫` costs one
  -- order of the weight.
  have h₁ := (hL φ hφU').norm.const_mul (2 * π * ‖v‖)
  have h₂ := (hL (∂_{v} φ) ((tsupport_fderiv_apply_subset ℝ v).trans hφU')).norm
  refine (h₁.add h₂).mono
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E ((s - 1) / 2)).1.continuous.smul
      ((∂_{v} T).continuous_localFourier φ)).aestronglyMeasurable (.of_forall fun η ↦ ?_)
  have hw : 1 ≤ 1 + ‖η‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  have hle : (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) ≤ (1 + ‖η‖ ^ 2) ^ (s / 2) :=
    Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  have hinner : (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ ≤
      2 * π * ‖v‖ * (1 + ‖η‖ ^ 2) ^ (s / 2) := by
    have hη := TauCeti.one_add_norm_sq_rpow_mul_norm_le η (s - 1)
    rw [sub_add_cancel] at hη
    calc (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ =
          2 * π * ((1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * |⟪v, η⟫|) := by
          rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Complex.norm_real,
            Complex.norm_two, Real.norm_of_nonneg pi_pos.le, Real.norm_eq_abs]
          ring
      _ ≤ 2 * π * ((1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * (‖v‖ * ‖η‖)) := by
          gcongr
          exact abs_real_inner_le_norm v η
      _ = 2 * π * ‖v‖ * ((1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖η‖) := by ring
      _ ≤ 2 * π * ‖v‖ * (1 + ‖η‖ ^ 2) ^ (s / 2) := by gcongr
  rw [Pi.add_apply, Real.norm_of_nonneg (by positivity), localFourier_lineDerivOp, norm_smul,
    norm_smul, norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) *
        ‖2 * π * I * ⟪v, η⟫ * T.localFourier φ η - T.localFourier (∂_{v} φ) η‖
      ≤ (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) *
          (‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ * ‖T.localFourier φ η‖ + ‖T.localFourier (∂_{v} φ) η‖) := by
        gcongr
        exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])
    _ = (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ * ‖T.localFourier φ η‖ +
          (1 + ‖η‖ ^ 2) ^ ((s - 1) / 2) * ‖T.localFourier (∂_{v} φ) η‖ := by ring
    _ ≤ 2 * π * ‖v‖ * (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier φ η‖ +
          (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier (∂_{v} φ) η‖ := by
        gcongr
    _ = 2 * π * ‖v‖ * ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier φ η‖) +
          (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier (∂_{v} φ) η‖ := by ring

/-- An iterated derivative `∂^m T` of order `n` of a distribution microlocally `H^s` at `(x, ξ)` is
microlocally `H^(s - n)` there. -/
theorem IsMicrolocallySobolevAt.iteratedLineDerivOp (hT : T.IsMicrolocallySobolevAt s x ξ)
    {n : ℕ} (m : Fin n → E) : (∂^{m} T).IsMicrolocallySobolevAt (s - n) x ξ := by
  induction n with
  | zero => simpa using hT
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, Nat.cast_succ, ← sub_sub]
    exact (ih _).lineDerivOp _

/-- **The `H^s` wave front set of a derivative.** A derivative costs one Sobolev order:
`WF_(s - 1)(∂_v T) ⊆ WF_s(T)`. -/
theorem sobolevWaveFrontSet_lineDerivOp_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) (v : E) :
    (∂_{v} T).sobolevWaveFrontSet (s - 1) ⊆ T.sobolevWaveFrontSet s := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hvT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  exact mem_sobolevWaveFrontSet_iff.2 ⟨hx, hξ, fun hT ↦ hvT (hT.lineDerivOp v)⟩

/-- The `H^s` wave front set of an iterated derivative of order `n`:
`WF_(s - n)(∂^m T) ⊆ WF_s(T)`. -/
theorem sobolevWaveFrontSet_iteratedLineDerivOp_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) {n : ℕ}
    (m : Fin n → E) : (∂^{m} T).sobolevWaveFrontSet (s - n) ⊆ T.sobolevWaveFrontSet s := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hmT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  exact mem_sobolevWaveFrontSet_iff.2 ⟨hx, hξ, fun hT ↦ hmT (hT.iteratedLineDerivOp m)⟩

/-- **Differential operators shift the `H^s` wave front set by their order.** For finitely many
smooth real coefficients `a i`, complex constants `c i` and iterated directions `m i` of orders
`k i ≤ N`, the operator `P T = ∑ i ∈ t, c i • a i ∂^(m i) T` satisfies
`WF_(s - N)(P T) ⊆ WF_s(T)`. Writing a smooth complex coefficient as `u + i v`, this covers every
linear differential operator of order at most `N` with smooth complex coefficients. -/
theorem sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset (s : ℝ) {ι : Type*}
    (t : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i)) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) {N : ℕ} (hk : ∀ i ∈ t, k i ≤ N) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • smulLeftCLM (ha i) (∂^{m i} T)).sobolevWaveFrontSet (s - N) ⊆
      T.sobolevWaveFrontSet s :=
  (sobolevWaveFrontSet_sum_subset _ t _).trans <| iUnion₂_subset fun i hi ↦
    (sobolevWaveFrontSet_smul_subset _ _ _).trans <|
      (sobolevWaveFrontSet_smulLeftCLM_subset _ _ _).trans <| inter_subset_left.trans <|
        (sobolevWaveFrontSet_mono (by gcongr; exact_mod_cast hk i hi) _).trans
          (sobolevWaveFrontSet_iteratedLineDerivOp_subset s T (m i))

/-! ### Local `H^s` regularity and the `H^s` singular support -/

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
operator `P T = ∑ i ∈ t, c i • a i ∂^(m i) T` with smooth coefficients and orders `k i ≤ N`,
`singsupp_(s - N)(P T) ⊆ singsupp_s(T)`. -/
theorem sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset (s : ℝ)
    {ι : Type*} (t : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i))
    {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {N : ℕ} (hk : ∀ i ∈ t, k i ≤ N) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • smulLeftCLM (ha i) (∂^{m i} T)).sobolevSingularSupport (s - N) ⊆
      T.sobolevSingularSupport s := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet]
  exact image_mono (sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset s t c ha
    m hk T)

/-- **Differential operators map `H^s_loc` to `H^(s - N)_loc`.** If `T` is `H^s` near `x`, then
`P T = ∑ i ∈ t, c i • a i ∂^(m i) T`, with smooth coefficients and orders `k i ≤ N`, is
`H^(s - N)` near `x`. -/
theorem IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp (hT : T.IsLocallySobolevAt s x)
    {ι : Type*} (t : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i))
    {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {N : ℕ} (hk : ∀ i ∈ t, k i ≤ N) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (ha i) (∂^{m i} T)).IsLocallySobolevAt (s - N) x := by
  by_contra h
  exact (mem_sobolevSingularSupport_iff.1
    (sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset s t c ha m hk T
      (mem_sobolevSingularSupport_iff.2 ⟨hT.mem, h⟩))).2 hT

end Distribution
