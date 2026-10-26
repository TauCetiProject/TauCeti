/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Regular
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Integral.RieszMarkovKakutani.Signed

/-!
# Distributions of order zero are Radon measures

Let `Ω` be an open set of a finite-dimensional real normed space `E`. A distribution
`T ∈ 𝓓'(Ω, ℝ)` has **order zero** if on each compact `K ⊆ Ω` it is bounded in the sup norm:
`|T φ| ≤ C_K ‖φ‖_∞` for the test functions `φ` supported in `K`. Such a distribution is the
difference of two regular measures on `Ω`:
`T φ = ∫ φ dν₁ - ∫ φ dν₂`, and conversely such a difference has order zero
(`Distribution.forall_exists_abs_le_iff_exists_regular`). The measures are finite on compact
subsets of `Ω` but need not be finite.

This is how a derivative of locally finite total variation becomes a measure: the distributional
derivatives of a function of locally bounded variation have order zero.

The proof extends `T` to compactly supported continuous functions on `Ω`. Mollifying a continuous
function with compact support in `Ω` by bumps of small radius gives test functions supported in a
fixed compact subset of `Ω` that converge to it uniformly
(`Continuous.exists_testFunction_dist_le`), and the sup-norm bound makes the values of `T` along
such a sequence converge, to a limit independent of the sequence. The extension is a linear
functional on `C_c(Ω, ℝ)` that is bounded on order intervals, so the Riesz–Markov–Kakutani theorem
for order-bounded functionals (`TauCeti.RealRMK.forall_bddAbove_image_Icc_iff_exists_regular`)
represents it by two regular measures.

The converse uses the sup-norm bound for integrals of test functions
(`TestFunction.norm_integral_le_measureReal_mul_norm`).

## Main results

* `Distribution.forall_exists_abs_le_iff_exists_regular`: a distribution has order zero if and
  only if it is the difference of the integrals against two regular measures on `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1 (distributions
  of order zero are measures).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §1.8 (the Riesz representation theorem) and §5.1 (its use for functions of bounded
  variation).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Metric Set CompactlySupportedContinuousMap
open scoped Distributions Topology BoundedContinuousFunction CompactlySupported

variable {E : Type*} [NormedAddCommGroup E] {Ω : Opens E}

namespace Distribution

/-! ### The extension of an order-zero distribution to continuous functions -/

/-- The extension by zero to `E` of a compactly supported continuous function on `Ω`. -/
private def zeroExt (f : C_c(Ω, ℝ)) : E → ℝ :=
  Function.extend Subtype.val f 0

open scoped Classical in
private lemma zeroExt_apply (f : C_c(Ω, ℝ)) (x : E) :
    zeroExt f x = if h : x ∈ Ω then f ⟨x, h⟩ else 0 := by
  split_ifs with h
  · exact Subtype.val_injective.extend_apply _ _ (⟨x, h⟩ : Ω)
  · exact Function.extend_apply' _ _ _ fun ⟨y, hy⟩ => h (hy ▸ y.2)

private lemma zeroExt_add (f g : C_c(Ω, ℝ)) (x : E) :
    zeroExt (f + g) x = zeroExt f x + zeroExt g x := by
  simp only [zeroExt_apply]
  split_ifs <;> simp

private lemma zeroExt_smul (c : ℝ) (f : C_c(Ω, ℝ)) (x : E) :
    zeroExt (c • f) x = c * zeroExt f x := by
  simp only [zeroExt_apply]
  split_ifs <;> simp

private lemma continuous_zeroExt (f : C_c(Ω, ℝ)) : Continuous (zeroExt f) :=
  f.hasCompactSupport.continuous_extend_zero Ω.isOpen f.continuous

private lemma tsupport_zeroExt_subset (f : C_c(Ω, ℝ)) :
    tsupport (zeroExt f) ⊆ (↑) '' tsupport f :=
  f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val

private lemma isCompact_image_tsupport (f : C_c(Ω, ℝ)) :
    IsCompact (((↑) : Ω → E) '' tsupport f) :=
  f.hasCompactSupport.isCompact.image continuous_subtype_val

variable [NormedSpace ℝ E]

private lemma zeroExt_toCompactlySupportedContinuousMap (φ : 𝓓(Ω, ℝ)) (x : E) :
    zeroExt φ.toCompactlySupportedContinuousMap x = φ x := by
  rw [zeroExt_apply]
  split_ifs with h
  · exact TestFunction.toCompactlySupportedContinuousMap_apply φ ⟨x, h⟩
  · exact (φ.zero_on_compl h).symm

/-- On a compact `K ⊆ Ω`, an order-zero bound can be taken with a nonnegative constant and tested
against any pointwise bound. -/
private lemma exists_nonneg_bound {T : 𝓓'(Ω, ℝ)}
    (hT : ∀ K, IsCompact K → K ⊆ Ω → ∃ C, ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ K →
      |T φ| ≤ C * ‖(φ : E →ᵇ ℝ)‖) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C, 0 ≤ C ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ K → ∀ c, (∀ x, |φ x| ≤ c) → |T φ| ≤ C * c := by
  obtain ⟨C, hC⟩ := hT K hK hKΩ
  refine ⟨max C 0, le_max_right _ _, fun φ hφ c hc => ?_⟩
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  have hφc : ‖(φ : E →ᵇ ℝ)‖ ≤ c := (BoundedContinuousFunction.norm_le hc0).2 fun x => by
    simpa using hc x
  exact (hC φ hφ).trans <| (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hφc (le_max_right _ _))

/-- `φ` is a sequence of test functions, supported in a common compact subset of `Ω`, that
approximates the extension by zero of `f` uniformly, with error at most `ε n` at step `n`. -/
private def IsApprox (f : C_c(Ω, ℝ)) (φ : ℕ → 𝓓(Ω, ℝ)) (ε : ℕ → ℝ) : Prop :=
  (∃ K, IsCompact K ∧ K ⊆ Ω ∧ ∀ n, tsupport (φ n) ⊆ K) ∧
    ∀ n x, |φ n x - zeroExt f x| ≤ ε n

private lemma isApprox_toCompactlySupportedContinuousMap (φ : 𝓓(Ω, ℝ)) :
    IsApprox φ.toCompactlySupportedContinuousMap (fun _ => φ) 0 :=
  ⟨⟨tsupport φ, φ.hasCompactSupport.isCompact, φ.tsupport_subset, fun _ => subset_rfl⟩,
    fun _ x => by simp [zeroExt_toCompactlySupportedContinuousMap]⟩

private lemma IsApprox.add {f g : C_c(Ω, ℝ)} {φ ψ : ℕ → 𝓓(Ω, ℝ)} {ε ε' : ℕ → ℝ}
    (hφ : IsApprox f φ ε) (hψ : IsApprox g ψ ε') :
    IsApprox (f + g) (φ + ψ) fun n => ε n + ε' n := by
  obtain ⟨⟨K, hK, hKΩ, hφK⟩, hφε⟩ := hφ
  obtain ⟨⟨K', hK', hK'Ω, hψK⟩, hψε⟩ := hψ
  refine ⟨⟨K ∪ K', hK.union hK', union_subset hKΩ hK'Ω, fun n => ?_⟩, fun n x => ?_⟩
  · exact (tsupport_add (φ n) (ψ n)).trans (union_subset_union (hφK n) (hψK n))
  · calc |(φ + ψ) n x - zeroExt (f + g) x|
        = |(φ n x - zeroExt f x) + (ψ n x - zeroExt g x)| := by
          rw [zeroExt_add, Pi.add_apply, FunLike.coe_add, Pi.add_apply]
          congr 1
          ring
      _ ≤ ε n + ε' n := (abs_add_le _ _).trans (add_le_add (hφε n x) (hψε n x))

private lemma IsApprox.smul {f : C_c(Ω, ℝ)} {φ : ℕ → 𝓓(Ω, ℝ)} {ε : ℕ → ℝ}
    (hφ : IsApprox f φ ε) (c : ℝ) : IsApprox (c • f) (c • φ) (fun n => |c| * ε n) := by
  obtain ⟨⟨K, hK, hKΩ, hφK⟩, hφε⟩ := hφ
  refine ⟨⟨K, hK, hKΩ, fun n => ?_⟩, fun n x => ?_⟩
  · exact (closure_mono (Function.support_const_smul_subset c _)).trans (hφK n)
  · simpa [zeroExt_smul, ← mul_sub, abs_mul] using
      mul_le_mul_of_nonneg_left (hφε n x) (abs_nonneg c)

variable {T : 𝓓'(Ω, ℝ)}
  (hT : ∀ K, IsCompact K → K ⊆ Ω → ∃ C, ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ K →
  |T φ| ≤ C * ‖(φ : E →ᵇ ℝ)‖)
include hT

/-- Two approximating sequences of the same function have values under `T` that are close, up to
a constant times the sum of their errors. -/
private lemma IsApprox.exists_abs_sub_le {f : C_c(Ω, ℝ)} {φ ψ : ℕ → 𝓓(Ω, ℝ)} {ε ε' : ℕ → ℝ}
    (hφ : IsApprox f φ ε) (hψ : IsApprox f ψ ε') :
    ∃ C, 0 ≤ C ∧ ∀ m n, |T (φ m) - T (ψ n)| ≤ C * (ε m + ε' n) := by
  obtain ⟨⟨K, hK, hKΩ, hφK⟩, hφε⟩ := hφ
  obtain ⟨⟨K', hK', hK'Ω, hψK⟩, hψε⟩ := hψ
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_bound hT (hK.union hK') (union_subset hKΩ hK'Ω)
  refine ⟨C, hC0, fun m n => ?_⟩
  rw [← map_sub]
  refine hC _ ?_ _ fun x => ?_
  · refine closure_minimal ?_ (hK.union hK').isClosed
    simpa using (Function.support_sub (φ m) (ψ n)).trans
      (union_subset_union ((subset_tsupport _).trans (hφK m)) ((subset_tsupport _).trans (hψK n)))
  · simpa using (abs_sub_le (φ m x) (zeroExt f x) (ψ n x)).trans
      (add_le_add (hφε m x) ((abs_sub_comm _ _).trans_le (hψε n x)))

variable [FiniteDimensional ℝ E]

omit hT in
/-- Every compactly supported continuous function on `Ω` has an approximating sequence with
errors `1 / (n + 1)`, supported in any closed thickening inside `Ω` of a compact set containing
its support. -/
private lemma exists_isApprox_of_subset (f : C_c(Ω, ℝ)) {K : Set E} (hK : IsCompact K)
    (hfK : ((↑) : Ω → E) '' tsupport f ⊆ K) {δ : ℝ} (hδ : 0 < δ) (hKΩ : cthickening δ K ⊆ Ω) :
    ∃ φ : ℕ → 𝓓(Ω, ℝ), (∀ n, tsupport (φ n) ⊆ cthickening δ K) ∧
      IsApprox f φ fun n => 1 / ((n : ℝ) + 1) := by
  have h (n : ℕ) := (continuous_zeroExt f).exists_testFunction_dist_le hK
    ((tsupport_zeroExt_subset f).trans hfK) hδ hKΩ (Nat.one_div_pos_of_nat (n := n))
  choose φ hφK hφ using h
  exact ⟨φ, hφK, ⟨cthickening δ K, hK.cthickening, hKΩ, hφK⟩,
    fun n x => by simpa [Real.dist_eq] using hφ n x⟩

omit hT in
private lemma exists_isApprox (f : C_c(Ω, ℝ)) :
    ∃ φ : ℕ → 𝓓(Ω, ℝ), IsApprox f φ fun n => 1 / ((n : ℝ) + 1) := by
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_image_tsupport f).exists_cthickening_subset_open Ω.isOpen
    (Subtype.coe_image_subset _ _)
  obtain ⟨φ, -, hφ⟩ := exists_isApprox_of_subset f (isCompact_image_tsupport f) subset_rfl hδ hδΩ
  exact ⟨φ, hφ⟩

omit hT in
/-- The extension of `T` to a compactly supported continuous function `f` on `Ω`: the limit of
the values of `T` along a chosen approximating sequence of `f`. -/
private def extend (T : 𝓓'(Ω, ℝ)) (f : C_c(Ω, ℝ)) : ℝ :=
  limUnder atTop fun n => T ((exists_isApprox f).choose n)

/-- Along every approximating sequence of `f` with errors tending to zero, the values of `T`
converge to the extension of `T` at `f`. -/
private lemma IsApprox.tendsto_extend {f : C_c(Ω, ℝ)} {φ : ℕ → 𝓓(Ω, ℝ)} {ε : ℕ → ℝ}
    (hφ : IsApprox f φ ε) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => T (φ n)) atTop (𝓝 (extend T f)) := by
  set a := (exists_isApprox f).choose
  have ha : IsApprox f a fun n => 1 / ((n : ℝ) + 1) := (exists_isApprox f).choose_spec
  -- The chosen sequence is Cauchy under `T`, so it converges to `extend T f`.
  have hlim : Tendsto (fun n => T (a n)) atTop (𝓝 (extend T f)) := by
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    obtain ⟨C, hC0, hC⟩ := ha.exists_abs_sub_le hT ha
    refine cauchySeq_of_le_tendsto_0 (fun N => C * (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)))
      (fun m n N hm hn => ?_) (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.add
        tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C)
    have hle (k : ℕ) (hk : N ≤ k) : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      Nat.one_div_le_one_div hk
    rw [Real.dist_eq]
    exact (hC m n).trans (mul_le_mul_of_nonneg_left (add_le_add (hle m hm) (hle n hn)) hC0)
  obtain ⟨C, -, hC⟩ := hφ.exists_abs_sub_le hT ha
  have hsub : Tendsto (fun n => T (φ n) - T (a n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => hC n n)
      (by simpa using (hε.add tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C)
  simpa using hsub.add hlim

/-- The extension of `T` as a linear functional on `C_c(Ω, ℝ)`. -/
private def extendₗ : C_c(Ω, ℝ) →ₗ[ℝ] ℝ where
  toFun := extend T
  map_add' f g := by
    have h₀ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hf := (exists_isApprox f).choose_spec.tendsto_extend hT h₀
    have hg := (exists_isApprox g).choose_spec.tendsto_extend hT h₀
    have hfg := ((exists_isApprox f).choose_spec.add (exists_isApprox g).choose_spec).tendsto_extend
      hT (by simpa using h₀.add h₀)
    exact tendsto_nhds_unique hfg ((hf.add hg).congr fun n => (map_add T _ _).symm)
  map_smul' c f := by
    have h₀ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hf := (exists_isApprox f).choose_spec
    have hcf := (hf.smul c).tendsto_extend hT (by simpa using h₀.const_mul |c|)
    exact tendsto_nhds_unique hcf (((hf.tendsto_extend hT h₀).const_mul c).congr fun n => by
      rw [Pi.smul_apply, map_smul, smul_eq_mul])

private lemma extendₗ_toCompactlySupportedContinuousMap (φ : 𝓓(Ω, ℝ)) :
    extendₗ hT φ.toCompactlySupportedContinuousMap = T φ :=
  tendsto_nhds_unique
    ((isApprox_toCompactlySupportedContinuousMap φ).tendsto_extend hT tendsto_const_nhds)
    tendsto_const_nhds

/-- The extension of `T` is bounded above on every order interval `[0, f]`. -/
private lemma bddAbove_extendₗ_image_Icc (f : C_c(Ω, ℝ)) :
    BddAbove (extendₗ hT '' Icc 0 f) := by
  set K := ((↑) : Ω → E) '' tsupport f
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_image_tsupport f).exists_cthickening_subset_open Ω.isOpen
    (Subtype.coe_image_subset _ _)
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_bound hT (isCompact_image_tsupport f).cthickening hδΩ
  obtain ⟨B, hB⟩ := (continuous_zeroExt f).bounded_above_of_compact_support
    ((isCompact_image_tsupport f).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_zeroExt_subset f))
  refine ⟨C * B, ?_⟩
  rintro _ ⟨g, ⟨hg, hgf⟩, rfl⟩
  -- `g` is supported where `f` is and is dominated by `f`.
  have hgK : ((↑) : Ω → E) '' tsupport g ⊆ K := by
    refine image_mono (closure_mono fun y hy => ?_)
    exact (lt_of_lt_of_le (lt_of_le_of_ne (le_def.1 hg y) (Ne.symm hy)) (le_def.1 hgf y)).ne'
  have hgB (x : E) : |zeroExt g x| ≤ B := by
    refine le_trans ?_ (by simpa using hB x)
    simp only [zeroExt_apply]
    split_ifs with h
    · exact abs_le_abs (le_def.1 hgf ⟨x, h⟩)
        (by linarith [show 0 ≤ g ⟨x, h⟩ by simpa using le_def.1 hg ⟨x, h⟩,
          le_def.1 hgf ⟨x, h⟩])
    · simp
  obtain ⟨φ, hφK, hφ⟩ := exists_isApprox_of_subset g (isCompact_image_tsupport f) hgK hδ hδΩ
  have hbound (n : ℕ) : T (φ n) ≤ C * (B + 1 / ((n : ℝ) + 1)) := by
    refine (le_abs_self _).trans (hC _ (hφK n) _ fun x => ?_)
    have h₁ := hφ.2 n x
    have h₂ := hgB x
    rw [abs_le] at h₁ h₂ ⊢
    constructor <;> linarith
  have hlim : Tendsto (fun n : ℕ => C * (B + 1 / ((n : ℝ) + 1))) atTop (𝓝 (C * B)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add B).const_mul C
  exact le_of_tendsto_of_tendsto'
    (hφ.tendsto_extend hT tendsto_one_div_add_atTop_nhds_zero_nat) hlim hbound

/-! ### The Radon representation -/

omit hT in
/-- **A distribution of order zero is a signed Radon measure.** A distribution `T` on `Ω` is
bounded on each compact `K ⊆ Ω` in the sup norm, `|T φ| ≤ C_K ‖φ‖_∞` for the test functions `φ`
supported in `K`, if and only if there are regular measures `ν₁` and `ν₂` on `Ω` with
`T φ = ∫ φ dν₁ - ∫ φ dν₂` for every test function `φ`. The measures are finite on compact subsets
of `Ω` but need not be finite. -/
theorem forall_exists_abs_le_iff_exists_regular [MeasurableSpace E] [BorelSpace E]
    (T : 𝓓'(Ω, ℝ)) :
    (∀ K, IsCompact K → K ⊆ Ω → ∃ C, ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ K →
      |T φ| ≤ C * ‖(φ : E →ᵇ ℝ)‖) ↔
    ∃ ν₁ ν₂ : Measure Ω, ν₁.Regular ∧ ν₂.Regular ∧
      ∀ φ : 𝓓(Ω, ℝ), T φ = ∫ x, φ x ∂ν₁ - ∫ x, φ x ∂ν₂ := by
  refine ⟨fun hT => ?_, ?_⟩
  · have := Ω.isOpen.locallyCompactSpace
    obtain ⟨ν₁, ν₂, h₁, h₂, h⟩ :=
      (TauCeti.RealRMK.forall_bddAbove_image_Icc_iff_exists_regular (extendₗ hT)).1
        (bddAbove_extendₗ_image_Icc hT)
    refine ⟨ν₁, ν₂, h₁, h₂, fun φ => ?_⟩
    simpa using (extendₗ_toCompactlySupportedContinuousMap hT φ).symm.trans
      (h φ.toCompactlySupportedContinuousMap)
  · rintro ⟨ν₁, ν₂, h₁, h₂, h⟩ K hK hKΩ
    refine ⟨ν₁.real (((↑) : Ω → E) ⁻¹' K) + ν₂.real (((↑) : Ω → E) ⁻¹' K), fun φ hφ => ?_⟩
    rw [h, add_mul, ← Real.norm_eq_abs]
    exact (norm_sub_le _ _).trans
      (add_le_add (φ.norm_integral_le_measureReal_mul_norm hK hKΩ hφ ν₁)
        (φ.norm_integral_le_measureReal_mul_norm hK hKΩ hφ ν₂))

end Distribution
