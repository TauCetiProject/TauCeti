/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Basic
public import TauCeti.Analysis.Normed.Module.WeakDual.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Normed.Module.RCLike.Rpow
import TauCeti.Topology.ContinuousMap.Compact

/-!
# Pietsch domination

Let `1 ≤ p < ∞` and let `B` be the closed unit ball of the dual of `E`, carrying the weak-star
topology, in which it is compact (Banach–Alaoglu). The **Pietsch domination theorem** says that
an operator `T : E →L[𝕜] F` satisfies `πₚ(T) ≤ C` exactly when there is a regular Borel
probability measure `ν` on `B` with
`‖T x‖ ≤ C (∫ |f x|ᵖ dν(f))^(1/p)` for all `x : E`.

The dominated estimate gives the bound on `πₚ(T)` by integrating the pointwise inequality
`∑ᵢ |f (xᵢ)|ᵖ ≤ (weak p-norm of x)ᵖ` against `ν`. Conversely, the functions
`f ↦ ∑ᵢ (‖T xᵢ‖ᵖ - Cᵖ |f (xᵢ)|ᵖ)` form a convex cone in `C(B, ℝ)` that the summing inequality
keeps disjoint from the open cone of functions bounded below by a positive constant. A
Hahn–Banach separation of these two cones produces a positive linear functional on `C(B, ℝ)`,
and the Riesz–Markov–Kakutani theorem represents it, after normalization, by the measure `ν`.

The measurable structure on `B` is the subtype structure of a Borel structure on the weak dual,
so `ν` is a Borel measure for the weak-star topology.

## Main results

* `ContinuousLinearMap.summingENorm_le_ofReal_of_norm_le_integral`: a dominating probability
  measure bounds the `p`-summing gauge.
* `ContinuousLinearMap.exists_isProbabilityMeasure_of_summingENorm_le_ofReal`: an operator with
  `πₚ(T) ≤ C` has a regular dominating probability measure.
* `ContinuousLinearMap.exists_isProbabilityMeasure_of_summingENorm_ne_top`: an absolutely
  `p`-summing operator is dominated with the constant `πₚ(T)`.
* `ContinuousLinearMap.summingENorm_le_ofReal_iff_exists_isProbabilityMeasure`: the Pietsch
  domination theorem.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 8.2.8.
* J. Diestel, H. Jarchow and A. Tonge, *Absolutely Summing Operators*, Theorem 2.12.
-/

public section

noncomputable section

open Metric MeasureTheory TauCeti
open scoped ENNReal CompactlySupported

namespace ContinuousLinearMap

/-- For `a, C, I ≥ 0` and `q > 0`, `a ≤ C * I ^ (1 / q)` if and only if `a ^ q ≤ C ^ q * I`. -/
private theorem le_mul_rpow_one_div_iff {a C I q : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hI : 0 ≤ I)
    (hq : 0 < q) : a ≤ C * I ^ (1 / q) ↔ a ^ q ≤ C ^ q * I := by
  rw [← Real.rpow_le_rpow_iff ha (by positivity) hq, Real.mul_rpow hC (by positivity), one_div,
    Real.rpow_inv_rpow hI hq.ne']

section NormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (𝕜 E) in
/-- The closed unit ball of the dual, as a set in the weak-star dual. -/
private abbrev dualBall : Set (WeakDual 𝕜 E) :=
  WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1

private theorem norm_le_one_of_mem_dualBall (f : dualBall 𝕜 E) :
    ‖WeakDual.toStrongDual (f : WeakDual 𝕜 E)‖ ≤ 1 :=
  mem_closedBall_zero_iff.mp f.2

/-- A functional in the dual unit ball satisfies `‖f x‖ ≤ ‖x‖`. -/
private theorem norm_apply_le_of_mem_dualBall (f : dualBall 𝕜 E) (x : E) :
    ‖(f : WeakDual 𝕜 E) x‖ ≤ ‖x‖ := by
  simpa using ((WeakDual.toStrongDual (f : WeakDual 𝕜 E)).le_opNorm x).trans
    (mul_le_of_le_one_left (norm_nonneg x) (norm_le_one_of_mem_dualBall f))

omit [Fact (1 ≤ p)] in
/-- For a finite measure on the dual unit ball, each function `f ↦ ‖f x‖ ^ p` is integrable. -/
private theorem integrable_norm_apply_rpow [MeasurableSpace (WeakDual 𝕜 E)]
    [OpensMeasurableSpace (WeakDual 𝕜 E)] (ν : Measure (dualBall 𝕜 E)) [IsFiniteMeasure ν]
    (x : E) : Integrable (fun f : dualBall 𝕜 E ↦ ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal) ν := by
  have h : Integrable (fun f ↦ WeakDual.evalRpow 1 p x f) ν :=
    Integrable.of_bound (WeakDual.evalRpow 1 p x).continuous.aestronglyMeasurable
      (‖x‖ ^ p.toReal) (ae_of_all _ fun f ↦ by
        simpa only [WeakDual.evalRpow_apply, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
            Real.rpow_le_rpow (norm_nonneg _) (norm_apply_le_of_mem_dualBall f x)
              ENNReal.toReal_nonneg)
  simpa only [WeakDual.evalRpow_apply] using h

/-- At each point `f` of the dual unit ball, `∑ᵢ ‖f (xᵢ)‖ ^ p` is at most the `p`-th power of the
weak `p`-norm of `x`. -/
private theorem sum_norm_apply_rpow_le {ι : Type*} [Fintype ι] (hp : p ≠ ∞) (x : ι → E)
    (f : dualBall 𝕜 E) :
    ∑ i, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal ≤ weakLpNorm (𝕜 := 𝕜) p x ^ p.toReal := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos (one_pos.trans_le Fact.out).ne' hp
  have h := (norm_eval_le_weakLpNorm p x (WeakDual.toStrongDual (f : WeakDual 𝕜 E))).trans
    (mul_le_of_le_one_right (apply_nonneg _ _) (norm_le_one_of_mem_dualBall f))
  rw [PiLp.norm_eq_sum hq, one_div,
    Real.rpow_inv_le_iff_of_pos (Finset.sum_nonneg fun _ _ ↦ by positivity) (apply_nonneg _ _)
      hq] at h
  simpa using h

/-- **Pietsch domination**, the easy direction: if `‖T x‖ ≤ C (∫ |f x|ᵖ dν(f))^(1/p)` for a
probability measure `ν` on the dual unit ball, then `πₚ(T) ≤ C`. -/
theorem summingENorm_le_ofReal_of_norm_le_integral [MeasurableSpace (WeakDual 𝕜 E)]
    [OpensMeasurableSpace (WeakDual 𝕜 E)]
    (hp : p ≠ ∞) {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1))
    [IsProbabilityMeasure ν]
    (hT : ∀ x : E,
      ‖T x‖ ≤ C * (∫ f, ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal ∂ν) ^ (1 / p.toReal)) :
    T.summingENorm p ≤ ENNReal.ofReal C := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos (one_pos.trans_le Fact.out).ne' hp
  have hint := integrable_norm_apply_rpow (p := p) ν
  rw [summingENorm_le_ofReal_iff hC]
  intro n x
  set W := weakLpNorm (𝕜 := 𝕜) p x
  have hW : 0 ≤ W := apply_nonneg _ _
  have hsum : ∑ i, ‖T (x i)‖ ^ p.toReal ≤ (C * W) ^ p.toReal :=
    calc
      ∑ i, ‖T (x i)‖ ^ p.toReal ≤
          ∑ i, C ^ p.toReal * ∫ f, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal ∂ν := by
        gcongr with i
        exact (le_mul_rpow_one_div_iff (norm_nonneg _) hC
          (integral_nonneg fun _ ↦ by positivity) hq).1 (hT _)
      _ = C ^ p.toReal * ∫ f, ∑ i, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal ∂ν := by
        rw [integral_finsetSum _ fun i _ ↦ hint (x i), Finset.mul_sum]
      _ ≤ C ^ p.toReal * ∫ _, W ^ p.toReal ∂ν :=
        mul_le_mul_of_nonneg_left (integral_mono (integrable_finsetSum _ fun i _ ↦ hint (x i))
          (integrable_const _) (sum_norm_apply_rpow_le hp x)) (by positivity)
      _ = (C * W) ^ p.toReal := by simp [Real.mul_rpow hC hW]
  rw [PiLp.norm_eq_sum hq, one_div, Real.rpow_inv_le_iff_of_pos
    (Finset.sum_nonneg fun _ _ ↦ by positivity) (by positivity) hq]
  simpa using hsum

end NormedField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The summing inequality rules out a nonnegative combination of the functions
`f ↦ ‖T x‖ ^ p - C ^ p * ‖f x‖ ^ p` that is bounded below on the dual ball by some `δ > 0`. -/
private theorem exists_sum_lt_of_summingENorm_le (hp : p ≠ ∞) {T : E →L[𝕜] F} {C : ℝ}
    (hC : 0 ≤ C) (hT : T.summingENorm p ≤ ENNReal.ofReal C) (w : E →₀ ℝ) (hw : ∀ x, 0 ≤ w x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : dualBall 𝕜 E, ∑ x ∈ w.support,
      w x * (‖T x‖ ^ p.toReal - C ^ p.toReal * ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal) < δ := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos (one_pos.trans_le Fact.out).ne' hp
  by_contra! hge
  set s := w.support
  -- Rescale the points so that `p`-th powers of norms pick up the weights.
  let y : s → E := fun x ↦ ((w x ^ p.toReal⁻¹ : ℝ) : 𝕜) • (x : E)
  set A := ∑ x ∈ s, w x * ‖T x‖ ^ p.toReal
  have hA : ‖WithLp.toLp p (fun i ↦ T (y i))‖ = A ^ (1 / p.toReal) := by
    rw [PiLp.norm_eq_sum hq]
    have hy (x : s) : ‖T (y x)‖ ^ p.toReal = w x * ‖T x‖ ^ p.toReal :=
      by rw [map_smul, norm_ofReal_rpow_inv_smul_rpow (hw x) hq.ne']
    rw [Finset.sum_congr rfl fun x _ ↦ hy x,
      Finset.sum_coe_sort s fun x ↦ w x * ‖T x‖ ^ p.toReal]
  have hge' (f : dualBall 𝕜 E) :
      C ^ p.toReal * ∑ x ∈ s, w x * ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal ≤ A - δ := by
    have := hge f
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum] at this ⊢
    simp only [mul_left_comm (C ^ p.toReal)]
    linarith
  have hAδ : 0 ≤ A - δ := by
    refine le_trans ?_ (hge' ⟨0, by simp⟩)
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun x _ ↦ mul_nonneg (hw x) (by positivity))
  -- The weak norm of `C • y` is at most `(A - δ) ^ (1 / p)`.
  have hweak : weakLpNorm (𝕜 := 𝕜) p ((C : 𝕜) • y) ≤ (A - δ) ^ (1 / p.toReal) := by
    rw [weakLpNorm_le_iff_unitBall]
    intro g hg
    have hmem : StrongDual.toWeakDual g ∈ dualBall 𝕜 E := by simpa using hg
    have h := hge' ⟨_, hmem⟩
    rw [PiLp.norm_eq_sum hq]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ by positivity) ?_ (by positivity)
    calc
      _ = ∑ x : s, C ^ p.toReal * (w x * ‖g x‖ ^ p.toReal) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        have hy : ‖g (y x)‖ ^ p.toReal = w x * ‖g x‖ ^ p.toReal :=
          by rw [map_smul, norm_ofReal_rpow_inv_smul_rpow (hw x) hq.ne']
        simp only [Pi.smul_apply, map_smul, norm_smul, RCLike.norm_ofReal,
          abs_of_nonneg hC]
        rw [Real.mul_rpow hC (norm_nonneg _), hy]
      _ = C ^ p.toReal * ∑ x ∈ s, w x * ‖g x‖ ^ p.toReal := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort s fun x ↦ w x * ‖g x‖ ^ p.toReal]
      _ ≤ A - δ := h
  have hne : T.summingENorm p ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hT
  have hsum : A ^ (1 / p.toReal) ≤ (A - δ) ^ (1 / p.toReal) :=
    calc
      A ^ (1 / p.toReal) ≤ (T.summingENorm p).toReal * weakLpNorm (𝕜 := 𝕜) p y :=
        hA ▸ norm_toLp_le_toReal_summingENorm_mul hne y
      _ ≤ C * weakLpNorm (𝕜 := 𝕜) p y :=
        mul_le_mul_of_nonneg_right (ENNReal.toReal_le_of_le_ofReal hC hT) (apply_nonneg _ _)
      _ = weakLpNorm (𝕜 := 𝕜) p ((C : 𝕜) • y) := by
        rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_nonneg hC]
      _ ≤ (A - δ) ^ (1 / p.toReal) := hweak
  rw [Real.rpow_le_rpow_iff (hAδ.trans (by linarith)) hAδ (by positivity)] at hsum
  linarith

/-- A continuous linear functional on `C(X, ℝ)` that is bounded above by some `u ≤ 0` on the
functions bounded below by a positive constant is nonpositive on the nonnegative functions. -/
private theorem apply_nonpos_of_forall_uniformlyPositive_lt {X : Type*} [TopologicalSpace X]
    (L : StrongDual ℝ C(X, ℝ)) {u : ℝ} (hu : u ≤ 0)
    (hL : ∀ h ∈ {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x}, L h < u) {h : C(X, ℝ)} (hh : 0 ≤ h) :
    L h ≤ 0 := by
  have hL1 : L 1 < 0 := (hL 1 ⟨1, one_pos, fun _ ↦ le_rfl⟩).trans_le hu
  -- `h + ε • 1` is bounded below by `ε`, so `L h + ε L 1 < 0`, for every `ε > 0`.
  by_contra! hpos
  have hε : 0 < L h / -L 1 := div_pos hpos (neg_pos.2 hL1)
  have hmem : h + (L h / -L 1) • (1 : C(X, ℝ)) ∈ {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x} :=
    ⟨_, hε, fun x ↦ by simpa using hh x⟩
  have hlt := (hL _ hmem).trans_le hu
  rw [map_add, map_smul, smul_eq_mul] at hlt
  have hcancel : L h / -L 1 * L 1 = -L h := by field_simp [hL1.ne]
  linarith

/-- A linear functional on `ι →₀ ℝ` that is bounded below on the nonnegative functions is
nonnegative on each `Finsupp.single i 1`. -/
private theorem apply_single_nonneg_of_forall_le {ι : Type*} (ψ : (ι →₀ ℝ) →ₗ[ℝ] ℝ) {u : ℝ}
    (hψ : ∀ w : ι →₀ ℝ, 0 ≤ w → u ≤ ψ w) (i : ι) : 0 ≤ ψ (Finsupp.single i 1) := by
  have hu : u ≤ 0 := (hψ 0 le_rfl).trans_eq (map_zero ψ)
  -- `t • Finsupp.single i 1` is nonnegative, so `u ≤ t ψ (Finsupp.single i 1)`, for every `t ≥ 0`.
  by_contra! hneg
  have ht : 0 ≤ u / ψ (Finsupp.single i 1) := div_nonneg_of_nonpos hu hneg.le
  have hle := hψ ((u / ψ (Finsupp.single i 1) + 1) • Finsupp.single i 1)
    (smul_nonneg (by linarith) (Finsupp.single_nonneg.2 zero_le_one))
  rw [map_smul, smul_eq_mul] at hle
  have hcancel : (u / ψ (Finsupp.single i 1) + 1) * ψ (Finsupp.single i 1) =
      u + ψ (Finsupp.single i 1) := by
    field_simp [hneg.ne]
  linarith

/-- A Hahn–Banach separation in `C(B, ℝ)` gives a continuous linear functional `L` on the
continuous functions on the dual ball that is negative on the constant `1`, nonpositive on
nonnegative functions, and satisfies `‖T x‖ ^ p * L 1 ≥ C ^ p * L (f ↦ ‖f x‖ ^ p)`. -/
private theorem exists_separating_functional (hp : p ≠ ∞) {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (hT : T.summingENorm p ≤ ENNReal.ofReal C) :
    ∃ L : StrongDual ℝ C(dualBall 𝕜 E, ℝ), L 1 < 0 ∧ (∀ h, 0 ≤ h → L h ≤ 0) ∧
      ∀ x : E, C ^ p.toReal * L (WeakDual.evalRpow 1 p x) ≤ ‖T x‖ ^ p.toReal * L 1 := by
  let g : E → C(dualBall 𝕜 E, ℝ) := fun x ↦
    ‖T x‖ ^ p.toReal • 1 - C ^ p.toReal • WeakDual.evalRpow 1 p x
  let Φ : (E →₀ ℝ) →ₗ[ℝ] C(dualBall 𝕜 E, ℝ) := Finsupp.linearCombination ℝ g
  have hΦ (w : E →₀ ℝ) (f : dualBall 𝕜 E) : Φ w f = ∑ x ∈ w.support,
      w x * (‖T x‖ ^ p.toReal - C ^ p.toReal * ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal) := by
    simp only [Φ, g, Finsupp.linearCombination_apply, Finsupp.sum, ContinuousMap.coe_sum,
      ContinuousMap.coe_smul, ContinuousMap.coe_sub, ContinuousMap.coe_one, Finset.sum_apply,
      Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one, WeakDual.evalRpow_apply]
  -- The convex cone of nonnegative combinations of the `g x`.
  let Q : Set C(dualBall 𝕜 E, ℝ) := Φ '' Set.Ici 0
  -- `Q` misses the open convex cone of functions bounded below by a positive constant.
  have hdisj : Disjoint {h : C(dualBall 𝕜 E, ℝ) | ∃ δ > 0, ∀ f, δ ≤ h f} Q := by
    rw [Set.disjoint_left]
    rintro h ⟨δ, hδ, hhδ⟩ ⟨w, hw, rfl⟩
    obtain ⟨f, hf⟩ := exists_sum_lt_of_summingENorm_le hp hC hT w (Finsupp.le_def.1 hw) hδ
    exact (hhδ f).not_gt (hΦ w f ▸ hf)
  obtain ⟨L, u, hLP, hLQ⟩ := geometric_hahn_banach_open ContinuousMap.convex_uniformlyPositive
    ContinuousMap.isOpen_uniformlyPositive ((convex_Ici 0).linear_image Φ) hdisj
  have hu : u ≤ 0 := (hLQ 0 ⟨0, Set.self_mem_Ici, map_zero Φ⟩).trans_eq (map_zero L)
  refine ⟨L, (hLP 1 ⟨1, one_pos, fun _ ↦ le_rfl⟩).trans_le hu,
    fun h hh ↦ apply_nonpos_of_forall_uniformlyPositive_lt L hu hLP hh, fun x ↦ ?_⟩
  -- `L` is bounded below on the cone `Q`, so it is nonnegative on each generator `g x`.
  have hgx := apply_single_nonneg_of_forall_le (L.toLinearMap ∘ₗ Φ)
    (fun w hw ↦ hLQ _ ⟨w, hw, rfl⟩) x
  simpa only [Φ, g, LinearMap.coe_comp, coe_coe, Function.comp_apply,
    Finsupp.linearCombination_single, one_smul, map_sub, map_smul, smul_eq_mul,
    sub_nonneg] using hgx

/-- **Riesz–Markov–Kakutani** for a continuous linear functional `L` on `C(X, ℝ)`, `X` compact
Hausdorff, that is nonpositive on nonnegative functions: `-L` is integration against a regular
measure. -/
private theorem exists_regular_integral_eq_neg {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (L : StrongDual ℝ C(X, ℝ))
    (hL : ∀ h, 0 ≤ h → L h ≤ 0) :
    ∃ μ : Measure X, μ.Regular ∧ ∀ h : C(X, ℝ), ∫ x, h x ∂μ = -L h := by
  -- The positive functional `-L`, on compactly supported (here: all) continuous functions.
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀
    { toFun h := -L h.toContinuousMap
      -- `toContinuousMap` commutes with addition and scalar multiplication by definition.
      map_add' h₁ h₂ := by rw [← neg_add, ← map_add]; rfl
      map_smul' c h := by
        rw [RingHom.id_apply, smul_eq_mul, mul_neg, ← smul_eq_mul, ← map_smul]; rfl }
    fun h hh ↦ neg_nonneg.2 (hL _ fun f ↦ hh f)
  exact ⟨RealRMK.rieszMeasure Λ, inferInstance, fun h ↦
    RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv h)⟩

/-- A continuous linear functional `L` on `C(X, ℝ)`, `X` compact Hausdorff, that is negative at
`1` and nonpositive on nonnegative functions is `h ↦ L 1 * ∫ h dν` for a regular probability
measure `ν`. -/
private theorem exists_isProbabilityMeasure_integral_eq_div {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (L : StrongDual ℝ C(X, ℝ))
    (hL1 : L 1 < 0) (hL : ∀ h, 0 ≤ h → L h ≤ 0) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ν.Regular ∧
      ∀ h : C(X, ℝ), ∫ x, h x ∂ν = L h / L 1 := by
  obtain ⟨μ, hreg, hμ⟩ := exists_regular_integral_eq_neg L hL
  have hμ1 : μ.real Set.univ = -L 1 := by simpa using hμ 1
  have hμ0 : μ Set.univ ≠ 0 := fun h0 ↦ by
    have : μ.real Set.univ = 0 := by simp [measureReal_def, h0]
    linarith
  have : NeZero μ := ⟨fun h ↦ hμ0 (by simp [h])⟩
  refine ⟨(μ Set.univ)⁻¹ • μ, inferInstance, Measure.Regular.smul (ENNReal.inv_ne_top.2 hμ0),
    fun h ↦ ?_⟩
  rw [integral_smul_measure, hμ, ENNReal.toReal_inv, ← measureReal_def, hμ1, smul_eq_mul,
    inv_mul_eq_div, neg_div_neg_eq]

/-- **Pietsch domination**, the main direction: if `πₚ(T) ≤ C` with `1 ≤ p < ∞`, there is a
regular Borel probability measure `ν` on the weak-star compact dual unit ball such that
`‖T x‖ ≤ C (∫ |f x|ᵖ dν(f))^(1/p)` for all `x`. -/
theorem exists_isProbabilityMeasure_of_summingENorm_le_ofReal [MeasurableSpace (WeakDual 𝕜 E)]
    [BorelSpace (WeakDual 𝕜 E)]
    (hp : p ≠ ∞) {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (hT : T.summingENorm p ≤ ENNReal.ofReal C) :
    ∃ ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1),
      IsProbabilityMeasure ν ∧ ν.Regular ∧ ∀ x : E,
        ‖T x‖ ≤ C * (∫ f, ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos (one_pos.trans_le Fact.out).ne' hp
  obtain ⟨L, hL1, hLpos, hLx⟩ := exists_separating_functional hp hC hT
  obtain ⟨ν, hν, hreg, hνL⟩ := exists_isProbabilityMeasure_integral_eq_div L hL1 hLpos
  refine ⟨ν, hν, hreg, fun x ↦ ?_⟩
  have hI : ∫ f, ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal ∂ν = L (WeakDual.evalRpow 1 p x) / L 1 := by
    simpa using hνL (WeakDual.evalRpow 1 p x)
  rw [le_mul_rpow_one_div_iff (norm_nonneg _) hC (integral_nonneg fun _ ↦ by positivity) hq, hI,
    mul_div_assoc', le_div_iff_of_neg hL1]
  exact hLx x

/-- An absolutely `p`-summing operator, `1 ≤ p < ∞`, is dominated by a regular Borel probability
measure on the dual unit ball with the constant `πₚ(T)`. -/
theorem exists_isProbabilityMeasure_of_summingENorm_ne_top [MeasurableSpace (WeakDual 𝕜 E)]
    [BorelSpace (WeakDual 𝕜 E)] (hp : p ≠ ∞) {T : E →L[𝕜] F} (hT : T.summingENorm p ≠ ∞) :
    ∃ ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1),
      IsProbabilityMeasure ν ∧ ν.Regular ∧ ∀ x : E, ‖T x‖ ≤
        (T.summingENorm p).toReal * (∫ f, ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal ∂ν) ^ (1 / p.toReal) :=
  exists_isProbabilityMeasure_of_summingENorm_le_ofReal hp ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal hT).ge

/-- **Pietsch domination theorem.** For `1 ≤ p < ∞` and `C ≥ 0`, an operator satisfies
`πₚ(T) ≤ C` if and only if there is a regular Borel probability measure `ν` on the weak-star
compact dual unit ball with `‖T x‖ ≤ C (∫ |f x|ᵖ dν(f))^(1/p)` for all `x`. -/
theorem summingENorm_le_ofReal_iff_exists_isProbabilityMeasure
    [MeasurableSpace (WeakDual 𝕜 E)] [BorelSpace (WeakDual 𝕜 E)]
    (hp : p ≠ ∞) {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C) :
    T.summingENorm p ≤ ENNReal.ofReal C ↔
      ∃ ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1),
        IsProbabilityMeasure ν ∧ ν.Regular ∧ ∀ x : E,
          ‖T x‖ ≤ C * (∫ f, ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal ∂ν) ^ (1 / p.toReal) :=
  ⟨exists_isProbabilityMeasure_of_summingENorm_le_ofReal hp hC,
    fun ⟨ν, _, _, hν⟩ ↦ summingENorm_le_ofReal_of_norm_le_integral hp hC ν hν⟩

end RCLike

end ContinuousLinearMap
