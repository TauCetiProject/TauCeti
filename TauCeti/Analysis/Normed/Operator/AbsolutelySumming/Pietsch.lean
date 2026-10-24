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

variable {𝕜 E F : Type*} [RCLike 𝕜]
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
  have hint (x : E) : Integrable (fun f : dualBall 𝕜 E ↦ ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal) ν :=
    by
      have h : Integrable (fun f ↦ WeakDual.evalRpow 1 p x f) ν :=
        (WeakDual.evalRpow 1 p x).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      simpa only [WeakDual.evalRpow_apply] using h
  rw [summingENorm_le_ofReal_iff hC]
  intro n x
  set W := weakLpNorm (𝕜 := 𝕜) p x
  have hW : 0 ≤ W := apply_nonneg _ _
  -- At each point of the ball, the integrand is at most `W ^ p`.
  have hpt (f : dualBall 𝕜 E) :
      ∑ i, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal ≤ W ^ p.toReal := by
    have h := norm_eval_le_weakLpNorm p x (WeakDual.toStrongDual (f : WeakDual 𝕜 E))
    rw [PiLp.norm_eq_sum hq] at h
    have h' := h.trans (mul_le_of_le_one_right hW (norm_le_one_of_mem_dualBall f))
    calc
      _ = ((∑ i, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal) ^ (1 / p.toReal)) ^ p.toReal :=
        by rw [one_div, Real.rpow_inv_rpow (Finset.sum_nonneg fun _ _ ↦ by positivity) hq.ne']
      _ ≤ W ^ p.toReal :=
        Real.rpow_le_rpow (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) _)
          (by simpa using h') hq.le
  have hsum : ∑ i, ‖T (x i)‖ ^ p.toReal ≤ (C * W) ^ p.toReal :=
    calc
      ∑ i, ‖T (x i)‖ ^ p.toReal ≤
          ∑ i, C ^ p.toReal * ∫ f, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal ∂ν := by
        gcongr with i
        have hI : 0 ≤ ∫ f, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal ∂ν :=
          integral_nonneg fun _ ↦ by positivity
        calc
          _ ≤ (C * (∫ f, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal ∂ν) ^ (1 / p.toReal)) ^
              p.toReal := Real.rpow_le_rpow (norm_nonneg _) (hT _) hq.le
          _ = _ := by rw [Real.mul_rpow hC (by positivity), one_div, Real.rpow_inv_rpow hI hq.ne']
      _ = C ^ p.toReal * ∫ f, ∑ i, ‖(f : WeakDual 𝕜 E) (x i)‖ ^ p.toReal ∂ν := by
        rw [integral_finsetSum _ fun i _ ↦ hint (x i), Finset.mul_sum]
      _ ≤ C ^ p.toReal * W ^ p.toReal := by
        gcongr
        calc
          _ ≤ ∫ _, W ^ p.toReal ∂ν :=
            integral_mono (integrable_finsetSum _ fun i _ ↦ hint (x i)) (integrable_const _) hpt
          _ = W ^ p.toReal := by simp
      _ = (C * W) ^ p.toReal := (Real.mul_rpow hC hW).symm
  rw [PiLp.norm_eq_sum hq]
  calc
    _ ≤ ((C * W) ^ p.toReal) ^ (1 / p.toReal) :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ by positivity) (by simpa using hsum)
        (by positivity)
    _ = C * W := by rw [one_div, Real.rpow_rpow_inv (mul_nonneg hC hW) hq.ne']

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

/-- A Hahn–Banach separation in `C(B, ℝ)` gives a continuous linear functional `L` on the
continuous functions on the dual ball that is negative on the constant `1`, nonpositive on
nonnegative functions, and satisfies `‖T x‖ ^ p * L 1 ≥ C ^ p * L (f ↦ ‖f x‖ ^ p)`. -/
private theorem exists_separating_functional (hp : p ≠ ∞) {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (hT : T.summingENorm p ≤ ENNReal.ofReal C) :
    ∃ L : StrongDual ℝ C(dualBall 𝕜 E, ℝ), L 1 < 0 ∧ (∀ h, 0 ≤ h → L h ≤ 0) ∧
      ∀ x : E, C ^ p.toReal * L (WeakDual.evalRpow 1 p x) ≤ ‖T x‖ ^ p.toReal * L 1 := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos (one_pos.trans_le Fact.out).ne' hp
  let g : E → C(dualBall 𝕜 E, ℝ) := fun x ↦
    ‖T x‖ ^ p.toReal • 1 - C ^ p.toReal • WeakDual.evalRpow 1 p x
  let Φ : (E →₀ ℝ) →ₗ[ℝ] C(dualBall 𝕜 E, ℝ) := Finsupp.linearCombination ℝ g
  have hΦ (w : E →₀ ℝ) (f : dualBall 𝕜 E) : Φ w f = ∑ x ∈ w.support,
      w x * (‖T x‖ ^ p.toReal - C ^ p.toReal * ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal) := by
    simp [Φ, g, Finsupp.linearCombination_apply, Finsupp.sum]
  -- The convex cone of nonnegative combinations of the `g x`.
  let Q : Set C(dualBall 𝕜 E, ℝ) := Φ '' {w | ∀ x, 0 ≤ w x}
  -- The open convex cone of functions bounded below by a positive constant.
  let P : Set C(dualBall 𝕜 E, ℝ) := {h | ∃ δ > 0, ∀ f, δ ≤ h f}
  have hPconv : Convex ℝ P := ContinuousMap.convex_uniformlyPositive
  have hPopen : IsOpen P := ContinuousMap.isOpen_uniformlyPositive
  have hQconv : Convex ℝ Q := by
    refine Convex.linear_image ?_ Φ
    intro w₁ hw₁ w₂ hw₂ a b ha hb _ x
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hw₁ x)) (mul_nonneg hb (hw₂ x))
  have hdisj : Disjoint P Q := by
    rw [Set.disjoint_left]
    rintro h ⟨δ, hδ, hhδ⟩ ⟨w, hw, rfl⟩
    obtain ⟨f, hf⟩ := exists_sum_lt_of_summingENorm_le hp hC hT w hw hδ
    exact (hhδ f).not_gt (hΦ w f ▸ hf)
  obtain ⟨L, u, hLP, hLQ⟩ := geometric_hahn_banach_open hPconv hPopen hQconv hdisj
  have hu : u ≤ 0 := by simpa using hLQ 0 ⟨0, fun _ ↦ le_rfl, map_zero Φ⟩
  have hL1 : L 1 < 0 := (hLP 1 ⟨1, one_pos, fun _ ↦ le_rfl⟩).trans_le hu
  refine ⟨L, hL1, fun h hh ↦ ?_, fun x ↦ ?_⟩
  · -- `h + ε • 1 ∈ P` for every `ε > 0`, so `L h + ε L 1 < 0`.
    by_contra! hpos
    have hε : 0 < L h / -L 1 := div_pos hpos (neg_pos.2 hL1)
    have hmem : h + (L h / -L 1) • (1 : C(dualBall 𝕜 E, ℝ)) ∈ P :=
      ⟨_, hε, fun f ↦ by simpa using hh f⟩
    have hlt := (hLP _ hmem).trans_le hu
    rw [map_add, map_smul, smul_eq_mul] at hlt
    have hcancel : L h / -L 1 * L 1 = -L h := by field_simp [hL1.ne]
    linarith
  · -- `t • g x ∈ Q` for every `t ≥ 0`, so `u ≤ t L (g x)`, which forces `L (g x) ≥ 0`.
    have hgx : 0 ≤ L (g x) := by
      by_contra! hneg
      have ht : 0 ≤ u / L (g x) := div_nonneg_of_nonpos hu hneg.le
      have hmem : Φ ((u / L (g x) + 1) • Finsupp.single x 1) ∈ Q :=
        ⟨_, fun y ↦ mul_nonneg (by linarith) (Finsupp.single_nonneg.2 zero_le_one y), rfl⟩
      have hle := hLQ _ hmem
      rw [map_smul, Finsupp.linearCombination_single, one_smul, map_smul, smul_eq_mul] at hle
      have hcancel : (u / L (g x) + 1) * L (g x) = u + L (g x) := by field_simp [hneg.ne]
      linarith
    simpa [g, sub_nonneg] using hgx

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
  -- The positive functional `-L`, on compactly supported (here: all) continuous functions.
  let Λ : C_c(dualBall 𝕜 E, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀
    { toFun h := -L h.toContinuousMap
      -- `toContinuousMap` commutes with addition and scalar multiplication by definition.
      map_add' h₁ h₂ := by rw [← neg_add, ← map_add]; rfl
      map_smul' c h := by
        rw [RingHom.id_apply, smul_eq_mul, mul_neg, ← smul_eq_mul, ← map_smul]; rfl }
    fun h hh ↦ neg_nonneg.2 (hLpos _ fun f ↦ hh f)
  let μ := RealRMK.rieszMeasure Λ
  have hμ (h : C(dualBall 𝕜 E, ℝ)) : ∫ f, h f ∂μ = -L h :=
    RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv h)
  have hμ1 : μ.real Set.univ = -L 1 := by simpa using hμ 1
  have hμ0 : μ Set.univ ≠ 0 := fun h0 ↦ by
    have : μ.real Set.univ = 0 := by simp [measureReal_def, h0]
    linarith
  have : NeZero μ := ⟨fun h ↦ hμ0 (by simp [h])⟩
  refine ⟨(μ Set.univ)⁻¹ • μ, inferInstance, Measure.Regular.smul (ENNReal.inv_ne_top.2 hμ0),
    fun x ↦ ?_⟩
  set I := ∫ f, ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal ∂((μ Set.univ)⁻¹ • μ) with hI_def
  have hI0 : 0 ≤ I := integral_nonneg fun _ ↦ by positivity
  have hI : I = -L (WeakDual.evalRpow 1 p x) / -L 1 := by
    have := hμ (WeakDual.evalRpow 1 p x)
    simp only [WeakDual.evalRpow_apply] at this
    rw [hI_def, integral_smul_measure, this, ENNReal.toReal_inv, ← measureReal_def, hμ1,
      smul_eq_mul, inv_mul_eq_div]
  have key : ‖T x‖ ^ p.toReal ≤ C ^ p.toReal * I := by
    rw [hI, mul_div_assoc', le_div_iff₀ (neg_pos.2 hL1)]
    linarith [hLx x]
  calc
    ‖T x‖ = (‖T x‖ ^ p.toReal) ^ (1 / p.toReal) := by
      rw [one_div, Real.rpow_rpow_inv (norm_nonneg _) hq.ne']
    _ ≤ (C ^ p.toReal * I) ^ (1 / p.toReal) :=
      Real.rpow_le_rpow (by positivity) key (by positivity)
    _ = C * I ^ (1 / p.toReal) := by
      rw [Real.mul_rpow (by positivity) hI0, one_div, Real.rpow_rpow_inv hC hq.ne']

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

end ContinuousLinearMap
