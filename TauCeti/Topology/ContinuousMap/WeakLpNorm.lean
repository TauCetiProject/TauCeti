/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Weak
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Weak `Lᵖ` norms of finite families in `C(K, 𝕜)`

On a compact space `K`, point evaluation `ContinuousMap.evalCLM 𝕜 x` is a continuous linear
functional of operator norm at most `1` (equal to `1` when the target is nontrivial). Evaluating
the weak `Lᵖ` norm of a finite family `f : ι → C(K, 𝕜)` against point evaluations shows that the
pointwise `ℓᵖ` norm `x ↦ ‖WithLp.toLp p (fun i ↦ f i x)‖` — bundled as the uniform norm of
`ContinuousMap.piLp p f : C(K, PiLp p fun _ ↦ 𝕜)` — is bounded above by
`TauCeti.weakLpNorm p f`. Over an `RCLike` scalar field, Hahn–Banach duality on `PiLp p` gives the
reverse inequality, so `TauCeti.weakLpNorm p f` equals the supremum over `x : K` of the pointwise
`ℓᵖ` norms. At `p = 2`, a family of weak `L²` norm at most `1` therefore has square function
`∑ i, ‖f i x‖ ^ 2 ≤ 1` everywhere on `K`.

## Main declarations

* `ContinuousMap.piLp`: bundle a family `∀ i, C(X, E i)` into `C(X, PiLp p E)`.
* `ContinuousMap.norm_evalCLM_le_one`, `ContinuousMap.norm_evalCLM`: operator norm of point
  evaluation on `C(K, E)` for compact `K`.
* `ContinuousMap.norm_toLp_apply_le_weakLpNorm`: pointwise `ℓᵖ` bound by `TauCeti.weakLpNorm`.
* `ContinuousMap.sum_norm_apply_sq_le_weakLpNorm_two`: pointwise square-function bound at `p = 2`.
* `ContinuousMap.weakLpNorm_eq_norm_piLp`: over `RCLike` scalars, `TauCeti.weakLpNorm p f` equals
  `‖ContinuousMap.piLp p f‖`.
-/

public section

noncomputable section

open scoped ENNReal

namespace ContinuousMap

section TopologicalSpace

variable {X ι : Type*} [TopologicalSpace X] {E : ι → Type*} [∀ i, TopologicalSpace (E i)]

/-- Bundle a family of continuous maps `∀ i, C(X, E i)` into a continuous map into `PiLp p E`. -/
def piLp (p : ℝ≥0∞) (f : ∀ i, C(X, E i)) : C(X, PiLp p E) where
  toFun x := WithLp.toLp p fun i ↦ f i x
  continuous_toFun := (PiLp.continuous_toLp p E).comp (ContinuousMap.pi f).continuous

/-- Evaluating `ContinuousMap.piLp` collects the pointwise values in `PiLp`. -/
@[simp]
theorem piLp_apply (p : ℝ≥0∞) (f : ∀ i, C(X, E i)) (x : X) :
    piLp p f x = WithLp.toLp p fun i ↦ f i x :=
  (rfl)

end TopologicalSpace

section EvalNorm

variable {K 𝕜 E : Type*} [TopologicalSpace K] [CompactSpace K] [NontriviallyNormedField 𝕜]

/-- Point evaluation on `C(K, E)` has operator norm at most `1`. -/
theorem norm_evalCLM_le_one [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : K) :
    ‖evalCLM 𝕜 (M := E) x‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa only [evalCLM_apply, one_mul] using f.norm_coe_le_norm x

/-- Point evaluation on `C(K, E)` has operator norm `1` when `E` is nontrivial. -/
@[simp]
theorem norm_evalCLM [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E] (x : K) :
    ‖evalCLM 𝕜 (M := E) x‖ = 1 := by
  refine le_antisymm (norm_evalCLM_le_one x) ?_
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hc : ‖ContinuousMap.const K v‖ ≤ ‖v‖ :=
    (ContinuousMap.norm_le _ hv0.le).2 fun _ ↦ le_rfl
  have hle := (evalCLM 𝕜 (M := E) x).le_opNorm (ContinuousMap.const K v)
  rw [evalCLM_apply, const_apply] at hle
  have hmul : 1 * ‖v‖ ≤ ‖evalCLM 𝕜 (M := E) x‖ * ‖v‖ := by
    simpa only [one_mul] using hle.trans (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
  exact le_of_mul_le_mul_right hmul hv0

end EvalNorm

section NontriviallyNormedField

variable {K 𝕜 ι : Type*} [TopologicalSpace K] [CompactSpace K] [NontriviallyNormedField 𝕜]
  [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- At every point `x : K`, the `ℓᵖ` norm of `(f i x)ᵢ` is bounded by the weak `Lᵖ` norm of `f`. -/
theorem norm_toLp_apply_le_weakLpNorm (f : ι → C(K, 𝕜)) (x : K) :
    ‖WithLp.toLp p fun i ↦ f i x‖ ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) p f := by
  calc
    ‖WithLp.toLp p fun i ↦ f i x‖ =
        ‖WithLp.toLp p fun i ↦ evalCLM 𝕜 x (f i)‖ := rfl
    _ ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) p f * ‖evalCLM 𝕜 (M := 𝕜) x‖ :=
        TauCeti.norm_eval_le_weakLpNorm p f (evalCLM 𝕜 x)
    _ ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) p f * 1 :=
        mul_le_mul_of_nonneg_left (norm_evalCLM_le_one x) (apply_nonneg _ _)
    _ = TauCeti.weakLpNorm (𝕜 := 𝕜) p f := mul_one _

/-- The uniform norm of `ContinuousMap.piLp p f` is bounded by `TauCeti.weakLpNorm p f`. -/
theorem norm_piLp_le_weakLpNorm (f : ι → C(K, 𝕜)) :
    ‖piLp p f‖ ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) p f :=
  (ContinuousMap.norm_le _ (apply_nonneg _ _)).2 (norm_toLp_apply_le_weakLpNorm p f)

/-- For finite `p`, the pointwise `p`-th power sum `∑ i, ‖f i x‖ ^ p.toReal` is at most
`TauCeti.weakLpNorm p f ^ p.toReal`. -/
theorem sum_norm_apply_rpow_le_weakLpNorm (hp : p ≠ ∞) (f : ι → C(K, 𝕜)) (x : K) :
    ∑ i, ‖f i x‖ ^ p.toReal ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) p f ^ p.toReal := by
  have hw : 0 ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) p f := apply_nonneg _ _
  calc
    ∑ i, ‖f i x‖ ^ p.toReal = ∑ i, ‖evalCLM 𝕜 x (f i)‖ ^ p.toReal := rfl
    _ ≤ (TauCeti.weakLpNorm (𝕜 := 𝕜) p f * ‖evalCLM 𝕜 (M := 𝕜) x‖) ^ p.toReal :=
        TauCeti.sum_norm_eval_rpow_le_weakLpNorm p hp f (evalCLM 𝕜 x)
    _ ≤ (TauCeti.weakLpNorm (𝕜 := 𝕜) p f * 1) ^ p.toReal :=
        Real.rpow_le_rpow (mul_nonneg hw (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (norm_evalCLM_le_one (𝕜 := 𝕜) (E := 𝕜) x) hw)
          ENNReal.toReal_nonneg
    _ = TauCeti.weakLpNorm (𝕜 := 𝕜) p f ^ p.toReal := by rw [mul_one]

/-- At `p = 2`, the pointwise square function `∑ i, ‖f i x‖ ^ 2` is bounded by the square of the
weak `L²` norm of `f`. -/
theorem sum_norm_apply_sq_le_weakLpNorm_two (f : ι → C(K, 𝕜)) (x : K) :
    ∑ i, ‖f i x‖ ^ 2 ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) 2 f ^ 2 := by
  simpa using sum_norm_apply_rpow_le_weakLpNorm (p := 2) ENNReal.ofNat_ne_top f x

/-- If `f : ι → C(K, 𝕜)` has weak `L²` norm at most `1`, then `∑ i, ‖f i x‖ ^ 2 ≤ 1` at every
point `x : K`. -/
theorem sum_norm_apply_sq_le_one_of_weakLpNorm_two_le_one {f : ι → C(K, 𝕜)}
    (hf : TauCeti.weakLpNorm (𝕜 := 𝕜) 2 f ≤ 1) (x : K) :
    ∑ i, ‖f i x‖ ^ 2 ≤ 1 := by
  have hw : 0 ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) 2 f := apply_nonneg _ _
  exact (sum_norm_apply_sq_le_weakLpNorm_two f x).trans (by nlinarith)

end NontriviallyNormedField

section RCLike

variable {K 𝕜 ι : Type*} [TopologicalSpace K] [CompactSpace K] [RCLike 𝕜]
  [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Over an `RCLike` field, the weak `Lᵖ` norm of a finite family in `C(K, 𝕜)` equals the uniform
norm of `ContinuousMap.piLp p f`. -/
theorem weakLpNorm_eq_norm_piLp (f : ι → C(K, 𝕜)) :
    TauCeti.weakLpNorm (𝕜 := 𝕜) p f = ‖piLp p f‖ := by
  classical
  refine le_antisymm ?_ (norm_piLp_le_weakLpNorm p f)
  refine (TauCeti.weakLpNorm_le_iff p f (norm_nonneg _)).2 fun φ ↦ ?_
  refine NormedSpace.norm_le_dual_bound 𝕜 _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun ψ ↦ ?_
  have hexp (a : ι → 𝕜) : WithLp.toLp p a = ∑ i, a i • PiLp.single p i (1 : 𝕜) := by
    ext j
    simp [Pi.single_apply]
  let g : C(K, 𝕜) := ∑ i, ψ (PiLp.single p i (1 : 𝕜)) • f i
  have hφg : ψ (WithLp.toLp p fun i ↦ φ (f i)) = φ g := by
    rw [hexp, map_sum]
    simp only [g, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hg : ‖g‖ ≤ ‖ψ‖ * ‖piLp p f‖ := by
    refine (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 fun x ↦ ?_
    have hgx : g x = ψ (piLp p f x) := by
      rw [piLp_apply, hexp, map_sum]
      simp only [g, sum_apply, smul_apply, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    rw [hgx]
    exact (ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((piLp p f).norm_coe_le_norm x)
      (norm_nonneg _))
  rw [hφg]
  calc
    ‖φ g‖ ≤ ‖φ‖ * ‖g‖ := φ.le_opNorm g
    _ ≤ ‖φ‖ * (‖ψ‖ * ‖piLp p f‖) := mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    _ = ‖piLp p f‖ * ‖φ‖ * ‖ψ‖ := by ring

end RCLike

end ContinuousMap
