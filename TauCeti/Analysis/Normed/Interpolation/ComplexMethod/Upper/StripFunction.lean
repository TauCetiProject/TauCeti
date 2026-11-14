/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.Analysis.Complex.VerticalStrip
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
import TauCeti.Analysis.Complex.PhragmenLindelof.VerticalStrip

/-!
# Upper strip functions for Calderón's upper complex interpolation method

For a compatible couple `(X₀, X₁)` of complex normed spaces, Calderón's upper complex interpolation
method `[X₀, X₁]^θ` is built from *upper strip functions* `G` on the closed vertical strip
`0 ≤ re z ≤ 1` taking values in the sum `X₀ + X₁`: functions continuous on the closed strip,
holomorphic on the open strip `0 < re z < 1`, of at most linear growth `‖G z‖ ≤ K * (1 + |im z|)`,
whose boundary increments on `re z = 0` and `re z = 1` lie in `X₀` and `X₁` with uniformly bounded
difference quotients `(t - s)⁻¹ • (G (j + t * I) - G (j + s * I))` (`j = 0, 1`, `t ≠ s`).

Because `X₀` and `X₁` inject into `X₀ + X₁`, the off-diagonal boundary difference quotients
`q = (q₀, q₁)` in `(offDiag univ →ᵇ X₀) × (offDiag univ →ᵇ X₁)` are uniquely determined by `G`
(`CompatibleCouple.IsUpperStripFunction.trace_unique`). Conversely, pinning at `t = 0` recovers
Lipschitz boundary curves `t ↦ G (t * I) - G 0` in `X₀` and `t ↦ G (1 + t * I) - G 1` in `X₁`
(`IsUpperStripFunction.fstBoundary`, `IsUpperStripFunction.sndBoundary`), while any strip function
of finite exponential order with Lipschitz boundary curves defines an upper strip function
(`IsUpperStripFunction.of_lipschitz`).

The main analytical estimates in this file establish Bergh–Löfström Lemma 4.1.3:

* `IsUpperStripFunction.norm_sub_add_mul_I_le_rpow_mul_rpow`: three-lines bound
  `‖G (z + h * I) - G z‖ ≤ |h| * ‖q₀‖ ^ (1 - re z) * ‖q₁‖ ^ re z` on vertical increments across
  the closed strip;
* `IsUpperStripFunction.norm_deriv_le_rpow_mul_rpow`: three-lines bound
  `‖deriv G z‖ ≤ ‖q₀‖ ^ (1 - re z) * ‖q₁‖ ^ re z` on complex derivatives in `0 < re z < 1`;
* `IsUpperStripFunction.lipschitzOnWith`: global `‖q‖`-Lipschitz continuity of `G` on the closed
  strip `0 ≤ re z ≤ 1`, which implies that `G` is determined up to the additive constant `G 0` by
  its boundary difference quotients `q` (`IsUpperStripFunction.eqOn_sub_apply_zero`).

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§5–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.1 (Lemma 4.1.3).
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2.4.
-/

public noncomputable section

open Asymptotics Bornology Complex Complex.HadamardThreeLines Filter Set Topology
open scoped BoundedContinuousFunction NNReal

namespace TauCeti

open Complex.HadamardThreeLines

/-- The bounded continuous difference-quotient function `(t, s) ↦ (t - s)⁻¹ • (g t - g s)` on
`offDiag (univ : Set ℝ)` associated with a `K`-Lipschitz curve `g : ℝ → E`. -/
def offDiagSlope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : ℝ≥0}
    {g : ℝ → E} (hg : LipschitzWith K g) : offDiag (univ : Set ℝ) →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => ((p.1.1 - p.1.2 : ℝ) : ℂ)⁻¹ • (g p.1.1 - g p.1.2))
    (by
      have hc1 : Continuous fun p : offDiag (univ : Set ℝ) => p.1.1 :=
        continuous_fst.comp continuous_subtype_val
      have hc2 : Continuous fun p : offDiag (univ : Set ℝ) => p.1.2 :=
        continuous_snd.comp continuous_subtype_val
      refine ((continuous_ofReal.comp (hc1.sub hc2)).inv₀ fun p => ?_).smul
        ((hg.continuous.comp hc1).sub (hg.continuous.comp hc2))
      exact ofReal_ne_zero.2 (sub_ne_zero.2 p.2.2.2))
    K fun p => by
      have hne : 0 < |p.1.1 - p.1.2| := abs_pos.2 (sub_ne_zero.2 p.2.2.2)
      have hlip : ‖g p.1.1 - g p.1.2‖ ≤ K * |p.1.1 - p.1.2| := by
        simpa [dist_eq_norm, Real.dist_eq] using hg.dist_le_mul p.1.1 p.1.2
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_mul_le_iff₀ hne, mul_comm]
      exact hlip

theorem norm_offDiagSlope_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : ℝ≥0}
    {g : ℝ → E} (hg : LipschitzWith K g) : ‖offDiagSlope hg‖ ≤ K :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ K.coe_nonneg _

theorem smul_offDiagSlope_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : ℝ≥0} {g : ℝ → E} (hg : LipschitzWith K g) {t s : ℝ} (h : t ≠ s) :
    (t - s : ℂ) • offDiagSlope hg ⟨(t, s), ⟨trivial, trivial, h⟩⟩ = g t - g s := by
  have hts : ((t - s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (sub_ne_zero.2 h)
  have hcast : (t - s : ℂ) = ((t - s : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  exact smul_inv_smul₀ hts (g t - g s)

namespace CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-- `G` is an *upper strip function* for Calderón's upper complex method `[X₀, X₁]^θ`, with
boundary difference quotients `q = (q₀, q₁)` on `offDiag (univ : Set ℝ)`: it is holomorphic on the
open strip `0 < re z < 1` and continuous up to its boundary, grows at most linearly on the closed
strip `0 ≤ re z ≤ 1`, and its boundary increments on `re z = 0` and `re z = 1` satisfy
`G (t * I) - G (s * I) = (t - s) • q₀ (t, s)` in `X₀` and
`G (1 + t * I) - G (1 + s * I) = (t - s) • q₁ (t, s)` in `X₁` for `t ≠ s`. -/
structure IsUpperStripFunction (G : ℂ → C.SumSpace)
    (q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)) : Prop where
  /-- `G` is holomorphic on the open strip and continuous on the closed strip. -/
  diffContOnCl : DiffContOnCl ℂ G (verticalStrip 0 1)
  /-- `G` grows at most linearly along the closed strip. -/
  exists_norm_le : ∃ K, ∀ z ∈ verticalClosedStrip 0 1, ‖G z‖ ≤ K * (1 + |z.im|)
  /-- On `re z = 0`, increments of `G` have difference quotient `q₀` in `X₀`. -/
  sub_mul_I {t s : ℝ} (h : t ≠ s) :
    G (t * I) - G (s * I) = (t - s : ℂ) • C.fstToSum (q.1 ⟨(t, s), ⟨trivial, trivial, h⟩⟩)
  /-- On `re z = 1`, increments of `G` have difference quotient `q₁` in `X₁`. -/
  sub_one_add_mul_I {t s : ℝ} (h : t ≠ s) :
    G (1 + t * I) - G (1 + s * I) =
      (t - s : ℂ) • C.sndToSum (q.2 ⟨(t, s), ⟨trivial, trivial, h⟩⟩)

namespace IsUpperStripFunction

variable {C} {G H : ℂ → C.SumSpace}
  {q r : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)}

theorem zero : C.IsUpperStripFunction 0 0 where
  diffContOnCl := diffContOnCl_const (c := 0)
  exists_norm_le := ⟨0, fun _ _ => by simp⟩
  sub_mul_I _ := by simp
  sub_one_add_mul_I _ := by simp

/-- Any constant function into the sum space is an upper strip function with zero boundary
difference quotients. -/
theorem const (u : C.SumSpace) : C.IsUpperStripFunction (fun _ => u) 0 where
  diffContOnCl := diffContOnCl_const
  exists_norm_le := ⟨‖u‖, fun z _ =>
    (mul_one ‖u‖).symm.trans_le
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) (norm_nonneg _))⟩
  sub_mul_I _ := by simp
  sub_one_add_mul_I _ := by simp

theorem add (hG : C.IsUpperStripFunction G q) (hH : C.IsUpperStripFunction H r) :
    C.IsUpperStripFunction (G + H) (q + r) where
  diffContOnCl := hG.diffContOnCl.add hH.diffContOnCl
  exists_norm_le := by
    obtain ⟨K, hK⟩ := hG.exists_norm_le; obtain ⟨L, hL⟩ := hH.exists_norm_le
    exact ⟨K + L, fun z hz => ((norm_add_le _ _).trans (add_le_add (hK z hz) (hL z hz))).trans_eq
      (add_mul _ _ _).symm⟩
  sub_mul_I h := by
    simp only [Pi.add_apply, FunLike.coe_add, Prod.fst_add, map_add, smul_add]
    rw [← hG.sub_mul_I h, ← hH.sub_mul_I h]; abel
  sub_one_add_mul_I h := by
    simp only [Pi.add_apply, FunLike.coe_add, Prod.snd_add, map_add, smul_add]
    rw [← hG.sub_one_add_mul_I h, ← hH.sub_one_add_mul_I h]; abel

theorem const_smul (hG : C.IsUpperStripFunction G q) (c : ℂ) :
    C.IsUpperStripFunction (c • G) (c • q) where
  diffContOnCl := hG.diffContOnCl.const_smul c
  exists_norm_le := by
    obtain ⟨K, hK⟩ := hG.exists_norm_le
    refine ⟨‖c‖ * K, fun z hz => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK z hz) (norm_nonneg c)
  sub_mul_I h := by
    simp only [Pi.smul_apply, ← smul_sub, hG.sub_mul_I h, Prod.smul_fst,
      FunLike.coe_smul, map_smul, smul_comm c]
  sub_one_add_mul_I h := by
    simp only [Pi.smul_apply, ← smul_sub, hG.sub_one_add_mul_I h, Prod.smul_snd,
      FunLike.coe_smul, map_smul, smul_comm c]

theorem neg (hG : C.IsUpperStripFunction G q) : C.IsUpperStripFunction (-G) (-q) := by
  simpa using hG.const_smul (-1)

theorem sub (hG : C.IsUpperStripFunction G q) (hH : C.IsUpperStripFunction H r) :
    C.IsUpperStripFunction (G - H) (q - r) := by
  simpa [sub_eq_add_neg] using hG.add hH.neg

/-- Shifting an upper strip function by a constant in the sum space leaves its boundary difference
quotients unchanged. -/
theorem add_const (hG : C.IsUpperStripFunction G q) (u : C.SumSpace) :
    C.IsUpperStripFunction (fun z => G z + u) q := by
  simpa [Pi.add_def] using hG.add (const u)

theorem sub_const (hG : C.IsUpperStripFunction G q) (u : C.SumSpace) :
    C.IsUpperStripFunction (fun z => G z - u) q := by
  simpa [sub_eq_add_neg] using hG.add_const (-u)

/-- An upper strip function can be replaced by any function agreeing with it on the closed strip. -/
theorem congr {G' : ℂ → C.SumSpace} (hG : C.IsUpperStripFunction G q)
    (hEq : EqOn G G' (verticalClosedStrip 0 1)) : C.IsUpperStripFunction G' q where
  diffContOnCl := ⟨hG.diffContOnCl.differentiableOn.congr
      (hEq.symm.mono (verticalStrip_subset_verticalClosedStrip 0 1)),
    hG.diffContOnCl.continuousOn.congr (closure_verticalStrip zero_lt_one ▸ hEq.symm)⟩
  exists_norm_le := by
    obtain ⟨K, hK⟩ := hG.exists_norm_le
    exact ⟨K, fun z hz => by rw [← hEq hz]; exact hK z hz⟩
  sub_mul_I hne := by rw [← hEq (by simp), ← hEq (by simp)]; exact hG.sub_mul_I hne
  sub_one_add_mul_I hne := by
    rw [← hEq (by simp), ← hEq (by simp)]; exact hG.sub_one_add_mul_I hne

/-- The boundary difference quotients `q` are uniquely determined by the upper strip function
`G`. -/
theorem trace_unique (hG : C.IsUpperStripFunction G q) (hG' : C.IsUpperStripFunction G r) :
    q = r := by
  refine Prod.ext (BoundedContinuousFunction.ext fun ⟨⟨t, s⟩, hp⟩ => ?_)
    (BoundedContinuousFunction.ext fun ⟨⟨t, s⟩, hp⟩ => ?_)
  · exact C.fstToSum_injective (smul_right_injective _ (sub_ne_zero.2 (by exact_mod_cast hp.2.2))
      ((hG.sub_mul_I hp.2.2).symm.trans (hG'.sub_mul_I hp.2.2)))
  · exact C.sndToSum_injective (smul_right_injective _ (sub_ne_zero.2 (by exact_mod_cast hp.2.2))
      ((hG.sub_one_add_mul_I hp.2.2).symm.trans (hG'.sub_one_add_mul_I hp.2.2)))

/-- An upper strip function is complex-differentiable at every point of the open strip. -/
theorem differentiableAt (hG : C.IsUpperStripFunction G q) {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    DifferentiableAt ℂ G z :=
  hG.diffContOnCl.differentiableOn.differentiableAt ((isOpen_verticalStrip 0 1).mem_nhds hz)

/-- An upper strip function has finite exponential order along the open strip. -/
theorem isBigO_exp_rpow (hG : C.IsUpperStripFunction G q) :
    ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A) := by
  obtain ⟨K, hK⟩ := hG.exists_norm_le
  set M := max K 0
  refine ⟨1, 2 * M + 1, IsBigO.of_norm_eventuallyLE ?_⟩
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop 1)).filter_mono
      inf_le_left,
    (eventually_mem_principal (verticalStrip 0 1)).filter_mono inf_le_right] with w hw1 hw
  have hGw : ‖G w‖ ≤ (2 * M + 1) * ‖w‖ :=
    calc ‖G w‖ ≤ K * (1 + |w.im|) := hK w (verticalStrip_subset_verticalClosedStrip 0 1 hw)
      _ ≤ M * (1 + ‖w‖) := mul_le_mul (le_max_left K 0) (by linarith [abs_im_le_norm w])
          (by positivity) (le_max_right K 0)
      _ ≤ (2 * M + 1) * ‖w‖ := by nlinarith [le_max_right K 0]
  rw [Real.rpow_one]
  exact hGw.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))

/-! ### Pinned Lipschitz boundary curves -/

/-- The left boundary curve `t ↦ G (t * I) - G 0` in `X₀`, pinned to vanish at `0`, recovered from
the difference quotient `q₀`. -/
def fstBoundary (q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)) (t : ℝ) :
    X₀ :=
  if h : t = 0 then 0 else (t : ℂ) • q.1 ⟨(t, 0), ⟨trivial, trivial, h⟩⟩

/-- The right boundary curve `t ↦ G (1 + t * I) - G 1` in `X₁`, pinned to vanish at `0`, recovered
from the difference quotient `q₁`. -/
def sndBoundary (q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)) (t : ℝ) :
    X₁ :=
  if h : t = 0 then 0 else (t : ℂ) • q.2 ⟨(t, 0), ⟨trivial, trivial, h⟩⟩

omit [NormedSpace ℂ X₁] in
@[simp]
theorem fstBoundary_zero (q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)) :
    fstBoundary q 0 = 0 := by simp [fstBoundary]

omit [NormedSpace ℂ X₀] in
@[simp]
theorem sndBoundary_zero (q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)) :
    sndBoundary q 0 = 0 := by simp [sndBoundary]

theorem fstToSum_fstBoundary (hG : C.IsUpperStripFunction G q) (t : ℝ) :
    C.fstToSum (fstBoundary q t) = G (t * I) - G 0 := by
  by_cases ht : t = 0
  · subst ht; simp
  · simpa [fstBoundary, ht] using (hG.sub_mul_I ht).symm

theorem sndToSum_sndBoundary (hG : C.IsUpperStripFunction G q) (t : ℝ) :
    C.sndToSum (sndBoundary q t) = G (1 + t * I) - G 1 := by
  by_cases ht : t = 0
  · subst ht; simp
  · simpa [sndBoundary, ht] using (hG.sub_one_add_mul_I ht).symm

theorem fstToSum_fstBoundary_sub (hG : C.IsUpperStripFunction G q) (t s : ℝ) :
    C.fstToSum (fstBoundary q t - fstBoundary q s) = G (t * I) - G (s * I) := by
  rw [map_sub, hG.fstToSum_fstBoundary, hG.fstToSum_fstBoundary]; abel

theorem sndToSum_sndBoundary_sub (hG : C.IsUpperStripFunction G q) (t s : ℝ) :
    C.sndToSum (sndBoundary q t - sndBoundary q s) = G (1 + t * I) - G (1 + s * I) := by
  rw [map_sub, hG.sndToSum_sndBoundary, hG.sndToSum_sndBoundary]; abel

theorem fstBoundary_sub_eq_smul (hG : C.IsUpperStripFunction G q) {t s : ℝ} (h : t ≠ s) :
    fstBoundary q t - fstBoundary q s = (t - s : ℂ) • q.1 ⟨(t, s), ⟨trivial, trivial, h⟩⟩ :=
  C.fstToSum_injective <| by rw [hG.fstToSum_fstBoundary_sub, hG.sub_mul_I h, map_smul]

theorem sndBoundary_sub_eq_smul (hG : C.IsUpperStripFunction G q) {t s : ℝ} (h : t ≠ s) :
    sndBoundary q t - sndBoundary q s = (t - s : ℂ) • q.2 ⟨(t, s), ⟨trivial, trivial, h⟩⟩ :=
  C.sndToSum_injective <| by rw [hG.sndToSum_sndBoundary_sub, hG.sub_one_add_mul_I h, map_smul]

private theorem lipschitzWith_of_sub_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q₀ : offDiag (univ : Set ℝ) →ᵇ E} {c : ℝ → E}
    (hc : ∀ {t s : ℝ} (h : t ≠ s), c t - c s = (t - s : ℂ) • q₀ ⟨(t, s), ⟨trivial, trivial, h⟩⟩) :
    LipschitzWith ‖q₀‖₊ c :=
  LipschitzWith.of_dist_le_mul fun t s => by
    rcases eq_or_ne t s with rfl | h
    · simp
    · rw [dist_eq_norm, Real.dist_eq, hc h, norm_smul, ← ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (q₀.norm_coe_le_norm _) (abs_nonneg _)

/-- The left boundary curve `fstBoundary q` of an upper strip function is `‖q₀‖`-Lipschitz. -/
theorem lipschitzWith_fstBoundary (hG : C.IsUpperStripFunction G q) :
    LipschitzWith ‖q.1‖₊ (fstBoundary q) :=
  lipschitzWith_of_sub_eq_smul hG.fstBoundary_sub_eq_smul

/-- The right boundary curve `sndBoundary q` of an upper strip function is `‖q₁‖`-Lipschitz. -/
theorem lipschitzWith_sndBoundary (hG : C.IsUpperStripFunction G q) :
    LipschitzWith ‖q.2‖₊ (sndBoundary q) :=
  lipschitzWith_of_sub_eq_smul hG.sndBoundary_sub_eq_smul

theorem norm_fstBoundary_sub_le (hG : C.IsUpperStripFunction G q) (t s : ℝ) :
    ‖fstBoundary q t - fstBoundary q s‖ ≤ ‖q.1‖ * |t - s| := by
  simpa [dist_eq_norm, Real.dist_eq] using hG.lipschitzWith_fstBoundary.dist_le_mul t s

theorem norm_sndBoundary_sub_le (hG : C.IsUpperStripFunction G q) (t s : ℝ) :
    ‖sndBoundary q t - sndBoundary q s‖ ≤ ‖q.2‖ * |t - s| := by
  simpa [dist_eq_norm, Real.dist_eq] using hG.lipschitzWith_sndBoundary.dist_le_mul t s

/-! ### Bergh–Löfström Lemma 4.1.3: three-lines estimates on difference quotients and derivatives -/

/-- Finite-order growth on the open strip is preserved under scaled vertical differences. -/
private theorem isBigO_exp_rpow_verticalDiffQuot {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {A B : ℝ}
    (hf : f =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A))
    (h : ℝ) (c : ℂ) :
    ∃ A' B' : ℝ, (fun z => c • (f (z + h * I) - f z)) =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)]
      fun w => Real.exp (B' * ‖w‖ ^ A') := by
  let l := cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)
  have htend : Tendsto (fun z : ℂ => z + h * I) l l := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
    · rw [← tendsto_norm_atTop_iff_cobounded]
      have hnorm : Tendsto (fun z : ℂ => ‖z‖ - ‖(h : ℂ) * I‖) l atTop :=
        (tendsto_atTop_add_const_right _ (-‖(h : ℂ) * I‖)
          (tendsto_norm_cobounded_atTop.mono_left inf_le_left)).congr fun _ =>
            (sub_eq_add_neg _ _).symm
      exact tendsto_atTop_mono (fun z => by
        have htri := norm_sub_le (z + h * I) ((h : ℂ) * I)
        rw [add_sub_cancel_right] at htri; linarith) hnorm
    · filter_upwards [(eventually_mem_principal (verticalStrip 0 1)).filter_mono inf_le_right]
        with z hz using by simpa using hz
  set p := max A 0
  have hlarge : ∀ᶠ z : ℂ in l, max 1 ‖(h : ℂ) * I‖ + 1 ≤ ‖z‖ :=
    (tendsto_norm_cobounded_atTop.eventually
      (eventually_ge_atTop (max 1 ‖(h : ℂ) * I‖ + 1))).filter_mono inf_le_left
  have hshift : (fun z => f (z + h * I)) =O[l] fun w => Real.exp (|B| * 2 ^ p * ‖w‖ ^ p) := by
    refine (hf.comp_tendsto htend).trans (IsBigO.of_norm_eventuallyLE ?_)
    filter_upwards [hlarge] with z hz
    have h1 : 1 ≤ ‖z + h * I‖ := by
      have htri := norm_sub_le (z + h * I) ((h : ℂ) * I)
      rw [add_sub_cancel_right] at htri; linarith [le_max_right 1 ‖(h : ℂ) * I‖]
    have h2 : ‖z + h * I‖ ≤ 2 * ‖z‖ := by
      linarith [norm_add_le z ((h : ℂ) * I), le_max_left 1 ‖(h : ℂ) * I‖,
        le_max_right 1 ‖(h : ℂ) * I‖]
    have hexp : B * ‖z + h * I‖ ^ A ≤ |B| * 2 ^ p * ‖z‖ ^ p :=
      calc B * ‖z + h * I‖ ^ A
          ≤ |B| * ‖z + h * I‖ ^ p :=
            mul_le_mul (le_abs_self B) (Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _))
              (Real.rpow_nonneg (norm_nonneg _) _) (abs_nonneg B)
        _ ≤ |B| * (2 * ‖z‖) ^ p := by gcongr
        _ = |B| * 2 ^ p * ‖z‖ ^ p := by rw [Real.mul_rpow zero_le_two (norm_nonneg _)]; ring
    simpa [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp] using hexp
  have hself : f =O[l] fun w => Real.exp (|B| * 2 ^ p * ‖w‖ ^ p) := by
    refine hf.trans (IsBigO.of_norm_eventuallyLE ?_)
    filter_upwards [hlarge] with z hz
    have hz1 : 1 ≤ ‖z‖ := by linarith [le_max_left 1 ‖(h : ℂ) * I‖]
    have h2p : |B| ≤ |B| * 2 ^ p :=
      le_mul_of_one_le_right (abs_nonneg B) (Real.one_le_rpow one_le_two (le_max_right _ _))
    have hexp : B * ‖z‖ ^ A ≤ |B| * 2 ^ p * ‖z‖ ^ p :=
      mul_le_mul ((le_abs_self B).trans h2p)
        (Real.rpow_le_rpow_of_exponent_le hz1 (le_max_left _ _))
        (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
    simpa [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp] using hexp
  exact ⟨p, |B| * 2 ^ p, (hshift.sub hself).const_smul_left c⟩

private theorem norm_verticalDiffQuot_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : E →L[ℂ] C.SumSpace} (hι : ∀ x, ‖ι x‖ ≤ ‖x‖) {q₀ : offDiag (univ : Set ℝ) →ᵇ E} {c h : ℝ}
    (hh : h ≠ 0)
    (hc : ∀ {t s : ℝ} (hne : t ≠ s),
      G (c + t * I) - G (c + s * I) = (t - s : ℂ) • ι (q₀ ⟨(t, s), ⟨trivial, trivial, hne⟩⟩))
    {w : ℂ} (hw : w.re = c) : ‖((h : ℂ) * I)⁻¹ • (G (w + h * I) - G w)‖ ≤ ‖q₀‖ := by
  have hwc : w = c + w.im * I := by nth_rw 1 [← re_add_im w]; simp [hw]
  have hwh : w + h * I = c + ((w.im + h : ℝ) : ℂ) * I := by nth_rw 1 [hwc]; push_cast; ring
  have hne : w.im + h ≠ w.im := by simpa using hh
  have hdiff : G (w + h * I) - G w =
      (((w.im + h : ℝ) : ℂ) - w.im) • ι (q₀ ⟨(w.im + h, w.im), ⟨trivial, trivial, hne⟩⟩) := by
    nth_rw 2 [hwc]; rw [hwh, hc hne]
  have hsub : ‖((w.im + h : ℝ) : ℂ) - w.im‖ = ‖(h : ℂ)‖ := by congr 1; push_cast; ring
  simp only [hdiff, norm_smul, norm_inv, norm_mul, norm_I, mul_one, hsub]
  rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.2 (ofReal_ne_zero.2 hh))]
  exact (hι _).trans (q₀.norm_coe_le_norm _)

/-- Three-lines bound on vertical increments under finite-order strip growth. -/
private theorem norm_sub_add_mul_I_le_rpow_mul_rpow_of_isBigO
    (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hgrowth : ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)]
      fun w => Real.exp (B * ‖w‖ ^ A))
    (h₀ : ∀ {t s : ℝ} (h : t ≠ s),
      G (t * I) - G (s * I) = (t - s : ℂ) • C.fstToSum (q.1 ⟨(t, s), ⟨trivial, trivial, h⟩⟩))
    (h₁ : ∀ {t s : ℝ} (h : t ≠ s), G (1 + t * I) - G (1 + s * I) =
      (t - s : ℂ) • C.sndToSum (q.2 ⟨(t, s), ⟨trivial, trivial, h⟩⟩))
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) (h : ℝ) :
    ‖G (z + h * I) - G z‖ ≤ |h| * (‖q.1‖ ^ (1 - z.re) * ‖q.2‖ ^ z.re) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  let D : ℂ → C.SumSpace := fun w => ((h : ℂ) * I)⁻¹ • (G (w + h * I) - G w)
  have hshift : Differentiable ℂ (fun w : ℂ => w + h * I) := by fun_prop
  have hdD : DiffContOnCl ℂ D (verticalStrip 0 1) :=
    ((hd.comp hshift.diffContOnCl fun w hw => by simpa using hw).sub hd).const_smul
      (((h : ℂ) * I)⁻¹)
  obtain ⟨A₁, B₁, hg₁⟩ := hgrowth
  have hgD := isBigO_exp_rpow_verticalDiffQuot hg₁ h (((h : ℂ) * I)⁻¹)
  have hD : ‖D z‖ ≤ ‖q.1‖ ^ (1 - z.re) * ‖q.2‖ ^ z.re := by
    simpa [sub_zero, div_one] using
      TauCeti.PhragmenLindelof.norm_le_interp_of_isBigO_exp_rpow zero_lt_one hdD hgD
        (fun w hw => norm_verticalDiffQuot_le C.norm_fstToSum_le hh
          (fun hne => by simpa using h₀ hne) hw)
        (fun w hw => norm_verticalDiffQuot_le C.norm_sndToSum_le hh
          (fun hne => by simpa using h₁ hne) hw) hz
  rw [← inv_mul_le_iff₀ (abs_pos.2 hh)]
  simpa [D, norm_smul, Real.norm_eq_abs] using hD

private theorem rpow_mul_rpow_le_norm {A B : Type*} [SeminormedAddCommGroup A]
    [SeminormedAddCommGroup B] (q : A × B) {x : ℝ} (hx : x ∈ Icc 0 1) :
    ‖q.1‖ ^ (1 - x) * ‖q.2‖ ^ x ≤ ‖q‖ := by
  calc ‖q.1‖ ^ (1 - x) * ‖q.2‖ ^ x
      ≤ ‖q‖ ^ (1 - x) * ‖q‖ ^ x := by
        gcongr; exacts [sub_nonneg.2 hx.2, norm_fst_le q, hx.1, norm_snd_le q]
    _ = ‖q‖ := by rw [← Real.rpow_add' (norm_nonneg q) (by simp), sub_add_cancel, Real.rpow_one]

/-- Finite-order growth on the open strip, combined with bounded boundary difference quotients,
automatically upgrades to linear growth on the closed strip. -/
theorem of_isBigO_exp_rpow (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hgrowth : ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)]
      fun w => Real.exp (B * ‖w‖ ^ A))
    (h₀ : ∀ {t s : ℝ} (h : t ≠ s),
      G (t * I) - G (s * I) = (t - s : ℂ) • C.fstToSum (q.1 ⟨(t, s), ⟨trivial, trivial, h⟩⟩))
    (h₁ : ∀ {t s : ℝ} (h : t ≠ s), G (1 + t * I) - G (1 + s * I) =
      (t - s : ℂ) • C.sndToSum (q.2 ⟨(t, s), ⟨trivial, trivial, h⟩⟩)) :
    C.IsUpperStripFunction G q where
  diffContOnCl := hd
  exists_norm_le := by
    have hseg : ContinuousOn (fun x : ℝ => G x) (Icc 0 1) :=
      (hd.continuousOn_verticalClosedStrip zero_lt_one).comp continuous_ofReal.continuousOn
        fun x hx => by simpa using hx
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hseg
    refine ⟨max M 0 + ‖q‖, fun z hz => ?_⟩
    have hz_re : (z.re : ℂ) ∈ verticalClosedStrip 0 1 := by simpa using hz
    have hvert : ‖G z - G z.re‖ ≤ |z.im| * ‖q‖ := by
      have h1 := norm_sub_add_mul_I_le_rpow_mul_rpow_of_isBigO hd hgrowth h₀ h₁ hz_re z.im
      rw [re_add_im] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (rpow_mul_rpow_le_norm q hz_re) (abs_nonneg _))
    have hbase : ‖G z.re‖ ≤ max M 0 := (hM z.re hz).trans (le_max_left M 0)
    have htri : ‖G z‖ ≤ ‖G z.re‖ + ‖G z - G z.re‖ := norm_le_insert' (G z) (G z.re)
    nlinarith [abs_nonneg z.im, norm_nonneg q, le_max_right M 0]
  sub_mul_I := h₀
  sub_one_add_mul_I := h₁

/-- **Bergh–Löfström Lemma 4.1.3 (difference quotients).** Vertical increments of an upper strip
function satisfy the three-lines estimate
`‖G (z + h * I) - G z‖ ≤ |h| * ‖q₀‖ ^ (1 - re z) * ‖q₁‖ ^ re z` across the closed strip. -/
theorem norm_sub_add_mul_I_le_rpow_mul_rpow (hG : C.IsUpperStripFunction G q) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (h : ℝ) :
    ‖G (z + h * I) - G z‖ ≤ |h| * (‖q.1‖ ^ (1 - z.re) * ‖q.2‖ ^ z.re) :=
  norm_sub_add_mul_I_le_rpow_mul_rpow_of_isBigO hG.diffContOnCl hG.isBigO_exp_rpow
    hG.sub_mul_I hG.sub_one_add_mul_I hz h

/-- **Bergh–Löfström Lemma 4.1.3 (three-lines derivative bound).** On the open strip `0 < re z < 1`,
the complex derivative of an upper strip function satisfies
`‖deriv G z‖ ≤ ‖q₀‖ ^ (1 - re z) * ‖q₁‖ ^ re z`. -/
theorem norm_deriv_le_rpow_mul_rpow (hG : C.IsUpperStripFunction G q) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) : ‖deriv G z‖ ≤ ‖q.1‖ ^ (1 - z.re) * ‖q.2‖ ^ z.re := by
  have hGz : HasDerivAt G (deriv G z) (z + (0 : ℂ) * I) := by
    simpa using (hG.differentiableAt hz).hasDerivAt
  have hφ : HasDerivAt (fun w : ℂ => z + w * I) I 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const I).const_add z
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 (hGz.scomp (0 : ℂ) hφ)
  let hseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hhpos (n : ℕ) : 0 < hseq n := by dsimp [hseq]; positivity
  have htend : Tendsto (fun n : ℕ => (hseq n : ℂ)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2
      ⟨(continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat,
        .of_forall fun n => ofReal_ne_zero.2 (hhpos n).ne'⟩
  have hlim := ((continuous_const_smul I⁻¹).tendsto (I • deriv G z)).comp (hslope.comp htend)
  rw [inv_smul_smul₀ I_ne_zero] at hlim
  refine le_of_tendsto hlim.norm (.of_forall fun n => ?_)
  dsimp only [Function.comp_def]
  rw [← smul_assoc, smul_eq_mul, ← mul_inv, norm_smul, norm_inv, norm_mul, norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (hhpos n).le, inv_mul_le_iff₀ (hhpos n)]
  simpa [abs_of_pos (hhpos n)] using
    hG.norm_sub_add_mul_I_le_rpow_mul_rpow (verticalStrip_subset_verticalClosedStrip 0 1 hz)
      (hseq n)

theorem norm_deriv_le (hG : C.IsUpperStripFunction G q) {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    ‖deriv G z‖ ≤ ‖q‖ :=
  (hG.norm_deriv_le_rpow_mul_rpow hz).trans
    (rpow_mul_rpow_le_norm q (verticalStrip_subset_verticalClosedStrip 0 1 hz))

/-- **Bergh–Löfström Lemma 4.1.3 (strip Lipschitz bound).** Every upper strip function with
boundary difference quotients `q` is `‖q‖`-Lipschitz on the entire closed strip `0 ≤ re z ≤ 1`. -/
theorem lipschitzOnWith (hG : C.IsUpperStripFunction G q) :
    LipschitzOnWith ‖q‖₊ G (verticalClosedStrip 0 1) := by
  have hopen : LipschitzOnWith ‖q‖₊ G (verticalStrip 0 1) :=
    (convex_verticalStrip 0 1).lipschitzOnWith_of_nnNorm_deriv_le
      (fun _ hz => hG.differentiableAt hz) fun _ hz => by
        rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]; exact hG.norm_deriv_le hz
  exact closure_verticalStrip zero_lt_one ▸ hopen.closure hG.diffContOnCl.continuousOn

theorem norm_sub_le (hG : C.IsUpperStripFunction G q) {z w : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (hw : w ∈ verticalClosedStrip 0 1) :
    ‖G z - G w‖ ≤ ‖q‖ * ‖z - w‖ := by
  simpa [dist_eq_norm] using hG.lipschitzOnWith.dist_le_mul z hz w hw

theorem norm_sub_apply_zero_le (hG : C.IsUpperStripFunction G q) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖G z - G 0‖ ≤ ‖q‖ * ‖z‖ := by
  simpa using hG.norm_sub_le hz (by simp : (0 : ℂ) ∈ verticalClosedStrip 0 1)

/-- Two upper strip functions with the same boundary difference quotients differ by a constant on
the closed strip: `G z - G 0 = H z - H 0`. -/
theorem eqOn_sub_apply_zero (hG : C.IsUpperStripFunction G q) (hH : C.IsUpperStripFunction H q) :
    EqOn (fun z => G z - G 0) (fun z => H z - H 0) (verticalClosedStrip 0 1) := fun z hz => by
  have h0 := (hG.sub hH).norm_sub_apply_zero_le hz
  simp only [sub_self, norm_zero, zero_mul, Pi.sub_apply, norm_le_zero_iff] at h0
  exact sub_eq_zero.1 (by rwa [sub_sub_sub_comm] at h0)

/-- Two upper strip functions with the same boundary difference quotients have the same complex
derivative at every point of the open strip. -/
theorem deriv_eq (hG : C.IsUpperStripFunction G q) (hH : C.IsUpperStripFunction H q) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) : deriv G z = deriv H z := by
  have heq : G =ᶠ[𝓝 z] fun w => H w + (G 0 - H 0) := by
    filter_upwards [(isOpen_verticalStrip 0 1).mem_nhds hz] with w hw
    have hw' : G w - G 0 = H w - H 0 :=
      hG.eqOn_sub_apply_zero hH (verticalStrip_subset_verticalClosedStrip 0 1 hw)
    rw [eq_add_of_sub_eq hw']; abel
  rw [heq.deriv_eq, deriv_add_const]

/-- Construct `IsUpperStripFunction` from Lipschitz boundary curves `g₀ : ℝ → X₀`, `g₁ : ℝ → X₁`
representing the boundary increments of `G` in `X₀ + X₁`, under finite-order strip growth. -/
theorem of_lipschitz (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hgrowth : ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)]
      fun w => Real.exp (B * ‖w‖ ^ A))
    {g₀ : ℝ → X₀} {g₁ : ℝ → X₁} {K₀ K₁ : ℝ≥0}
    (hg₀ : LipschitzWith K₀ g₀) (hg₁ : LipschitzWith K₁ g₁)
    (h₀ : ∀ t s : ℝ, G (t * I) - G (s * I) = C.fstToSum (g₀ t - g₀ s))
    (h₁ : ∀ t s : ℝ, G (1 + t * I) - G (1 + s * I) = C.sndToSum (g₁ t - g₁ s)) :
    C.IsUpperStripFunction G (offDiagSlope hg₀, offDiagSlope hg₁) :=
  of_isBigO_exp_rpow hd hgrowth
    (fun {t s} h => by rw [h₀ t s, ← map_smul, smul_offDiagSlope_apply hg₀ h])
    (fun {t s} h => by rw [h₁ t s, ← map_smul, smul_offDiagSlope_apply hg₁ h])

end IsUpperStripFunction

end CompatibleCouple

end TauCeti
