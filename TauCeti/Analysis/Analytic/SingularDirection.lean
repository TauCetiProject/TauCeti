/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Singular directions of analytic functions

A direction `v` is *singular* for a function `f` at a point `x` if `f` vanishes identically on
the line through `x` in the direction `v`, near `x`: `f (x + ξ • v) = 0` for all small `ξ`.
For an analytic function this is a countable family of equations in the pair `(x, v)`: if `f` has
the power series `p` at `x`, then `f (x + ξ • v) = ∑ₙ ξ ^ n • p n (v, …, v)`, so `v` is singular
exactly when every homogeneous term `p n (v, …, v)` vanishes
(`HasFPowerSeriesAt.eventually_apply_add_smul_eq_zero_iff`). Over a field of characteristic zero,
these terms are the directional derivatives `Dⁿ f (x) (v, …, v) / n!`, and `v` is singular exactly
when all the directional derivatives of `f` at `x` in the direction `v` vanish, starting with the
value `f x` itself (`AnalyticAt.eventually_apply_add_smul_eq_zero_iff`).

Where `f` is analytic, the directional derivatives `(x, v) ↦ Dⁿ f (x) (v, …, v)` are analytic
functions of the pair `(x, v)` (`AnalyticOnNhd.iteratedFDeriv_apply_diag`), so the incidence set
of points `x` of a set `s` on a neighbourhood of which `f` is analytic and of directions singular
at `x` is the common zero set in `s × E` of a countable family of analytic functions
(`AnalyticOnNhd.setOf_eventually_apply_add_smul_eq_zero`). At a fixed point, the singular
directions form a closed set (`AnalyticAt.isClosed_setOf_eventually_apply_add_smul_eq_zero`)
invariant under multiplication by nonzero scalars
(`TauCeti.eventually_apply_add_smul_smul_eq_zero_iff`), so they may be represented by unit vectors
or by points of projective space.

Finally, singular directions of a function of real variables can be detected after
complexification. If `F` is complex analytic at the real point `x` of `ι → ℂ` and agrees with
`f` on the real points near `x`, then a real direction `v` is singular for `f` at `x` exactly when
it is singular for `F` along the complex line through `x`
(`AnalyticAt.eventually_real_apply_add_smul_eq_zero_iff`), so exactly when the complex
directional derivatives `Dⁿ F (x) (v, …, v)` all vanish
(`AnalyticAt.eventually_real_apply_add_smul_eq_zero_iff_iteratedFDeriv`). These complex equations
are holomorphic in `(x, v)` wherever `F` is holomorphic (`AnalyticOnNhd.iteratedFDeriv_apply_diag`
over `ℂ`), so the real incidence set consists of the real points of the common zero set of a
countable family of holomorphic functions.

This is the analytic description of the singular directions in Łojasiewicz's lemma that the
directions singular for an analytic function not identically zero, at some point of a connected
open set, form a meagre set of directions.

## Main results

* `HasFPowerSeriesAt.eventually_apply_add_smul_eq_zero_iff`: `v` is singular for `f` at `x` if
  and only if every term of the power series of `f` at `x` vanishes at `(v, …, v)`.
* `AnalyticAt.eventually_apply_add_smul_eq_zero_iff`: `v` is singular for `f` at `x` if and only
  if every directional derivative `Dⁿ f (x) (v, …, v)` vanishes.
* `AnalyticOnNhd.iteratedFDeriv_apply_diag`: the directional derivatives are analytic in `(x, v)`.
* `AnalyticOnNhd.setOf_eventually_apply_add_smul_eq_zero`: the incidence set of points and
  singular directions is the common zero set of the directional derivatives.
* `AnalyticAt.eventually_real_apply_add_smul_eq_zero_iff_iteratedFDeriv`: a real direction is
  singular for a function of real variables if and only if all the directional derivatives of its
  complexification vanish.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2, Lemma 3.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- Whether `f` vanishes near `x` on the line through `x` in the direction `v` does not change
when `v` is rescaled by a nonzero scalar. -/
theorem eventually_apply_add_smul_smul_eq_zero_iff {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Zero F] {f : E → F} {x v : E} {c : 𝕜} (hc : c ≠ 0) :
    (∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • c • v) = 0) ↔ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0 := by
  have h : map (· * c) (𝓝 (0 : 𝕜)) = 𝓝 0 := by
    simpa using (Homeomorph.mulRight₀ c hc).map_nhds_eq 0
  conv_rhs => rw [← h, eventually_map]
  simp only [smul_smul]

end TauCeti

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x v : E}

namespace HasFPowerSeriesAt

/-- **Singular directions and power series.** If `f` has the power series `p` at `x`, then `f`
vanishes near `x` on the line through `x` in the direction `v` if and only if every homogeneous
term `p n` of the series vanishes at `(v, …, v)`. -/
theorem eventually_apply_add_smul_eq_zero_iff {p : FormalMultilinearSeries 𝕜 E F}
    (hf : HasFPowerSeriesAt f p x) :
    (∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0) ↔ ∀ n, p n (fun _ ↦ v) = 0 := by
  set u : 𝕜 →L[𝕜] E := (ContinuousLinearMap.id 𝕜 𝕜).smulRight v
  -- the restriction of `f` to the line has the power series `p` composed with `ξ ↦ ξ • v`
  have h0 : HasFPowerSeriesAt (fun z ↦ f (x + z)) p (u 0) := by
    rw [map_zero]
    convert hf.comp_sub (-x) using 1
    · ext z
      rw [sub_neg_eq_add, add_comm]
    · rw [add_neg_cancel]
  have hline : HasFPowerSeriesAt (fun ξ : 𝕜 ↦ f (x + ξ • v)) (p.compContinuousLinearMap u) 0 :=
    h0.compContinuousLinearMap
  have hcoeff (n : ℕ) : p.compContinuousLinearMap u n (fun _ ↦ 1) = p n (fun _ ↦ v) := by
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    congr 1
    ext
    simp [u]
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · rw [← hcoeff, hline.eq_zero_of_eventually h]
    simp
  · have hzero : p.compContinuousLinearMap u = 0 := by
      ext n : 1
      rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self (p.compContinuousLinearMap u n)]
      ext
      simp [hcoeff, h]
    exact (hzero ▸ hline).eventually_eq_zero

end HasFPowerSeriesAt

namespace AnalyticAt

variable [CharZero 𝕜] [CompleteSpace F]

/-- **Singular directions and directional derivatives.** A function `f` analytic at `x` vanishes
near `x` on the line through `x` in the direction `v` if and only if all its directional
derivatives `Dⁿ f (x) (v, …, v)` vanish, including the value `f x` for `n = 0`. -/
theorem eventually_apply_add_smul_eq_zero_iff (hf : AnalyticAt 𝕜 f x) :
    (∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0) ↔ ∀ n, iteratedFDeriv 𝕜 n f x (fun _ ↦ v) = 0 := by
  obtain ⟨p, r, hp⟩ := hf
  rw [hp.hasFPowerSeriesAt.eventually_apply_add_smul_eq_zero_iff]
  refine forall_congr' fun n ↦ ?_
  rw [← hp.factorial_smul v n, ← Nat.cast_smul_eq_nsmul 𝕜, smul_eq_zero,
    or_iff_right (Nat.cast_ne_zero.2 n.factorial_ne_zero)]

/-- The directions singular for a function analytic at `x` form a closed set. -/
theorem isClosed_setOf_eventually_apply_add_smul_eq_zero (hf : AnalyticAt 𝕜 f x) :
    IsClosed {v | ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} := by
  simp_rw [hf.eventually_apply_add_smul_eq_zero_iff, ofPred_forall]
  exact isClosed_iInter fun n ↦ isClosed_eq
    ((iteratedFDeriv 𝕜 n f x).coe_continuous.comp (continuous_pi fun _ ↦ continuous_id))
    continuous_const

end AnalyticAt

namespace AnalyticOnNhd

variable [CompleteSpace F] {s : Set E}

/-- The directional derivatives `(x, v) ↦ Dⁿ f (x) (v, …, v)` of a function analytic on a
neighbourhood of `s` are analytic in the pair `(x, v)` on a neighbourhood of `s ×ˢ univ`. -/
theorem iteratedFDeriv_apply_diag (hf : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (fun q : E × E ↦ iteratedFDeriv 𝕜 n f q.1 fun _ ↦ q.2) (s ×ˢ univ) := by
  intro q hq
  have happly : AnalyticAt 𝕜 (fun r : (E [×n]→L[𝕜] F) × (Fin n → E) ↦ r.1 r.2)
      (iteratedFDeriv 𝕜 n f q.1, fun _ ↦ q.2) := by
    simpa using (ContinuousLinearMap.id 𝕜 (E [×n]→L[𝕜] F)).analyticAt_uncurry_of_multilinear
      (x := (iteratedFDeriv 𝕜 n f q.1, fun _ ↦ q.2))
  have hdiag : AnalyticAt 𝕜 (fun q : E × E ↦ fun _ : Fin n ↦ q.2) q :=
    analyticAt_pi_iff.2 fun _ ↦ analyticAt_snd
  have hpair : AnalyticAt 𝕜 (fun q : E × E ↦ (iteratedFDeriv 𝕜 n f q.1, fun _ : Fin n ↦ q.2)) q :=
    (((hf.iteratedFDeriv n) q.1 hq.1).comp analyticAt_fst).prod hdiag
  exact happly.comp_of_eq hpair rfl

variable [CharZero 𝕜]

/-- **The incidence set of singular directions.** For `f` analytic on a neighbourhood of `s`, the
pairs `(x, v)` with `x ∈ s` such that `f` vanishes near `x` on the line through `x` in the direction
`v` are the common zeros in `s ×ˢ univ` of the directional derivatives
`(x, v) ↦ Dⁿ f (x) (v, …, v)`, which are analytic by `AnalyticOnNhd.iteratedFDeriv_apply_diag`. -/
theorem setOf_eventually_apply_add_smul_eq_zero (hf : AnalyticOnNhd 𝕜 f s) :
    {q : E × E | q.1 ∈ s ∧ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (q.1 + ξ • q.2) = 0} =
      s ×ˢ univ ∩ ⋂ n, {q | iteratedFDeriv 𝕜 n f q.1 (fun _ ↦ q.2) = 0} := by
  ext q
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_iInter]
  exact and_congr_right fun hq ↦ (hf q.1 hq).eventually_apply_add_smul_eq_zero_iff

end AnalyticOnNhd

end NontriviallyNormedField

section Complexification

variable {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace ℂ G]
  {F : (ι → ℂ) → G} {f : (ι → ℝ) → G} {x v : ι → ℝ}

namespace AnalyticAt

/-- **Singular directions after complexification.** Let `F` be complex analytic at the real point
`x` of `ι → ℂ` and agree with `f` at the real points near `x`. Then `f` vanishes near `x` on the
real line through `x` in the real direction `v` if and only if `F` vanishes near `x` on the complex
line through `x` in the direction `v`. -/
theorem eventually_real_apply_add_smul_eq_zero_iff (hF : AnalyticAt ℂ F fun i ↦ (x i : ℂ))
    (hFf : ∀ᶠ y in 𝓝 x, F (fun i ↦ (y i : ℂ)) = f y) :
    (∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) ↔
      ∀ᶠ ζ in 𝓝 (0 : ℂ), F ((fun i ↦ (x i : ℂ)) + ζ • fun i ↦ (v i : ℂ)) = 0 := by
  set g : ℂ → G := fun ζ ↦ F ((fun i ↦ (x i : ℂ)) + ζ • fun i ↦ (v i : ℂ))
  have hg : AnalyticAt ℂ g 0 := by
    refine hF.comp_of_eq (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) ?_
    simp
  -- on the real points of the complex line, `g` is the restriction of `f` to the real line
  have hline : Tendsto (fun ξ : ℝ ↦ x + ξ • v) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous fun ξ : ℝ ↦ x + ξ • v := by fun_prop
    simpa using hcont.tendsto 0
  have hgf : ∀ᶠ ξ : ℝ in 𝓝 0, g ξ = f (x + ξ • v) := by
    filter_upwards [hline.eventually hFf] with ξ hξ
    rw [← hξ]
    simp only [g]
    congr 1
    funext i
    simp
  have hreal : Tendsto (fun ξ : ℝ ↦ (ξ : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun ξ hξ ↦ by
      simpa using hξ
  refine ⟨fun h ↦ hg.frequently_zero_iff_eventually_zero.1 ?_, fun h ↦ ?_⟩
  · refine hreal.frequently (Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds (h.and hgf)] with ξ ⟨hξ, hgξ⟩
    rw [hgξ, hξ]
  · filter_upwards [Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero |>.eventually h,
      hgf] with ξ hξ hgξ
    rw [← hgξ]
    exact hξ

/-- **Singular directions and complex directional derivatives.** Let `F` be complex analytic at
the real point `x` of `ι → ℂ` and agree with `f` at the real points near `x`. Then `f` vanishes
near `x` on the real line through `x` in the real direction `v` if and only if all the complex
directional derivatives `Dⁿ F (x) (v, …, v)` vanish. -/
theorem eventually_real_apply_add_smul_eq_zero_iff_iteratedFDeriv [CompleteSpace G]
    (hF : AnalyticAt ℂ F fun i ↦ (x i : ℂ)) (hFf : ∀ᶠ y in 𝓝 x, F (fun i ↦ (y i : ℂ)) = f y) :
    (∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) ↔
      ∀ n, iteratedFDeriv ℂ n F (fun i ↦ (x i : ℂ)) (fun _ ↦ fun i ↦ (v i : ℂ)) = 0 := by
  rw [hF.eventually_real_apply_add_smul_eq_zero_iff hFf, hF.eventually_apply_add_smul_eq_zero_iff]

end AnalyticAt

end Complexification
