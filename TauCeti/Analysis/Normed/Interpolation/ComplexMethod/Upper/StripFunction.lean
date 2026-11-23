/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.VerticalStrip.Basic
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
public import TauCeti.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Analysis.Complex.PhragmenLindelof.VerticalStrip
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Upper strip functions for Calderón's upper complex interpolation method

For a compatible couple `(X₀, X₁)` of complex normed spaces, Calderón's upper complex interpolation
method `[X₀, X₁]^θ` is built from *upper strip functions* `G : ℂ → X₀ + X₁` on `0 ≤ re z ≤ 1`:
functions continuous on the closed strip, holomorphic on `0 < re z < 1`, of at most linear growth
`‖G z‖ ≤ K * (1 + |im z|)`, whose boundary increments on `re z = 0` and `re z = 1` have bounded
continuous difference quotients `q = (q₀, q₁)` in `(offDiag univ →ᵇ X₀) × (offDiag univ →ᵇ X₁)`.

Injectivity of `X₀, X₁ → X₀ + X₁` makes `q` unique (`IsUpperStripFunction.trace_unique`); pinning
at `0` via `BoundedContinuousFunction.pinnedCurve` recovers Lipschitz boundary curves
(`IsUpperStripFunction.fstToSum_pinnedCurve`, `IsUpperStripFunction.sndToSum_pinnedCurve`), and
conversely Lipschitz boundary curves under finite-order strip growth yield an upper strip function
via `LipschitzWith.offDiagSlope` (`IsUpperStripFunction.of_lipschitz`). We prove Bergh–Löfström
Lemma 4.1.3: three-lines bounds on vertical increments
(`IsUpperStripFunction.norm_add_mul_I_sub_le_abs_mul_rpow_mul_rpow`) and complex derivatives
(`IsUpperStripFunction.norm_deriv_le_rpow_mul_rpow`), and `‖q‖`-Lipschitz continuity on the closed
strip (`IsUpperStripFunction.lipschitzOnWith`), determining `G` up to `G 0`
(`IsUpperStripFunction.eqOn_sub_apply_zero`).

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§5–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.1.
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2.4.
-/

public noncomputable section

open Asymptotics Bornology Complex Complex.HadamardThreeLines Filter Set Topology
open TauCeti.Complex.HadamardThreeLines
open scoped BoundedContinuousFunction NNReal

namespace TauCeti.CompatibleCouple

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

theorem zero : C.IsUpperStripFunction 0 0 :=
  ⟨diffContOnCl_const (c := 0), ⟨0, fun _ _ => by simp⟩, fun _ => by simp, fun _ => by simp⟩

/-- Any constant function into the sum space is an upper strip function with zero boundary
difference quotients. -/
theorem const (u : C.SumSpace) : C.IsUpperStripFunction (fun _ => u) 0 :=
  ⟨diffContOnCl_const, ⟨‖u‖, fun _ _ => (mul_one ‖u‖).symm.trans_le
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) (norm_nonneg _))⟩,
    fun _ => by simp, fun _ => by simp⟩

theorem add (hG : C.IsUpperStripFunction G q) (hH : C.IsUpperStripFunction H r) :
    C.IsUpperStripFunction (G + H) (q + r) where
  diffContOnCl := hG.diffContOnCl.add hH.diffContOnCl
  exists_norm_le := let ⟨K, hK⟩ := hG.exists_norm_le; let ⟨L, hL⟩ := hH.exists_norm_le
    ⟨K + L, fun z hz => ((norm_add_le _ _).trans (add_le_add (hK z hz) (hL z hz))).trans_eq
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
  exists_norm_le := let ⟨K, hK⟩ := hG.exists_norm_le; ⟨‖c‖ * K, fun z hz => by
    simpa [norm_smul, mul_assoc] using mul_le_mul_of_nonneg_left (hK z hz) (norm_nonneg c)⟩
  sub_mul_I h := by simp [← smul_sub, hG.sub_mul_I h, smul_comm c]
  sub_one_add_mul_I h := by simp [← smul_sub, hG.sub_one_add_mul_I h, smul_comm c]

theorem neg (hG : C.IsUpperStripFunction G q) : C.IsUpperStripFunction (-G) (-q) := by
  simpa using hG.const_smul (-1)

theorem sub (hG : C.IsUpperStripFunction G q) (hH : C.IsUpperStripFunction H r) :
    C.IsUpperStripFunction (G - H) (q - r) := by simpa [sub_eq_add_neg] using hG.add hH.neg

/-- Shifting an upper strip function by a constant in the sum space leaves its boundary difference
quotients unchanged. -/
theorem add_const (hG : C.IsUpperStripFunction G q) (u : C.SumSpace) :
    C.IsUpperStripFunction (fun z => G z + u) q := by simpa [Pi.add_def] using hG.add (const u)

theorem sub_const (hG : C.IsUpperStripFunction G q) (u : C.SumSpace) :
    C.IsUpperStripFunction (fun z => G z - u) q := by simpa [sub_eq_add_neg] using hG.add_const (-u)

/-- An upper strip function can be replaced by any function agreeing with it on the closed strip. -/
theorem congr {G' : ℂ → C.SumSpace} (hG : C.IsUpperStripFunction G q)
    (hEq : EqOn G G' (verticalClosedStrip 0 1)) : C.IsUpperStripFunction G' q where
  diffContOnCl := ⟨hG.diffContOnCl.differentiableOn.congr
      (hEq.symm.mono (verticalStrip_subset_verticalClosedStrip 0 1)),
    hG.diffContOnCl.continuousOn.congr (closure_verticalStrip zero_lt_one ▸ hEq.symm)⟩
  exists_norm_le := let ⟨K, hK⟩ := hG.exists_norm_le; ⟨K, fun z hz => hEq hz ▸ hK z hz⟩
  sub_mul_I hne := by rw [← hEq (by simp), ← hEq (by simp)]; exact hG.sub_mul_I hne
  sub_one_add_mul_I hne := by rw [← hEq (by simp), ← hEq (by simp)]; exact hG.sub_one_add_mul_I hne

/-- The boundary difference quotients `q` are uniquely determined by the upper strip function
`G`. -/
theorem trace_unique (hG : C.IsUpperStripFunction G q) (hG' : C.IsUpperStripFunction G r) : q = r :=
  Prod.ext
    (BoundedContinuousFunction.ext fun ⟨_, hp⟩ => C.fstToSum_injective <| smul_right_injective _
      (sub_ne_zero.2 <| mod_cast hp.2.2) ((hG.sub_mul_I hp.2.2).symm.trans (hG'.sub_mul_I hp.2.2)))
    (BoundedContinuousFunction.ext fun ⟨_, hp⟩ => C.sndToSum_injective <| smul_right_injective _
      (sub_ne_zero.2 <| mod_cast hp.2.2)
      ((hG.sub_one_add_mul_I hp.2.2).symm.trans (hG'.sub_one_add_mul_I hp.2.2)))

/-- An upper strip function is complex-differentiable at every point of the open strip. -/
theorem differentiableAt (hG : C.IsUpperStripFunction G q) {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    DifferentiableAt ℂ G z :=
  hG.diffContOnCl.differentiableOn.differentiableAt ((isOpen_verticalStrip 0 1).mem_nhds hz)

/-- An upper strip function has finite exponential order along the open strip. -/
theorem exists_isBigO_exp_rpow (hG : C.IsUpperStripFunction G q) :
    ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A) := by
  obtain ⟨K, hK⟩ := hG.exists_norm_le
  refine ⟨1, 2 * max K 0 + 1, IsBigO.of_norm_eventuallyLE ?_⟩
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop 1)).filter_mono
    inf_le_left, (eventually_mem_principal (verticalStrip 0 1)).filter_mono inf_le_right]
    with w hw1 hw
  have hGw : ‖G w‖ ≤ (2 * max K 0 + 1) * ‖w‖ :=
    (hK w (verticalStrip_subset_verticalClosedStrip 0 1 hw)).trans <|
      (mul_le_mul (le_max_left K 0) (by linarith [abs_im_le_norm w] : 1 + |w.im| ≤ 2 * ‖w‖)
        (by positivity) (le_max_right K 0)).trans (by nlinarith [le_max_right K 0])
  simpa [Real.rpow_one] using
    hGw.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))

/-! ### Pinned Lipschitz boundary curves -/

theorem fstToSum_pinnedCurve (hG : C.IsUpperStripFunction G q) (t : ℝ) :
    C.fstToSum (q.1.pinnedCurve t) = G (t * I) - G 0 := by
  rcases eq_or_ne t 0 with rfl | ht; · simp
  simpa [q.1.pinnedCurve_of_ne_zero ht, ← coe_smul] using (hG.sub_mul_I ht).symm

theorem sndToSum_pinnedCurve (hG : C.IsUpperStripFunction G q) (t : ℝ) :
    C.sndToSum (q.2.pinnedCurve t) = G (1 + t * I) - G 1 := by
  rcases eq_or_ne t 0 with rfl | ht; · simp
  simpa [q.2.pinnedCurve_of_ne_zero ht, ← coe_smul] using (hG.sub_one_add_mul_I ht).symm

theorem fstToSum_pinnedCurve_sub (hG : C.IsUpperStripFunction G q) (t s : ℝ) :
    C.fstToSum (q.1.pinnedCurve t - q.1.pinnedCurve s) = G (t * I) - G (s * I) := by
  rw [map_sub, hG.fstToSum_pinnedCurve, hG.fstToSum_pinnedCurve]; abel

theorem sndToSum_pinnedCurve_sub (hG : C.IsUpperStripFunction G q) (t s : ℝ) :
    C.sndToSum (q.2.pinnedCurve t - q.2.pinnedCurve s) = G (1 + t * I) - G (1 + s * I) := by
  rw [map_sub, hG.sndToSum_pinnedCurve, hG.sndToSum_pinnedCurve]; abel

theorem pinnedCurve_fst_sub_eq_smul (hG : C.IsUpperStripFunction G q) {t s : ℝ} (h : t ≠ s) :
    q.1.pinnedCurve t - q.1.pinnedCurve s = (t - s : ℂ) • q.1 ⟨(t, s), ⟨trivial, trivial, h⟩⟩ :=
  C.fstToSum_injective <| by rw [hG.fstToSum_pinnedCurve_sub, hG.sub_mul_I h, map_smul]

theorem pinnedCurve_snd_sub_eq_smul (hG : C.IsUpperStripFunction G q) {t s : ℝ} (h : t ≠ s) :
    q.2.pinnedCurve t - q.2.pinnedCurve s = (t - s : ℂ) • q.2 ⟨(t, s), ⟨trivial, trivial, h⟩⟩ :=
  C.sndToSum_injective <| by rw [hG.sndToSum_pinnedCurve_sub, hG.sub_one_add_mul_I h, map_smul]

/-- The left boundary curve `q.1.pinnedCurve` of an upper strip function is `‖q₀‖`-Lipschitz. -/
theorem lipschitzWith_pinnedCurve_fst (hG : C.IsUpperStripFunction G q) :
    LipschitzWith ‖q.1‖₊ q.1.pinnedCurve :=
  BoundedContinuousFunction.lipschitzWith_of_sub_eq_smul fun h => by
    simpa [← ofReal_sub, coe_smul] using hG.pinnedCurve_fst_sub_eq_smul h

/-- The right boundary curve `q.2.pinnedCurve` of an upper strip function is `‖q₁‖`-Lipschitz. -/
theorem lipschitzWith_pinnedCurve_snd (hG : C.IsUpperStripFunction G q) :
    LipschitzWith ‖q.2‖₊ q.2.pinnedCurve :=
  BoundedContinuousFunction.lipschitzWith_of_sub_eq_smul fun h => by
    simpa [← ofReal_sub, coe_smul] using hG.pinnedCurve_snd_sub_eq_smul h

theorem norm_pinnedCurve_fst_sub_le (hG : C.IsUpperStripFunction G q) (t s : ℝ) :
    ‖q.1.pinnedCurve t - q.1.pinnedCurve s‖ ≤ ‖q.1‖ * |t - s| := by
  simpa [dist_eq_norm, Real.dist_eq] using hG.lipschitzWith_pinnedCurve_fst.dist_le_mul t s

theorem norm_pinnedCurve_snd_sub_le (hG : C.IsUpperStripFunction G q) (t s : ℝ) :
    ‖q.2.pinnedCurve t - q.2.pinnedCurve s‖ ≤ ‖q.2‖ * |t - s| := by
  simpa [dist_eq_norm, Real.dist_eq] using hG.lipschitzWith_pinnedCurve_snd.dist_le_mul t s

/-! ### Bergh–Löfström Lemma 4.1.3: three-lines estimates on difference quotients and derivatives -/

private theorem norm_verticalDiffQuot_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : E →L[ℂ] C.SumSpace} (hι : ∀ x, ‖ι x‖ ≤ ‖x‖) {q₀ : offDiag (univ : Set ℝ) →ᵇ E} {c h : ℝ}
    (hh : h ≠ 0) (hc : ∀ {t s : ℝ} (hne : t ≠ s),
      G (c + t * I) - G (c + s * I) = (t - s : ℂ) • ι (q₀ ⟨(t, s), ⟨trivial, trivial, hne⟩⟩))
    {w : ℂ} (hw : w.re = c) : ‖((h : ℂ) * I)⁻¹ • (G (w + h * I) - G w)‖ ≤ ‖q₀‖ := by
  have hwc : w = c + w.im * I := by nth_rw 1 [← re_add_im w]; simp [hw]
  have hwh : w + h * I = c + ((w.im + h : ℝ) : ℂ) * I := by nth_rw 1 [hwc]; push_cast; ring
  have hne : w.im + h ≠ w.im := by simpa using hh
  have hdiff : G (w + h * I) - G w =
      (((w.im + h : ℝ) : ℂ) - w.im) • ι (q₀ ⟨(w.im + h, w.im), ⟨trivial, trivial, hne⟩⟩) := by
    nth_rw 2 [hwc]; rw [hwh, hc hne]
  have hsub : ‖((w.im + h : ℝ) : ℂ) - w.im‖ = ‖(h : ℂ)‖ := by congr 1; push_cast; ring
  simp only [hdiff, norm_smul, norm_inv, norm_mul, norm_I, mul_one, hsub,
    inv_mul_cancel_left₀ (norm_ne_zero_iff.2 (ofReal_ne_zero.2 hh))]
  exact (hι _).trans (q₀.norm_coe_le_norm _)

/-- Three-lines bound on vertical increments under finite-order strip growth. -/
private theorem norm_add_mul_I_sub_le_abs_mul_rpow_mul_rpow_of_isBigO
    (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hgrowth : ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A))
    (h₀ : ∀ {t s : ℝ} (h : t ≠ s),
      G (t * I) - G (s * I) = (t - s : ℂ) • C.fstToSum (q.1 ⟨(t, s), ⟨trivial, trivial, h⟩⟩))
    (h₁ : ∀ {t s : ℝ} (h : t ≠ s), G (1 + t * I) - G (1 + s * I) =
      (t - s : ℂ) • C.sndToSum (q.2 ⟨(t, s), ⟨trivial, trivial, h⟩⟩))
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) (h : ℝ) :
    ‖G (z + h * I) - G z‖ ≤ |h| * (‖q.1‖ ^ (1 - z.re) * ‖q.2‖ ^ z.re) := by
  rcases eq_or_ne h 0 with rfl | hh; · simp
  let D : ℂ → C.SumSpace := fun w => ((h : ℂ) * I)⁻¹ • (G (w + h * I) - G w)
  have hshift : Differentiable ℂ (fun w : ℂ => w + h * I) := by fun_prop
  have hdD : DiffContOnCl ℂ D (verticalStrip 0 1) :=
    ((hd.comp hshift.diffContOnCl fun w hw => by simpa using hw).sub hd).const_smul ((h : ℂ) * I)⁻¹
  obtain ⟨A₁, B₁, hg₁⟩ := hgrowth
  have hD : ‖D z‖ ≤ ‖q.1‖ ^ (1 - z.re) * ‖q.2‖ ^ z.re := by
    simpa [sub_zero, div_one] using TauCeti.PhragmenLindelof.norm_le_interp_of_isBigO_exp_rpow
      zero_lt_one hdD ⟨_, _, (TauCeti.PhragmenLindelof.isBigO_add_mul_I_sub_exp_rpow h
        hg₁).const_smul_left (((h : ℂ) * I)⁻¹)⟩
      (fun _ hw => norm_verticalDiffQuot_le C.norm_fstToSum_le hh (fun hne => by simpa using h₀ hne)
        hw)
      (fun _ hw => norm_verticalDiffQuot_le C.norm_sndToSum_le hh (fun hne => by simpa using h₁ hne)
        hw) hz
  simpa [D, norm_smul, Real.norm_eq_abs, mul_inv_cancel_left₀ (abs_ne_zero.2 hh)] using
    mul_le_mul_of_nonneg_left hD (abs_nonneg h)

/-- Finite-order growth on the open strip, combined with bounded boundary difference quotients,
automatically upgrades to linear growth on the closed strip. -/
theorem of_isBigO_exp_rpow (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hgrowth : ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A))
    (h₀ : ∀ {t s : ℝ} (h : t ≠ s),
      G (t * I) - G (s * I) = (t - s : ℂ) • C.fstToSum (q.1 ⟨(t, s), ⟨trivial, trivial, h⟩⟩))
    (h₁ : ∀ {t s : ℝ} (h : t ≠ s), G (1 + t * I) - G (1 + s * I) =
      (t - s : ℂ) • C.sndToSum (q.2 ⟨(t, s), ⟨trivial, trivial, h⟩⟩)) :
    C.IsUpperStripFunction G q where
  diffContOnCl := hd
  exists_norm_le := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hd.continuousOn_verticalClosedStrip zero_lt_one).comp continuous_ofReal.continuousOn
        fun x (hx : x ∈ Icc 0 1) => by simpa using hx)
    refine ⟨max M 0 + ‖q‖, fun z hz => ?_⟩
    have hz_re : (z.re : ℂ) ∈ verticalClosedStrip 0 1 := by simpa using hz
    have h1 := norm_add_mul_I_sub_le_abs_mul_rpow_mul_rpow_of_isBigO hd hgrowth h₀ h₁ hz_re z.im
    rw [re_add_im] at h1
    have hvert := h1.trans (mul_le_mul_of_nonneg_left (q.norm_fst_rpow_mul_norm_snd_rpow_le hz_re)
      (abs_nonneg _))
    have hGzre : ‖G z.re‖ ≤ max M 0 := (hM z.re hz).trans (le_max_left M 0)
    nlinarith [norm_sub_norm_le (G z) (G z.re), abs_nonneg z.im, norm_nonneg q, le_max_right M 0]
  sub_mul_I := h₀
  sub_one_add_mul_I := h₁

/-- **Bergh–Löfström Lemma 4.1.3 (difference quotients).** Vertical increments of an upper strip
function satisfy the three-lines estimate
`‖G (z + h * I) - G z‖ ≤ |h| * ‖q₀‖ ^ (1 - re z) * ‖q₁‖ ^ re z` across the closed strip. -/
theorem norm_add_mul_I_sub_le_abs_mul_rpow_mul_rpow (hG : C.IsUpperStripFunction G q) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (h : ℝ) :
    ‖G (z + h * I) - G z‖ ≤ |h| * (‖q.1‖ ^ (1 - z.re) * ‖q.2‖ ^ z.re) :=
  norm_add_mul_I_sub_le_abs_mul_rpow_mul_rpow_of_isBigO hG.diffContOnCl hG.exists_isBigO_exp_rpow
    hG.sub_mul_I hG.sub_one_add_mul_I hz h

/-- **Bergh–Löfström Lemma 4.1.3 (three-lines derivative bound).** On the open strip `0 < re z < 1`,
the complex derivative of an upper strip function satisfies
`‖deriv G z‖ ≤ ‖q₀‖ ^ (1 - re z) * ‖q₁‖ ^ re z`. -/
theorem norm_deriv_le_rpow_mul_rpow (hG : C.IsUpperStripFunction G q) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) : ‖deriv G z‖ ≤ ‖q.1‖ ^ (1 - z.re) * ‖q.2‖ ^ z.re := by
  have hGz : HasDerivAt G (deriv G z) (z + ((0 : ℝ) : ℂ) * I) := by
    simpa using (hG.differentiableAt hz).hasDerivAt
  have hφ : HasDerivAt (fun h : ℝ => z + (h : ℂ) * I) I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add z
  refine (hGz.scomp (0 : ℝ) hφ).le_of_lip' (by positivity) (.of_forall fun h => ?_)
    |>.trans_eq' (by simp [norm_smul])
  simpa [Real.norm_eq_abs, mul_comm] using
    hG.norm_add_mul_I_sub_le_abs_mul_rpow_mul_rpow (verticalStrip_subset_verticalClosedStrip 0 1 hz)
      h

theorem norm_deriv_le (hG : C.IsUpperStripFunction G q) {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    ‖deriv G z‖ ≤ ‖q‖ :=
  (hG.norm_deriv_le_rpow_mul_rpow hz).trans
    (q.norm_fst_rpow_mul_norm_snd_rpow_le (verticalStrip_subset_verticalClosedStrip 0 1 hz))

/-- **Bergh–Löfström Lemma 4.1.3 (strip Lipschitz bound).** Every upper strip function with
boundary difference quotients `q` is `‖q‖`-Lipschitz on the entire closed strip `0 ≤ re z ≤ 1`. -/
theorem lipschitzOnWith (hG : C.IsUpperStripFunction G q) :
    LipschitzOnWith ‖q‖₊ G (verticalClosedStrip 0 1) :=
  closure_verticalStrip zero_lt_one ▸
    ((convex_verticalStrip 0 1).lipschitzOnWith_of_nnNorm_deriv_le
      (fun _ hz => hG.differentiableAt hz) fun _ hz =>
        mod_cast hG.norm_deriv_le hz).closure hG.diffContOnCl.continuousOn

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
    rw [eq_add_of_sub_eq (hG.eqOn_sub_apply_zero hH
      (verticalStrip_subset_verticalClosedStrip 0 1 hw)), sub_add_eq_add_sub, add_sub_assoc]
  rw [heq.deriv_eq, deriv_add_const]

/-- Construct `IsUpperStripFunction` from Lipschitz boundary curves `g₀ : ℝ → X₀`, `g₁ : ℝ → X₁`
representing the boundary increments of `G` in `X₀ + X₁`, under finite-order strip growth. -/
theorem of_lipschitz (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hgrowth : ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A))
    {g₀ : ℝ → X₀} {g₁ : ℝ → X₁} {K₀ K₁ : ℝ≥0}
    (hg₀ : LipschitzWith K₀ g₀) (hg₁ : LipschitzWith K₁ g₁)
    (h₀ : ∀ t s : ℝ, G (t * I) - G (s * I) = C.fstToSum (g₀ t - g₀ s))
    (h₁ : ∀ t s : ℝ, G (1 + t * I) - G (1 + s * I) = C.sndToSum (g₁ t - g₁ s)) :
    C.IsUpperStripFunction G (hg₀.offDiagSlope, hg₁.offDiagSlope) :=
  of_isBigO_exp_rpow hd hgrowth
    (fun h => by rw [h₀ _ _, ← ofReal_sub, ← map_smul, coe_smul, hg₀.smul_offDiagSlope_apply h])
    (fun h => by rw [h₁ _ _, ← ofReal_sub, ← map_smul, coe_smul, hg₁.smul_offDiagSlope_apply h])

end IsUpperStripFunction

end TauCeti.CompatibleCouple
