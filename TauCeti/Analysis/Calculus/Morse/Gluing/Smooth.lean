/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Gluing.Compactification
import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Smooth gluing through a split hyperbolic box

For smooth entrance and exit graphs, the equation `w = k (r • g (r • w))` has a smooth
branch across `r = 0`, with `w 0 = k 0`. The derivative in `w` of its residual is the
identity there. The Banach implicit function theorem therefore also proves local
exhaustiveness: every solution near `(0, k 0)` belongs to this branch.

The entrance and exit pairs of this branch are smooth through the broken pair. The
expanding entrance coordinate has derivative `k 0`, so the parameter is nondegenerate
when the broken exit is nonzero. These are local assertions in the split box; no global
trajectory compactification or compatibility between corner charts is asserted.

The central analytic input is Mathlib's `ContDiffAt.implicitFunction`, together with
`ContDiffOn.exists_isOpen_contDiffOn_implicitFunction` for one common smooth neighbourhood.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing with a pseudo-gradient linear near critical points).
-/

public section

open Filter Function Metric Set
open scoped ContDiff Topology NNReal

namespace TauCeti

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ] [CompleteSpace Eᵤ]
  {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} {s : Set Eᵤ} {t : Set Eₛ} {n : ℕ∞ω}

/-- Smooth local solutions of the split-box matching equation, including all solutions
near the broken exit coordinate. Smoothness holds on one open neighbourhood, also at
infinite regularity. Only the expanding factor needs to be complete. -/
theorem exists_contDiffOn_splitGluing_fixedPoint
    (hg : ContDiffOn ℝ n g s) (hs : IsOpen s) (hₛ : (0 : Eᵤ) ∈ s)
    (hk : ContDiffOn ℝ n k t) (ht : IsOpen t) (hₜ : (0 : Eₛ) ∈ t) (hn : n ≠ 0) :
    ∃ (U : Set ℝ) (w : ℝ → Eᵤ), IsOpen U ∧ 0 ∈ U ∧ ContDiffOn ℝ n w U ∧
      w 0 = k 0 ∧ (∀ r ∈ U, k (r • g (r • w r)) = w r) ∧
      (∀ᶠ q : ℝ × Eᵤ in 𝓝 (0, k 0),
        k (q.1 • g (q.1 • q.2)) = q.2 ↔ w q.1 = q.2) := by
  let a : ℝ × Eᵤ → Eᵤ := fun q ↦ q.1 • q.2
  let b : ℝ × Eᵤ → Eₛ := fun q ↦ q.1 • g (a q)
  let D : Set (ℝ × Eᵤ) := a ⁻¹' s ∩ b ⁻¹' t
  let F : ℝ × Eᵤ → Eᵤ := fun q ↦ q.2 - k (b q)
  have ha : ContDiff ℝ n a := contDiff_fst.smul contDiff_snd
  have hb : ContDiffOn ℝ n b (a ⁻¹' s) :=
    contDiffOn_fst.smul (hg.comp ha.contDiffOn fun _ hq ↦ hq)
  have hD : IsOpen D := hb.continuousOn.isOpen_inter_preimage
    (hs.preimage ha.continuous) ht
  have hbase : (0, k 0) ∈ D := by simp [D, a, b, hₛ, hₜ]
  have hF : ContDiffOn ℝ n F D := contDiffOn_snd.sub
    (hk.comp (hb.mono inter_subset_left) fun _ hq ↦ hq.2)
  have hF₀ : ContDiffAt ℝ n F (0, k 0) := hF.contDiffAt (hD.mem_nhds hbase)
  have hg₀ := (hg.contDiffAt (hs.mem_nhds hₛ)).differentiableAt hn
  have hk₀ := (hk.contDiffAt (ht.mem_nhds hₜ)).differentiableAt hn
  -- At the broken parameter, both scalar factors kill the spatial derivative.
  have ha₀ : HasFDerivAt a
      ((ContinuousLinearMap.fst ℝ ℝ Eᵤ).smulRight (k 0)) (0, k 0) := by
    convert (hasFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ), k 0))).smul
      (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ), k 0))) using 1; simp
  have hga₀ : HasFDerivAt (fun q ↦ g (a q))
      ((fderiv ℝ g 0).comp ((ContinuousLinearMap.fst ℝ ℝ Eᵤ).smulRight (k 0)))
      (0, k 0) := by
    exact (by simpa [a] using hg₀.hasFDerivAt :
      HasFDerivAt g (fderiv ℝ g 0) (a (0, k 0))).comp (0, k 0) ha₀
  have hb₀ : HasFDerivAt b
      ((ContinuousLinearMap.fst ℝ ℝ Eᵤ).smulRight (g 0)) (0, k 0) := by
    convert (hasFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ), k 0))).smul hga₀ using 1; simp [a]
  have hFderiv : HasFDerivAt F
      (ContinuousLinearMap.snd ℝ ℝ Eᵤ - (fderiv ℝ k 0).comp
        ((ContinuousLinearMap.fst ℝ ℝ Eᵤ).smulRight (g 0))) (0, k 0) := by
    convert (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ), k 0))).sub
      ((by simpa [b] using hk₀.hasFDerivAt :
        HasFDerivAt k (fderiv ℝ k 0) (b (0, k 0))).comp (0, k 0) hb₀) using 1
    rfl
  have hvertical : (fderiv ℝ F (0, k 0)).comp (ContinuousLinearMap.inr ℝ ℝ Eᵤ) =
      ContinuousLinearMap.id ℝ Eᵤ := by
    rw [hFderiv.fderiv]
    ext v
    simp
  have hinv : ((fderiv ℝ F (0, k 0)).comp
      (ContinuousLinearMap.inr ℝ ℝ Eᵤ)).IsInvertible := by
    rw [hvertical]
    exact ⟨ContinuousLinearEquiv.refl ℝ Eᵤ, rfl⟩
  -- Extract one smooth neighbourhood, then restrict it to the matching-equation germ.
  let w := hF₀.implicitFunction hn hinv
  obtain ⟨V, hV, hV₀, hwV⟩ :=
    hF.exists_isOpen_contDiffOn_implicitFunction hD hbase hn hinv
  have hw₀ : w 0 = k 0 := hF₀.implicitFunction_apply_self hn hinv
  have hfixed : ∀ᶠ r in 𝓝 (0 : ℝ), k (r • g (r • w r)) = w r := by
    apply Eventually.mono (hF₀.eventually_apply_implicitFunction hn hinv)
    intro r hr
    exact (sub_eq_zero.mp (by simpa [F, b, a] using hr)).symm
  obtain ⟨W, hWsub, hW, hW₀⟩ := _root_.mem_nhds_iff.mp hfixed
  refine ⟨V ∩ W, w, hV.inter hW, ⟨hV₀, hW₀⟩, hwV.mono inter_subset_left, hw₀,
    fun r hr ↦ hWsub hr.2, ?_⟩
  simpa only [F, b, a, zero_smul, sub_self, sub_eq_zero, eq_comm] using
    hF₀.eventually_apply_eq_iff_implicitFunction hn hinv

variable {ε r₀ : ℝ} {Kg Kk : ℝ≥0}

/-- The exhaustive Lipschitz split-box gluing family has a smooth extension through its
broken endpoint. On a smaller positive parameter interval its entrance/exit pairs are
exactly `splitGluingPairs`. The extension is smooth on an open neighbourhood of zero,
and its expanding entrance coordinate has the nonzero derivative `k 0`.

The local smoothness assumptions concern the graph maps near zero; the Lipschitz and
sphere assumptions are those of the existing exhaustive split-passage construction. -/
theorem exists_contDiffOn_splitGluingPairs
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε)
    (hε : 0 < ε) (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1)
    (hgs : ContDiffOn ℝ n g s) (hs : IsOpen s) (hₛ : (0 : Eᵤ) ∈ s)
    (hkt : ContDiffOn ℝ n k t) (ht : IsOpen t) (hₜ : (0 : Eₛ) ∈ t) (hn : n ≠ 0) :
    ∃ (U : Set ℝ) (δ : ℝ) (w : ℝ → Eᵤ),
      IsOpen U ∧ 0 ∈ U ∧ 0 < δ ∧ δ ≤ r₀ ∧ Icc 0 δ ⊆ U ∧
      ContDiffOn ℝ n w U ∧ w 0 = k 0 ∧
      ContDiffOn ℝ n (fun r ↦
        (WithLp.toLp 2 (g (r • w r), r • w r),
          WithLp.toLp 2 (r • g (r • w r), w r))) U ∧
      (fun r ↦ (WithLp.toLp 2 (g (r • w r), r • w r),
        WithLp.toLp 2 (r • g (r • w r), w r))) '' Ioc 0 δ = splitGluingPairs ε δ g k ∧
      (∀ᶠ q : ℝ × Eᵤ in 𝓝 (0, k 0),
        k (q.1 • g (q.1 • q.2)) = q.2 ↔ w q.1 = q.2) ∧
      HasDerivAt (fun r ↦ r • w r) (k 0) 0 ∧ k 0 ≠ 0 := by
  obtain ⟨V, v, hV, hV₀, hv, hv₀, -, hunique⟩ :=
    exists_contDiffOn_splitGluing_fixedPoint hgs hs hₛ hkt ht hₜ hn
  obtain ⟨w, hw, hw₀, hwnorm, hwfixed, himage⟩ :=
    exists_setOf_mem_splitPassage_source_graph_eq_image hg hgε hk hkε hε hr₀₁ hK
  -- The old exhaustive family converges to the same base point, so local IFT uniqueness
  -- identifies it with the smooth branch for small nonnegative parameters.
  have hwtend : Tendsto (fun r ↦ (r, w r)) (𝓝[Icc 0 r₀] 0) (𝓝 (0, k 0)) := by
    simpa only [hw₀, id_eq] using continuousWithinAt_id.tendsto.prodMk_nhds
      (hw.continuousOn.continuousWithinAt (left_mem_Icc.mpr hr₀.le)).tendsto
  have heq : ∀ᶠ r in 𝓝[Icc 0 r₀] 0, w r = v r := by
    filter_upwards [hwtend.eventually hunique, self_mem_nhdsWithin] with r hr hrr
    exact ((hr.mp (hwfixed r hrr))).symm
  obtain ⟨W, hW, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp heq
  -- Shrink the open smooth neighbourhood so that the entrance graph is evaluated in `s`.
  let U : Set ℝ := V ∩ (fun r ↦ r • v r) ⁻¹' s
  have hvscale : ContDiffOn ℝ n (fun r ↦ r • v r) V := contDiffOn_id.smul hv
  have hU : IsOpen U := hvscale.continuousOn.isOpen_inter_preimage hV hs
  have hU₀ : 0 ∈ U := by simp [U, hV₀, hₛ]
  have hUv : ContDiffOn ℝ n v U := hv.mono inter_subset_left
  have hUscale : ContDiffOn ℝ n (fun r ↦ r • v r) U := hvscale.mono inter_subset_left
  have hUg : ContDiffOn ℝ n (fun r ↦ g (r • v r)) U :=
    hgs.comp hUscale fun _ hr ↦ hr.2
  let F : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ) := fun r ↦
    (WithLp.toLp 2 (g (r • v r), r • v r), WithLp.toLp 2 (r • g (r • v r), v r))
  have hF : ContDiffOn ℝ n F U :=
    (WithLp.contDiff_toLp.comp_contDiffOn (hUg.prodMk hUscale)).prodMk
      (WithLp.contDiff_toLp.comp_contDiffOn ((contDiffOn_id.smul hUg).prodMk hUv))
  obtain ⟨d, hd, hdsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hU₀) hW)
  let δ := min r₀ (d / 2)
  have hδ : 0 < δ := lt_min hr₀ (half_pos hd)
  have hδr : δ ≤ r₀ := min_le_left _ _
  have hsmall {r : ℝ} (hr : r ∈ Icc 0 δ) : r ∈ U ∩ W := by
    apply hdsub
    rw [mem_ball, dist_zero_right, Real.norm_of_nonneg hr.1]
    exact hr.2.trans_lt ((min_le_right r₀ (d / 2)).trans_lt (half_lt_self hd))
  have heqδ {r : ℝ} (hr : r ∈ Icc 0 δ) : w r = v r :=
    hWsub ⟨(hsmall hr).2, ⟨hr.1, hr.2.trans hδr⟩⟩
  have hvnorm {r : ℝ} (hr : r ∈ Icc 0 δ) : ‖v r‖ = ε := by
    rw [← heqδ hr]
    exact hwnorm r ⟨hr.1, hr.2.trans hδr⟩
  have hpass {r : ℝ} (hr : r ∈ Ioc 0 δ) :
      (F r).2 = splitPassage ε (F r).1 :=
    (splitPassage_toLp_smul (g (r • v r)) (hvnorm (Ioc_subset_Icc_self hr)) hε hr.1).symm
  have hentry {r : ℝ} (hr : r ∈ Ioc 0 δ) :
      (F r).1 ∈ {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧
        z.fst = g z.snd ∧ (splitPassage ε z).snd = k (splitPassage ε z).fst} := by
    rw [himage]
    exact ⟨r, ⟨hr.1, hr.2.trans hδr⟩, by simp only [F, heqδ (Ioc_subset_Icc_self hr)]⟩
  have himageδ : F '' Ioc 0 δ = splitGluingPairs ε δ g k := by
    ext p
    rw [mem_splitGluingPairs]
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hrentry := hentry hr
      refine ⟨hrentry.1, ?_, hrentry.2.2.1, hpass hr, ?_⟩
      · simp only [F, WithLp.toLp_snd, norm_smul, Real.norm_of_nonneg hr.1.le,
          hvnorm (Ioc_subset_Icc_self hr)]
        exact mul_le_mul_of_nonneg_right hr.2 hε.le
      · rw [hpass hr]
        exact hrentry.2.2.2
    · rintro ⟨hsrc, hbound, hgraph, hexit, hkgraph⟩
      have hentry' : p.1 ∈ {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧
          z.fst = g z.snd ∧ (splitPassage ε z).snd = k (splitPassage ε z).fst} :=
        ⟨hsrc, hbound.trans (mul_le_mul_of_nonneg_right hδr hε.le), hgraph,
          by rwa [← hexit]⟩
      rw [himage] at hentry'
      obtain ⟨r, hr, hre⟩ := hentry'
      have hnormr : r * ε = ‖p.1.snd‖ := by
        simpa only [WithLp.toLp_snd, norm_smul, Real.norm_of_nonneg hr.1.le,
          hwnorm r (Ioc_subset_Icc_self hr)] using congrArg (fun z ↦ ‖z.snd‖) hre
      have hrδ : r ∈ Ioc 0 δ := ⟨hr.1, (mul_le_mul_iff_left₀ hε).mp
        (by simpa only [mul_comm ε] using hnormr.trans_le hbound)⟩
      have hFe : (F r).1 = p.1 := by
        simpa only [F, heqδ (Ioc_subset_Icc_self hrδ)] using hre
      refine ⟨r, hrδ, Prod.ext hFe ?_⟩
      rw [hpass hrδ, hFe, ← hexit]
  have hderiv : HasDerivAt (fun r ↦ r • v r) (k 0) 0 := by
    convert (hasDerivAt_id (0 : ℝ)).smul
      ((hUv.contDiffAt (hU.mem_nhds hU₀)).differentiableAt hn).hasDerivAt using 1 <;>
      first | rfl | simp [hv₀]
  have hk₀norm : ‖k 0‖ = ε := hkε 0 (mem_closedBall_zero_iff.mpr
    (by simpa using mul_nonneg hr₀.le hε.le))
  exact ⟨U, δ, v, hU, hU₀, hδ, hδr, fun _ hr ↦ (hsmall hr).1,
    hUv, hv₀, hF, himageδ, hunique, hderiv, norm_pos_iff.mp (hk₀norm.symm ▸ hε)⟩

end TauCeti
