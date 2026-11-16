/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Morse.CWModel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Puncture
import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
import TauCeti.Geometry.Manifold.Morse.Generic.Relative

/-!
# Finite CW type of a compact smooth manifold with finitely many points removed

Deleting a finite set `S` from a compact boundaryless smooth manifold `M` leaves an open manifold
`M \ S` of finite CW type (`Set.Finite.finiteCWType_compl_of_isManifold`). No connectedness,
dimension, or triangulation hypothesis is needed. Together with the finite CW type of `M` itself
(`TauCeti.FiniteCWType.of_isManifold`) and the Mayer--Vietoris puncture formula
(`TauCeti.eulerChar_compl_of_finite`), this computes the cellular Euler characteristic
`χ(M \ S) = χ(M) - (-1) ^ dim M · #S` (`Set.Finite.eulerChar_compl_of_isManifold`).

## Proof outline

First equip the model space with a Euclidean inner product via
`ModelWithCorners.transContinuousLinearEquiv`. Choose pairwise disjoint open neighbourhoods `W p`
of the points `p ∈ S` and smooth bump functions `b p` supported in `W p`. Multiplying `b p` by
`(b p).rIn ^ 2 * (‖extChartAt I p · - extChartAt I p p‖ ^ 2)⁻¹` produces a nonnegative function on
`M` that is smooth away from `p`, tends to `+∞` at `p`, and has nonzero derivative wherever its
value exceeds `1` (where `b p` is locally `1` and the coordinate expression is radial reciprocal
squared norm).

Summing these poles over `p ∈ S` and restricting to `U = Sᶜ` gives a smooth nonnegative function
`F₀ : C^∞(U, ℝ)` whose sublevels `{F₀ ≤ B}` are closed away from `S` in compact `M`, hence compact
in `U`, and which has no critical points on `{1 < F₀}`. Relative compact Morse approximation
(`ContMDiffMap.exists_isMorseOn_hasCompactSupport_sub_compl`) perturbs `F₀` by a compactly
supported function on `{F₀ < 2}` to a smooth function `g` that is Morse on `{F₀ ≤ 4}` and agrees
with `F₀` on `{2 < F₀}`. Then `g` is globally Morse on `U`, proper, bounded below, and has
critical points only inside the compact set `{F₀ ≤ 4}`, hence finitely many; the proper Morse CW
model (`TauCeti.IsMorse.finiteCWType_of_isProperMap`) concludes.

## Main results

* `Set.Finite.finiteCWType_compl_of_isManifold`: the complement of a finite set in a compact
  boundaryless smooth manifold has finite CW type.
* `Set.Finite.eulerChar_compl_of_isManifold`: `χ(M \ S) = χ(M) - (-1) ^ dim M · #S` for a finite
  subset `S` of a compact boundaryless smooth manifold `M`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5.
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 6, Section 1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
-/

public section

noncomputable section

open Filter Function Metric Module Set Topology TauCeti
open TopologicalSpace (Opens)
open scoped ContDiff Manifold RealInnerProductSpace

universe u v w

namespace TauCeti

section InnerProductModel

variable {V : Type v} {H : Type w} {M : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Local reciprocal-squared-norm pole at `c`, cut off by a smooth bump function `b` at `c` and
normalised by `b.rIn ^ 2` so that `b` is identically `1` wherever the pole exceeds `1`. -/
private def puncturePole {c : M} (b : SmoothBumpFunction I c) (x : M) : ℝ :=
  b x * (b.rIn ^ 2 * (‖extChartAt I c x - extChartAt I c c‖ ^ 2)⁻¹)

private lemma puncturePole_nonneg {c : M} (b : SmoothBumpFunction I c) (x : M) :
    0 ≤ puncturePole b x :=
  mul_nonneg b.nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (sq_nonneg _)))

private lemma tsupport_puncturePole_subset {c : M} (b : SmoothBumpFunction I c) :
    tsupport (puncturePole b) ⊆ tsupport b :=
  tsupport_mul_subset_left

private lemma contMDiffAt_puncturePole [IsManifold I ∞ M] [T2Space M] {c x : M}
    (b : SmoothBumpFunction I c) (hxc : x ≠ c) :
    ContMDiffAt I 𝓘(ℝ) ∞ (puncturePole b) x := by
  by_cases hx : x ∈ tsupport b
  · have hsrc : x ∈ (extChartAt I c).source := b.tsupport_subset_extChartAt_source hx
    have hne : ‖extChartAt I c x - extChartAt I c c‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 <| norm_ne_zero_iff.2 <| sub_ne_zero.2 fun heq ↦
        hxc ((extChartAt I c).injOn hsrc (mem_extChartAt_source c) heq)
    have hcoord : ContDiffAt ℝ ∞
        (fun z : V ↦ b.rIn ^ 2 * (‖z - extChartAt I c c‖ ^ 2)⁻¹) (extChartAt I c x) :=
      contDiffAt_const.mul (((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ).inv hne)
    exact b.contMDiffAt.mul (hcoord.contMDiffAt.comp x
      (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc)))
  · exact contMDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (tsupport_puncturePole_subset b h))

omit [FiniteDimensional ℝ V] in
private lemma mem_criticalPoints_congr [I.Boundaryless] {f₁ f₂ : M → ℝ} {x : M}
    (h : f₁ =ᶠ[𝓝 x] f₂) :
    x ∈ criticalPoints I f₁ ↔ x ∈ criticalPoints I f₂ := by
  have htend : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    simpa only [extChartAt_to_inv] using (continuousAt_extChartAt_symm (I := I) x).tendsto
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    (h.comp_tendsto htend).fderiv_eq]

/-- Wherever `puncturePole b x > 1`, the point `x` lies inside the inner radius `b.rIn` of `b`, so
in the extended chart at `c` the pole agrees locally with `z ↦ b.rIn ^ 2 * (‖z - e c‖ ^ 2)⁻¹`. -/
private lemma eventuallyEq_puncturePole_comp_extChartAt_symm [I.Boundaryless] {c x : M}
    (b : SmoothBumpFunction I c) (h1 : 1 < puncturePole b x) :
    x ∈ (extChartAt I c).source ∧ extChartAt I c x - extChartAt I c c ≠ 0 ∧
      puncturePole b ∘ (extChartAt I c).symm =ᶠ[𝓝 (extChartAt I c x)]
        fun z : V ↦ b.rIn ^ 2 * (‖z - extChartAt I c c‖ ^ 2)⁻¹ := by
  have hb0 : b x ≠ 0 := fun hb0 ↦ by
    rw [puncturePole, hb0, zero_mul] at h1
    linarith
  have hsrc : x ∈ (chartAt H c).source := b.support_subset_source (mem_support.2 hb0)
  have hsrc' : x ∈ (extChartAt I c).source := by rwa [extChartAt_source]
  have hne : extChartAt I c x - extChartAt I c c ≠ 0 := fun h0 ↦ by
    rw [puncturePole, h0] at h1
    norm_num at h1
  have hdist : dist (extChartAt I c x) (extChartAt I c c) < b.rIn := by
    by_contra! hle
    rw [dist_eq_norm] at hle
    have hsq_pos : 0 < ‖extChartAt I c x - extChartAt I c c‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.2 hne)
    have hinv : b.rIn ^ 2 * (‖extChartAt I c x - extChartAt I c c‖ ^ 2)⁻¹ ≤ 1 :=
      (div_le_one hsq_pos).2 (pow_le_pow_left₀ b.rIn_pos.le hle 2)
    have hle1 : puncturePole b x ≤ 1 :=
      (mul_le_mul b.le_one hinv (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hsq_pos.le))
        zero_le_one).trans_eq (one_mul 1)
    linarith
  have hz₀ : extChartAt I c x ∈ (extChartAt I c).target := (extChartAt I c).map_source hsrc'
  have htend : Tendsto (extChartAt I c).symm (𝓝 (extChartAt I c x)) (𝓝 x) := by
    simpa only [(extChartAt I c).left_inv hsrc'] using
      ((continuousOn_extChartAt_symm c).continuousAt (extChartAt_target_mem_nhds' hz₀)).tendsto
  refine ⟨hsrc', hne, ?_⟩
  filter_upwards [htend.eventually (b.eventuallyEq_one_of_dist_lt hsrc hdist),
    extChartAt_target_mem_nhds' hz₀] with z hbz hzt
  have hbz1 : b ((extChartAt I c).symm z) = 1 := hbz
  rw [Function.comp_apply, puncturePole, hbz1, (extChartAt I c).right_inv hzt, one_mul]

/-- `puncturePole b` has no critical points where its value exceeds `1`. -/
private lemma notMem_criticalPoints_puncturePole [I.Boundaryless] [IsManifold I ∞ M] {c x : M}
    (b : SmoothBumpFunction I c) (h1 : 1 < puncturePole b x) :
    x ∉ criticalPoints I (puncturePole b) := by
  obtain ⟨hsrc, hne, hev⟩ := eventuallyEq_puncturePole_comp_extChartAt_symm b h1
  set z₀ := extChartAt I c x
  set u₀ := z₀ - extChartAt I c c
  have hsq_pos : 0 < ‖u₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 hne)
  have hsq : HasFDerivAt (fun z : V ↦ ‖z - extChartAt I c c‖ ^ 2)
      (2 • (innerSL ℝ u₀).comp (.id ℝ V)) z₀ :=
    ((hasFDerivAt_id z₀).sub_const (extChartAt I c c)).norm_sq
  have hq := ((hasDerivAt_inv hsq_pos.ne').const_mul (b.rIn ^ 2)).comp_hasFDerivAt z₀ hsq
  have hfderiv := hq.congr_of_eventuallyEq hev
  rw [mem_criticalPoints_iff_mfderiv_eq_zero,
    mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hsrc hfderiv.differentiableAt,
    hfderiv.fderiv]
  intro hzero
  have heval := congr($hzero u₀)
  simp only [smul_apply, ContinuousLinearMap.comp_id, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, zero_apply] at heval
  have hneg : b.rIn ^ 2 * -((‖u₀‖ ^ 2) ^ 2)⁻¹ * (2 * ‖u₀‖ ^ 2) < 0 :=
    mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (sq_pos_of_pos b.rIn_pos)
        (neg_neg_of_pos (inv_pos.2 (sq_pos_of_pos hsq_pos))))
      (by positivity)
  exact hneg.ne heval

/-- `puncturePole b` blows up to `+∞` on punctured neighbourhoods of `c`. -/
private lemma tendsto_puncturePole_nhdsNE {c : M} (b : SmoothBumpFunction I c) :
    Tendsto (puncturePole b) (𝓝[≠] c) atTop := by
  have hcont : ContinuousAt (fun x ↦ ‖extChartAt I c x - extChartAt I c c‖ ^ 2) c := by
    have h0 : ContinuousAt (fun z : V ↦ ‖z - extChartAt I c c‖ ^ 2) (extChartAt I c c) :=
      (((continuous_id.sub continuous_const).norm).pow 2).continuousAt
    exact h0.comp (continuousAt_extChartAt c)
  have hsq : Tendsto (fun x ↦ ‖extChartAt I c x - extChartAt I c c‖ ^ 2) (𝓝[≠] c) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) c),
      self_mem_nhdsWithin] with x hsrc hxc
    exact mem_Ioi.2 <| sq_pos_of_pos <| norm_pos_iff.2 <| sub_ne_zero.2 fun heq ↦
      hxc ((extChartAt I c).injOn hsrc (mem_extChartAt_source c) heq)
  have hinv : Tendsto (fun x ↦ b.rIn ^ 2 * (‖extChartAt I c x - extChartAt I c c‖ ^ 2)⁻¹)
      (𝓝[≠] c) atTop :=
    Tendsto.const_mul_atTop (sq_pos_of_pos b.rIn_pos) (tendsto_inv_nhdsGT_zero.comp hsq)
  refine hinv.congr' ?_
  filter_upwards [nhdsWithin_le_nhds b.eventuallyEq_one] with x hbx
  simp [puncturePole, hbx]

/-- Sum of isolated puncture poles over a finite set `S`. -/
private def punctureSum {S : Set M} [Fintype S] (b : ∀ p : S, SmoothBumpFunction I (p : M))
    (x : M) : ℝ :=
  ∑ p : S, puncturePole (b p) x

private lemma punctureSum_eventuallyEq {S : Set M} [Fintype S] {W : M → Set M}
    (hWo : ∀ p, IsOpen (W p)) (hWd : S.Pairwise (Disjoint on W))
    {b : ∀ p : S, SmoothBumpFunction I (p : M)} (hbW : ∀ p : S, tsupport (b p) ⊆ W p)
    (p : S) {x : M} (hx : x ∈ W p) :
    punctureSum b =ᶠ[𝓝 x] puncturePole (b p) := by
  filter_upwards [(hWo p.1).mem_nhds hx] with y hy
  rw [punctureSum, Finset.sum_eq_single p _ (by simp)]
  intro q _ hqp
  have hdisj : Disjoint (W p.1) (W q.1) := hWd p.2 q.2 (Subtype.coe_ne_coe.2 hqp.symm)
  have hyq : y ∉ tsupport (puncturePole (b q)) := fun hts ↦
    hdisj.le_bot ⟨hy, hbW q (tsupport_puncturePole_subset (b q) hts)⟩
  exact image_eq_zero_of_notMem_tsupport hyq

private lemma notMem_criticalPoints_punctureSum [I.Boundaryless] [IsManifold I ∞ M]
    {S : Set M} [Fintype S] {W : M → Set M}
    (hWo : ∀ p, IsOpen (W p)) (hWd : S.Pairwise (Disjoint on W))
    {b : ∀ p : S, SmoothBumpFunction I (p : M)} (hbW : ∀ p : S, tsupport (b p) ⊆ W p)
    {x : M} (h1 : 1 < punctureSum b x) : x ∉ criticalPoints I (punctureSum b) := by
  obtain ⟨p, -, hp0⟩ : ∃ p ∈ Finset.univ, 0 < puncturePole (b p) x := by
    by_contra! hle
    have : punctureSum b x ≤ 0 := Finset.sum_nonpos hle
    linarith
  have hxW : x ∈ W p :=
    hbW p (tsupport_puncturePole_subset (b p) (subset_tsupport _ (mem_support.2 hp0.ne')))
  have hev := punctureSum_eventuallyEq hWo hWd hbW p hxW
  rw [mem_criticalPoints_congr hev]
  exact notMem_criticalPoints_puncturePole (b p) (hev.eq_of_nhds ▸ h1)

private lemma isCompact_sublevel_punctureSum [T2Space M] [CompactSpace M] {S : Set M}
    (hS : S.Finite) [Fintype S] (b : ∀ p : S, SmoothBumpFunction I (p : M))
    (hcont : Continuous (punctureSum b ∘ Subtype.val :
      (⟨Sᶜ, hS.isClosed.isOpen_compl⟩ : Opens M) → ℝ)) (B : ℝ) :
    IsCompact {x : (⟨Sᶜ, hS.isClosed.isOpen_compl⟩ : Opens M) | punctureSum b x ≤ B} := by
  let U : Opens M := ⟨Sᶜ, hS.isClosed.isOpen_compl⟩
  have hnhds (p : S) : ∃ O : Set M, IsOpen O ∧ (p : M) ∈ O ∧
      ∀ y ∈ O, y ≠ (p : M) → B < puncturePole (b p) y := by
    obtain ⟨O, hO, hpO, hsub⟩ :=
      mem_nhdsWithin.1 ((tendsto_puncturePole_nhdsNE (b p)).eventually_gt_atTop B)
    exact ⟨O, hO, hpO, fun y hy hne ↦ hsub ⟨hy, hne⟩⟩
  choose O hOopen hpO hOB using hnhds
  have hSO : S ⊆ ⋃ p : S, O p := fun z hz ↦ mem_iUnion.2 ⟨⟨z, hz⟩, hpO ⟨z, hz⟩⟩
  have hK : IsCompact (Subtype.val ⁻¹' (⋃ p : S, O p)ᶜ : Set U) := by
    refine Topology.IsEmbedding.subtypeVal.isCompact_iff.2 ?_
    have himg : Subtype.val '' (Subtype.val ⁻¹' (⋃ p : S, O p)ᶜ : Set U) = (⋃ p : S, O p)ᶜ := by
      ext y
      simp only [mem_image, mem_preimage, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun ⟨_, hy⟩ ↦ hy, fun hy ↦ ⟨fun hyS ↦ hy (hSO hyS), hy⟩⟩
    rw [himg]
    exact (isOpen_iUnion hOopen).isClosed_compl.isCompact
  refine hK.of_isClosed_subset (isClosed_le hcont continuous_const) fun x hx hp ↦ ?_
  obtain ⟨p, hp'⟩ := mem_iUnion.1 hp
  have hlt : B < puncturePole (b p) x := hOB p x hp' fun h ↦ x.2 (h ▸ p.2)
  have hle : puncturePole (b p) x ≤ punctureSum b x :=
    Finset.single_le_sum (fun q _ ↦ puncturePole_nonneg (b q) x) (Finset.mem_univ p)
  exact hx.not_gt (hlt.trans_le hle)

/-- Compactly supported perturbation of a nonnegative function with compact sublevels remains
proper and bounded below. -/
private lemma isProperMap_and_bddBelow_of_hasCompactSupport_sub {X : Type u} [TopologicalSpace X]
    {f g : X → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_sub : ∀ B, IsCompact {x | f x ≤ B})
    (hf_cont : Continuous f) (hg_cont : Continuous g)
    (hgc : HasCompactSupport fun x ↦ g x - f x) :
    IsProperMap g ∧ BddBelow (range g) := by
  let d : X → ℝ := fun x ↦ g x - f x
  have hd_cont : Continuous d := hg_cont.sub hf_cont
  refine ⟨isProperMap_iff_isCompact_preimage.2 ⟨hg_cont, fun Q hQ ↦ ?_⟩, ?_⟩
  · obtain ⟨B, hB⟩ := hQ.bddAbove
    refine (hgc.union (hf_sub B)).of_isClosed_subset (hQ.isClosed.preimage hg_cont) fun x hx ↦ ?_
    by_cases hts : x ∈ tsupport d
    · exact Or.inl hts
    · have hzero : d x = 0 := image_eq_zero_of_notMem_tsupport hts
      exact Or.inr (hB (by simpa [sub_eq_zero.1 hzero] using hx))
  · obtain ⟨m, hm⟩ : BddBelow (range d) := by
      refine ((hgc.image hd_cont).union (isCompact_singleton (x := (0 : ℝ)))).bddBelow.mono ?_
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ tsupport d
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr (image_eq_zero_of_notMem_tsupport hx)
    refine ⟨m, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hmx : m ≤ g x - f x := hm (mem_range_self x)
    linarith [hf_nonneg x]

private theorem finiteCWType_compl_of_innerProductSpace [T2Space M] [CompactSpace M]
    (I : ModelWithCorners ℝ V H) [I.Boundaryless] [IsManifold I ∞ M] {S : Set M}
    (hS : S.Finite) : FiniteCWType ↥Sᶜ := by
  let := hS.fintype
  obtain ⟨W, hW, hWd⟩ := hS.t2_separation
  have hb (p : S) : ∃ b : SmoothBumpFunction I (p : M), tsupport b ⊆ W p := by
    obtain ⟨b, hbW, -⟩ :=
      (SmoothBumpFunction.nhds_basis_support (I := I)
        ((hW p).2.mem_nhds (hW p).1)).mem_iff.1 univ_mem
    exact ⟨b, hbW⟩
  choose b hbW using hb
  let U : Opens M := ⟨Sᶜ, hS.isClosed.isOpen_compl⟩
  let F₀ : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ :=
    ⟨punctureSum b ∘ Subtype.val, fun x ↦ ContMDiffAt.comp x
      (ContMDiffAt.sum fun p _ ↦ contMDiffAt_puncturePole (b p) fun h ↦ x.2 (h ▸ p.2))
      contMDiff_subtype_val.contMDiffAt⟩
  have hF₀_cont : Continuous F₀ := F₀.contMDiff.continuous
  have hF₀_crit {x : U} (hx : 1 < F₀ x) : x ∉ criticalPoints I F₀ := fun hcrit ↦
    notMem_criticalPoints_punctureSum (fun p ↦ (hW p).2) hWd hbW hx
      (mem_criticalPoints_comp_subtypeVal.1 hcrit)
  have hK : IsCompact {x : U | F₀ x ≤ 4} := isCompact_sublevel_punctureSum hS b hF₀_cont 4
  have hKC : IsMorseOn I F₀ ({x : U | F₀ x ≤ 4} ∩ {x : U | 2 ≤ F₀ x}) :=
    isMorseOn_iff_criticalPoints.2 ⟨F₀.contMDiff.contMDiffOn, fun _ hx hcrit ↦
      (hF₀_crit (lt_of_lt_of_le one_lt_two hx.2) hcrit).elim⟩
  obtain ⟨g, -, hgK, hgc, hgs⟩ := F₀.exists_isMorseOn_hasCompactSupport_sub_compl hK
    (isClosed_le continuous_const hF₀_cont) hKC (𝒰 := univ) univ_mem
  have hg_high {x : U} (hx : 2 < F₀ x) : x ∉ criticalPoints I g := by
    have hnts : x ∉ tsupport fun y ↦ g y - F₀ y := fun hts ↦ (hgs hts) hx.le
    have hev : (g : U → ℝ) =ᶠ[𝓝 x] F₀ := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hnts] with y hy
      exact sub_eq_zero.1 hy
    rw [mem_criticalPoints_congr hev]
    exact hF₀_crit (lt_trans one_lt_two hx)
  have hg_morse : IsMorse I g := by
    rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints]
    refine ⟨g.contMDiff.contMDiffOn, fun x _ hcrit ↦ ?_⟩
    by_cases hxK : F₀ x ≤ 4
    · exact hgK.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hxK hcrit
    · exact (hg_high (by linarith) hcrit).elim
  have hg_fin : (criticalPoints I g).Finite :=
    (hg_morse.finite_criticalPoints_inter hK).subset fun x hcrit ↦
      ⟨hcrit, not_lt.1 fun hgt : 4 < F₀ x ↦ hg_high (by linarith) hcrit⟩
  obtain ⟨hg_prop, hg_bdd⟩ := isProperMap_and_bddBelow_of_hasCompactSupport_sub
    (fun x : U ↦ Finset.sum_nonneg fun p _ ↦ puncturePole_nonneg (b p) x)
    (isCompact_sublevel_punctureSum hS b hF₀_cont) hF₀_cont g.contMDiff.continuous hgc
  exact hg_morse.finiteCWType_of_isProperMap hg_prop hg_bdd hg_fin

end InnerProductModel

end TauCeti

namespace Set.Finite

variable {E : Type v} {H : Type w} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [CompactSpace M] {S : Set M}

/-- **Complements of finite sets in compact smooth manifolds have finite CW type.** Let `M` be a
compact Hausdorff smooth manifold modelled on a boundaryless real model `I` over a
finite-dimensional space, and let `S ⊆ M` be finite. Then `M \ S` has finite CW type. -/
theorem finiteCWType_compl_of_isManifold (hS : S.Finite) (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I ∞ M] : FiniteCWType ↥Sᶜ := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let I' := I.transContinuousLinearEquiv e
  have : I'.Boundaryless :=
    ⟨by rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      image_univ_of_surjective e.surjective]⟩
  exact TauCeti.finiteCWType_compl_of_innerProductSpace I' hS

/-- **The Euler characteristic of a punctured compact smooth manifold.** Let `M` be a compact
Hausdorff smooth manifold modelled on a boundaryless real model `I` over a finite-dimensional
space `E`, and let `S ⊆ M` be finite. Then `χ(M \ S) = χ(M) - (-1) ^ dim E · #S`. -/
theorem eulerChar_compl_of_isManifold (hS : S.Finite) (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I ∞ M] :
    @eulerChar ↥Sᶜ _ (hS.finiteCWType_compl_of_isManifold I) =
      @eulerChar M _ (FiniteCWType.of_isManifold M I) - (-1) ^ finrank ℝ E * S.ncard := by
  let _ : ChartedSpace E H := I.toHomeomorph.symm.chartedSpace
  let _ : ChartedSpace E M := .comp E H M
  have := FiniteCWType.of_isManifold M I
  have := hS.finiteCWType_compl_of_isManifold I
  exact eulerChar_compl_of_finite (E := E) hS

end Set.Finite

end
