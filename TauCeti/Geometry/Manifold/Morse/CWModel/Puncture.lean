/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Morse.CWModel
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Algebra.Order.Group.Bounds
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Puncture
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.LinearEquiv
import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
import TauCeti.Geometry.Manifold.Morse.Generic.Strong

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
in `U` (so `F₀` is proper), and which has no critical points on `{1 < F₀}`. Relative proper Morse
approximation (`ContMDiffMap.exists_isMorse_isProperMap_mem_ball`) perturbs `F₀` within `C⁰`
distance `1` while keeping it unchanged near `{2 ≤ F₀}`, producing a globally Morse proper
bounded-below function `g` on `U` whose critical points all lie inside the compact sublevel
`{F₀ ≤ 2}`, hence finitely many; the proper Morse CW model
(`TauCeti.IsMorse.finiteCWType_of_isProperMap`) concludes.

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
  filter_upwards [(hWo p.val).mem_nhds hx] with y hy
  rw [punctureSum, Finset.sum_eq_single p _ (by simp)]
  intro q _ hqp
  have hdisj : Disjoint (W p.val) (W q.val) :=
    hWd p.property q.property (Subtype.coe_ne_coe.2 hqp.symm)
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
  rw [hev.mem_criticalPoints_iff]
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
  have hK : IsCompact (Subtype.val ⁻¹' (⋃ p : S, O p)ᶜ : Set U) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage'
      (isOpen_iUnion hOopen).isClosed_compl.isCompact
      (by rw [Subtype.range_coe]; exact compl_subset_compl.2 hSO)
  refine hK.of_isClosed_subset (isClosed_le hcont continuous_const) fun x hx hp ↦ ?_
  obtain ⟨p, hp'⟩ := mem_iUnion.1 hp
  have hlt : B < puncturePole (b p) x := hOB p x hp' fun h ↦ x.property (h ▸ p.property)
  have hle : puncturePole (b p) x ≤ punctureSum b x :=
    Finset.single_le_sum (fun q _ ↦ puncturePole_nonneg (b q) x) (Finset.mem_univ p)
  exact hx.not_gt (hlt.trans_le hle)

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
      (ContMDiffAt.sum fun p _ ↦ contMDiffAt_puncturePole (b p) fun h ↦ x.property (h ▸ p.property))
      contMDiff_subtypeVal.contMDiffAt⟩
  have hF₀_cont : Continuous F₀ := F₀.contMDiff.continuous
  have hF₀_crit {x : U} (hx : 1 < F₀ x) : x ∉ criticalPoints I F₀ := fun hcrit ↦
    notMem_criticalPoints_punctureSum (fun p ↦ (hW p).2) hWd hbW hx
      (mem_criticalPoints_comp_subtypeVal.1 hcrit)
  have hF₀_sub (B : ℝ) : IsCompact {x : U | F₀ x ≤ B} :=
    isCompact_sublevel_punctureSum hS b hF₀_cont B
  have hF₀_prop : IsProperMap F₀ :=
    isProperMap_iff_isCompact_preimage.2 ⟨hF₀_cont, fun Q hQ ↦
      let ⟨B, hB⟩ := hQ.bddAbove
      (hF₀_sub B).of_isClosed_subset (hQ.isClosed.preimage hF₀_cont) fun _ hx ↦ hB hx⟩
  have hF₀_morseC : IsMorseOn I F₀ {x : U | 2 ≤ F₀ x} :=
    isMorseOn_iff_criticalPoints.2 ⟨F₀.contMDiff.contMDiffOn, fun _ hx hcrit ↦
      (hF₀_crit (lt_of_lt_of_le one_lt_two hx) hcrit).elim⟩
  obtain ⟨g, -, hg_morse, hg_prop, hg_dist, hgs⟩ :=
    F₀.exists_isMorse_isProperMap_mem_ball .empty hF₀_prop
      (isClosed_le continuous_const hF₀_cont) hF₀_morseC
  have hg_bdd : BddBelow (range g) :=
    BddBelow.range_of_abs_sub_le
      ⟨0, forall_mem_range.2 fun x : U ↦ Finset.sum_nonneg fun p _ ↦ puncturePole_nonneg (b p) x⟩
      fun x ↦ (hg_dist x).le
  have hg_fin : (criticalPoints I g).Finite := by
    refine (hg_morse.finite_criticalPoints_inter (hF₀_sub 2)).subset fun x hcrit ↦ ⟨hcrit, ?_⟩
    simp only [mem_ofPred_eq]
    by_contra! hgt
    have hnts : x ∉ tsupport fun y ↦ g y - F₀ y := fun hts ↦ hgs hts hgt.le
    have hev : (g : U → ℝ) =ᶠ[𝓝 x] F₀ :=
      (notMem_tsupport_iff_eventuallyEq.1 hnts).mono fun _ hy ↦ sub_eq_zero.1 hy
    exact hF₀_crit (one_lt_two.trans hgt) (hev.mem_criticalPoints_iff.1 hcrit)
  exact hg_morse.finiteCWType_of_isProperMap hg_prop hg_bdd hg_fin

end InnerProductModel

end TauCeti

namespace Set.Finite

variable {E : Type v} {H : Type w} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [CompactSpace M] {S : Set M}

/-- **Complements of finite sets in compact smooth manifolds have finite CW type.** Let `M` be a
compact Hausdorff smooth manifold modelled on a boundaryless real model `I`, and let `S ⊆ M` be
finite. Then `M \ S` has finite CW type. -/
theorem finiteCWType_compl_of_isManifold (hS : S.Finite) (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I ∞ M] : FiniteCWType ↥Sᶜ := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact FiniteCWType.of_discreteTopology ↥Sᶜ
  · have : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
    let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
      ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
    exact TauCeti.finiteCWType_compl_of_innerProductSpace (I.transContinuousLinearEquiv e) hS

/-- **The Euler characteristic of a punctured compact smooth manifold.** Let `M` be a compact
Hausdorff smooth manifold modelled on a boundaryless real model `I` over `E`, and let `S ⊆ M` be
finite. Then `χ(M \ S) = χ(M) - (-1) ^ dim E · #S`. -/
theorem eulerChar_compl_of_isManifold (hS : S.Finite) (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I ∞ M] :
    @eulerChar ↥Sᶜ _ (hS.finiteCWType_compl_of_isManifold I) =
      @eulerChar M _ (FiniteCWType.of_isManifold M I) - (-1) ^ finrank ℝ E * S.ncard := by
  rcases isEmpty_or_nonempty M with _ | _
  · have := FiniteCWType.of_isManifold M I
    have := hS.finiteCWType_compl_of_isManifold I
    simp [eulerChar_of_discreteTopology, S.eq_empty_of_isEmpty]
  · have : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
    let _ : ChartedSpace E H := I.toHomeomorph.symm.chartedSpace
    let _ : ChartedSpace E M := .comp E H M
    have := FiniteCWType.of_isManifold M I
    have := hS.finiteCWType_compl_of_isManifold I
    exact eulerChar_compl_of_finite (E := E) hS

end Set.Finite

end
