/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.Basic
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Vigier's monotone convergence theorem

On a complete real or complex inner product space `E`, a monotone net of bounded operators that
is bounded above in the Loewner order converges in the strong operator topology, and its strong
limit is its least upper bound; dually for antitone nets bounded below. Consequently the Loewner
order makes `E →L[𝕜] E` a `ConditionallyCompletePartialOrder`: every nonempty directed set that
is bounded above has a supremum (`ContinuousLinearMap.instConditionallyCompletePartialOrder`),
and monotone nets converge strongly to it
(`ContinuousLinearMap.tendsto_toPointwiseConvergenceCLM_ciSup`,
`ContinuousLinearMap.tendsto_toPointwiseConvergenceCLM_ciInf`). Conversely, the strong limit of
a monotone net, when it exists, is its least upper bound
(`ContinuousLinearMap.isLUB_of_tendsto_pointwise`), so the monotone nets that converge strongly
are exactly the bounded ones, with their suprema as limits. This order completeness is what
projection lattices and normal functionals on von Neumann algebras are built on.

The convergence rests on the inequality `‖D x‖² ≤ ‖C‖ re ⟪D x, x⟫` for `0 ≤ D ≤ C`
(`ContinuousLinearMap.norm_apply_sq_le_of_nonneg_of_le`): applied to the increments of the net,
it makes the net pointwise Cauchy, since the increasing quadratic forms `re ⟪f i x, x⟫` converge.
Positivity passes to strong limits (`ContinuousLinearMap.IsPositive.of_tendsto_pointwise`), which
identifies the limit as the least upper bound.

## References

* Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Lemma 5.1.4.
-/

public section

open Filter Topology Set
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A strong limit of positive operators is positive. -/
theorem IsPositive.of_tendsto_pointwise {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → E →L[𝕜] E} {T₀ : E →L[𝕜] E} (hT : ∀ᶠ i in l, (T i).IsPositive)
    (hlim : ∀ x, Tendsto (fun i => T i x) l (𝓝 (T₀ x))) : T₀.IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · exact tendsto_nhds_unique
      (((hlim x).inner tendsto_const_nhds).congr' (hT.mono fun i hi => hi.isSymmetric x y))
      (tendsto_const_nhds.inner (hlim y))
  · rw [reApplyInnerSelf_apply]
    exact ge_of_tendsto ((RCLike.continuous_re.tendsto _).comp
      ((hlim x).inner tendsto_const_nhds)) (hT.mono fun i hi => hi.re_inner_nonneg_left x)

/-- A monotone net of operators converging strongly to `T` has `T` as its least upper bound in
the Loewner order. -/
theorem isLUB_of_tendsto_pointwise {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {f : ι → E →L[𝕜] E} (hf : Monotone f) {T : E →L[𝕜] E}
    (hT : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (T x))) : IsLUB (range f) T := by
  refine ⟨?_, fun S hS => ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact le_def.mpr <| IsPositive.of_tendsto_pointwise
      ((eventually_ge_atTop i).mono fun j hj => le_def.mp (hf hj))
      fun x => by simpa using (hT x).sub (tendsto_const_nhds (x := f i x))
  · exact le_def.mpr <| IsPositive.of_tendsto_pointwise
      (Eventually.of_forall fun j => le_def.mp (hS (mem_range_self j)))
      fun x => by simpa using (tendsto_const_nhds (x := S x)).sub (hT x)

/-- An antitone net of operators converging strongly to `T` has `T` as its greatest lower bound
in the Loewner order. -/
theorem isGLB_of_tendsto_pointwise {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {f : ι → E →L[𝕜] E} (hf : Antitone f) {T : E →L[𝕜] E}
    (hT : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (T x))) : IsGLB (range f) T := by
  refine ⟨?_, fun S hS => ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact le_def.mpr <| IsPositive.of_tendsto_pointwise
      ((eventually_ge_atTop i).mono fun j hj => le_def.mp (hf hj))
      fun x => by simpa using (tendsto_const_nhds (x := f i x)).sub (hT x)
  · exact le_def.mpr <| IsPositive.of_tendsto_pointwise
      (Eventually.of_forall fun j => le_def.mp (hS (mem_range_self j)))
      fun x => by simpa using (hT x).sub (tendsto_const_nhds (x := S x))

variable [CompleteSpace E]

/-- A monotone net bounded above converges pointwise: the increasing quadratic forms
`re ⟪f i x, x⟫` converge, and `‖D x‖² ≤ ‖B - f i₀‖ re ⟪D x, x⟫` for the increments
`D = f j - f i` with `i₀ ≤ i ≤ j` makes `f i x` a Cauchy net. -/
private theorem exists_tendsto_apply_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {f : ι → E →L[𝕜] E} (hf : Monotone f) {B : E →L[𝕜] E} (hB : ∀ i, f i ≤ B)
    (i₀ : ι) (x : E) : ∃ y, Tendsto (fun i => f i x) atTop (𝓝 y) := by
  set q : ι → ℝ := fun i => RCLike.re ⟪f i x, x⟫_𝕜
  have hq : Monotone q := fun i j hij => by
    simpa [q, inner_sub_left, sub_nonneg] using (le_def.mp (hf hij)).re_inner_nonneg_left x
  have hqb : BddAbove (range q) := ⟨RCLike.re ⟪B x, x⟫_𝕜, by
    rintro _ ⟨i, rfl⟩
    simpa [q, inner_sub_left, sub_nonneg] using (le_def.mp (hB i)).re_inner_nonneg_left x⟩
  have hb : Tendsto (fun i => ‖B - f i₀‖ * ((⨆ i, q i) - q i)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := ⨆ i, q i)).sub
      (tendsto_atTop_ciSup hq hqb)).const_mul ‖B - f i₀‖
  refine cauchySeq_tendsto_of_complete (Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε => ?_⟩)
  obtain ⟨N, hN, hNi₀⟩ := ((hb.eventually (gt_mem_nhds (by positivity : 0 < (ε / 2) ^ 2))).and
    (eventually_ge_atTop i₀)).exists
  have hball : ∀ n, N ≤ n → dist (f n x) (f N x) < ε / 2 := fun n hn => by
    have hq' : RCLike.re ⟪(f n - f N) x, x⟫_𝕜 ≤ (⨆ i, q i) - q N := by
      simpa [q, inner_sub_left] using le_ciSup hqb n
    rw [dist_eq_norm, ← sub_apply]
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    calc _ ≤ _ := norm_apply_sq_le_of_nonneg_of_le (sub_nonneg.mpr (hf hn))
          (sub_le_sub (hB n) (hf hNi₀)) x
      _ ≤ ‖B - f i₀‖ * ((⨆ i, q i) - q N) := mul_le_mul_of_nonneg_left hq' (norm_nonneg _)
      _ < _ := hN
  refine ⟨(fun i => f i x) '' Ici N, image_mem_map (Ici_mem_atTop N), ?_⟩
  rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
  calc dist (f n x) (f m x) ≤ dist (f n x) (f N x) + dist (f m x) (f N x) :=
        dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hball n hn) (hball m hm)
    _ = ε := add_halves ε

/-- The core of Vigier's theorem: a monotone net bounded above converges strongly, and its limit
is its least upper bound. -/
private theorem exists_isLUB_tendsto_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {f : ι → E →L[𝕜] E} (hf : Monotone f) (hbdd : BddAbove (range f)) :
    ∃ T, IsLUB (range f) T ∧ ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (T x)) := by
  obtain ⟨B, hB⟩ := hbdd
  replace hB : ∀ i, f i ≤ B := fun i => hB (mem_range_self i)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  choose y hy using exists_tendsto_apply_of_monotone hf hB i₀
  -- The pointwise limit is a bounded operator, since beyond `i₀` the increments `f i - f i₀` lie
  -- between `0` and `B - f i₀`, so the tail of the net is norm bounded.
  have hbd : Bornology.IsBounded (f '' Ici i₀) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨‖f i₀‖ + ‖B - f i₀‖, ?_⟩
    rintro _ ⟨i, hi, rfl⟩
    calc ‖f i‖ = ‖f i₀ + (f i - f i₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖f i₀‖ + ‖f i - f i₀‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        exact norm_le_norm_of_nonneg_of_le (sub_nonneg.mpr (hf hi)) (sub_le_sub_right (hB i) _)
  have hmem : y ∈ closure ((fun (g : E →L[𝕜] E) => (g : E → E)) '' (f '' Ici i₀)) :=
    mem_closure_of_tendsto (tendsto_pi_nhds.mpr hy)
      ((eventually_ge_atTop i₀).mono fun i hi => mem_image_of_mem _ (mem_image_of_mem _ hi))
  have hT : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (ofMemClosureImageCoeBounded y hbd hmem x)) :=
    fun x => by simpa only [ofMemClosureImageCoeBounded_apply] using hy x
  exact ⟨_, isLUB_of_tendsto_pointwise hf hT, hT⟩

/-- The antitone form of `exists_isLUB_tendsto_of_monotone`, by negation. -/
private theorem exists_isGLB_tendsto_of_antitone {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {f : ι → E →L[𝕜] E} (hf : Antitone f) (hbdd : BddBelow (range f)) :
    ∃ T, IsGLB (range f) T ∧ ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (T x)) := by
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨T, -, hlim⟩ := exists_isLUB_tendsto_of_monotone (f := fun i => -f i)
    (fun i j hij => neg_le_neg (hf hij))
    ⟨-B, by rintro _ ⟨i, rfl⟩; exact neg_le_neg (hB (mem_range_self i))⟩
  have hT : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 ((-T) x)) := fun x => by
    simpa using (hlim x).neg
  exact ⟨-T, isGLB_of_tendsto_pointwise hf hT, hT⟩

open Classical in
/-- **Vigier's theorem**, order-theoretic form: with the Loewner order, the bounded operators on
a complete inner product space form a conditionally complete partial order. Every nonempty set
of operators that is directed upwards and bounded above has a least upper bound `sSup`, and
dually for `sInf`. On a set without least upper bound `sSup` is `0`, and likewise for `sInf`. -/
noncomputable instance instConditionallyCompletePartialOrder :
    ConditionallyCompletePartialOrder (E →L[𝕜] E) where
  sSup s := if h : ∃ T, IsLUB s T then h.choose else 0
  sInf s := if h : ∃ T, IsGLB s T then h.choose else 0
  isLUB_csSup_of_directed s hd hne hbdd := by
    have := hd.isDirectedOrder
    have := hne.to_subtype
    obtain ⟨T, hT, -⟩ := exists_isLUB_tendsto_of_monotone (f := Subtype.val)
      (Subtype.mono_coe _) (by rwa [Subtype.range_coe])
    have hex : ∃ T, IsLUB s T := ⟨T, by rwa [Subtype.range_coe] at hT⟩
    simpa [hex] using hex.choose_spec
  isGLB_csInf_of_directed s hd hne hbdd := by
    have := hd.isCodirectedOrder
    have := hne.to_subtype
    have hrange : range (fun a : (↥s)ᵒᵈ => (OrderDual.ofDual a).1) = s :=
      (OrderDual.ofDual.surjective.range_comp _).trans Subtype.range_coe
    obtain ⟨T, hT, -⟩ := exists_isGLB_tendsto_of_antitone (ι := (↥s)ᵒᵈ)
      (f := fun a => (OrderDual.ofDual a).1) (fun _ _ hab => hab) (by rwa [hrange])
    have hex : ∃ T, IsGLB s T := ⟨T, hrange ▸ hT⟩
    simpa [hex] using hex.choose_spec

/-- **Vigier's theorem**: a monotone net of operators bounded above in the Loewner order
converges in the strong operator topology to its supremum. -/
theorem tendsto_toPointwiseConvergenceCLM_ciSup {ι : Type*} [Preorder ι] {f : ι → E →L[𝕜] E}
    (hf : Monotone f) (hbdd : BddAbove (range f)) :
    Tendsto (fun i => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (f i)) atTop
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (⨆ i, f i))) := by
  obtain h | h := eq_or_ne atTop (⊥ : Filter ι)
  · rw [h]
    exact tendsto_bot
  obtain ⟨h₁, h₂⟩ := atTop_neBot_iff.mp ⟨h⟩
  obtain ⟨T, hT, hlim⟩ := exists_isLUB_tendsto_of_monotone hf hbdd
  rw [(hf.directed_le.isLUB_ciSup hbdd).unique hT]
  exact PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr hlim

/-- **Vigier's theorem** for decreasing nets: an antitone net of operators bounded below in the
Loewner order converges in the strong operator topology to its infimum. -/
theorem tendsto_toPointwiseConvergenceCLM_ciInf {ι : Type*} [Preorder ι] {f : ι → E →L[𝕜] E}
    (hf : Antitone f) (hbdd : BddBelow (range f)) :
    Tendsto (fun i => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (f i)) atTop
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (⨅ i, f i))) := by
  obtain h | h := eq_or_ne atTop (⊥ : Filter ι)
  · rw [h]
    exact tendsto_bot
  obtain ⟨h₁, h₂⟩ := atTop_neBot_iff.mp ⟨h⟩
  obtain ⟨T, hT, hlim⟩ := exists_isGLB_tendsto_of_antitone hf hbdd
  rw [(hf.directed_ge.isGLB_ciInf hbdd).unique hT]
  exact PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr hlim

end ContinuousLinearMap
