/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Topology.Algebra.Group.NoSmallSubgroups
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
import Mathlib.Analysis.Calculus.MeanValue

/-!
# No small subgroups in the diffeomorphism group

In the weak Whitney topology on the diffeomorphisms of a compact boundaryless manifold, a
sufficiently small identity neighbourhood contains no nontrivial subgroup. Only first derivatives
are used: in coordinates the displacement of a nearby diffeomorphism is `1/2`-Lipschitz, so
squaring increases a nonzero displacement by a factor of at least `3/2`. All the powers cannot
continue to lie in the neighbourhood, since their displacements there are bounded.

This is a variant of the Bochner–Montgomery argument for groups of differentiable
transformations. Instead of averaging over a subgroup, it compares a power to its square.

## References

* S. Bochner and D. Montgomery, *Groups of differentiable and real or complex analytic
  transformations*, Ann. of Math. (2) 46 (1945), 685–694.
-/

public section

open Filter Function Manifold Metric Set Topology
open scoped ContDiff Topology TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A bounded power orbit in a chart is fixed if the displacement of each power is
`1/2`-Lipschitz between the initial point and the corresponding orbit point. -/
private theorem apply_eq_self_of_small_powers (f : M ≃ₘ^n⟮I, I⟯ M)
    (c : M) {x : M} (hx : x ∈ (extChartAt I c).source) {R : ℝ}
    (hR : ∀ j : ℕ, ‖extChartAt I c ((f ^ j) x) - extChartAt I c x‖ ≤ R)
    (hsrc : f x ∈ (extChartAt I c).source)
    (hdisp : ∀ j : ℕ,
      ‖(extChartAt I c ((f ^ j) ((f ^ j) x)) - extChartAt I c ((f ^ j) x)) -
        (extChartAt I c ((f ^ j) x) - extChartAt I c x)‖ ≤
        (1 / 2 : ℝ) * ‖extChartAt I c ((f ^ j) x) - extChartAt I c x‖) : f x = x := by
  let d : ℕ → ℝ := fun j ↦ ‖extChartAt I c ((f ^ j) x) - extChartAt I c x‖
  have hb : BddAbove (range d) := ⟨R, forall_mem_range.2 hR⟩
  have hd (j : ℕ) : d j ≤ sSup (range d) := le_csSup hb (mem_range_self j)
  -- Compare each displacement with that of the doubled power before taking the supremum.
  have hstep (j : ℕ) : d j ≤ (2 / 3 : ℝ) * sSup (range d) := by
    let a := extChartAt I c x
    let b := extChartAt I c ((f ^ j) x)
    let z := extChartAt I c ((f ^ j) ((f ^ j) x))
    have htri := norm_sub_le (z - a) ((z - b) - (b - a))
    rw [show z - a - (z - b - (b - a)) = (2 : ℝ) • (b - a) by module,
      norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri
    have hz : ‖z - a‖ ≤ sSup (range d) := by
      simpa only [d, z, a, pow_add, mul_apply] using hd (j + j)
    linarith [hdisp j]
  have hs := csSup_le (range_nonempty d) (forall_mem_range.2 hstep)
  have hzero : d 1 = 0 := le_antisymm (by linarith [hd 1]) (norm_nonneg _)
  apply (extChartAt I c).injOn hsrc hx
  simpa only [d, pow_one, norm_eq_zero, sub_eq_zero] using hzero

variable [I.Boundaryless] [IsManifold I n M]

/-- In a chart the displacement of a diffeomorphism is `1/2`-Lipschitz on a closed ball
if its first coordinate derivative is uniformly within `1/2` of the identity there. -/
private theorem norm_chartDisplacement_sub_le (f : M ≃ₘ^n⟮I, I⟯ M) (hn : 1 ≤ n) (c : M)
    {r : ℝ} (hB : closedBall (extChartAt I c c) r ⊆ (extChartAt I c).target)
    (hf : ∀ u : (extChartAt I c).target, (u : E) ∈ closedBall (extChartAt I c c) r →
      f ((extChartAt I c).symm u) ∈ (extChartAt I c).source ∧
      dist (iteratedFDerivWithin ℝ 1 (extChartAt I c ∘ f ∘ (extChartAt I c).symm)
        (extChartAt I c).target u)
        (iteratedFDerivWithin ℝ 1 id (extChartAt I c).target u) ≤ 1 / 2)
    {u v : E} (hu : u ∈ closedBall (extChartAt I c c) r)
    (hv : v ∈ closedBall (extChartAt I c c) r) :
    ‖(extChartAt I c (f ((extChartAt I c).symm v)) - v) -
      (extChartAt I c (f ((extChartAt I c).symm u)) - u)‖ ≤ (1 / 2 : ℝ) * ‖v - u‖ := by
  let e := extChartAt I c
  let g : E → E := e ∘ f ∘ e.symm
  have hsub : (extChartAt I c (f ((extChartAt I c).symm v)) - v) -
      (extChartAt I c (f ((extChartAt I c).symm u)) - u) = g v - g u - (v - u) := by
    dsimp [g, e]
    abel
  rw [hsub]
  refine (convex_closedBall _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f' := fun w ↦ fderivWithin ℝ g e.target w) (φ := ContinuousLinearMap.id ℝ E) ?_ ?_ hu hv
  · intro w hw
    have hwT := hB hw
    have he : ContMDiffAt 𝓘(ℝ, E) I n e.symm w :=
      (contMDiffOn_extChartAt_symm c).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds hwT)
    have hed : ContMDiffAt I 𝓘(ℝ, E) n e (f (e.symm w)) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using (hf ⟨w, hwT⟩ hw).1)
    have hg : DifferentiableWithinAt ℝ g e.target w :=
      ((hed.comp w (f.contMDiff.contMDiffAt.comp w he)).contDiffAt.differentiableAt
        (ENat.one_le_iff_ne_zero_withTop.mp hn)).differentiableWithinAt
    exact hg.hasFDerivWithinAt.mono hB
  · intro w hw
    have hwT := hB hw
    have hdiff := uniqueDiffOn_extChartAt_target c w hwT
    simpa only [g, e, dist_iteratedFDerivWithin_one _ _ hdiff hdiff, dist_eq_norm,
      fderivWithin_id hdiff] using (hf ⟨w, hwT⟩ hw).2

variable [CompactSpace M]

omit [I.Boundaryless] in
/-- A compact chart test holds near the identity when its open set of jets contains the
corresponding jets of the coordinate identity. -/
private theorem preimage_chartJetSet_mem_nhds_one (c : M) (m : ℕ) (hm : m ≤ n)
    {K : Set (extChartAt I c).target} (hK : IsCompact K)
    {V : Set (E [×m]→L[ℝ] E)} (hV : IsOpen V)
    (hId : ∀ w ∈ K, iteratedFDerivWithin ℝ m id (extChartAt I c).target w ∈ V) :
    toContMDiffMap ⁻¹' ContMDiffMap.chartJetSet c c m K V ∈ 𝓝 (1 : M ≃ₘ^n⟮I, I⟯ M) := by
  let e := extChartAt I c
  have he : EqOn (e ∘ (1 : M ≃ₘ^n⟮I, I⟯ M).toContMDiffMap ∘ e.symm) id e.target :=
    fun z hz ↦ by simpa only [comp_apply, coe_coe, one_apply, id_eq] using e.right_inv hz
  refine ((ContMDiffMap.isOpen_chartJetSet c c m hm hK hV).preimage
    continuous_toContMDiffMap).mem_nhds (ContMDiffMap.mem_chartJetSet.2 fun w hw ↦ ⟨?_, ?_⟩)
  · simpa only [coe_coe, one_apply] using e.map_target w.property
  · rw [iteratedFDerivWithin_congr he w.property]
    exact hId w hw

/-- First-order Whitney control of displacement on a compact coordinate set. -/
private theorem eventually_chart_derivative_close (hn : 1 ≤ n) (c : M)
    {K : Set (extChartAt I c).target} (hK : IsCompact K) :
    ∀ᶠ f : M ≃ₘ^n⟮I, I⟯ M in 𝓝 1, ∀ u ∈ K,
      f ((extChartAt I c).symm u) ∈ (extChartAt I c).source ∧
      dist (iteratedFDerivWithin ℝ 1 (extChartAt I c ∘ f ∘ (extChartAt I c).symm)
        (extChartAt I c).target u)
        (iteratedFDerivWithin ℝ 1 id (extChartAt I c).target u) ≤ 1 / 2 := by
  let e := extChartAt I c
  let D := iteratedFDeriv ℝ 1 (id : E → E) (e c)
  have hD (w : E) (hw : w ∈ e.target) : iteratedFDerivWithin ℝ 1 id e.target w = D := by
    rw [iteratedFDerivWithin_of_isOpen 1 (isOpen_extChartAt_target c) hw]
    ext m
    simp only [D, iteratedFDeriv_one_apply, fderiv_id]
  have hU := preimage_chartJetSet_mem_nhds_one (n := n) c 1 (by simpa using hn) hK
    (V := ball D (1 / 2)) isOpen_ball fun w _ ↦ by
    rw [hD _ w.property]
    exact mem_ball_self (by norm_num)
  filter_upwards [hU] with f hf u hu
  obtain ⟨hsrc, hb⟩ := ContMDiffMap.mem_chartJetSet.1 hf u hu
  refine ⟨hsrc, ?_⟩
  rw [hD _ u.property]
  simpa only [coe_coe] using (mem_ball.1 hb).le

variable [ProperSpace E]

/-- A neighbourhood of the identity detects all movers in a smaller coordinate ball:
if every natural power of `f` lies in the neighbourhood, `f` fixes that ball pointwise. -/
private theorem exists_nhds_forall_pow_apply_eq (hn : 1 ≤ n) (c : M) :
    ∃ (W : Set M) (U : Set (M ≃ₘ^n⟮I, I⟯ M)), IsOpen W ∧ c ∈ W ∧ U ∈ 𝓝 1 ∧
      ∀ f : M ≃ₘ^n⟮I, I⟯ M, (∀ j : ℕ, f ^ j ∈ U) → ∀ x ∈ W, f x = x := by
  let e := extChartAt I c
  obtain ⟨r, hr, hB⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_extChartAt_target (I := I) c).mem_nhds (mem_extChartAt_target c))
  let K (s : ℝ) : Set e.target := Subtype.val ⁻¹' closedBall (e c) s
  have hK (s : ℝ) (hs : s ≤ r) : IsCompact (K s) :=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage' (isCompact_closedBall _ _)
      (by rw [Subtype.range_coe_subtype]; exact (closedBall_subset_closedBall hs).trans hB)
  let V₀ : Set (E [×0]→L[ℝ] E) := (fun A ↦ A 0) ⁻¹' ball (e c) r
  let U₀ : Set (M ≃ₘ^n⟮I, I⟯ M) :=
    toContMDiffMap ⁻¹' ContMDiffMap.chartJetSet c c 0 (K (r / 2)) V₀
  have hU₀ : U₀ ∈ 𝓝 (1 : M ≃ₘ^n⟮I, I⟯ M) := by
    refine preimage_chartJetSet_mem_nhds_one c 0 (by simp) (hK _ (by linarith))
      (isOpen_ball.preimage (by fun_prop)) fun w hw ↦ ?_
    simpa only [V₀, mem_preimage, iteratedFDerivWithin_zero_apply, id_eq] using
      (closedBall_subset_ball (by linarith : r / 2 < r) hw)
  have hU₁ := eventually_chart_derivative_close hn c (hK r le_rfl)
  refine ⟨e.source ∩ e ⁻¹' ball (e c) (r / 2), U₀ ∩ _,
    isOpen_extChartAt_preimage' (I := I) c isOpen_ball,
    ⟨mem_extChartAt_source c, mem_ball_self (by positivity)⟩,
    inter_mem hU₀ hU₁, ?_⟩
  intro f hf x hx
  have hxK : e x ∈ closedBall (e c) (r / 2) := ball_subset_closedBall hx.2
  have h₀ (j : ℕ) : (f ^ j) x ∈ e.source ∧ e ((f ^ j) x) ∈ ball (e c) r := by
    have h := ContMDiffMap.mem_chartJetSet.1 (hf j).1 ⟨e x, e.map_source hx.1⟩ hxK
    simpa only [e, coe_coe, V₀, mem_preimage, iteratedFDerivWithin_zero_apply, comp_apply,
      (extChartAt I c).left_inv hx.1] using h
  have hxB : e x ∈ closedBall (e c) r := closedBall_subset_closedBall (by linarith) hxK
  refine apply_eq_self_of_small_powers f c hx.1 (R := 2 * r) (fun j ↦ ?_)
    (by simpa only [pow_one] using (h₀ 1).1)
    (fun j ↦ ?_)
  · rw [← dist_eq_norm]
    exact (dist_triangle _ (e c) _).trans (by linarith [mem_ball.1 (h₀ j).2, mem_closedBall'.1 hxB])
  · have h := norm_chartDisplacement_sub_le (f ^ j) hn c hB (hf j).2 hxB
      (ball_subset_closedBall (h₀ j).2)
    simpa only [e, (extChartAt I c).left_inv hx.1, (extChartAt I c).left_inv (h₀ j).1] using h

/-- The group of `C^n` diffeomorphisms of a compact boundaryless real manifold, for `n ≥ 1`,
has no small subgroups in the weak Whitney topology. -/
theorem hasNoSmallSubgroups_weakWhitney (hn : 1 ≤ n) :
    TauCeti.HasNoSmallSubgroups (M ≃ₘ^n⟮I, I⟯ M) := by
  classical
  choose W U hWo hW hU hfix using exists_nhds_forall_pow_apply_eq (I := I) hn (M := M)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover W hWo (fun x _ ↦ mem_iUnion.2 ⟨x, hW x⟩)
  refine TauCeti.HasNoSmallSubgroups.of_forall_pow_mem ⟨⋂ c ∈ s, U c, ?_, ?_⟩
  · exact (biInter_finset_mem _).2 fun c _ ↦ hU c
  · intro f hf
    ext x
    obtain ⟨c, hc⟩ := mem_iUnion.1 (hs (mem_univ x))
    obtain ⟨hcs, hx⟩ := mem_iUnion.1 hc
    rw [one_apply]
    exact hfix c f (fun j ↦ mem_iInter₂.1 (hf j) c hcs) x hx

end Diffeomorph
