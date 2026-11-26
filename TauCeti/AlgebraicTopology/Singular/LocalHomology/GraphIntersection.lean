/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Holomorphic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Analytic.IsolatedCriticalPoints
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.IsolatedZero
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.LinearAlgebra.LinearIndependent.Prod
import TauCeti.LinearAlgebra.LinearMap.Coprod
import TauCeti.Topology.Algebra.Group.Basic

/-!
# Local intersection numbers of holomorphic discs with a holomorphic graph

Orient `ℂ²`, regarded as a real manifold of dimension `4`, by a homological orientation `o`, used
on both the source and the target. Two holomorphic discs `u₁, u₂ : ℂ → ℂ²` meeting at
`u₁ z₀ = u₂ w₀` have, as local intersection number, the local index at `(z₀, w₀)` of the map
`F (z, w) = u₁ z - u₂ w` (`TauCeti.HomologicalOrientation.localIndex`). It is positive at an
isolated intersection, and `1` at a transverse one
(`TauCeti.HomologicalOrientation.localIndex_pos_of_apply_eq_sub`,
`TauCeti.HomologicalOrientation.localIndex_eq_one_of_apply_eq_sub`). This file computes it when
the first disc is the graph `z ↦ (z, f z)` of a holomorphic function `f`, and the second disc
`u = (a, b)` is arbitrary, possibly tangent to the graph and possibly singular.

**The local intersection number is an order of vanishing**
(`TauCeti.HomologicalOrientation.localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub`). The
disc `u` meets the graph where `φ w = b w - f (a w)` vanishes, and the local intersection number at
`((u w₀).1, w₀)` is the order of vanishing of `φ` at `w₀`. Both sides are `0` when `u` runs inside
the graph near `w₀`. The two classical cases are:

* **tangent immersed branches.** For two graphs `z ↦ (z, f z)` and `w ↦ (w, g w)` meeting at
  `(z₀, f z₀)`, the local intersection number is the order of contact, the order of vanishing of
  `g - f` at `z₀` (`localIndex_eq_analyticOrderNatAt_sub_of_apply_eq_graph_sub_graph` in the
  namespace `TauCeti.HomologicalOrientation`): the line `w = 0` and the curve `w = z ^ k` meet at
  the origin with multiplicity `k`;
* **critical branches.** The intersection number with a singular disc counts its order of contact
  along the parametrization: the line `w = 0` meets the cusp `w ↦ (w², w³)` with multiplicity `3`,
  and the line `w = z` meets it with multiplicity `2`.

An isolated intersection counts `1` exactly when it is transverse: the tangent vectors `(1, f' z₀)`
and `u' w₀` are linearly independent over `ℂ`
(`TauCeti.HomologicalOrientation.localIndex_eq_one_iff_of_apply_eq_graph_sub`). So each tangency of
immersed branches, and each meeting with a critical branch, contributes at least `2`
(`TauCeti.HomologicalOrientation.two_le_localIndex_of_apply_eq_graph_sub`,
`TauCeti.HomologicalOrientation.two_le_localIndex_of_apply_eq_graph_sub_of_deriv_eq_zero`). These
are the model cases, for the standard complex structure of `ℂ²`, of the local intersection
multiplicities of tangent and critical branches of pseudoholomorphic curves in a four-manifold.

**Changes of coordinates and immersed branches.** Local intersection numbers do not depend on the
parametrizations of the discs: reparametrizing them by maps with nonzero complex derivatives at the
intersection does not change the local index
(`TauCeti.HomologicalOrientation.localIndex_eq_of_apply_eq_comp_sub_comp`). Nor do they depend on
the coordinates of the target, for changes of coordinates whose derivative at the intersection
point is complex linear, such as unitary maps
(`TauCeti.HomologicalOrientation.localIndex_eq_of_apply_eq_sub_of_hasStrictFDerivAt`). Hence the
order of vanishing computes the local intersection number of a disc `u₂` with every disc `u₁` that
runs in a holomorphic graph over one of the coordinate axes with a coordinate of nonzero derivative,
not only with the graph itself: after reparametrizing `u₁` by the inverse of that coordinate, and
exchanging the two coordinates of `ℂ²` if the graph is over the second axis, `u₁` is the graph
(`localIndex_eq_analyticOrderNatAt_of_apply_eq_sub_of_eventually_snd_eq`,
`localIndex_eq_analyticOrderNatAt_of_apply_eq_sub_of_eventually_fst_eq` in the namespace
`TauCeti.HomologicalOrientation`). Every holomorphic disc immersed at a point runs near it in such
a graph, over an axis on which its tangent vector has a nonzero component, since the local inverse
of that coordinate is holomorphic (`AnalyticAt.analyticAt_localInverse`); so these statements apply
to every pair of holomorphic discs whose first disc `u₁` is immersed.

## Proof

Near the intersection, the solutions of `F (z, w) = (0, -ε)` are the points `((u w).1, w)` with
`φ w = ε`, and at such a point the complex derivative of `F` is invertible exactly when
`φ' w = b' w - f' (a w) a' w ≠ 0`. If `φ` vanishes to order `m` at `w₀`, then for small `ε ≠ 0` the
equation `φ w = ε` has exactly `m` simple solutions near `w₀` (`TauCeti.localDegree_card`, a Rouché
argument), so `(0, -ε)` has `m` regular preimages near the intersection, and the local index counts
them (`TauCeti.HomologicalOrientation.localIndex_eq_ncard_of_hasFDerivAt`). The solutions of
`φ w = ε` concentrate at `w₀` as `ε` tends to `0`, so they all lie in a ball about the intersection
in `ℂ²`, whatever the derivative of `a`.

## Main results

In the namespace `TauCeti.HomologicalOrientation`:

* `localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub`: the local intersection number of a
  holomorphic graph and a holomorphic disc is the order of vanishing of `b - f ∘ a`.
* `localIndex_eq_analyticOrderNatAt_sub_of_apply_eq_graph_sub_graph`: two holomorphic graphs meet
  with their order of contact.
* `localIndex_eq_one_iff_of_apply_eq_graph_sub`: the local intersection number is `1` exactly at a
  transverse intersection.
* `two_le_localIndex_of_apply_eq_graph_sub`,
  `two_le_localIndex_of_apply_eq_graph_sub_of_deriv_eq_zero`: an isolated tangential intersection,
  in particular a meeting with a critical branch, counts at least `2`.
* `localIndex_eq_of_apply_eq_comp_sub_comp`: local intersection numbers do not depend on the
  parametrizations of the discs.
* `localIndex_eq_analyticOrderNatAt_of_apply_eq_sub_of_eventually_snd_eq`,
  `localIndex_eq_analyticOrderNatAt_of_apply_eq_sub_of_eventually_fst_eq`: the local intersection
  number of a disc with a disc running in a holomorphic graph over the first or the second
  coordinate axis is an order of vanishing.

The examples at the end of the file compute the local intersection numbers of the line `w = 0` with
the curves `w = z ^ k` (it is `k`, and in particular `2` for the parabola) and of the lines `w = 0`
and `w = z` with the cusp `w ↦ (w², w³)` (they are `3` and `2`), and of the vertical line `z = 0`
with the curve `z = w²` (it is `2`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix E.2 (local intersection numbers of tangent and critical branches).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages of a regular value).
-/

public section

noncomputable section

open Filter Metric Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

/-- The function `φ w = (u w).2 - f (u w).1`, whose zeros are the meetings of the disc `u` with
the graph of `f`, is analytic where `u` and `f` are. -/
private theorem analyticAt_snd_sub_comp_fst {f : ℂ → ℂ} {u : ℂ → ℂ × ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f (u w).1) (hu : AnalyticAt ℂ u w) :
    AnalyticAt ℂ (fun w ↦ (u w).2 - f (u w).1) w := by
  have h₁ : AnalyticAt ℂ (fun w ↦ (u w).1) w := AnalyticAt.comp (f := u) analyticAt_fst hu
  have h₂ : AnalyticAt ℂ (fun w ↦ (u w).2) w := AnalyticAt.comp (f := u) analyticAt_snd hu
  exact h₂.sub (AnalyticAt.comp (f := fun w ↦ (u w).1) hf h₁)

/-- The derivative of `φ w = (u w).2 - f (u w).1`. -/
private theorem hasDerivAt_snd_sub_comp_fst {f : ℂ → ℂ} {u : ℂ → ℂ × ℂ} {w : ℂ}
    (hf : DifferentiableAt ℂ f (u w).1) (hu : DifferentiableAt ℂ u w) :
    HasDerivAt (fun w ↦ (u w).2 - f (u w).1) ((deriv u w).2 - deriv f (u w).1 * (deriv u w).1)
      w :=
  (hasFDerivAt_snd.comp_hasDerivAt w hu.hasDerivAt).sub
    (hf.hasDerivAt.comp w (hasFDerivAt_fst.comp_hasDerivAt w hu.hasDerivAt))

/-- In every small disc about a zero `w₀` of order `m` of an analytic function `φ`, the equation
`φ w = ε` has exactly `m` solutions for every small `ε ≠ 0`. -/
private theorem exists_ncard_eq_analyticOrderNatAt {φ : ℂ → ℂ} {w₀ : ℂ} {r s : ℝ}
    (hφ : AnalyticOnNhd ℂ φ (closedBall w₀ r)) (hφ₀ : φ w₀ = 0)
    (hiso : ∀ w ∈ closedBall w₀ r, w ≠ w₀ → φ w ≠ 0)
    (hder : ∀ w ∈ ball w₀ r, w ≠ w₀ → deriv φ w ≠ 0) (hs : 0 < s) (hsr : s ≤ r) :
    ∃ δ > 0, ∀ ε : ℂ, ε ≠ 0 → ‖ε‖ < δ →
      {w ∈ ball w₀ s | φ w = ε}.Finite ∧
        {w ∈ ball w₀ s | φ w = ε}.ncard = analyticOrderNatAt φ w₀ := by
  obtain ⟨δ, hδ, h⟩ := localDegree_card hs (hφ.mono (closedBall_subset_closedBall hsr))
    (fun w hw hne ↦ by rw [hφ₀]; exact hiso w (closedBall_subset_closedBall hsr hw) hne)
    (fun w hw hne ↦ hder w (ball_subset_ball hsr hw) hne)
  refine ⟨δ, hδ, fun ε hε hεδ ↦ ?_⟩
  obtain ⟨hfin, hcard, -⟩ := h ε (by rwa [hφ₀]) (by rwa [hφ₀, sub_zero])
  simp only [hφ₀, sub_zero] at hcard
  exact ⟨hfin, hcard⟩

section Graph

variable {F : C(ℂ × ℂ, ℂ × ℂ)} {f : ℂ → ℂ} {u : ℂ → ℂ × ℂ}

/-- The map `F (z, w) = (z, f z) - u w` in coordinates. -/
private theorem apply_eq_of_apply_eq_graph_sub (hF : ∀ p, F p = (p.1, f p.1) - u p.2)
    (z w : ℂ) : F (z, w) = (z - (u w).1, f z - (u w).2) := by
  rw [hF, Prod.mk_sub_mk]

/-- The map `F (z, w) = (z, f z) - u w` vanishes at every point `((u w).1, w)` where the disc `u`
meets the graph of `f`. -/
private theorem apply_eq_zero_of_apply_eq_graph_sub (hF : ∀ p, F p = (p.1, f p.1) - u p.2)
    {w : ℂ} (h : f (u w).1 = (u w).2) : F ((u w).1, w) = 0 := by
  rw [apply_eq_of_apply_eq_graph_sub hF, h, sub_self, sub_self, Prod.mk_zero_zero]

/-- Near the meeting point `((u w₀).1, w₀)`, the solutions of `F p = (0, -ε)` are the points
`((u w).1, w)` of the disc with `(u w).2 - f (u w).1 = ε`. -/
private theorem setOf_apply_eq_eq_image (hF : ∀ p, F p = (p.1, f p.1) - u p.2) (w₀ : ℂ) (r : ℝ)
    (ε : ℂ) :
    {p ∈ ball ((u w₀).1, w₀) r | F p = (0, -ε)} = (fun w ↦ ((u w).1, w)) ''
      {w ∈ ball w₀ r | (u w).1 ∈ ball (u w₀).1 r ∧ (u w).2 - f (u w).1 = ε} := by
  ext ⟨z, w⟩
  simp only [mem_ofPred_eq, mem_image, Prod.mk.injEq, ← ball_prod_same, mem_prod,
    apply_eq_of_apply_eq_graph_sub hF, sub_eq_zero]
  constructor
  · rintro ⟨⟨hz, hw⟩, rfl, hε⟩
    exact ⟨w, ⟨hw, hz, by linear_combination -hε⟩, rfl, rfl⟩
  · rintro ⟨w, ⟨hw, hz, hε⟩, rfl, rfl⟩
    exact ⟨⟨hz, hw⟩, rfl, by linear_combination -hε⟩

/-- If the disc `u` meets the graph of `f` at no point of a closed disc about `w₀` other than `w₀`,
then `((u w₀).1, w₀)` is the only solution of `F p = F ((u w₀).1, w₀)` in the closed ball of the
same radius. -/
private theorem eq_of_mem_closedBall_of_apply_eq (hF : ∀ p, F p = (p.1, f p.1) - u p.2) {w₀ : ℂ}
    (h : f (u w₀).1 = (u w₀).2) {r : ℝ}
    (hiso : ∀ w ∈ closedBall w₀ r, w ≠ w₀ → (u w).2 - f (u w).1 ≠ 0) {p : ℂ × ℂ}
    (hp : p ∈ closedBall ((u w₀).1, w₀) r) (hFp : F p = F ((u w₀).1, w₀)) :
    p = ((u w₀).1, w₀) := by
  obtain ⟨z, w⟩ := p
  rw [← closedBall_prod_same, mem_prod] at hp
  rw [apply_eq_zero_of_apply_eq_graph_sub hF h, apply_eq_of_apply_eq_graph_sub hF] at hFp
  simp only [Prod.mk_eq_zero, sub_eq_zero] at hFp
  obtain ⟨rfl, hfw⟩ := hFp
  obtain rfl : w = w₀ := by
    by_contra hne
    exact hiso w hp.2 hne (by rw [hfw, sub_self])
  rfl

/-- At a point `((u w).1, w)` of the disc where `f` and `u` are differentiable, the map
`F (z, w) = (z, f z) - u w` has the complex derivative `(s, t) ↦ s (1, f' z) - t u' w`. -/
private theorem hasFDerivAt_of_apply_eq_graph_sub (hF : ∀ p, F p = (p.1, f p.1) - u p.2) {w : ℂ}
    (hf : DifferentiableAt ℂ f (u w).1) (hu : DifferentiableAt ℂ u w) :
    HasFDerivAt F ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight ((1 : ℂ), deriv f (u w).1) -
      (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight (deriv u w)) ((u w).1, w) :=
  (((hasDerivAt_id _).prodMk hf.hasDerivAt).hasFDerivAt_comp_fst_sub_comp_snd
    hu.hasDerivAt).congr_of_eventuallyEq (.of_forall hF)

/-- At a point `((u w).1, w)` of the disc where `f` and `u` are differentiable and the derivative of
`φ w = (u w).2 - f (u w).1` is nonzero, the map `F (z, w) = (z, f z) - u w` has an injective
complex derivative. -/
private theorem exists_hasFDerivAt_injective_of_apply_eq_graph_sub
    (hF : ∀ p, F p = (p.1, f p.1) - u p.2) {w : ℂ} (hf : DifferentiableAt ℂ f (u w).1)
    (hu : DifferentiableAt ℂ u w) (hφ : deriv (fun w ↦ (u w).2 - f (u w).1) w ≠ 0) :
    ∃ L : ℂ × ℂ →L[ℂ] ℂ × ℂ, HasFDerivAt F L ((u w).1, w) ∧ Function.Injective L := by
  refine ⟨_, hasFDerivAt_of_apply_eq_graph_sub hF hf hu,
    LinearMap.injective_fst_smulRight_sub_snd_smulRight_iff.2
      (linearIndependent_pair_mk_one_iff.2 ?_)⟩
  rwa [← (hasDerivAt_snd_sub_comp_fst hf hu).deriv]

variable {n : ℕ} (o : HomologicalOrientation (ℂ × ℂ) (ℂ × ℂ) n)

/-- If the disc `u` runs inside the graph of `f` near `w₀`, their intersection at `u w₀` is not
isolated, and the local index there is `0`. -/
private theorem localIndex_eq_zero_of_apply_eq_graph_sub (hF : ∀ p, F p = (p.1, f p.1) - u p.2)
    {w₀ : ℂ} (h : f (u w₀).1 = (u w₀).2) (hu : ContinuousAt u w₀)
    (hconst : ∀ᶠ w in 𝓝 w₀, (u w).2 - f (u w).1 = 0) :
    o.localIndex o F ((u w₀).1, w₀) = 0 := by
  refine o.localIndex_of_frequently_eq o F ?_
  have htend : Tendsto (fun w ↦ ((u w).1, w)) (𝓝[≠] w₀) (𝓝[≠] ((u w₀).1, w₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(((continuousAt_fst.comp hu).prodMk
      continuousAt_id).tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact fun heq ↦ hw (congrArg Prod.snd heq)
  refine htend.frequently (Eventually.frequently ?_)
  filter_upwards [nhdsWithin_le_nhds hconst] with w hw
  rw [apply_eq_zero_of_apply_eq_graph_sub hF (sub_eq_zero.1 hw).symm,
    apply_eq_zero_of_apply_eq_graph_sub hF h]

variable (hn : finrank ℝ (ℂ × ℂ) = n)

include hn

/-- The isolated case of `localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub`, on a closed disc
of radius `r` about `w₀` on which `φ w = (u w).2 - f (u w).1` is analytic with `w₀` as its only zero
and only possible critical point, and along which `u` and `f` are analytic. -/
private theorem localIndex_eq_analyticOrderNatAt_of_closedBall
    (hF : ∀ p, F p = (p.1, f p.1) - u p.2) {w₀ : ℂ} (h : f (u w₀).1 = (u w₀).2) {r : ℝ}
    (hr : 0 < r) (hφr : AnalyticOnNhd ℂ (fun w ↦ (u w).2 - f (u w).1) (closedBall w₀ r))
    (hiso : ∀ w ∈ closedBall w₀ r, w ≠ w₀ → (u w).2 - f (u w).1 ≠ 0)
    (hder : ∀ w ∈ ball w₀ r, w ≠ w₀ → deriv (fun w ↦ (u w).2 - f (u w).1) w ≠ 0)
    (hgood : ∀ w ∈ ball w₀ r, AnalyticAt ℂ u w ∧ AnalyticAt ℂ f (u w).1) :
    o.localIndex o F ((u w₀).1, w₀) = analyticOrderNatAt (fun w ↦ (u w).2 - f (u w).1) w₀ := by
  have hφ₀ : (u w₀).2 - f (u w₀).1 = 0 := sub_eq_zero.2 h.symm
  -- The first coordinate of `u` maps the ball of radius `r'` into the ball of radius `r`. The map
  -- `F` stays `δ₂` away from `0` on the sphere of radius `r`, and below `δ₃` and `δ₄` the
  -- solutions of `φ w = ε` in the balls of radius `r` and `min r' r` are counted by the order.
  have ha := continuousAt_fst.comp (hgood w₀ (mem_ball_self hr)).1.continuousAt
  obtain ⟨r', hr', hr'a⟩ := Metric.mem_nhds_iff.1 (ha.preimage_mem_nhds (ball_mem_nhds _ hr))
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_le_norm_of_mem_sphere
    (f := fun p ↦ F p - F ((u w₀).1, w₀)) (F.continuous.continuousOn.sub continuousOn_const)
    fun p hp ↦ sub_ne_zero.2 fun heq ↦ ne_of_mem_sphere hp hr.ne'
      (eq_of_mem_closedBall_of_apply_eq hF h hiso (sphere_subset_closedBall hp) heq)
  obtain ⟨δ₃, hδ₃, hcnt₃⟩ := exists_ncard_eq_analyticOrderNatAt hφr hφ₀ hiso hder hr le_rfl
  obtain ⟨δ₄, hδ₄, hcnt₄⟩ := exists_ncard_eq_analyticOrderNatAt hφr hφ₀ hiso hder
    (lt_min hr' hr) (min_le_right _ _)
  obtain ⟨ε, hε, hεδ⟩ := NormedField.exists_norm_lt ℂ (lt_min (lt_min hδ₂ hδ₃) hδ₄)
  obtain ⟨hfin₃, hcard₃⟩ := hcnt₃ ε (norm_pos_iff.1 hε)
    (hεδ.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨-, hcard₄⟩ := hcnt₄ ε (norm_pos_iff.1 hε) (hεδ.trans_le (min_le_right _ _))
  -- The solutions of `F p = (0, -ε)` in the ball of radius `r` lie on the disc over solutions of
  -- `φ w = ε`, away from `w₀`, where `F` has an invertible complex derivative.
  have hS := setOf_apply_eq_eq_image hF w₀ r ε
  have hreg : ∀ p ∈ ball ((u w₀).1, w₀) r, F p = (0, -ε) →
      ∃ L : ℂ × ℂ →L[ℂ] ℂ × ℂ, HasFDerivAt F L p ∧ Function.Injective L := by
    intro p hp hFp
    have hmem : p ∈ {p ∈ ball ((u w₀).1, w₀) r | F p = (0, -ε)} := ⟨hp, hFp⟩
    rw [hS] at hmem
    obtain ⟨w, ⟨hw, -, hφw⟩, rfl⟩ := hmem
    obtain ⟨huw, hfw⟩ := hgood w hw
    exact exists_hasFDerivAt_injective_of_apply_eq_graph_sub hF hfw.differentiableAt
      huw.differentiableAt (hder w hw fun h' ↦ norm_pos_iff.1 hε (by rw [← hφw, h', hφ₀]))
  choose! L hL using hreg
  have hy : ‖((0 : ℂ), -ε) - F ((u w₀).1, w₀)‖ < δ₂ := by
    rw [apply_eq_zero_of_apply_eq_graph_sub hF h, sub_zero]
    simpa [Prod.norm_def] using hεδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  rw [o.localIndex_eq_ncard_of_hasFDerivAt hn hr.le hδ₂le
    (fun p hp ↦ eq_of_mem_closedBall_of_apply_eq hF h hiso (ball_subset_closedBall hp)) hy
    (fun p hp hFp ↦ (hL p hp hFp).1) (fun p hp hFp ↦ (hL p hp hFp).2), hS,
    ncard_image_of_injective _ fun _ _ hab ↦ congrArg Prod.snd hab]
  -- These solutions lie over the solutions of `φ w = ε` in the ball of radius `r`, and include
  -- those in the ball of radius `min r' r`: both have `m` elements.
  have hsub₁ : {w ∈ ball w₀ (min r' r) | (u w).2 - f (u w).1 = ε} ⊆
      {w ∈ ball w₀ r | (u w).1 ∈ ball (u w₀).1 r ∧ (u w).2 - f (u w).1 = ε} := fun w ⟨hw, hφw⟩ ↦
    ⟨ball_subset_ball (min_le_right _ _) hw, hr'a (ball_subset_ball (min_le_left _ _) hw), hφw⟩
  have hsub₂ : {w ∈ ball w₀ r | (u w).1 ∈ ball (u w₀).1 r ∧ (u w).2 - f (u w).1 = ε} ⊆
      {w ∈ ball w₀ r | (u w).2 - f (u w).1 = ε} := fun w ⟨hw, _, hφw⟩ ↦ ⟨hw, hφw⟩
  have h₁ := hcard₄ ▸ ncard_le_ncard hsub₁ (hfin₃.subset hsub₂)
  have h₂ := hcard₃ ▸ ncard_le_ncard hsub₂ hfin₃
  exact_mod_cast le_antisymm h₂ h₁

/-- **The local intersection number of a holomorphic graph and a holomorphic disc is an order of
vanishing.** Let `f : ℂ → ℂ` be holomorphic near `(u w₀).1` and `u : ℂ → ℂ²` near `w₀`, such that
the disc `u` meets the graph `z ↦ (z, f z)` at `u w₀`. Then their local intersection number, the
local index at `((u w₀).1, w₀)` of the map `F (z, w) = (z, f z) - u w`, is the order of vanishing at
`w₀` of `w ↦ (u w).2 - f (u w).1`. Both sides are `0` when `u` runs inside the graph near `w₀`. -/
theorem localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub
    (hF : ∀ p, F p = (p.1, f p.1) - u p.2) {w₀ : ℂ} (hf : AnalyticAt ℂ f (u w₀).1)
    (hu : AnalyticAt ℂ u w₀) (h : f (u w₀).1 = (u w₀).2) :
    o.localIndex o F ((u w₀).1, w₀) = analyticOrderNatAt (fun w ↦ (u w).2 - f (u w).1) w₀ := by
  have hφ₀ : (u w₀).2 - f (u w₀).1 = 0 := sub_eq_zero.2 h.symm
  have hφa := analyticAt_snd_sub_comp_fst hf hu
  rcases hφa.eventually_eq_or_eventually_ne (analyticAt_const (v := (0 : ℂ))) with hconst | hisol
  · rw [o.localIndex_eq_zero_of_apply_eq_graph_sub hF h hu.continuousAt hconst, analyticOrderNatAt,
      analyticOrderAt_eq_top.2 hconst, ENat.toNat_top, Nat.cast_zero]
  -- A radius `r` below which `u` and `f` are analytic along the disc, and on whose closed ball
  -- `φ w = (u w).2 - f (u w).1` is analytic with `w₀` as its only zero and only critical point.
  obtain ⟨r₁, hr₁, hgood⟩ := Metric.eventually_nhds_iff_ball.1 (hu.eventually_analyticAt.and
    ((continuousAt_fst.comp hu.continuousAt).tendsto.eventually hf.eventually_analyticAt))
  obtain ⟨r, ⟨hφr, hisor, hderr⟩, hr, hrr₁⟩ :=
    ((hφa.eventually_analyticOnNhd_closedBall_and_ne_and_deriv_ne_zero
      (hisol.mono fun w hw ↦ by rwa [hφ₀])).and (Ioo_mem_nhdsGT hr₁)).exists
  exact o.localIndex_eq_analyticOrderNatAt_of_closedBall hn hF h hr hφr
    (fun w hw hne ↦ by simpa [hφ₀] using hisor w hw hne) hderr
    (fun w hw ↦ hgood w (ball_subset_ball hrr₁.le hw))

/-- **Two holomorphic graphs meet with their order of contact.** If `f` and `g` are holomorphic
near `z₀` and `f z₀ = g z₀`, the local intersection number at `(z₀, z₀)` of the graphs
`z ↦ (z, f z)` and `w ↦ (w, g w)`, the local index of `F (z, w) = (z, f z) - (w, g w)`, is the
order of vanishing of `g - f` at `z₀`. It is `0` when the graphs agree near `z₀`. -/
theorem localIndex_eq_analyticOrderNatAt_sub_of_apply_eq_graph_sub_graph {g : ℂ → ℂ}
    (hF : ∀ p, F p = (p.1, f p.1) - (p.2, g p.2)) {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hg : AnalyticAt ℂ g z₀) (h : f z₀ = g z₀) :
    o.localIndex o F (z₀, z₀) = analyticOrderNatAt (fun z ↦ g z - f z) z₀ :=
  o.localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub hn (u := fun w ↦ (w, g w)) hF hf
    (analyticAt_id.prod hg) h

/-- **A transverse intersection, and only a transverse one, counts `1`.** In the setting of
`localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub`, the local intersection number of the graph
of `f` and the disc `u` at `u w₀` is `1` exactly when their tangent vectors `(1, f' ((u w₀).1))`
and `u' w₀` are linearly independent over `ℂ`. -/
theorem localIndex_eq_one_iff_of_apply_eq_graph_sub (hF : ∀ p, F p = (p.1, f p.1) - u p.2)
    {w₀ : ℂ} (hf : AnalyticAt ℂ f (u w₀).1) (hu : AnalyticAt ℂ u w₀)
    (h : f (u w₀).1 = (u w₀).2) :
    o.localIndex o F ((u w₀).1, w₀) = 1 ↔
      LinearIndependent ℂ ![((1 : ℂ), deriv f (u w₀).1), deriv u w₀] := by
  have hφ₀ : (u w₀).2 - f (u w₀).1 = 0 := sub_eq_zero.2 h.symm
  have key := (analyticAt_snd_sub_comp_fst hf hu).analyticOrderAt_sub_eq_one_iff_deriv_ne_zero
  simp only [hφ₀, sub_zero] at key
  rw [(hasDerivAt_snd_sub_comp_fst hf.differentiableAt hu.differentiableAt).deriv] at key
  rw [o.localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub hn hF hf hu h, Nat.cast_eq_one,
    linearIndependent_pair_mk_one_iff, ← key, analyticOrderNatAt]
  exact ENat.toNat_eq_iff one_ne_zero

/-- **Tangential intersections count at least `2`.** In the setting of
`localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub`, suppose that the disc `u` does not run
inside the graph of `f` near `w₀`, so that their intersection at `u w₀` is isolated, and that it is
not transverse: the tangent vectors `(1, f' ((u w₀).1))` and `u' w₀` are linearly dependent over
`ℂ`. Then the local intersection number is at least `2`. -/
theorem two_le_localIndex_of_apply_eq_graph_sub (hF : ∀ p, F p = (p.1, f p.1) - u p.2) {w₀ : ℂ}
    (hf : AnalyticAt ℂ f (u w₀).1) (hu : AnalyticAt ℂ u w₀) (h : f (u w₀).1 = (u w₀).2)
    (hiso : ¬ ∀ᶠ w in 𝓝 w₀, (u w).2 = f (u w).1)
    (htan : ¬ LinearIndependent ℂ ![((1 : ℂ), deriv f (u w₀).1), deriv u w₀]) :
    2 ≤ o.localIndex o F ((u w₀).1, w₀) := by
  have hne₁ : o.localIndex o F ((u w₀).1, w₀) ≠ 1 := fun h₁ ↦
    htan ((o.localIndex_eq_one_iff_of_apply_eq_graph_sub hn hF hf hu h).1 h₁)
  have hne₀ : analyticOrderNatAt (fun w ↦ (u w).2 - f (u w).1) w₀ ≠ 0 := by
    intro hzero
    rcases ENat.toNat_eq_zero.1 hzero with h₀ | htop
    · rcases analyticOrderAt_eq_zero.1 h₀ with h₀ | h₀
      · exact h₀ (analyticAt_snd_sub_comp_fst hf hu)
      · exact h₀ (sub_eq_zero.2 h.symm)
    · exact hiso ((analyticOrderAt_eq_top.1 htop).mono fun w hw ↦ sub_eq_zero.1 hw)
  rw [o.localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub hn hF hf hu h] at hne₁ ⊢
  omega

/-- **Critical branches count at least `2`.** If the disc `u` is critical at `w₀`, `u' w₀ = 0`,
and meets the graph of `f` at `u w₀` without running inside it near `w₀`, then their local
intersection number there is at least `2`. -/
theorem two_le_localIndex_of_apply_eq_graph_sub_of_deriv_eq_zero
    (hF : ∀ p, F p = (p.1, f p.1) - u p.2) {w₀ : ℂ} (hf : AnalyticAt ℂ f (u w₀).1)
    (hu : AnalyticAt ℂ u w₀) (h : f (u w₀).1 = (u w₀).2)
    (hiso : ¬ ∀ᶠ w in 𝓝 w₀, (u w).2 = f (u w).1) (hcrit : deriv u w₀ = 0) :
    2 ≤ o.localIndex o F ((u w₀).1, w₀) :=
  o.two_le_localIndex_of_apply_eq_graph_sub hn hF hf hu h hiso fun hli ↦
    hli.ne_zero 1 (by simp [hcrit])

/-! #### Changes of coordinates and immersed branches -/

/-- **Local intersection numbers do not depend on the parametrizations of the discs.** If
`φ₁` and `φ₂` are strictly complex differentiable at `z₀` and `w₀` with nonzero derivatives, as
holomorphic reparametrizations are, then the local intersection number of the discs `u₁ ∘ φ₁` and
`u₂ ∘ φ₂` at `(z₀, w₀)`, the local index of `G (z, w) = u₁ (φ₁ z) - u₂ (φ₂ w)`, is that of `u₁` and
`u₂` at `(φ₁ z₀, φ₂ w₀)`, the local index of `F (z, w) = u₁ z - u₂ w`. -/
theorem localIndex_eq_of_apply_eq_comp_sub_comp {F G : C(ℂ × ℂ, ℂ × ℂ)} {u₁ u₂ : ℂ → ℂ × ℂ}
    {φ₁ φ₂ : C(ℂ, ℂ)} (hF : ∀ p, F p = u₁ p.1 - u₂ p.2)
    (hG : ∀ p, G p = u₁ (φ₁ p.1) - u₂ (φ₂ p.2)) {z₀ w₀ a b : ℂ} (h₁ : HasStrictDerivAt φ₁ a z₀)
    (h₂ : HasStrictDerivAt φ₂ b w₀) (ha : a ≠ 0) (hb : b ≠ 0) :
    o.localIndex o G (z₀, w₀) = o.localIndex o F (φ₁ z₀, φ₂ w₀) := by
  have hGF : G = F.comp (φ₁.prodMap φ₂) := ContinuousMap.ext fun p ↦ by simp [hF, hG]
  have hd : HasStrictFDerivAt (φ₁.prodMap φ₂)
      ((((1 : ℂ →L[ℂ] ℂ).smulRight a).prodMap ((1 : ℂ →L[ℂ] ℂ).smulRight b)).restrictScalars ℝ)
      (z₀, w₀) :=
    (HasStrictFDerivAt.prodMap (z₀, w₀) h₁ h₂).restrictScalars ℝ
  rw [hGF, o.localIndex_comp_eq_of_hasStrictFDerivAt o hn hd]
  · simp
  · rintro ⟨z, w⟩ ⟨z', w'⟩ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    simp only [ContinuousLinearMap.coe_prodMap', Prod.map_fst, Prod.map_snd,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul] at h₁ h₂
    simp [mul_right_cancel₀ ha h₁, mul_right_cancel₀ hb h₂]

/-- **The local intersection number with a disc running in a holomorphic graph.** Let `u₁` be a
disc whose first coordinate is strictly complex differentiable at `z₀` with nonzero derivative, and
which runs near `z₀` in the graph `{(z, f z)}` of a function `f` holomorphic at `(u₁ z₀).1`. Then
the local intersection number of `u₁` with a holomorphic disc `u₂` at `u₁ z₀ = u₂ w₀`, the local
index at `(z₀, w₀)` of `F (z, w) = u₁ z - u₂ w`, is the order of vanishing at `w₀` of
`w ↦ (u₂ w).2 - f (u₂ w).1`. -/
theorem localIndex_eq_analyticOrderNatAt_of_apply_eq_sub_of_eventually_snd_eq
    {F : C(ℂ × ℂ, ℂ × ℂ)} {u₁ u₂ : ℂ → ℂ × ℂ} (hF : ∀ p, F p = u₁ p.1 - u₂ p.2) {z₀ w₀ a : ℂ}
    (h₁ : HasStrictDerivAt (fun z ↦ (u₁ z).1) a z₀) (ha : a ≠ 0)
    (hf : AnalyticAt ℂ f (u₁ z₀).1) (hgraph : ∀ᶠ z in 𝓝 z₀, (u₁ z).2 = f (u₁ z).1)
    (h₂ : AnalyticAt ℂ u₂ w₀) (h : u₁ z₀ = u₂ w₀) :
    o.localIndex o F (z₀, w₀) = analyticOrderNatAt (fun w ↦ (u₂ w).2 - f (u₂ w).1) w₀ := by
  -- Reparametrizing `u₁` by the inverse of its first coordinate turns it into the graph of `f`, so
  -- this is `localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub` read through
  -- `localIndex_eq_of_apply_eq_comp_sub_comp`.
  set c := (u₁ z₀).1
  obtain ⟨hu₁, hu₂⟩ := continuous_and_continuous_of_continuous_sub (F.continuous.congr hF)
  have hg : Continuous fun z ↦ (u₁ z).1 := continuous_fst.comp hu₁
  -- Cut `f` off outside a closed ball about `c` on which it is continuous, so that the graph of the
  -- cut-off function `f₀` is the image of a continuous map.
  obtain ⟨r₀, hr₀, hfr₀⟩ := Metric.eventually_nhds_iff_ball.1 hf.eventually_analyticAt
  set r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  set f₀ : ℂ → ℂ := fun y ↦ f (centeredRadialRetraction c r y)
  have hf₀ : Continuous f₀ := by
    refine ContinuousOn.comp_continuous (s := closedBall c r) (fun y hy ↦ ?_)
      (lipschitzWith_centeredRadialRetraction hr.le).continuous
      (centeredRadialRetraction_mem_closedBall hr.le)
    exact (hfr₀ y (closedBall_subset_ball (half_lt_self hr₀) hy)).continuousAt.continuousWithinAt
  have hf₀f : f₀ =ᶠ[𝓝 c] f :=
    (centeredRadialRetraction_eventuallyEq_id (mem_ball_self hr)).fun_comp f
  set F₀ : C(ℂ × ℂ, ℂ × ℂ) := ⟨fun p ↦ (p.1, f₀ p.1) - u₂ p.2, by fun_prop⟩
  set g : C(ℂ, ℂ) := ⟨fun z ↦ (u₁ z).1, hg⟩
  -- Near `(z₀, w₀)`, `F` is `F₀` read through the reparametrization `g × id`.
  have hFG : F =ᶠ[𝓝 (z₀, w₀)] F₀.comp (g.prodMap (ContinuousMap.id ℂ)) := by
    have hz : ∀ᶠ z in 𝓝 z₀, (u₁ z).2 = f (u₁ z).1 ∧ f₀ (u₁ z).1 = f (u₁ z).1 :=
      hgraph.and (hg.continuousAt.tendsto.eventually hf₀f)
    filter_upwards [hz.prod_inl_nhds w₀] with p hp
    simp [hF, F₀, g, hp.2, ← hp.1]
  rw [o.localIndex_congr o hn hFG, o.localIndex_eq_of_apply_eq_comp_sub_comp hn (F := F₀)
    (u₁ := fun z ↦ (z, f₀ z)) (u₂ := u₂) (fun _ ↦ rfl) (fun _ ↦ rfl) (φ₁ := g) h₁
    (hasStrictDerivAt_id w₀) ha one_ne_zero]
  have hc : (u₂ w₀).1 = c := by rw [← h]
  have hφ : (u₂ w₀).2 = f₀ (u₂ w₀).1 := by
    rw [hc, hf₀f.self_of_nhds, ← hgraph.self_of_nhds, h]
  have key := o.localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub hn (F := F₀) (fun _ ↦ rfl)
    (hc ▸ hf.congr hf₀f.symm) h₂ hφ.symm
  rw [hc] at key
  -- The cut-off does not change the order of vanishing, since `u₂` stays near `c` near `w₀`.
  have hcongr : (fun w ↦ (u₂ w).2 - f₀ (u₂ w).1) =ᶠ[𝓝 w₀] fun w ↦ (u₂ w).2 - f (u₂ w).1 := by
    have : Tendsto (fun w ↦ (u₂ w).1) (𝓝 w₀) (𝓝 c) := hc ▸ (continuous_fst.comp hu₂).tendsto w₀
    filter_upwards [this.eventually hf₀f] with w hw
    rw [hw]
  simpa [g, analyticOrderNatAt, analyticOrderAt_congr hcongr] using key

/-- **The local intersection number with a disc running in a holomorphic graph over the second
coordinate.** Let `u₁` be a disc whose second coordinate is strictly complex differentiable at
`z₀` with nonzero derivative, and which runs near `z₀` in the graph `{(f w, w)}` of a function `f`
holomorphic at `(u₁ z₀).2`. Then the local intersection number of `u₁` with a holomorphic disc
`u₂` at `u₁ z₀ = u₂ w₀` is the order of vanishing at `w₀` of `w ↦ (u₂ w).1 - f (u₂ w).2`.

If the holomorphic disc `u₁` is immersed, it has a coordinate of nonzero derivative, so by the
holomorphic inverse function theorem it runs in a holomorphic graph over the first or the second
coordinate, and one of the two statements applies. -/
theorem localIndex_eq_analyticOrderNatAt_of_apply_eq_sub_of_eventually_fst_eq
    {F : C(ℂ × ℂ, ℂ × ℂ)} {u₁ u₂ : ℂ → ℂ × ℂ} (hF : ∀ p, F p = u₁ p.1 - u₂ p.2) {z₀ w₀ a : ℂ}
    (h₁ : HasStrictDerivAt (fun z ↦ (u₁ z).2) a z₀) (ha : a ≠ 0)
    (hf : AnalyticAt ℂ f (u₁ z₀).2) (hgraph : ∀ᶠ z in 𝓝 z₀, (u₁ z).1 = f (u₁ z).2)
    (h₂ : AnalyticAt ℂ u₂ w₀) (h : u₁ z₀ = u₂ w₀) :
    o.localIndex o F (z₀, w₀) = analyticOrderNatAt (fun w ↦ (u₂ w).1 - f (u₂ w).2) w₀ := by
  -- Exchanging the two coordinates of `ℂ²` is a unitary change of coordinates of the target, which
  -- does not change local intersection numbers, and reduces this to the graph over the first one.
  set S : ℂ × ℂ →L[ℂ] ℂ × ℂ := (ContinuousLinearEquiv.prodComm ℂ ℂ ℂ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
  set F' : C(ℂ × ℂ, ℂ × ℂ) := ContinuousMap.prodSwap.comp F
  have hF' (p : ℂ × ℂ) : F' p = S (u₁ p.1) - S (u₂ p.2) := by
    ext <;> simp [F', S, hF]
  have hS : HasStrictFDerivAt S (S.restrictScalars ℝ) (u₁ z₀) :=
    (S.restrictScalars ℝ).hasStrictFDerivAt
  obtain ⟨hu₁, hu₂⟩ := continuous_and_continuous_of_continuous_sub (F.continuous.congr hF)
  rw [← o.localIndex_eq_of_apply_eq_sub_of_hasStrictFDerivAt o hn hF hF'
    (hu₁.comp continuous_fst).continuousAt (hu₂.comp continuous_snd).continuousAt h hS
    (ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).injective]
  exact o.localIndex_eq_analyticOrderNatAt_of_apply_eq_sub_of_eventually_snd_eq hn
    (u₁ := fun z ↦ (u₁ z).swap) (u₂ := fun w ↦ (u₂ w).swap)
    (fun p ↦ by ext <;> simp [F', hF]) h₁ ha hf hgraph ((S.analyticAt _).comp h₂) (by rw [h])

/-! #### Examples -/

/-- The line `w = 0` and the curve `w = z ^ (k + 1)` of `ℂ²` meet at the origin with local
intersection number `k + 1`; for `k = 1` this is the parabola, tangent to the line. -/
example (k : ℕ) :
    o.localIndex o ⟨fun p ↦ (p.1 - p.2, -p.2 ^ (k + 1)), by fun_prop⟩ (0, 0) = k + 1 := by
  rw [o.localIndex_eq_analyticOrderNatAt_sub_of_apply_eq_graph_sub_graph hn (f := fun _ ↦ 0)
    (g := (· ^ (k + 1))) (fun p ↦ by simp [Prod.mk_sub_mk]) analyticAt_const
    (analyticAt_id.pow _) (by simp)]
  have hpow : (fun z : ℂ ↦ z ^ (k + 1) - 0) = (· - 0) ^ (k + 1) := funext fun z ↦ by simp
  rw [analyticOrderNatAt, hpow, analyticOrderAt_centeredMonomial, ENat.toNat_natCast]
  exact Nat.cast_succ k

/-- The line `w = 0` and the cusp `w ↦ (w², w³)` of `ℂ²`, critical at `0`, meet at the origin with
local intersection number `3`. -/
example : o.localIndex o ⟨fun p ↦ (p.1 - p.2 ^ 2, -p.2 ^ 3), by fun_prop⟩ (0, 0) = 3 := by
  have := o.localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub hn
    (F := ⟨fun p ↦ (p.1 - p.2 ^ 2, -p.2 ^ 3), by fun_prop⟩) (f := fun _ ↦ 0)
    (u := fun w ↦ (w ^ 2, w ^ 3)) (w₀ := 0) (fun p ↦ by simp [Prod.mk_sub_mk]) analyticAt_const
    (by fun_prop) (by simp)
  have hpow : (fun w : ℂ ↦ ((w ^ 2, w ^ 3) : ℂ × ℂ).2 - 0) = (· - 0) ^ 3 := funext fun w ↦ by simp
  simp only [hpow, analyticOrderNatAt, analyticOrderAt_centeredMonomial] at this
  simpa using this

/-- The line `w = z` and the cusp `w ↦ (w², w³)` of `ℂ²` meet at the origin with local intersection
number `2`: the cusp has a horizontal tangent cone, transverse to the line, but it is critical. -/
example : o.localIndex o ⟨fun p ↦ (p.1 - p.2 ^ 2, p.1 - p.2 ^ 3), by fun_prop⟩ (0, 0) = 2 := by
  have := o.localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub hn
    (F := ⟨fun p ↦ (p.1 - p.2 ^ 2, p.1 - p.2 ^ 3), by fun_prop⟩) (f := id)
    (u := fun w ↦ (w ^ 2, w ^ 3)) (w₀ := 0) (fun p ↦ by simp [Prod.mk_sub_mk]) analyticAt_id
    (by fun_prop) (by simp)
  have hord : analyticOrderAt (fun w : ℂ ↦ ((w ^ 2, w ^ 3) : ℂ × ℂ).2 - id (w ^ 2, w ^ 3).1) 0 =
      (2 : ℕ) :=
    (AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)).2
      ⟨fun w ↦ w - 1, by fun_prop, by norm_num,
        .of_forall fun w ↦ by simp only [id, smul_eq_mul]; ring⟩
  rw [analyticOrderNatAt, hord, ENat.toNat_natCast] at this
  simpa using this

/-- The vertical line `z = 0` and the curve `z = w²` of `ℂ²`, tangent to it at the origin, meet
there with local intersection number `2`. The line is a graph over the second coordinate, so the
intersection number is computed after exchanging the coordinates. -/
example : o.localIndex o ⟨fun p ↦ (-p.2 ^ 2, p.1 - p.2), by fun_prop⟩ (0, 0) = 2 := by
  have := o.localIndex_eq_analyticOrderNatAt_of_apply_eq_sub_of_eventually_fst_eq hn
    (F := ⟨fun p ↦ (-p.2 ^ 2, p.1 - p.2), by fun_prop⟩) (f := fun _ ↦ 0)
    (u₁ := fun z ↦ (0, z)) (u₂ := fun w ↦ (w ^ 2, w)) (z₀ := 0) (w₀ := 0)
    (fun p ↦ by simp [Prod.mk_sub_mk]) (hasStrictDerivAt_id 0) one_ne_zero analyticAt_const
    (.of_forall fun _ ↦ rfl) (by fun_prop) (by simp)
  have hpow : (fun w : ℂ ↦ ((w ^ 2, w) : ℂ × ℂ).1 - 0) = (· - 0) ^ 2 := funext fun w ↦ by simp
  simp only [hpow, analyticOrderNatAt, analyticOrderAt_centeredMonomial] at this
  simpa using this

end Graph

end HomologicalOrientation

end TauCeti
