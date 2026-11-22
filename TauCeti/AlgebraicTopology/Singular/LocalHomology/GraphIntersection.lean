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
import TauCeti.LinearAlgebra.LinearIndependent.Prod
import TauCeti.LinearAlgebra.LinearMap.Coprod

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
multiplicities of tangent and critical branches of pseudoholomorphic curves in a four-manifold. A
disc immersed at a point is a graph over its tangent line after a unitary change of coordinates of
`ℂ²`; the invariance of local intersection numbers under such changes of coordinates, which would
extend these statements to every pair of discs one of which is immersed, is not proved here.

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

The examples at the end of the file compute the local intersection numbers of the line `w = 0` with
the curves `w = z ^ k` (it is `k`, and in particular `2` for the parabola) and of the lines `w = 0`
and `w = z` with the cusp `w ↦ (w², w³)` (they are `3` and `2`).

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

include hn in
/-- The isolated case of `localIndex_eq_analyticOrderNatAt_of_apply_eq_graph_sub`, on a closed disc
of radius `r` about `w₀` on which `φ w = (u w).2 - f (u w).1` is analytic with `w₀` as its only zero
and only possible critical point, and along which `u` and `f` are analytic. -/
private theorem localIndex_eq_analyticOrderNatAt_of_closedBall
    (hF : ∀ p, F p = (p.1, f p.1) - u p.2) {w₀ : ℂ} (h : f (u w₀).1 = (u w₀).2) {r : ℝ}
    (hr : 0 < r) (hφr : AnalyticOnNhd ℂ (fun w ↦ (u w).2 - f (u w).1) (closedBall w₀ r))
    (hiso : ∀ w ∈ closedBall w₀ r, w ≠ w₀ → (u w).2 - f (u w).1 ≠ 0)
    (hder : ∀ w ∈ ball w₀ r, w ≠ w₀ → deriv (fun w ↦ (u w).2 - f (u w).1) w ≠ 0)
    (hgood : ∀ w ∈ ball w₀ r, AnalyticAt ℂ u w ∧ AnalyticAt ℂ f (u w).1)
    (ha : ContinuousAt (fun w ↦ (u w).1) w₀) :
    o.localIndex o F ((u w₀).1, w₀) = analyticOrderNatAt (fun w ↦ (u w).2 - f (u w).1) w₀ := by
  have hφ₀ : (u w₀).2 - f (u w₀).1 = 0 := sub_eq_zero.2 h.symm
  -- The first coordinate of `u` maps the ball of radius `r'` into the ball of radius `r`. The map
  -- `F` stays `δ₂` away from `0` on the sphere of radius `r`, and below `δ₃` and `δ₄` the
  -- solutions of `φ w = ε` in the balls of radius `r` and `min r' r` are counted by the order.
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
  rw [o.localIndex_eq_ncard_of_hasFDerivAt hn hr hδ₂ hδ₂le
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

include hn in
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
    (fun w hw ↦ hgood w (ball_subset_ball hrr₁.le hw)) (continuousAt_fst.comp hu.continuousAt)

include hn in
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

include hn in
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

include hn in
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

include hn in
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

/-! #### Examples -/

include hn in
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

include hn in
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

include hn in
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

end Graph

end HomologicalOrientation

end TauCeti
