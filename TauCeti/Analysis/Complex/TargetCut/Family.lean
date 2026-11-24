/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Zeros
public import TauCeti.Analysis.Complex.TargetCut
public import TauCeti.LinearAlgebra.AffineSpace.MarkingStabilizer
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Transverse target cuts along families of sphere maps

A sphere component `u : ℂ → X`, with a special point at `∞`, is stabilized by the full preimage
`u⁻¹(D)` of a target cut `D` that it meets transversally (`TauCeti.IsTransverseCutAt`): the points
of `u⁻¹(D)` are added to the domain as an unordered set of further marked points, which is finite
(`TauCeti.finite_preimage_of_isTransverseCutAt`) and makes the isotropy of `u` finite
(`TauCeti.card_markedIsotropy_dvd_factorial`). A chart of a moduli space of such maps around `u`
uses one stabilization for all the maps `u p` of a family near `u = u p₀`. For this the number of
cut points must not change along the family, the cut points must move continuously, and every
nearby map must still meet `D` transversally. This file proves that this holds near `p₀`.

The cut `D` is closed and is cut out near every point of `u p₀⁻¹(D)` by a local defining function:
near `u p₀ z` it is the zero set of a function `g` with values in `ℂ`, such that the compositions
`g ∘ u p` are differentiable with derivatives depending continuously on `(p, w)` and the
derivative of `g ∘ u p₀` at `z` is invertible. Near `z` the cut points of `u p` are then the zeros
of `g ∘ u p`, and by the persistence of nondegenerate zeros
(`IsCompact.eventually_exists_equiv_sep_eq_zero`) each map `u p` near `u p₀` has exactly one cut
point near `z`, at which it is again transverse. Away from these points neither `u p₀` nor `u p`
for `p` near `p₀` meets `D`: near `∞` by the hypothesis that, for `p` near `p₀`, the maps `u p` do
not meet `D` outside a common compact set (uniformly near `∞`), and on that compact set by
continuity. Hence:

* every map `u p` with `p` near `p₀` meets `D` transversally at each of its cut points, and its cut
  points are in a bijection with those of `u p₀` moving each by at most any prescribed `ε > 0`
  (`TauCeti.eventually_isTransverseCutAt_and_exists_equiv_preimage`);
* the number of cut points is finite and locally constant
  (`TauCeti.eventually_finite_preimage_and_ncard_eq`);
* if the marked points `M` of the component together with the cut points of `u p₀` contain two
  distinct points, the isotropy of every `u p` near `u p₀` is finite of order dividing
  `|u p₀⁻¹(D)|!` (`TauCeti.eventually_card_markedIsotropy_dvd_factorial`), the same bound for the
  whole family.

The hypothesis on the cut points of `u p₀` is `TauCeti.IsTransverseCutFamilyAt`. It holds for maps
into a manifold `M` depending in `C¹` on a parameter in a normed space, with `D` cut out by `C¹`
local defining functions `g` whose differentials composed with those of `u p₀` are injective at
the cut points (`TauCeti.isTransverseCutFamilyAt_of_contMDiffOn`), which is transversality of
`u p₀` to a codimension-two submanifold `D`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Section 9.2, on stabilization by the full
  preimage of a codimension-two submanifold transverse to the map.
* K. Cieliebak and K. Mohnke, *Symplectic hypersurfaces and transversality in Gromov–Witten
  theory*, J. Symplectic Geom. 5 (2007), 281–356, Section 6, on the stabilization of domains by
  transverse preimages of a hypersurface along families of maps.
* V. Guillemin and A. Pollack, *Differential topology*, Prentice-Hall, 1974, Chapter 1, §6, on
  the stability of transversality.
-/

public section

noncomputable section

open Filter Metric Set Topology
open scoped Manifold Nat

namespace TauCeti

section General

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] {u : P → ℂ → X} {s : Set P}
  {p₀ : P} {D : Set X}

/-- The data used to follow a cut point `z` of `u p₀` along the family `u` over the parameters `s`:
near `u p₀ z` the set `D` is the zero set of a continuous function `g : X → ℂ` on an open set `W`,
the compositions `g ∘ u p`, `p ∈ s`, are differentiable at the points that `u p` maps into `W`,
with derivatives continuous in `(p, w)` there, and the derivative of `g ∘ u p₀` at `z` is
invertible. It implies that `u p₀` meets `D` transversally at `z`
(`TauCeti.IsTransverseCutFamilyAt.isTransverseCutAt`), and it holds for `C¹` families of maps
into a manifold and `C¹` local defining functions
(`TauCeti.isTransverseCutFamilyAt_of_contMDiffOn`). -/
def IsTransverseCutFamilyAt (u : P → ℂ → X) (s : Set P) (D : Set X) (p₀ : P) (z : ℂ) : Prop :=
  ∃ (W : Set X) (g : X → ℂ), IsOpen W ∧ u p₀ z ∈ W ∧ (∀ x ∈ W, x ∈ D ↔ g x = 0) ∧
    ContinuousOn g W ∧ (∀ p ∈ s, ∀ w, u p w ∈ W → DifferentiableAt ℝ (g ∘ u p) w) ∧
    ContinuousOn (fun q : P × ℂ ↦ fderiv ℝ (g ∘ u q.1) q.2) {q | q.1 ∈ s ∧ u q.1 q.2 ∈ W} ∧
    (fderiv ℝ (g ∘ u p₀) z).IsInvertible

/-- Unfold `IsTransverseCutFamilyAt u s D p₀ z` into the local defining function `g` of `D` on
the open set `W` and the regularity of the compositions `g ∘ u p`. -/
theorem isTransverseCutFamilyAt_iff {z : ℂ} : IsTransverseCutFamilyAt u s D p₀ z ↔
    ∃ (W : Set X) (g : X → ℂ), IsOpen W ∧ u p₀ z ∈ W ∧ (∀ x ∈ W, x ∈ D ↔ g x = 0) ∧
      ContinuousOn g W ∧ (∀ p ∈ s, ∀ w, u p w ∈ W → DifferentiableAt ℝ (g ∘ u p) w) ∧
      ContinuousOn (fun q : P × ℂ ↦ fderiv ℝ (g ∘ u q.1) q.2) {q | q.1 ∈ s ∧ u q.1 q.2 ∈ W} ∧
      (fderiv ℝ (g ∘ u p₀) z).IsInvertible :=
  Iff.rfl

/-- A cut point that can be followed along the family is a transverse cut point of `u p₀`. -/
theorem IsTransverseCutFamilyAt.isTransverseCutAt {z : ℂ} (hp₀ : p₀ ∈ s)
    (h : IsTransverseCutFamilyAt u s D p₀ z) : IsTransverseCutAt (u p₀) D z := by
  obtain ⟨W, g, hW, hzW, hWD, -, hgd, -, hinv⟩ := h
  exact .of_isInvertible_fderiv (eventually_of_mem (hW.mem_nhds hzW) hWD) (hgd p₀ hp₀ z hzW) hinv

/-- **The cut point near a transverse cut point persists.** Let `D` be cut out by `g` on an open
set `W`, with `g ∘ u p` differentiable where `u p` takes values in `W` and its derivative continuous
in `(p, w)`, and let `z` be the only cut point of `u p₀` in a closed ball `B` around `z` which
`u p` maps into `W` for all `p ∈ s` near `p₀`, with `g ∘ u p₀` of invertible derivative at `z`.
Then for `p ∈ s` near `p₀` the map `u p` has exactly one cut point in `B`, at which it meets `D`
transversally. -/
private theorem eventually_exists_inter_closedBall_eq_singleton (hp₀ : p₀ ∈ s)
    (hu : ContinuousOn (Function.uncurry u) (s ×ˢ univ)) {W : Set X} {g : X → ℂ}
    (hW : IsOpen W) (hWD : ∀ x ∈ W, x ∈ D ↔ g x = 0) (hg : ContinuousOn g W)
    (hgd : ∀ p ∈ s, ∀ w, u p w ∈ W → DifferentiableAt ℝ (g ∘ u p) w)
    (hgd' : ContinuousOn (fun q : P × ℂ ↦ fderiv ℝ (g ∘ u q.1) q.2)
      {q | q.1 ∈ s ∧ u q.1 q.2 ∈ W})
    {z : ℂ} (hz : (fderiv ℝ (g ∘ u p₀) z).IsInvertible) {r : ℝ} (hr : 0 < r)
    (hsW : ∀ᶠ p in 𝓝[s] p₀, ∀ w ∈ closedBall z r, u p w ∈ W)
    (hrD : u p₀ ⁻¹' D ∩ closedBall z r = {z}) :
    ∀ᶠ p in 𝓝[s] p₀, ∃ w, u p ⁻¹' D ∩ closedBall z r = {w} ∧ IsTransverseCutAt (u p) D w := by
  have hK : IsCompact (closedBall z r) := isCompact_closedBall z r
  set s' := {p ∈ s | ∀ w ∈ closedBall z r, u p w ∈ W}
  have hs' : s' ∈ 𝓝[s] p₀ := inter_mem self_mem_nhdsWithin hsW
  have hle : 𝓝[s] p₀ ≤ 𝓝[s'] p₀ := le_inf nhdsWithin_le_nhds (le_principal_iff.2 hs')
  -- On the ball, the cut points of `u p` are the zeros of `g ∘ u p`.
  have hzero (p) (hp : p ∈ s') : u p ⁻¹' D ∩ closedBall z r =
      {w ∈ closedBall z r | (g ∘ u p) w = 0} := by
    ext w
    exact ⟨fun ⟨hwD, hw⟩ ↦ ⟨hw, (hWD _ (hp.2 w hw)).1 hwD⟩,
      fun ⟨hw, hw0⟩ ↦ ⟨(hWD _ (hp.2 w hw)).2 hw0, hw⟩⟩
  have hp₀' : p₀ ∈ s' := ⟨hp₀, hsW.self_of_nhdsWithin hp₀⟩
  have h := hK.eventually_exists_equiv_sep_eq_zero (𝕜 := ℝ) (u := fun p ↦ g ∘ u p) (s := s')
    (fun p hp w hw ↦ hgd p hp.1 w (hp.2 w hw))
    (hg.comp (hu.mono (prod_mono (sep_subset _ _) (subset_univ _))) fun q hq ↦ hq.1.2 _ hq.2)
    (hgd'.mono fun q hq ↦ ⟨hq.1.1, hq.1.2 _ hq.2⟩) hp₀' (fun w hw hw0 ↦ ?_) one_pos
  · filter_upwards [h.filter_mono hle, hs'] with p hpe hp
    obtain ⟨hnd, e, -⟩ := hpe
    have h1 : {w ∈ closedBall z r | (g ∘ u p) w = 0}.ncard = 1 := by
      rw [← Set.ncard_congr' e, ← hzero p₀ hp₀', hrD, ncard_singleton]
    obtain ⟨w, hw⟩ := ncard_eq_one.1 h1
    have hwK : w ∈ {w ∈ closedBall z r | (g ∘ u p) w = 0} := hw ▸ mem_singleton w
    exact ⟨w, (hzero p hp).trans hw, .of_isInvertible_fderiv
      (eventually_of_mem (hW.mem_nhds (hp.2 w hwK.1)) hWD) (hgd p hp.1 w (hp.2 w hwK.1))
      (hnd w hwK.1 hwK.2).2⟩
  · -- The only zero of `g ∘ u p₀` in the ball is its centre.
    have hw' : w ∈ u p₀ ⁻¹' D ∩ closedBall z r := (hzero p₀ hp₀').symm ▸ ⟨hw, hw0⟩
    rw [hrD, mem_singleton_iff] at hw'
    subst hw'
    exact ⟨ball_subset_interior_closedBall (mem_ball_self hr), hz⟩

/-- **Assembling the cut points.** If every cut point of `v` lies in one of the closed balls of
radius `r` around the points of `Z`, which are pairwise disjoint, and `v` has exactly one cut point
in each of these balls, at which it meets `D` transversally, then `v` meets `D` transversally at
each of its cut points, and these are in a bijection with `Z` moving each point by at most `r`. -/
private theorem isTransverseCutAt_and_exists_equiv {v : ℂ → X} {Z : Set ℂ} {r : ℝ}
    (hdisj : Z.PairwiseDisjoint fun z ↦ closedBall z r)
    (hcover : ∀ w ∈ v ⁻¹' D, ∃ z ∈ Z, w ∈ closedBall z r)
    (hloc : ∀ z ∈ Z, ∃ w, v ⁻¹' D ∩ closedBall z r = {w} ∧ IsTransverseCutAt v D w) :
    (∀ z ∈ v ⁻¹' D, IsTransverseCutAt v D z) ∧ ∃ e : Z ≃ v ⁻¹' D, ∀ z, dist (e z : ℂ) z ≤ r := by
  choose! ψ hψ htr using hloc
  have hψmem (z) (hz : z ∈ Z) : ψ z ∈ v ⁻¹' D ∩ closedBall z r := (hψ z hz).symm ▸ rfl
  -- Every cut point of `v` is `ψ z` for the ball around some `z ∈ Z` containing it.
  have hψ' (w) (hw : w ∈ v ⁻¹' D) : ∃ z ∈ Z, ψ z = w := by
    obtain ⟨z, hz, hwz⟩ := hcover w hw
    have hw' : w ∈ v ⁻¹' D ∩ closedBall z r := ⟨hw, hwz⟩
    rw [hψ z hz] at hw'
    exact ⟨z, hz, hw'.symm⟩
  have hbij : BijOn ψ Z (v ⁻¹' D) := ⟨fun z hz ↦ (hψmem z hz).1,
    fun z hz z' hz' hzz' ↦ hdisj.elim hz hz' (not_disjoint_iff.2 ⟨ψ z, (hψmem z hz).2,
      hzz' ▸ (hψmem z' hz').2⟩), fun w hw ↦ hψ' w hw⟩
  refine ⟨fun w hw ↦ ?_, hbij.equiv ψ, fun z ↦ mem_closedBall.1 (hψmem z z.property).2⟩
  obtain ⟨z, hz, rfl⟩ := hψ' w hw
  exact htr z hz

/-- **Transverse target cuts persist along families of sphere maps.** Let `u p : ℂ → X` be maps,
continuous jointly in `(p, z)` for `p ∈ s`, that for `p` near `p₀` do not meet the closed set `D`
outside a common compact set (uniformly near `∞`), and suppose that every cut point of `u p₀` can
be followed along the family (`TauCeti.IsTransverseCutFamilyAt`): near it `D` is the zero set of a
function `g` such that the compositions `g ∘ u p` vary in `C¹` with `p` and `g ∘ u p₀` has
invertible derivative there. Then for every `ε > 0` and every `p ∈ s` near `p₀`, the map `u p`
meets `D` transversally at each of its cut points, and these are in a bijection with the cut points
of `u p₀` moving each by at most `ε`. -/
theorem eventually_isTransverseCutAt_and_exists_equiv_preimage (hD : IsClosed D) (hp₀ : p₀ ∈ s)
    (hu : ContinuousOn (Function.uncurry u) (s ×ˢ univ))
    (hinf : ∀ᶠ q in 𝓝[s] p₀ ×ˢ cocompact ℂ, Function.uncurry u q ∉ D)
    (hcut : ∀ z ∈ u p₀ ⁻¹' D, IsTransverseCutFamilyAt u s D p₀ z) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝[s] p₀, (∀ z ∈ u p ⁻¹' D, IsTransverseCutAt (u p) D z) ∧
      ∃ e : u p₀ ⁻¹' D ≃ u p ⁻¹' D, ∀ z, dist (e z : ℂ) z ≤ ε := by
  set Z := u p₀ ⁻¹' D
  -- The maps `u p` converge to `u p₀` as `p → p₀`, jointly with their argument.
  have hconv (w : ℂ) : Tendsto (fun q : P × ℂ ↦ u q.1 q.2) (𝓝[s] p₀ ×ˢ 𝓝 w) (𝓝 (u p₀ w)) := by
    rw [← nhdsWithin_univ w, ← nhdsWithin_prod_eq]
    exact (hu (p₀, w) ⟨hp₀, trivial⟩).tendsto
  have hu₀ : Continuous (u p₀) := continuousOn_univ.1 (hu.uncurry_left p₀ hp₀)
  have hZ : Z.Finite := finite_preimage_of_isTransverseCutAt hu₀ hD
    (hinf.curry.self_of_nhdsWithin hp₀) fun z hz ↦ (hcut z hz).isTransverseCutAt hp₀
  choose! W g hW hzW hWD hg hgd hgd' hinv using hcut
  -- One radius `r < ε` of pairwise disjoint closed balls around the cut points of `u p₀`, each
  -- mapped by `u p₀` into its set `W`.
  obtain ⟨V, hV, hVdisj⟩ := hZ.t2_separation
  have hball (z) (hz : z ∈ Z) : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall z r ⊆ u p₀ ⁻¹' W z ∩ V z :=
    (eventually_closedBall_subset (inter_mem (((hW z hz).preimage hu₀).mem_nhds (hzW z hz))
      ((hV z).2.mem_nhds (hV z).1))).filter_mono nhdsWithin_le_nhds
  obtain ⟨r, hrW, hr⟩ := ((hZ.eventually_all.2 hball).and (Ioo_mem_nhdsGT hε)).exists
  have hdisj : Z.PairwiseDisjoint fun z ↦ closedBall z r :=
    hVdisj.mono_on fun z hz ↦ (hrW z hz).trans inter_subset_right
  have hrD (z) (hz : z ∈ Z) : Z ∩ closedBall z r = {z} :=
    eq_singleton_iff_unique_mem.2 ⟨⟨hz, mem_closedBall_self hr.1.le⟩, fun w hw ↦ by
      exact hdisj.elim hw.1 hz (not_disjoint_iff.2 ⟨w, mem_closedBall_self hr.1.le, hw.2⟩)⟩
  -- Near `p₀`, `u p` has exactly one cut point in each ball, and it is transverse there.
  have hloc : ∀ᶠ p in 𝓝[s] p₀, ∀ z ∈ Z, ∃ w, u p ⁻¹' D ∩ closedBall z r = {w} ∧
      IsTransverseCutAt (u p) D w :=
    hZ.eventually_all.2 fun z hz ↦ eventually_exists_inter_closedBall_eq_singleton hp₀ hu
      (hW z hz) (hWD z hz) (hg z hz) (hgd z hz) (hgd' z hz) (hinv z hz) hr.1
      ((isCompact_closedBall z r).eventually_forall_mem_of_tendsto_prod_nhds (hW z hz)
        (fun w _ ↦ hconv w) fun w hw ↦ (hrW z hz hw).1) (hrD z hz)
  -- Near `p₀`, `u p` has no cut point outside the balls: near `∞` by `hinf`, and on the
  -- remaining compact set `C` by continuity.
  obtain ⟨t, ht, c, hc, htc⟩ := eventually_prod_iff.1 hinf
  obtain ⟨C, hC, hCc⟩ := mem_cocompact.1 hc
  have haway : ∀ᶠ p in 𝓝[s] p₀, ∀ w ∈ C \ ⋃ z ∈ Z, ball z r, u p w ∈ Dᶜ :=
    (hC.diff (isOpen_biUnion fun _ _ ↦ isOpen_ball)).eventually_forall_mem_of_tendsto_prod_nhds
      hD.isOpen_compl (fun w _ ↦ hconv w) fun w hw hwD ↦
        hw.2 (mem_biUnion hwD (mem_ball_self hr.1))
  filter_upwards [hloc, haway, ht] with p hp hpaway hpt
  refine (isTransverseCutAt_and_exists_equiv hdisj (fun w hw ↦ ?_) hp).imp_right
    fun ⟨e, he⟩ ↦ ⟨e, fun z ↦ (he z).trans hr.2.le⟩
  have hwC : w ∈ C := by
    by_contra hwC
    exact htc hpt (hCc hwC) hw
  by_contra! hcon
  exact hpaway w ⟨hwC, by simpa using fun z hz hwz ↦ hcon z hz (ball_subset_closedBall hwz)⟩ hw

/-- **The number of transverse cut points is locally constant along a family.** Under the
hypotheses of `TauCeti.eventually_isTransverseCutAt_and_exists_equiv_preimage`, for `p ∈ s` near
`p₀` the map `u p` has finitely many cut points, as many as `u p₀`. -/
theorem eventually_finite_preimage_and_ncard_eq (hD : IsClosed D) (hp₀ : p₀ ∈ s)
    (hu : ContinuousOn (Function.uncurry u) (s ×ˢ univ))
    (hinf : ∀ᶠ q in 𝓝[s] p₀ ×ˢ cocompact ℂ, Function.uncurry u q ∉ D)
    (hcut : ∀ z ∈ u p₀ ⁻¹' D, IsTransverseCutFamilyAt u s D p₀ z) :
    ∀ᶠ p in 𝓝[s] p₀, (u p ⁻¹' D).Finite ∧ (u p ⁻¹' D).ncard = (u p₀ ⁻¹' D).ncard := by
  have h := eventually_isTransverseCutAt_and_exists_equiv_preimage hD hp₀ hu hinf hcut one_pos
  have hZ : (u p₀ ⁻¹' D).Finite := finite_preimage_of_isTransverseCutAt
    (continuousOn_univ.1 (hu.uncurry_left p₀ hp₀)) hD (hinf.curry.self_of_nhdsWithin hp₀)
    (h.self_of_nhdsWithin hp₀).1
  filter_upwards [h] with p hp
  obtain ⟨-, e, -⟩ := hp
  have := hZ.to_subtype
  exact ⟨Set.finite_coe_iff.1 (Finite.of_equiv _ e), (Set.ncard_congr' e).symm⟩

/-- **The isotropy bound of the stabilization holds along a family.** Under the hypotheses of
`TauCeti.eventually_isTransverseCutAt_and_exists_equiv_preimage`, if the marked points `M` of the
sphere component together with the cut points of `u p₀` contain two distinct points, then for
`p ∈ s` near `p₀` the isotropy of `u p` with the marked points `M` is finite of order dividing
`|u p₀⁻¹(D)|!`. -/
theorem eventually_card_markedIsotropy_dvd_factorial (hD : IsClosed D) (hp₀ : p₀ ∈ s)
    (hu : ContinuousOn (Function.uncurry u) (s ×ˢ univ))
    (hinf : ∀ᶠ q in 𝓝[s] p₀ ×ˢ cocompact ℂ, Function.uncurry u q ∉ D)
    (hcut : ∀ z ∈ u p₀ ⁻¹' D, IsTransverseCutFamilyAt u s D p₀ z)
    {M : Set ℂ} (hM : (M ∪ u p₀ ⁻¹' D).Nontrivial) :
    ∀ᶠ p in 𝓝[s] p₀, Nat.card (markedIsotropy (u p) M) ∣ (Nat.card (u p₀ ⁻¹' D))! := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hM
  have hε : 0 < dist x y / 3 := by linarith [dist_pos.2 hxy]
  filter_upwards [eventually_isTransverseCutAt_and_exists_equiv_preimage hD hp₀ hu hinf hcut hε,
    eventually_finite_preimage_and_ncard_eq hD hp₀ hu hinf hcut] with p hp hfin
  obtain ⟨-, e, he⟩ := hp
  -- Each point of `M ∪ u p₀⁻¹(D)` has a point of `M ∪ u p⁻¹(D)` within `dist x y / 3`.
  have hnear (a) (ha : a ∈ M ∪ u p₀ ⁻¹' D) : ∃ b ∈ M ∪ u p ⁻¹' D, dist b a ≤ dist x y / 3 := by
    rcases ha with ha | ha
    · exact ⟨a, Or.inl ha, by simpa using hε.le⟩
    · exact ⟨e ⟨a, ha⟩, Or.inr (e ⟨a, ha⟩).property, he ⟨a, ha⟩⟩
  obtain ⟨x', hx', hxx'⟩ := hnear x hx
  obtain ⟨y', hy', hyy'⟩ := hnear y hy
  have hne : x' ≠ y' := by
    rintro rfl
    linarith [dist_triangle_left x y x']
  rw [Nat.card_congr e]
  exact card_markedIsotropy_dvd_factorial hfin.1 ⟨x', hx', y', hy', hne⟩

end General

section Manifold

variable {E H M Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] {u : Q → ℂ → M} {s U : Set Q} {q₀ : Q} {D : Set M}

/-- **Cut points of `C¹` families of maps into a manifold can be followed.** Let `u q : ℂ → M` be
maps into a manifold depending on a parameter `q` in an open set `U` of a normed space, with
`(q, z) ↦ u q z` of class `C¹` on `U × ℂ`, and let `z` be a cut point of `u q₀`, `q₀ ∈ s ⊆ U`.
If near `u q₀ z` the set `D` is the zero set of a `C¹` function `g` on an open set `W`, with
`dg ∘ d(u q₀)` injective at `z`, then the cut point `z` can be followed along the family. The
derivative of `g ∘ u q` at `w` is that of `g ∘ uncurry u` at `(q, w)` restricted to `ℂ`. -/
theorem isTransverseCutFamilyAt_of_contMDiffOn (hU : IsOpen U) (hsU : s ⊆ U) (hq₀ : q₀ ∈ s)
    (hu : ContMDiffOn 𝓘(ℝ, Q × ℂ) I 1 (Function.uncurry u) (U ×ˢ univ)) {W : Set M}
    {g : M → ℂ} (hW : IsOpen W) (hWD : ∀ x ∈ W, x ∈ D ↔ g x = 0)
    (hg : ContMDiffOn I 𝓘(ℝ, ℂ) 1 g W) {z : ℂ} (hzW : u q₀ z ∈ W)
    (hinj : Function.Injective
      ((mfderiv I 𝓘(ℝ, ℂ) g (u q₀ z)).comp (mfderiv 𝓘(ℝ, ℂ) I (u q₀) z))) :
    IsTransverseCutFamilyAt u s D q₀ z := by
  refine ⟨W, g, hW, hzW, hWD, ?_⟩
  set O := (U ×ˢ univ) ∩ Function.uncurry u ⁻¹' W
  have hO : IsOpen O := hu.continuousOn.isOpen_inter_preimage (hU.prod isOpen_univ) hW
  have hF : ContDiffOn ℝ 1 (g ∘ Function.uncurry u) O :=
    contMDiffOn_iff_contDiffOn.1 (hg.comp (hu.mono inter_subset_left) fun _ hq ↦ hq.2)
  have hSO : {q : Q × ℂ | q.1 ∈ s ∧ u q.1 q.2 ∈ W} ⊆ O := fun q hq ↦ ⟨⟨hsU hq.1, trivial⟩, hq.2⟩
  -- Along the slice `w ↦ (q, w)`, the derivative is that of `g ∘ uncurry u` composed with `inr`.
  have hderiv (a : Q) (w : ℂ) (hq : (a, w) ∈ O) : HasFDerivAt (g ∘ u a)
      ((fderiv ℝ (g ∘ Function.uncurry u) (a, w)).comp (ContinuousLinearMap.inr ℝ Q ℂ)) w :=
    (((hF.contDiffAt (hO.mem_nhds hq)).differentiableAt one_ne_zero).hasFDerivAt).comp w
      (hasFDerivAt_prodMk_right a w)
  refine ⟨hg.continuousOn, fun q hq w hw ↦ (hderiv q w (hSO ⟨hq, hw⟩)).differentiableAt,
    ((hF.continuousOn_fderiv_of_isOpen hO le_rfl).clm_comp continuousOn_const).mono hSO |>.congr
      fun q hq ↦ (hderiv q.1 q.2 (hSO hq)).fderiv, ?_⟩
  -- At `z`, the derivative of `g ∘ u q₀` is `dg ∘ du q₀`, which is injective.
  let dg : TangentSpace I (u q₀ z) →L[ℝ] ℂ := mfderiv I 𝓘(ℝ, ℂ) g (u q₀ z)
  let du : ℂ →L[ℝ] TangentSpace I (u q₀ z) := mfderiv 𝓘(ℝ, ℂ) I (u q₀) z
  have hgm : HasMFDerivAt I 𝓘(ℝ, ℂ) g (u q₀ z) dg :=
    ((hg.contMDiffAt (hW.mem_nhds hzW)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  have hum : HasMFDerivAt 𝓘(ℝ, ℂ) I (u q₀) z du :=
    (((hu.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hsU hq₀, trivial⟩)).comp z
      (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt).mdifferentiableAt
        one_ne_zero).hasMFDerivAt
  obtain ⟨L, hL⟩ := exists_hasFDerivAt_comp_of_hasMFDerivAt hgm hum hinj
  exact ⟨L, hL.fderiv.symm⟩

end Manifold

end TauCeti
