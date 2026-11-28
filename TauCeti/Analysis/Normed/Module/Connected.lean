/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Pi
import TauCeti.Topology.Connected.Basic
import TauCeti.Topology.ConnectedComponents

/-!
# Connectedness of punctured balls and thickenings

In an affine space over a real seminormed space of dimension greater than one, removing a countable
set from an open ball of positive radius leaves a path-connected set; in particular so does
removing the centre. This is the local form of Mathlib's
`Set.Countable.isPathConnected_compl_of_one_lt_rank`, to which it reduces through the homeomorphism
`OpenPartialHomeomorph.univBall` of the model vector space onto the ball. The punctured ball is
the local input for showing that removing a discrete set from a connected manifold of dimension
greater than one keeps it connected: through a partial homeomorphism to the affine space, every
point of its source has arbitrarily small neighbourhoods whose punctured versions are connected.
On an open subset of the affine space itself, applying `TauCeti.isPreconnected_compl_of_isDiscrete`
to the open subtype shows that removing a set relatively closed and discrete in `U` from a
preconnected open set `U` keeps it preconnected
(`IsPreconnected.sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`), without manifold machinery.

It also gives a punctured-neighbourhood obstruction to being locally Euclidean: if removing a point
`x₀` splits every sufficiently small neighbourhood into more than two pairwise disjoint open pieces,
then no open neighbourhood of `x₀` is homeomorphic to an open subset of `Fin n → ℝ`
(`TauCeti.not_homeomorph_of_punctured_nhds_splits`).

In any real seminormed space, the `δ`-thickening of a preconnected set is again preconnected
(`IsPreconnected.thickening`), because `thickening δ s = s + ball 0 δ` is the continuous sum image
of the product of two preconnected sets.

## Main declarations

* `Set.Countable.isPathConnected_ball_sdiff`: an open ball with a countable set removed is path
  connected.
* `TauCeti.isPathConnected_ball_sdiff_singleton`, `TauCeti.isConnected_ball_sdiff_singleton`: a
  punctured open ball is path connected, hence connected.
* `TauCeti.exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source`: every point in the
  source of a partial homeomorphism to the affine space has arbitrarily small neighbourhoods whose
  punctured versions are connected.
* `IsPreconnected.sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`: removing a set relatively closed
  and discrete in `U` from a preconnected open subset `U` of a real affine space of dimension
  greater than one keeps it preconnected.
* `IsPreconnected.thickening`: the `δ`-thickening of a preconnected set in a real seminormed space
  is preconnected.
* `TauCeti.not_homeomorph_of_punctured_nhds_splits`: a point whose punctured neighbourhoods split
  into more than two open pieces has no open neighbourhood homeomorphic to an open set of
  `Fin n → ℝ`.
* `TauCeti.instConnectedSpaceNonZero`: the nonzero vectors of a nontrivial complex normed space are
  connected, since as a real vector space it has dimension at least two.
-/

public section

open Function Metric Set Topology
open scoped Pointwise

namespace TauCeti

variable {E P : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace P] [NormedAddTorsor E P]

/-- In an affine space over a real seminormed space of dimension greater than one, an open ball of
positive radius with a countable set removed is path connected. -/
theorem _root_.Set.Countable.isPathConnected_ball_sdiff (h : 1 < Module.rank ℝ E) {s : Set P}
    (hs : s.Countable) (x : P) {r : ℝ} (hr : 0 < r) : IsPathConnected (ball x r \ s) := by
  set e := OpenPartialHomeomorph.univBall x r
  have he : Function.Injective e :=
    e.toPartialEquiv.injective_of_source_eq_univ (OpenPartialHomeomorph.univBall_source x r)
  -- `e` maps the whole vector space onto the ball, so `ball x r \ s` is the image of `(e ⁻¹' s)ᶜ`.
  have hrange : range e = ball x r := by
    rw [← image_univ, ← OpenPartialHomeomorph.univBall_source x r, e.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target x hr]
  rw [← hrange, ← image_compl_preimage]
  exact ((hs.preimage he).isPathConnected_compl_of_one_lt_rank h).image
    (OpenPartialHomeomorph.continuous_univBall x r)

/-- In an affine space over a real seminormed space of dimension greater than one, an open ball of
positive radius with its centre removed is path connected. -/
theorem isPathConnected_ball_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : P) {r : ℝ}
    (hr : 0 < r) : IsPathConnected (ball x r \ {x}) :=
  (countable_singleton x).isPathConnected_ball_sdiff h x hr

/-- In an affine space over a real seminormed space of dimension greater than one, an open ball of
positive radius with its centre removed is connected. -/
theorem isConnected_ball_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : P) {r : ℝ}
    (hr : 0 < r) : IsConnected (ball x r \ {x}) :=
  (isPathConnected_ball_sdiff_singleton h x hr).isConnected

/-- If `P` is an affine space over a real seminormed space of dimension greater than one, every
point `x` in the source of a partial homeomorphism `φ : X → P` has arbitrarily small neighbourhoods
`V` with `V \ {x}` connected. -/
theorem exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source
    {X : Type*} [TopologicalSpace X]
    (h : 1 < Module.rank ℝ E) (φ : OpenPartialHomeomorph X P) {x : X} (hx : x ∈ φ.source)
    {U : Set X} (hU : U ∈ 𝓝 x) : ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}) := by
  -- The inverse chart carries the balls about `φ x` inside `φ.target` to a basis of `𝓝 x`.
  have hbasis := (nhds_basis_ball.restrict_subset
    (φ.open_target.mem_nhds (φ.map_source hx))).map φ.symm
  rw [φ.symm_map_nhds_eq hx] at hbasis
  obtain ⟨r, ⟨hr, hbt⟩, hrU⟩ := hbasis.mem_iff.1 hU
  have hsdiff : φ.symm '' ball (φ x) r \ {x} = φ.symm '' (ball (φ x) r \ {φ x}) := by
    rw [(φ.symm.injOn.mono hbt).image_sdiff_subset (singleton_subset_iff.2 (mem_ball_self hr)),
      image_singleton, φ.left_inv hx]
  refine ⟨_, hbasis.mem_of_mem ⟨hr, hbt⟩, hrU, ?_⟩
  rw [hsdiff]
  exact (isConnected_ball_sdiff_singleton h (φ x) hr).image _
    (φ.continuousOn_symm.mono (sdiff_subset.trans hbt))

/-- Removing a set relatively closed and discrete in `U` from a preconnected open subset `U` of a
real affine space of dimension greater than one leaves it preconnected. -/
theorem _root_.IsPreconnected.sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) {U s : Set P} (hUc : IsPreconnected U) (hU : IsOpen U)
    (hs : IsClosed (Subtype.val ⁻¹' s : Set U))
    (hd : IsDiscrete (Subtype.val ⁻¹' s : Set U)) : IsPreconnected (U \ s) :=
  hUc.sdiff_of_isDiscrete hs hd fun x _ _ hW ↦
    exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source h
      ((⟨U, hU⟩ : TopologicalSpace.Opens P).openPartialHomeomorphSubtypeCoe ⟨x⟩)
      (mem_univ x) hW

/-- The `δ`-thickening of a preconnected set in a real seminormed space is preconnected. -/
theorem _root_.IsPreconnected.thickening {s : Set E} (hs : IsPreconnected s) (δ : ℝ) :
    IsPreconnected (thickening δ s) := by
  rw [← add_ball_zero, ← image2_add, ← image_uncurry_prod]
  exact (hs.prod (convex_ball (0 : E) δ).isPreconnected).image _ continuous_add.continuousOn

end TauCeti

namespace TauCeti

/-- Auxiliary dimension-`1` step for `not_homeomorph_of_punctured_nhds_splits`: removing the centre
splits an open interval in `Fin 1 → ℝ` into two connected pieces, which cannot meet `m ≥ 3`
pairwise disjoint open sets covering the punctured neighbourhood. -/
private theorem not_homeomorph_finOne_of_punctured_nhds_splits
    {X : Type*} [TopologicalSpace X] {x₀ : X} {m : ℕ} (hm : 2 < m) {Q : Fin m → Set X}
    (hQ_disj : Pairwise (Disjoint on Q))
    {U : Set X} {V : Set (Fin 1 → ℝ)} (hx₀ : x₀ ∈ U) (hV : IsOpen V) (e : U ≃ₜ V)
    {r : ℝ} (hr : 0 < r) (hballV : Metric.ball (e ⟨x₀, hx₀⟩).val r ⊆ V)
    {S₀ : Set X}
    (hS₀_eq : S₀ = Subtype.val ''
      (e.symm '' (Subtype.val ⁻¹' (Metric.ball (e ⟨x₀, hx₀⟩).val r \ {(e ⟨x₀, hx₀⟩).val}) :
        Set V)))
    (hpre_sub : ∀ {C : Set X}, IsPreconnected C → C ⊆ S₀ → ∃ k : Fin m, C ⊆ Q k)
    (hS₀_Q : ∀ k : Fin m, (S₀ ∩ Q k).Nonempty) : False := by
  let y₀ : Fin 1 → ℝ := (e ⟨x₀, hx₀⟩).val
  let φ := IsometryEquiv.funUnique (Fin 1) ℝ
  let z₀ : ℝ := φ y₀
  have hball : φ.symm '' Metric.ball z₀ r = Metric.ball y₀ r := by simp [z₀]
  have hy₀ : φ.symm z₀ = (e ⟨x₀, hx₀⟩).val := φ.symm_apply_apply y₀
  let C : Set ℝ → Set X := fun I ↦ Subtype.val '' (e.symm '' (Subtype.val ⁻¹' (φ.symm '' I)))
  have hpiece : ∀ I : Set ℝ, I ⊆ Metric.ball z₀ r → z₀ ∉ I → IsPreconnected I →
      ∃ i : Fin m, C I ⊆ Q i := by
    intro I hI hz₀ hIconn
    have hIV : φ.symm '' I ⊆ V := (image_mono hI).trans (hball.symm ▸ hballV)
    have hA : IsPreconnected (Subtype.val ⁻¹' (φ.symm '' I) : Set V) :=
      (hIconn.image _ φ.symm.continuous.continuousOn).preimage_of_isOpenMap
        Subtype.val_injective hV.isOpenMap_subtypeVal (Subtype.range_coe_subtype ▸ hIV)
    have hC_pre : IsPreconnected (C I) :=
      (hA.image _ e.symm.continuous.continuousOn).image _ continuous_subtypeVal.continuousOn
    have hC_sub : C I ⊆ S₀ := by
      rw [hS₀_eq]
      refine image_mono (image_mono (preimage_mono ?_))
      rw [← hball, ← hy₀]
      exact Set.subset_sdiff_singleton (image_mono hI) fun ⟨t, ht, htv⟩ ↦
        hz₀ (φ.symm.injective htv ▸ ht)
    exact hpre_sub hC_pre hC_sub
  let J₁ : Set ℝ := Ioo (z₀ - r) z₀
  let J₂ : Set ℝ := Ioo z₀ (z₀ + r)
  obtain ⟨i₁, hi₁⟩ := hpiece J₁
    (Real.ball_eq_Ioo z₀ r ▸ Ioo_subset_Ioo_right (by linarith)) (fun h ↦ lt_irrefl _ h.2)
    isPreconnected_Ioo
  obtain ⟨i₂, hi₂⟩ := hpiece J₂
    (Real.ball_eq_Ioo z₀ r ▸ Ioo_subset_Ioo_left (by linarith)) (fun h ↦ lt_irrefl _ h.1)
    isPreconnected_Ioo
  have hJ : J₁ ∪ J₂ = Metric.ball z₀ r \ {z₀} := by
    rw [Real.ball_eq_Ioo]
    exact Set.Ioo_union_Ioo_eq_Ioo_sdiff_singleton (by linarith) (by linarith)
  have hS₀_cover : S₀ ⊆ C J₁ ∪ C J₂ := by
    have hdiff : φ.symm '' Metric.ball z₀ r \ {(e ⟨x₀, hx₀⟩).val} = φ.symm '' (J₁ ∪ J₂) := by
      rw [hJ, Set.image_sdiff φ.symm.injective, image_singleton, hy₀]
    rw [hS₀_eq, ← hball, hdiff]
    simp only [C, image_union, preimage_union, subset_rfl]
  obtain ⟨k, hk₁, hk₂⟩ := Fin.exists_ne_and_ne_of_two_lt i₁ i₂ hm
  obtain ⟨x, hxS, hxQ⟩ := hS₀_Q k
  rcases hS₀_cover hxS with hxC | hxC
  · exact Set.disjoint_left.mp (hQ_disj hk₁) hxQ (hi₁ hxC)
  · exact Set.disjoint_left.mp (hQ_disj hk₂) hxQ (hi₂ hxC)

/-- Punctured-neighbourhood obstruction to being locally Euclidean: if `x₀` has a family of
`m > 2` pairwise disjoint open sets `Q k` covering `{x₀}ᶜ` such that every open neighbourhood of
`x₀` meets every `Q k` away from `x₀`, then no open neighbourhood of `x₀` is homeomorphic to an
open subset of `Fin n → ℝ`. -/
theorem not_homeomorph_of_punctured_nhds_splits
    {X : Type*} [TopologicalSpace X] {x₀ : X} {m : ℕ} (hm : 2 < m)
    (Q : Fin m → Set X) (hQ_open : ∀ k, IsOpen (Q k)) (hQ_disj : Pairwise (Disjoint on Q))
    (hQ_cover : ∀ {x}, x ≠ x₀ → x ∈ ⋃ k, Q k)
    (hQ_mem : ∀ W : Set X, IsOpen W → x₀ ∈ W → ∀ k, ((W \ {x₀}) ∩ Q k).Nonempty)
    {n : ℕ} {U : Set X} {V : Set (Fin n → ℝ)} (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hV : IsOpen V) :
    IsEmpty (U ≃ₜ V) := by
  refine ⟨fun e ↦ ?_⟩
  let y₀ : Fin n → ℝ := (e ⟨x₀, hx₀⟩).val
  obtain ⟨r, hr, hballV⟩ := Metric.isOpen_iff.mp hV y₀ (e ⟨x₀, hx₀⟩).property
  let B : Set U := (fun u ↦ (e u).val) ⁻¹' Metric.ball y₀ r
  have hB_open : IsOpen B :=
    Metric.isOpen_ball.preimage (continuous_subtypeVal.comp e.continuous)
  have hu₀ : ⟨x₀, hx₀⟩ ∈ B := Metric.mem_ball_self hr
  let W : Set X := Subtype.val '' B
  have hW_open : IsOpen W := hU.isOpenMap_subtypeVal B hB_open
  have hxW : x₀ ∈ W := ⟨⟨x₀, hx₀⟩, hu₀, rfl⟩
  let S₀ : Set X := Subtype.val '' (B \ {⟨x₀, hx₀⟩})
  have hS₀_eq_sdiff : S₀ = W \ {x₀} := by
    simp only [S₀, W, Set.image_sdiff Subtype.val_injective, image_singleton]
  have hS₀_Q : ∀ k : Fin m, (S₀ ∩ Q k).Nonempty := fun k ↦
    hS₀_eq_sdiff ▸ hQ_mem W hW_open hxW k
  have hS₀_sub : S₀ ⊆ ⋃ k, Q k := fun _ hx ↦ hQ_cover (hS₀_eq_sdiff ▸ hx).2
  have hpre_sub : ∀ {C : Set X}, IsPreconnected C → C ⊆ S₀ → ∃ k, C ⊆ Q k := by
    intro C hC hCS
    by_cases hne : C.Nonempty
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hS₀_sub (hCS hx))
      exact ⟨k, hC.subset_of_subset_iUnion hQ_open hQ_disj (hCS.trans hS₀_sub) ⟨x, hx, hk⟩⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact ⟨⟨0, by omega⟩, empty_subset _⟩
  have hS₀_eq :
      S₀ = Subtype.val '' (e.symm '' (Subtype.val ⁻¹' (Metric.ball y₀ r \ {y₀}) : Set V)) := by
    have hpre : (e.symm.symm ⁻¹' (Subtype.val ⁻¹' {y₀} : Set V)) = {⟨x₀, hx₀⟩} := by
      ext u; simp [y₀, Subtype.val_inj, e.injective.eq_iff]
    rw [e.symm.image_eq_preimage_symm, Set.preimage_sdiff, Set.preimage_sdiff, hpre]
    rfl
  rcases lt_trichotomy n 1 with hn0 | rfl | hn2
  · obtain rfl : n = 0 := Nat.lt_one_iff.mp hn0
    have hsub0 : Subsingleton (Fin 0 → ℝ) := inferInstance
    have hsubV : Subsingleton V := ⟨fun a b ↦ Subtype.ext (hsub0.elim a.val b.val)⟩
    obtain ⟨_, ⟨u, ⟨-, hune⟩, rfl⟩, -⟩ := hS₀_Q ⟨0, by omega⟩
    exact hune (e.injective (hsubV.elim (e u) (e ⟨x₀, hx₀⟩)))
  · exact not_homeomorph_finOne_of_punctured_nhds_splits hm hQ_disj hx₀ hV e hr hballV hS₀_eq
      hpre_sub hS₀_Q
  · have hrank : 1 < Module.rank ℝ (Fin n → ℝ) := by
      rw [← Module.finrank_eq_rank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      exact_mod_cast hn2
    have hA : IsPreconnected (Subtype.val ⁻¹' (Metric.ball y₀ r \ {y₀}) : Set V) :=
      (isConnected_ball_sdiff_singleton hrank y₀ hr).isPreconnected.preimage_of_isOpenMap
        Subtype.val_injective hV.isOpenMap_subtypeVal
        (Subtype.range_coe_subtype ▸ sdiff_subset.trans hballV)
    have hS₀_pre : IsPreconnected S₀ := by
      rw [hS₀_eq]
      exact (hA.image _ e.symm.continuous.continuousOn).image _ continuous_subtypeVal.continuousOn
    obtain ⟨i, hi⟩ := hpre_sub hS₀_pre Subset.rfl
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨k, hki⟩ := exists_ne i
    obtain ⟨_, hxS, hxQ⟩ := hS₀_Q k
    exact Set.disjoint_left.mp (hQ_disj hki) hxQ (hi hxS)

/-- The nonzero vectors of a nontrivial complex normed space are connected: as a real vector space
it has dimension at least two. -/
instance instConnectedSpaceNonZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nontrivial E] : ConnectedSpace {v : E // v ≠ 0} := by
  have h1 : 1 ≤ Module.rank ℂ E := Cardinal.one_le_iff_pos.mpr rank_pos
  have h : 1 < Module.rank ℝ E := by
    rw [rank_real_of_complex]
    calc (1 : Cardinal) < 2 := Cardinal.one_lt_two
      _ = 2 * 1 := (mul_one 2).symm
      _ ≤ 2 * Module.rank ℂ E := by gcongr
  exact isConnected_iff_connectedSpace.mp (isConnected_compl_singleton_of_one_lt_rank h 0)

end TauCeti
