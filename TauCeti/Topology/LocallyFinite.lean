/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Locally finite families

A locally finite family of sets stays locally finite when it is reindexed along the first
projection `ι × κ → ι` with `κ` finite (`LocallyFinite.comp_fst`). Together with
`LocallyFinite.subset`, this makes a family indexed by `ι × κ` whose `(i, k)`-th member lies in
the `i`-th member of a locally finite family locally finite. Dually, the pointwise union of
finitely many locally finite families is locally finite (`LocallyFinite.iUnion`).

In a pseudometric space, a locally finite family of closed sets has the following useful local
description: around each point there is a ball such that every member of the family meeting the
ball contains the centre.

On a normal paracompact space, positive continuous functions on the members of a locally finite
closed family admit a single positive continuous strict minorant. This allows local error
tolerances to be assembled without a uniform lower bound on a noncompact space. The minorant is
constructed with Mathlib's `exists_continuous_forall_mem_convex_of_local_const`.
-/

public section

open Set

namespace LocallyFinite

variable {ι κ X : Type*} [TopologicalSpace X] {f : ι → Set X}

/-- A locally finite family stays locally finite when reindexed along the first projection
`ι × κ → ι`, for `κ` finite. -/
theorem comp_fst [Finite κ] (hf : LocallyFinite f) : LocallyFinite fun p : ι × κ ↦ f p.1 :=
  fun x ↦
    let ⟨U, hU, hfin⟩ := hf x
    ⟨U, hU, (hfin.prod (finite_univ (α := κ))).subset fun _ hp ↦ ⟨hp, mem_univ _⟩⟩

/-- Positive continuous tolerances on a locally finite family of closed sets admit a positive
continuous strict minorant on the whole space. No covering or compactness assumption is needed. -/
theorem exists_continuous_pos_lt [NormalSpace X] [ParacompactSpace X]
    (hf : LocallyFinite f) (hclosed : ∀ i, IsClosed (f i)) {ε : ι → X → ℝ}
    (hε : ∀ i, ContinuousOn (ε i) (f i)) (hpos : ∀ i, ∀ x ∈ f i, 0 < ε i x) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ i, ∀ x ∈ f i, δ x < ε i x := by
  classical
  let t (x : X) : Set ℝ := Ioi 0 ∩ ⋂ i, ⋂ (_ : x ∈ f i), Iio (ε i x)
  have hconv (x : X) : Convex ℝ (t x) :=
    (convex_Ioi (0 : ℝ)).inter (convex_iInter fun i ↦
      convex_iInter fun _ ↦ convex_Iio (ε i x))
  have hlocal (x : X) : ∃ c : ℝ, ∀ᶠ y in nhds x, c ∈ t y := by
    -- Finitely many constraints are active at x. Each admits a local positive constant.
    have hi (i : ι) (hx : x ∈ f i) :
        ∃ c > 0, ∀ᶠ y in nhds x, y ∈ f i → c < ε i y := by
      refine ⟨ε i x / 2, half_pos (hpos i x hx), ?_⟩
      have := (hε i x hx).eventually (Ioi_mem_nhds (half_lt_self (hpos i x hx)))
      exact eventually_nhdsWithin_iff.mp this
    have hfinite (s : Finset ι) (hs : ∀ i ∈ s, x ∈ f i) :
        ∃ c > 0, ∀ᶠ y in nhds x, ∀ i ∈ s, y ∈ f i → c < ε i y := by
      induction s using Finset.induction_on with
      | empty => exact ⟨1, one_pos, Filter.Eventually.of_forall (by simp)⟩
      | @insert i s his ih =>
        obtain ⟨a, ha, hya⟩ := hi i (hs i (by simp))
        obtain ⟨b, hb, hyb⟩ := ih (fun j hj ↦ hs j (by simp [hj]))
        refine ⟨min a b, lt_min ha hb, ?_⟩
        filter_upwards [hya, hyb] with y hya hyb j hj hy
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (min_le_left _ _).trans_lt (hya hy)
        · exact (min_le_right _ _).trans_lt (hyb j hj hy)
    obtain ⟨c, hc, hyc⟩ := hfinite (hf.point_finite x).toFinset (by simp)
    refine ⟨c, ?_⟩
    filter_upwards [hyc, hf.eventually_subset hclosed x] with y hy hsub
    exact ⟨hc, by simpa only [mem_iInter, mem_Iio] using
      (fun i hi ↦ hy i (by simpa using hsub hi) hi)⟩
  obtain ⟨δ, hδ⟩ := exists_continuous_forall_mem_convex_of_local_const hconv hlocal
  refine ⟨δ, fun x ↦ (hδ x).1, fun i x hx ↦ ?_⟩
  exact mem_iInter.mp (mem_iInter.mp (hδ x).2 i) hx

/-- The pointwise union of finitely many locally finite families is locally finite. -/
protected theorem iUnion [Finite κ] {f : κ → ι → Set X} (hf : ∀ k, LocallyFinite (f k)) :
    LocallyFinite fun i ↦ ⋃ k, f k i := by
  simp_rw [locallyFinite_iff_smallSets] at hf ⊢
  intro x
  filter_upwards [Filter.eventually_all.2 fun k ↦ hf k x] with t ht
  simpa only [iUnion_inter, nonempty_iUnion, ofPred_exists] using finite_iUnion ht

end LocallyFinite

namespace TauCeti

open Metric Set

/-- Around each point there is a ball such that every member of a locally finite family of closed
sets that meets the ball contains the centre. -/
theorem exists_pos_forall_mem_of_mem_ball {X ι : Type*} [PseudoMetricSpace X]
    {s : ι → Set X} (hs : ∀ i, IsClosed (s i)) (hlf : LocallyFinite s) (x : X) :
    ∃ r > 0, ∀ i, ∀ y ∈ ball x r, y ∈ s i → x ∈ s i := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlf.eventually_subset hs x)
  exact ⟨r, hr, fun i y hy hys ↦ hball y hy hys⟩

end TauCeti
