/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Topology
public import Mathlib.Topology.Order.MonotoneConvergence
public import TauCeti.Analysis.AffineBoundTightening.Operator
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# The endpoint limit of simultaneous affine bound tightening

The raw iterates `rawRun A q₀ k` of the simultaneous tightening step have monotone lower and
antitone upper endpoints. This file takes their coordinatewise supremum and infimum,
`endpointLimit A q₀`, and shows that when every iterate is nonempty this is the actual limit of
the iteration: its endpoints are ordered and lie within `q₀`, the raw iterates converge to it in the
finite product topology, and by continuity of `step A q₀` it is a fixed tuple. Every fixed tuple
lies within it, so its packed interval is the greatest packed ordered fixed tuple, and every affine
graph point enclosed by `q₀` lies in its box. The limit is in general not reached at any finite
iterate.

As a consequence, every public iterate is nonempty if and only if `step A q₀` has an ordered raw
fixed tuple.

## Main definitions

* `TauCeti.AffineBoundTightening.endpointLimit`: coordinatewise suprema of lower endpoints and
  infima of upper endpoints of the raw iterates.

## Main results

* `TauCeti.AffineBoundTightening.tendsto_rawRun_endpointLimit`: if every raw iterate is ordered,
  the raw iterates converge to `endpointLimit A q₀`.
* `TauCeti.AffineBoundTightening.isFixedPt_step_endpointLimit`: under the same hypothesis the limit
  is a fixed tuple of `step A q₀`.
* `TauCeti.AffineBoundTightening.within_endpointLimit_of_isFixedPt_step`: every fixed tuple lies
  within `endpointLimit A q₀`.
* `TauCeti.AffineBoundTightening.graph_mem_Icc_endpointLimit`: every affine graph point enclosed
  by `q₀` lies in the box of `endpointLimit A q₀`.
* `TauCeti.AffineBoundTightening.forall_coe_publicRun_nonempty_iff_exists_isFixedPt_step`: all
  public iterates are nonempty if and only if an ordered raw fixed tuple exists.
* `TauCeti.AffineBoundTightening.actual_limit`: under nonempty public iterates, the limit is
  ordered, within `q₀`, the limit of the raw iterates, fixed, and greatest among packed ordered
  fixed tuples.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, LNCS 6508, pp. 65–76, §2.3 Theorem 2.2 p. 70 and §4.1 pp. 72–73.
* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *On feasibility based bounds tightening*,
  Optimization Online (2012), Theorem 4.1 p. 14, which makes the nonempty-limit hypothesis
  explicit.
-/

public section

open scoped Topology
open Filter Set

namespace TauCeti.AffineBoundTightening

noncomputable section

variable {n m : ℕ}

/-- Coordinatewise suprema of the lower endpoints and infima of the upper endpoints of the actual
raw iterates `rawRun A q₀ k`. If some iterate is invalid the lower endpoints need not be bounded
above, and the supremum is then a junk value; the convergence results assume ordered iterates. -/
def endpointLimit (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) : Raw n m :=
  (fun c => ⨆ k, (rawRun A q₀ k).1 c, fun c => ⨅ k, (rawRun A q₀ k).2 c)

/-- Each lower endpoint of `endpointLimit A q₀` is the supremum of the raw iterates' lower
endpoints. -/
@[simp]
theorem endpointLimit_fst (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (c : Coord n m) :
    (endpointLimit A q₀).1 c = ⨆ k, (rawRun A q₀ k).1 c :=
  (rfl)

/-- Each upper endpoint of `endpointLimit A q₀` is the infimum of the raw iterates' upper
endpoints. -/
@[simp]
theorem endpointLimit_snd (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (c : Coord n m) :
    (endpointLimit A q₀).2 c = ⨅ k, (rawRun A q₀ k).2 c :=
  (rfl)

/-! ### Tuples contained in every iterate -/

/-- A raw tuple lying within every raw iterate lies within `endpointLimit A q₀`. -/
theorem within_endpointLimit_of_forall {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (h : ∀ k, Within q (rawRun A q₀ k)) : Within q (endpointLimit A q₀) :=
  within_iff.mpr
    ⟨fun c => ciSup_le fun k => (h k).fst_le c, fun c => le_ciInf fun k => (h k).le_snd c⟩

/-- Every raw fixed tuple of `step A q₀` lies within `endpointLimit A q₀`. -/
theorem within_endpointLimit_of_isFixedPt_step {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : Function.IsFixedPt (step A q₀) q) : Within q (endpointLimit A q₀) :=
  within_endpointLimit_of_forall (within_rawRun_of_isFixedPt_step hq)

/-- A point in the box of every raw iterate lies in the box of `endpointLimit A q₀`. -/
theorem mem_Icc_endpointLimit_of_forall {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    {x : Coord n m → ℝ} (h : ∀ k, x ∈ Icc (rawRun A q₀ k).1 (rawRun A q₀ k).2) :
    x ∈ Icc (endpointLimit A q₀).1 (endpointLimit A q₀).2 :=
  ⟨fun c => ciSup_le fun k => (h k).1 c, fun c => le_ciInf fun k => (h k).2 c⟩

/-- Every affine graph point enclosed by `q₀` lies in the box of `endpointLimit A q₀`. -/
theorem graph_mem_Icc_endpointLimit {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    {x : Fin n → ℝ} (hx : graph A x ∈ Icc q₀.1 q₀.2) :
    graph A x ∈ Icc (endpointLimit A q₀).1 (endpointLimit A q₀).2 :=
  mem_Icc_endpointLimit_of_forall (graph_mem_Icc_rawRun A q₀ x hx)

/-- If `q₀` is itself fixed by `step A q₀`, then `endpointLimit A q₀ = q₀`. -/
theorem endpointLimit_eq_self_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    (h : Function.IsFixedPt (step A q₀) q₀) : endpointLimit A q₀ = q₀ := by
  have hrun (k : ℕ) : rawRun A q₀ k = q₀ := by
    rw [rawRun_def]
    exact h.iterate k
  ext c <;> simp [hrun]

/-! ### Bounds and convergence under ordered iterates -/

section Ordered

variable {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}

/-- If every raw iterate is ordered, the lower endpoints in each coordinate are bounded above. -/
theorem bddAbove_range_rawRun_fst (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2)
    (c : Coord n m) : BddAbove (range fun k => (rawRun A q₀ k).1 c) :=
  ⟨q₀.2 c, forall_mem_range.mpr fun k =>
    (hord k c).trans ((rawRun_within_initial A q₀ k).le_snd c)⟩

/-- If every raw iterate is ordered, the upper endpoints in each coordinate are bounded below. -/
theorem bddBelow_range_rawRun_snd (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2)
    (c : Coord n m) : BddBelow (range fun k => (rawRun A q₀ k).2 c) :=
  ⟨q₀.1 c, forall_mem_range.mpr fun k =>
    ((rawRun_within_initial A q₀ k).fst_le c).trans (hord k c)⟩

/-- If every raw iterate is ordered, `endpointLimit A q₀` lies within every raw iterate. -/
theorem endpointLimit_within_rawRun (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2)
    (k : ℕ) : Within (endpointLimit A q₀) (rawRun A q₀ k) :=
  within_iff.mpr
    ⟨fun c => le_ciSup (bddAbove_range_rawRun_fst hord c) k,
     fun c => ciInf_le (bddBelow_range_rawRun_snd hord c) k⟩

/-- If every raw iterate is ordered, `endpointLimit A q₀` lies within `q₀`. -/
theorem endpointLimit_within_initial (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2) :
    Within (endpointLimit A q₀) q₀ := by
  simpa using endpointLimit_within_rawRun hord 0

/-- If every raw iterate is ordered, `endpointLimit A q₀` has ordered endpoints. -/
theorem endpointLimit_fst_le_snd (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2) :
    (endpointLimit A q₀).1 ≤ (endpointLimit A q₀).2 :=
  fun c => ciSup_le fun j => le_ciInf fun k =>
    (monotone_rawRun_fst A q₀).forall_le_of_antitone (antitone_rawRun_snd A q₀) hord j k c

/-- If every raw iterate is ordered, the box of `endpointLimit A q₀` is the intersection of the
boxes of all raw iterates. -/
theorem Icc_endpointLimit_eq_iInter (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2) :
    Icc (endpointLimit A q₀).1 (endpointLimit A q₀).2 =
      ⋂ k, Icc (rawRun A q₀ k).1 (rawRun A q₀ k).2 :=
  Subset.antisymm (subset_iInter fun k => (endpointLimit_within_rawRun hord k).Icc_subset)
    fun _ hx => mem_Icc_endpointLimit_of_forall (mem_iInter.mp hx)

/-- If every raw iterate is ordered, each lower endpoint sequence converges to the corresponding
lower endpoint of `endpointLimit A q₀`. -/
theorem tendsto_rawRun_fst (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2)
    (c : Coord n m) :
    Tendsto (fun k => (rawRun A q₀ k).1 c) atTop (𝓝 ((endpointLimit A q₀).1 c)) :=
  tendsto_atTop_ciSup (fun _ _ hjk => monotone_rawRun_fst A q₀ hjk c)
    (bddAbove_range_rawRun_fst hord c)

/-- If every raw iterate is ordered, each upper endpoint sequence converges to the corresponding
upper endpoint of `endpointLimit A q₀`. -/
theorem tendsto_rawRun_snd (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2)
    (c : Coord n m) :
    Tendsto (fun k => (rawRun A q₀ k).2 c) atTop (𝓝 ((endpointLimit A q₀).2 c)) :=
  tendsto_atTop_ciInf (fun _ _ hjk => antitone_rawRun_snd A q₀ hjk c)
    (bddBelow_range_rawRun_snd hord c)

/-- If every raw iterate is ordered, the raw iterates converge to `endpointLimit A q₀` in the
finite product topology. -/
theorem tendsto_rawRun_endpointLimit (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2) :
    Tendsto (rawRun A q₀) atTop (𝓝 (endpointLimit A q₀)) :=
  (tendsto_pi_nhds.mpr (tendsto_rawRun_fst hord)).prodMk_nhds
    (tendsto_pi_nhds.mpr (tendsto_rawRun_snd hord))

/-- If every raw iterate is ordered, `endpointLimit A q₀` is a fixed tuple of `step A q₀`. -/
theorem isFixedPt_step_endpointLimit (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2) :
    Function.IsFixedPt (step A q₀) (endpointLimit A q₀) := by
  have h := tendsto_rawRun_endpointLimit hord
  rw [show rawRun A q₀ = fun k => (step A q₀)^[k] q₀ from funext (rawRun_def A q₀)] at h
  exact isFixedPt_of_tendsto_iterate h (continuous_step A q₀).continuousAt

/-- If every raw iterate is ordered, the packed `endpointLimit A q₀` is the greatest packed ordered
raw fixed tuple of `step A q₀`. -/
theorem isGreatest_pack_endpointLimit (hord : ∀ k, (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2) :
    IsGreatest {s : State n m | ∃ q : Raw n m, q.1 ≤ q.2 ∧
      Function.IsFixedPt (step A q₀) q ∧ s = pack q} (pack (endpointLimit A q₀)) := by
  refine ⟨⟨endpointLimit A q₀, endpointLimit_fst_le_snd hord,
    isFixedPt_step_endpointLimit hord, rfl⟩, ?_⟩
  rintro _ ⟨q, -, hq, rfl⟩
  exact (within_endpointLimit_of_isFixedPt_step hq).pack_le

end Ordered

/-! ### Nonempty public iterates -/

/-- Every public iterate is nonempty if and only if `step A q₀` has an ordered raw fixed tuple. -/
theorem forall_coe_publicRun_nonempty_iff_exists_isFixedPt_step
    (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    (∀ k, (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty) ↔
      ∃ q : Raw n m, q.1 ≤ q.2 ∧ Function.IsFixedPt (step A q₀) q := by
  constructor
  · intro h
    have hord (k : ℕ) := (coe_publicRun_nonempty_iff A q₀ k).mp (h k)
    exact ⟨endpointLimit A q₀, endpointLimit_fst_le_snd hord, isFixedPt_step_endpointLimit hord⟩
  · rintro ⟨q, hq, hfix⟩ k
    exact coe_publicRun_nonempty_of_isFixedPt_step hq hfix k

/-- If every public iterate is nonempty, `endpointLimit A q₀` is ordered and within `q₀`, is the
limit of the raw iterates in the finite product topology, is a fixed tuple of `step A q₀`, and its
packed interval is the greatest packed ordered raw fixed tuple. -/
theorem actual_limit (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m)
    (h : ∀ k, (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty) :
    (endpointLimit A q₀).1 ≤ (endpointLimit A q₀).2 ∧
    Within (endpointLimit A q₀) q₀ ∧
    Tendsto (rawRun A q₀) atTop (𝓝 (endpointLimit A q₀)) ∧
    Function.IsFixedPt (step A q₀) (endpointLimit A q₀) ∧
    IsGreatest {s : State n m | ∃ q : Raw n m, q.1 ≤ q.2 ∧
      Function.IsFixedPt (step A q₀) q ∧ s = pack q} (pack (endpointLimit A q₀)) := by
  have hord (k : ℕ) := (coe_publicRun_nonempty_iff A q₀ k).mp (h k)
  exact ⟨endpointLimit_fst_le_snd hord, endpointLimit_within_initial hord,
    tendsto_rawRun_endpointLimit hord, isFixedPt_step_endpointLimit hord,
    isGreatest_pack_endpointLimit hord⟩

end

end TauCeti.AffineBoundTightening
