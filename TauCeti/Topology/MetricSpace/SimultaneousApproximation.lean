/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Simultaneous approximation along filters and nets

Let `F k : α → X` be a family of maps into a pseudometric space, indexed by `k : κ`, with
targets `x k`, and let `p` be a predicate on `α`. The following are equivalent:

* there is a proper filter on `α`, eventually satisfying `p`, along which every `F k` tends
  to `x k`;
* for every finite set of indices and every `ε > 0`, a single point satisfying `p` brings each
  of those `F k` within `ε` of `x k`;
* there is a net indexed by the directed set `Finset κ × ℕ`, all of whose values satisfy `p`,
  along which every `F k` tends to `x k`.

This is the form in which approximate identities in normed algebras are usually constructed
(approximation on finite sets) and used (bounded nets, or filters with an eventual bound).
-/

public section

open Filter Topology

namespace TauCeti

variable {α κ X : Type*} [PseudoMetricSpace X] {p : α → Prop} {F : κ → α → X} {x : κ → X}

/-- Along a proper filter that eventually satisfies `p` and along which each `F k` tends to
`x k`, finitely many of these convergences can be met simultaneously by a point satisfying
`p`. -/
theorem exists_forall_mem_dist_lt_of_tendsto {l : Filter α} [l.NeBot] (hp : ∀ᶠ e in l, p e)
    (hF : ∀ k, Tendsto (F k) l (𝓝 (x k))) (s : Finset κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ e, p e ∧ ∀ k ∈ s, dist (F k e) (x k) < ε :=
  (hp.and <| (s.eventually_all).2 fun k _ ↦ Metric.tendsto_nhds.1 (hF k) ε hε).exists

/-- If finitely many of the convergences `F k → x k` can always be met simultaneously by a
point satisfying `p`, then they hold along a net indexed by `Finset κ × ℕ` whose values all
satisfy `p`. At the index `(s, n)` the net brings each `F k` with `k ∈ s` within `1 / (n + 1)`
of `x k`. -/
theorem exists_net_tendsto_of_forall_finset_dist_lt
    (h : ∀ s : Finset κ, ∀ ε > 0, ∃ e, p e ∧ ∀ k ∈ s, dist (F k e) (x k) < ε) :
    ∃ e : Finset κ × ℕ → α, (∀ i, p (e i)) ∧ ∀ k, Tendsto (fun i ↦ F k (e i)) atTop (𝓝 (x k)) := by
  classical
  choose e hep hed using fun i : Finset κ × ℕ ↦ h i.1 (1 / (i.2 + 1)) (by positivity)
  refine ⟨e, hep, fun k ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine eventually_atTop.2 ⟨({k}, N), fun i hi ↦
    (hed i k (hi.1 (Finset.mem_singleton_self k))).trans_le (le_trans ?_ hN.le)⟩
  gcongr
  exact hi.2

/-- A proper filter eventually satisfying `p` along which every `F k` tends to `x k` exists
exactly when, for every finite set of indices and every `ε > 0`, a single point satisfying `p`
brings each of those `F k` within `ε` of `x k`. -/
theorem exists_neBot_tendsto_iff_forall_finset_dist_lt :
    (∃ l : Filter α, l.NeBot ∧ (∀ᶠ e in l, p e) ∧ ∀ k, Tendsto (F k) l (𝓝 (x k))) ↔
      ∀ s : Finset κ, ∀ ε > 0, ∃ e, p e ∧ ∀ k ∈ s, dist (F k e) (x k) < ε := by
  refine ⟨fun ⟨l, _, hp, hF⟩ s ε hε ↦ exists_forall_mem_dist_lt_of_tendsto hp hF s hε,
    fun h ↦ ?_⟩
  obtain ⟨e, hep, heF⟩ := exists_net_tendsto_of_forall_finset_dist_lt h
  classical
  exact ⟨map e atTop, atTop_neBot.map e, eventually_map.2 (.of_forall hep), heF⟩

/-- A proper filter eventually satisfying `p` along which every `F k` tends to `x k` exists
exactly when there is such a net indexed by `Finset κ × ℕ`, all of whose values satisfy `p`. -/
theorem exists_neBot_tendsto_iff_exists_net :
    (∃ l : Filter α, l.NeBot ∧ (∀ᶠ e in l, p e) ∧ ∀ k, Tendsto (F k) l (𝓝 (x k))) ↔
      ∃ e : Finset κ × ℕ → α, (∀ i, p (e i)) ∧
        ∀ k, Tendsto (fun i ↦ F k (e i)) atTop (𝓝 (x k)) := by
  refine ⟨fun h ↦ exists_net_tendsto_of_forall_finset_dist_lt
    (exists_neBot_tendsto_iff_forall_finset_dist_lt.1 h), fun ⟨e, hep, heF⟩ ↦ ?_⟩
  classical
  exact ⟨map e atTop, atTop_neBot.map e, eventually_map.2 (.of_forall hep), heF⟩

end TauCeti
