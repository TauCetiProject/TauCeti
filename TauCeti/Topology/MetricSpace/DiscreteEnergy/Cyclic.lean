/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.DiscreteEnergy.Insertion

/-!
# Discrete energy of closed metric paths

A closed discrete path in a metric space `M` is a tuple of vertices `x 0, …, x n`, visited at
increasing times `t 0 < ⋯ < t n` and followed by a return to `x 0` at the time `t (n + 1)`. Its
**cyclic discrete energy** (`TauCeti.cyclicDiscreteEnergy`) is the discrete energy of the closed
tuple `x 0, …, x n, x 0`,

`½ ∑ᵢ dist (x i, x (i + 1))² / (t (i + 1) - t i)`,

where the indices `i : Fin (n + 1)` are read cyclically, so that the last edge joins `x n` back to
`x 0` (`TauCeti.cyclicDiscreteEnergy_eq_sum`). The vertices are free: there is no fixed endpoint.
These tuples are the finite-dimensional carriers of closed broken geodesics, which approximate the
free loop space of a compact manifold in the same way as the fixed-endpoint carriers of
`TauCeti.Topology.MetricSpace.DiscreteEnergy.Basic` approximate its spaces of paths.

The file develops the cyclic carrier alongside the fixed-endpoint one.

* **Estimates.** The energy is continuous, nonnegative, and zero exactly on constant tuples. It
  bounds each squared edge, the closing edge included, by twice the energy times its time step,
  so a fine time mesh makes every edge of a tuple of bounded energy short
  (`TauCeti.dist_lt_of_cyclicDiscreteEnergy_lt`). This is what allows the vertices to be joined by
  short minimizing segments.
* **Sublevels.** Strict energy sublevels are open. A closed sublevel is compact once the first
  vertex is confined to a closed ball of a proper space, and is compact outright in a compact
  space (`TauCeti.isCompact_cyclicDiscreteEnergy_le`).
* **The seam.** Which vertex comes first is a choice of where the loop is cut open. Rotating the
  vertices, `i ↦ x (i + k)`, does not change the energy when the time steps are rotated with them,
  in particular for uniform time steps (`TauCeti.cyclicDiscreteEnergy_comp_add_right`).
* **Subdivision.** Forgetting vertices, while keeping the first one and the return time, does not
  increase the energy (`TauCeti.cyclicDiscreteEnergy_cyclicDiscreteEnergyForget_le`), and gives
  continuous maps of strict sublevels, compatible with identities and composition. Conversely,
  sampling constant-speed minimizing segments along the edges inserts vertices without changing
  the energy (`TauCeti.cyclicDiscreteEnergy_cyclicDiscreteEnergyInsert`), and a continuous choice
  of segments gives a continuous insertion map of strict sublevels with forgetting as a left
  inverse (`TauCeti.cyclicDiscreteEnergyForgetMap_comp_cyclicDiscreteEnergyInsertMap`).

The cyclic energy is the fixed-endpoint discrete energy `TauCeti.discreteEnergy` of the closed
tuple, so each result is deduced from the corresponding one for paths. As there, the energy carries
the normalization `½`.

## Main definitions

* `TauCeti.cyclicDiscreteEnergy t x`: the discrete energy of the closed tuple `x 0, …, x n, x 0`.
* `TauCeti.cyclicDiscreteEnergyStrictSublevel t c`: the tuples of energy less than `c`.
* `TauCeti.cyclicDiscreteEnergyForgetMap`: forgetting vertices, between strict sublevels.
* `TauCeti.cyclicDiscreteEnergyInsertMap`: geodesic insertion of vertices, between strict
  sublevels.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16 (finite-dimensional approximations of path spaces by broken geodesics).
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, §11.2 (broken geodesic
  approximations of the free loop space).
-/

public section

open scoped BigOperators

namespace TauCeti

variable {M : Type*} {l m n : ℕ}

/-- In the closed tuple `x 0, …, x n, x 0`, the vertex after the `i`-th one is `x (i + 1)`, with
the cyclic successor of `Fin (n + 1)`. -/
private theorem snoc_self_zero_succ (x : Fin (n + 1) → M) (i : Fin (n + 1)) :
    (Fin.snoc x (x 0) : Fin (n + 2) → M) i.succ = x (i + 1) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.coeSucc_eq_succ]

section Energy

variable [PseudoMetricSpace M]

/-- The **cyclic discrete energy** of the vertices `x 0, …, x n` at the times
`t 0, …, t (n + 1)`: the discrete energy of the closed tuple `x 0, …, x n, x 0`, the last time
being the return to `x 0`. -/
noncomputable def cyclicDiscreteEnergy (t : Fin (n + 2) → ℝ) (x : Fin (n + 1) → M) : ℝ :=
  discreteEnergy t (Fin.snoc x (x 0))

/-- The cyclic discrete energy is the discrete energy of the closed tuple. -/
theorem cyclicDiscreteEnergy_def (t : Fin (n + 2) → ℝ) (x : Fin (n + 1) → M) :
    cyclicDiscreteEnergy t x = discreteEnergy t (Fin.snoc x (x 0)) := (rfl)

/-- The cyclic discrete energy as a sum over the `n + 1` edges of the closed path, with indices
read cyclically: the edge at `i` joins `x i` to `x (i + 1)`, and the last one joins `x n` back to
`x 0`. -/
theorem cyclicDiscreteEnergy_eq_sum (t : Fin (n + 2) → ℝ) (x : Fin (n + 1) → M) :
    cyclicDiscreteEnergy t x = (1 / 2) * ∑ i : Fin (n + 1),
      dist (x i) (x (i + 1)) ^ 2 / (t i.succ - t i.castSucc) := by
  simp only [cyclicDiscreteEnergy_def, discreteEnergy_def, Fin.snoc_castSucc,
    snoc_self_zero_succ]

/-- The cyclic discrete energy is continuous in all vertices, with no restriction on the times. -/
@[fun_prop]
theorem continuous_cyclicDiscreteEnergy (t : Fin (n + 2) → ℝ) :
    Continuous (cyclicDiscreteEnergy (M := M) t) :=
  (continuous_discreteEnergy t).comp
    (Continuous.finSnoc (A := fun _ : Fin (n + 2) => M) continuous_id (continuous_apply 0))

@[simp]
theorem cyclicDiscreteEnergy_const (t : Fin (n + 2) → ℝ) (p : M) :
    cyclicDiscreteEnergy t (fun _ : Fin (n + 1) ↦ p) = 0 := by
  simp [cyclicDiscreteEnergy_eq_sum]

/-- The cyclic discrete energy is nonnegative for nondecreasing times. -/
theorem cyclicDiscreteEnergy_nonneg {t : Fin (n + 2) → ℝ} (ht : Monotone t)
    (x : Fin (n + 1) → M) : 0 ≤ cyclicDiscreteEnergy t x :=
  discreteEnergy_nonneg ht _

/-- For increasing times in a metric space, a closed tuple has zero energy exactly when it is
constant. -/
@[simp]
theorem cyclicDiscreteEnergy_eq_zero_iff {M : Type*} [MetricSpace M] {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) (x : Fin (n + 1) → M) :
    cyclicDiscreteEnergy t x = 0 ↔ ∀ j, x j = x 0 := by
  rw [cyclicDiscreteEnergy_def, discreteEnergy_eq_zero_iff ht]
  refine ⟨fun h j ↦ by simpa using h j.castSucc, fun h j ↦ ?_⟩
  refine Fin.lastCases ?_ (fun j ↦ ?_) j <;> simp [h]

/-- Each squared edge of a closed tuple, the closing edge from `x n` to `x 0` included, is bounded
by twice the cyclic energy times its time step. -/
theorem dist_sq_le_cyclicDiscreteEnergy_mul_step {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) (i : Fin (n + 1)) :
    dist (x i) (x (i + 1)) ^ 2 ≤ 2 * cyclicDiscreteEnergy t x * (t i.succ - t i.castSucc) := by
  rw [cyclicDiscreteEnergy_def]
  simpa only [Fin.snoc_castSucc, snoc_self_zero_succ] using
    dist_sq_le_discreteEnergy_mul_step ht (Fin.snoc x (x 0)) i

/-- A fine mesh forces every edge of a closed tuple in a strict energy sublevel, the closing edge
included, to be shorter than the chosen positive radius. -/
theorem dist_lt_of_cyclicDiscreteEnergy_lt {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) {c ρ : ℝ} (hρ : 0 < ρ) (hx : cyclicDiscreteEnergy t x < c)
    (hmesh : ∀ i : Fin (n + 1), t i.succ - t i.castSucc < ρ ^ 2 / (2 * c))
    (i : Fin (n + 1)) : dist (x i) (x (i + 1)) < ρ := by
  rw [cyclicDiscreteEnergy_def] at hx
  simpa only [Fin.snoc_castSucc, snoc_self_zero_succ] using
    dist_lt_of_discreteEnergy_lt ht (Fin.snoc x (x 0)) hρ hx hmesh i

/-- Every vertex of a closed tuple stays in the energy-controlled closed ball about the first
vertex. -/
theorem dist_le_sqrt_cyclicDiscreteEnergy {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) (j : Fin (n + 1)) :
    dist (x 0) (x j) ≤ √(2 * (t (Fin.last (n + 1)) - t 0) * cyclicDiscreteEnergy t x) := by
  rw [cyclicDiscreteEnergy_def]
  simpa only [Fin.snoc_castSucc, Fin.snoc_apply_zero] using
    dist_le_sqrt_discreteEnergy ht (Fin.snoc x (x 0)) j.castSucc

/-! ### Moving the seam -/

/-- **Moving the seam.** Cutting a closed tuple open at the vertex `x k` instead of `x 0`, that is
rotating its vertices to `i ↦ x (i + k)`, does not change its energy when the time steps are
rotated with them. -/
theorem cyclicDiscreteEnergy_comp_add_right {s t : Fin (n + 2) → ℝ} (k : Fin (n + 1))
    (hst : ∀ i : Fin (n + 1), s i.succ - s i.castSucc = t (i + k).succ - t (i + k).castSucc)
    (x : Fin (n + 1) → M) :
    cyclicDiscreteEnergy s (fun i ↦ x (i + k)) = cyclicDiscreteEnergy t x := by
  rw [cyclicDiscreteEnergy_eq_sum, cyclicDiscreteEnergy_eq_sum,
    ← Equiv.sum_comp (Equiv.addRight k) (fun i ↦ dist (x i) (x (i + 1)) ^ 2 /
      (t i.succ - t i.castSucc))]
  simp [hst, add_right_comm]

/-- For uniform time steps, rotating the vertices of a closed tuple does not change its
energy. -/
theorem cyclicDiscreteEnergy_comp_add_right_of_step_eq {t : Fin (n + 2) → ℝ} {h : ℝ}
    (ht : ∀ i : Fin (n + 1), t i.succ - t i.castSucc = h) (k : Fin (n + 1))
    (x : Fin (n + 1) → M) :
    cyclicDiscreteEnergy t (fun i ↦ x (i + k)) = cyclicDiscreteEnergy t x :=
  cyclicDiscreteEnergy_comp_add_right k (fun i ↦ by rw [ht, ht]) x

/-! ### Sublevels -/

/-- The closed tuples whose cyclic discrete energy is strictly less than `c`. -/
def cyclicDiscreteEnergyStrictSublevel (t : Fin (n + 2) → ℝ) (c : ℝ) :
    Set (Fin (n + 1) → M) :=
  {x | cyclicDiscreteEnergy t x < c}

@[simp]
theorem mem_cyclicDiscreteEnergyStrictSublevel {t : Fin (n + 2) → ℝ} {c : ℝ}
    {x : Fin (n + 1) → M} :
    x ∈ cyclicDiscreteEnergyStrictSublevel t c ↔ cyclicDiscreteEnergy t x < c := Iff.rfl

/-- Strict cyclic energy sublevels are open in the full vertex product. -/
theorem isOpen_cyclicDiscreteEnergyStrictSublevel (t : Fin (n + 2) → ℝ) (c : ℝ) :
    IsOpen (cyclicDiscreteEnergyStrictSublevel (M := M) t c) :=
  isOpen_lt (continuous_cyclicDiscreteEnergy t) continuous_const

/-- Decreasing the cutoff gives the canonical inclusion of cyclic energy carriers. -/
theorem cyclicDiscreteEnergyStrictSublevel_mono (t : Fin (n + 2) → ℝ) {a c : ℝ} (hac : a ≤ c) :
    cyclicDiscreteEnergyStrictSublevel (M := M) t a ⊆ cyclicDiscreteEnergyStrictSublevel t c :=
  fun _ hx ↦ hx.trans_le hac

/-- In a proper space, the closed tuples of energy at most `a` whose first vertex lies in a closed
ball form a compact set. The first vertex has to be confined, since the vertices are free. -/
theorem isCompact_cyclicDiscreteEnergy_le_of_dist_le [ProperSpace M] {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) (p : M) (r a : ℝ) :
    IsCompact {x : Fin (n + 1) → M | dist (x 0) p ≤ r ∧ cyclicDiscreteEnergy t x ≤ a} := by
  refine (isCompact_univ_pi fun _ : Fin (n + 1) ↦
    isCompact_closedBall p (r + √(2 * (t (Fin.last (n + 1)) - t 0) * a))).of_isClosed_subset
      ((isClosed_le ((continuous_apply 0).dist continuous_const) continuous_const).inter
        (isClosed_le (continuous_cyclicDiscreteEnergy t) continuous_const)) ?_
  rintro x ⟨hp, ha⟩ j -
  have hT : 0 ≤ t (Fin.last (n + 1)) - t 0 := sub_nonneg.mpr (ht.monotone (Fin.zero_le _))
  have hj : dist (x 0) (x j) ≤ √(2 * (t (Fin.last (n + 1)) - t 0) * a) :=
    (dist_le_sqrt_cyclicDiscreteEnergy ht x j).trans (by gcongr)
  rw [Metric.mem_closedBall]
  linarith [dist_triangle (x j) (x 0) p, dist_comm (x j) (x 0)]

/-- In a compact space, the closed tuples of cyclic energy at most `a` form a compact set. -/
theorem isCompact_cyclicDiscreteEnergy_le [CompactSpace M] (t : Fin (n + 2) → ℝ) (a : ℝ) :
    IsCompact {x : Fin (n + 1) → M | cyclicDiscreteEnergy t x ≤ a} :=
  (isClosed_le (continuous_cyclicDiscreteEnergy t) continuous_const).isCompact

/-- In a compact space, for `a < c`, the closed sublevel `{E ≤ a}` is compact as a subset of the
strict sublevel `cyclicDiscreteEnergyStrictSublevel t c`. -/
theorem isCompact_cyclicDiscreteEnergyStrictSublevel_le [CompactSpace M] (t : Fin (n + 2) → ℝ)
    {a c : ℝ} (hac : a < c) :
    IsCompact {x : cyclicDiscreteEnergyStrictSublevel (M := M) t c |
      cyclicDiscreteEnergy t (x : Fin (n + 1) → M) ≤ a} :=
  Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_cyclicDiscreteEnergy_le t a)
    fun x hx ↦ ⟨⟨x, hx.trans_lt hac⟩, rfl⟩

end Energy

/-! ### Forgetting vertices -/

section Forget

/-- Retain the vertices of the closed tuple `x 0, …, x n, x 0` selected by `r`, dropping the last
selected slot. The theorems below ask `r` to keep the first and the last slot, so that the
retained tuple again starts at `x 0` and closes up there. -/
def cyclicDiscreteEnergyForget (r : Fin (m + 2) ↪o Fin (n + 2)) (x : Fin (n + 1) → M) :
    Fin (m + 1) → M :=
  fun j ↦ (Fin.snoc x (x 0) : Fin (n + 2) → M) (r j.castSucc)

/-- The retained vertex at an index is the selected vertex of the closed tuple. -/
@[simp]
theorem cyclicDiscreteEnergyForget_apply (r : Fin (m + 2) ↪o Fin (n + 2)) (x : Fin (n + 1) → M)
    (j : Fin (m + 1)) :
    cyclicDiscreteEnergyForget r x j = (Fin.snoc x (x 0) : Fin (n + 2) → M) (r j.castSucc) :=
  (rfl)

/-- Closing up the retained tuple gives precisely the selected subsequence of the closed tuple. -/
theorem snoc_cyclicDiscreteEnergyForget {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (x : Fin (n + 1) → M) :
    (Fin.snoc (cyclicDiscreteEnergyForget r x) (cyclicDiscreteEnergyForget r x 0) :
      Fin (m + 2) → M) = (Fin.snoc x (x 0) : Fin (n + 2) → M) ∘ r := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [h0, hlast]
  · simp

/-- Vertex-forgetting is continuous in all vertices. -/
@[fun_prop]
theorem continuous_cyclicDiscreteEnergyForget [TopologicalSpace M]
    (r : Fin (m + 2) ↪o Fin (n + 2)) : Continuous (cyclicDiscreteEnergyForget (M := M) r) := by
  unfold cyclicDiscreteEnergyForget
  exact continuous_pi fun j ↦ (continuous_apply (r j.castSucc)).comp
    (Continuous.finSnoc (A := fun _ : Fin (n + 2) => M) continuous_id (continuous_apply 0))

/-- Retaining every vertex is the identity. -/
@[simp]
theorem cyclicDiscreteEnergyForget_refl (x : Fin (n + 1) → M) :
    cyclicDiscreteEnergyForget (RelEmbedding.refl (· ≤ · : Fin (n + 2) → Fin (n + 2) → Prop))
      x = x := by
  ext j
  simp

/-- Successive vertex-forgetting agrees with selecting the composite subsequence. -/
@[simp]
theorem cyclicDiscreteEnergyForget_trans (r : Fin (m + 2) ↪o Fin (n + 2))
    (s : Fin (l + 2) ↪o Fin (m + 2)) (x : Fin (n + 1) → M) :
    cyclicDiscreteEnergyForget s (cyclicDiscreteEnergyForget r x) =
      cyclicDiscreteEnergyForget (s.trans r) x := by
  ext j
  -- A strictly increasing selection sends every slot but the last one away from the last slot.
  obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.mpr
    ((s.strictMono j.castSucc_lt_last).trans_le (Fin.le_last _)).ne
  simp [← hk]

variable [PseudoMetricSpace M]

/-- Forgetting vertices, while retaining the first vertex, the return time and the original times,
cannot increase the cyclic discrete energy. -/
theorem cyclicDiscreteEnergy_cyclicDiscreteEnergyForget_le {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (x : Fin (n + 1) → M) :
    cyclicDiscreteEnergy (t ∘ r) (cyclicDiscreteEnergyForget r x) ≤ cyclicDiscreteEnergy t x := by
  rw [cyclicDiscreteEnergy_def, cyclicDiscreteEnergy_def, snoc_cyclicDiscreteEnergyForget h0 hlast]
  exact discreteEnergy_comp_le ht _ r

/-- Vertex-forgetting takes a strict cyclic energy sublevel into the corresponding coarse
sublevel. The cutoff is unchanged. -/
theorem mapsTo_cyclicDiscreteEnergyForget {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (c : ℝ) :
    Set.MapsTo (cyclicDiscreteEnergyForget r) (cyclicDiscreteEnergyStrictSublevel (M := M) t c)
      (cyclicDiscreteEnergyStrictSublevel (t ∘ r) c) :=
  fun x hx ↦ (cyclicDiscreteEnergy_cyclicDiscreteEnergyForget_le ht h0 hlast x).trans_lt hx

/-- The continuous vertex-forgetting map between strict cyclic energy sublevels. Neither an
admissible mesh nor a choice of interpolating segments is needed. -/
def cyclicDiscreteEnergyForgetMap {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (c : ℝ) :
    C(cyclicDiscreteEnergyStrictSublevel (M := M) t c,
      cyclicDiscreteEnergyStrictSublevel (M := M) (t ∘ r) c) where
  toFun x := ⟨cyclicDiscreteEnergyForget r x, mapsTo_cyclicDiscreteEnergyForget ht h0 hlast c x.2⟩
  continuous_toFun :=
    ((continuous_cyclicDiscreteEnergyForget r).comp continuous_subtype_val).subtype_mk _

/-- The sublevel map has the same underlying vertex tuple as the ambient vertex-forgetting
map. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_apply {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (c : ℝ)
    (x : cyclicDiscreteEnergyStrictSublevel (M := M) t c) :
    (cyclicDiscreteEnergyForgetMap ht r h0 hlast c x : Fin (m + 1) → M) =
      cyclicDiscreteEnergyForget r x := (rfl)

/-- The identity selection induces the identity on the strict cyclic energy sublevel. The time
tuple `t ∘ RelEmbedding.refl _` is definitionally `t`, so the two sublevels coincide. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_refl {t : Fin (n + 2) → ℝ} (ht : StrictMono t) (c : ℝ) :
    cyclicDiscreteEnergyForgetMap ht (RelEmbedding.refl (· ≤ ·)) (by simp) (by simp) c =
      ContinuousMap.id (cyclicDiscreteEnergyStrictSublevel (M := M) t c) := by
  ext x : 2
  exact cyclicDiscreteEnergyForget_refl _

/-- The continuous sublevel maps commute with further vertex-forgetting. The time tuples
`(t ∘ r) ∘ s` and `t ∘ (s.trans r)` are definitionally equal, so both sides have the same target
sublevel. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_trans {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (s : Fin (l + 2) ↪o Fin (m + 2))
    (hr0 : r 0 = 0) (hrlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (hs0 : s 0 = 0) (hslast : s (Fin.last (l + 1)) = Fin.last (m + 1)) (c : ℝ) :
    (cyclicDiscreteEnergyForgetMap (ht.comp r.strictMono) s hs0 hslast c).comp
        (cyclicDiscreteEnergyForgetMap (M := M) ht r hr0 hrlast c) =
      cyclicDiscreteEnergyForgetMap ht (s.trans r)
        (by simp only [RelEmbedding.trans_apply, hs0, hr0])
        (by simp only [RelEmbedding.trans_apply, hslast, hrlast]) c := by
  ext x : 2
  exact cyclicDiscreteEnergyForget_trans r s _

end Forget

/-! ### Geodesic insertion -/

section Insert

/-- Insert vertices into a closed tuple by sampling the curves `γ i` along its edges: the fine
closed tuple is `TauCeti.discreteEnergyInsert`, and its repeated last vertex is dropped. -/
noncomputable def cyclicDiscreteEnergyInsert (t : Fin (n + 2) → ℝ)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (γ : Fin (m + 1) → ℝ → M) :
    Fin (n + 1) → M :=
  fun j ↦ discreteEnergyInsert t r h0 hlast γ j.castSucc

/-- The inserted vertex at an index is the sampled vertex of the fine closed tuple. -/
@[simp]
theorem cyclicDiscreteEnergyInsert_apply (t : Fin (n + 2) → ℝ)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (γ : Fin (m + 1) → ℝ → M)
    (j : Fin (n + 1)) :
    cyclicDiscreteEnergyInsert t r h0 hlast γ j = discreteEnergyInsert t r h0 hlast γ j.castSucc :=
  (rfl)

/-- When the last curve ends where the first one starts, closing up the inserted tuple recovers
the whole sampled closed tuple. -/
theorem snoc_cyclicDiscreteEnergyInsert {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) {γ : Fin (m + 1) → ℝ → M}
    (hγ : γ (Fin.last m) 1 = γ 0 0) :
    (Fin.snoc (cyclicDiscreteEnergyInsert t r h0 hlast γ)
      (cyclicDiscreteEnergyInsert t r h0 hlast γ 0) : Fin (n + 2) → M) =
        discreteEnergyInsert t r h0 hlast γ := by
  funext j
  refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [discreteEnergyInsert_last ht, hγ]
  · simp

/-- Inserting samples of curves joining consecutive vertices, cyclically, retains every vertex of
the coarse closed tuple: forgetting the inserted vertices recovers it. -/
theorem cyclicDiscreteEnergyForget_cyclicDiscreteEnergyInsert {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (x : Fin (m + 1) → M)
    (γ : Fin (m + 1) → ℝ → M) (hsource : ∀ i, γ i 0 = x i)
    (htarget : ∀ i, γ i 1 = x (i + 1)) :
    cyclicDiscreteEnergyForget r (cyclicDiscreteEnergyInsert t r h0 hlast γ) = x := by
  funext j
  rw [cyclicDiscreteEnergyForget_apply,
    snoc_cyclicDiscreteEnergyInsert ht r h0 hlast (by simp [htarget, hsource]),
    discreteEnergyInsert_comp_apply ht r h0 hlast (Fin.snoc x (x 0)) γ
      (fun i ↦ by simp [hsource]) (fun i ↦ by rw [snoc_self_zero_succ, htarget])]
  simp

variable [PseudoMetricSpace M]

/-- **Geodesic insertion preserves the cyclic energy.** Sampling constant-speed minimizing segments
along the edges of a closed tuple, the closing edge included, on any refinement of its times,
gives a fine closed tuple of the same energy. -/
theorem cyclicDiscreteEnergy_cyclicDiscreteEnergyInsert {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (x : Fin (m + 1) → M)
    (γ : Fin (m + 1) → ℝ → M) (hγ : ∀ i, IsGeodesicSegment (γ i) (x i) (x (i + 1))) :
    cyclicDiscreteEnergy t (cyclicDiscreteEnergyInsert t r h0 hlast γ) =
      cyclicDiscreteEnergy (t ∘ r) x := by
  rw [cyclicDiscreteEnergy_def,
    snoc_cyclicDiscreteEnergyInsert ht r h0 hlast (by simp [(hγ _).target, (hγ 0).source]),
    discreteEnergy_discreteEnergyInsert ht r h0 hlast (Fin.snoc x (x 0)) γ
      (fun i ↦ by simpa only [Fin.snoc_castSucc, snoc_self_zero_succ] using hγ i),
    cyclicDiscreteEnergy_def]

/-- In a geodesic space every closed tuple has an energy-preserving refinement retaining all its
vertices. No continuous choice of geodesics is asserted. -/
theorem exists_cyclicDiscreteEnergyForget_eq_and_cyclicDiscreteEnergy_eq [IsGeodesicSpace M]
    {t : Fin (n + 2) → ℝ} (ht : StrictMono t) (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (x : Fin (m + 1) → M) :
    ∃ y : Fin (n + 1) → M, cyclicDiscreteEnergyForget r y = x ∧
      cyclicDiscreteEnergy t y = cyclicDiscreteEnergy (t ∘ r) x := by
  choose γ hγ using fun i : Fin (m + 1) ↦
    IsGeodesicSpace.exists_isGeodesicSegment (x i) (x (i + 1))
  exact ⟨cyclicDiscreteEnergyInsert t r h0 hlast γ,
    cyclicDiscreteEnergyForget_cyclicDiscreteEnergyInsert ht r h0 hlast x γ
      (fun i ↦ (hγ i).source) (fun i ↦ (hγ i).target),
    cyclicDiscreteEnergy_cyclicDiscreteEnergyInsert ht r h0 hlast x γ hγ⟩

/-- A continuous choice of constant-speed minimizing segments along the edges of the coarse closed
tuples induces a continuous insertion map of strict cyclic energy sublevels. The choice is needed
only on the source sublevel. -/
noncomputable def cyclicDiscreteEnergyInsertMap {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (c : ℝ)
    (γ : cyclicDiscreteEnergyStrictSublevel (M := M) (t ∘ r) c → Fin (m + 1) → ℝ → M)
    (hγ : ∀ x i, IsGeodesicSegment (γ x i) ((x : Fin (m + 1) → M) i)
      ((x : Fin (m + 1) → M) (i + 1)))
    (hcont : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun x ↦ γ x i u)) :
    C(cyclicDiscreteEnergyStrictSublevel (M := M) (t ∘ r) c,
      cyclicDiscreteEnergyStrictSublevel (M := M) t c) := by
  have hf (x : cyclicDiscreteEnergyStrictSublevel (M := M) (t ∘ r) c) :
      cyclicDiscreteEnergyInsert t r h0 hlast (γ x) ∈ cyclicDiscreteEnergyStrictSublevel t c := by
    rw [mem_cyclicDiscreteEnergyStrictSublevel,
      cyclicDiscreteEnergy_cyclicDiscreteEnergyInsert ht r h0 hlast _ (γ x) (hγ x)]
    exact x.2
  exact ⟨fun x ↦ ⟨cyclicDiscreteEnergyInsert t r h0 hlast (γ x), hf x⟩,
    (continuous_pi fun j : Fin (n + 1) ↦ (continuous_apply j.castSucc).comp
      (continuous_discreteEnergyInsert ht.monotone r h0 hlast γ hcont)).subtype_mk _⟩

section Sublevel

variable {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (c : ℝ)
    (γ : cyclicDiscreteEnergyStrictSublevel (M := M) (t ∘ r) c → Fin (m + 1) → ℝ → M)
    (hγ : ∀ x i, IsGeodesicSegment (γ x i) ((x : Fin (m + 1) → M) i)
      ((x : Fin (m + 1) → M) (i + 1)))
    (hcont : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun x ↦ γ x i u))

/-- The underlying tuple of the sublevel insertion is the sampled fine tuple. -/
@[simp]
theorem cyclicDiscreteEnergyInsertMap_apply
    (x : cyclicDiscreteEnergyStrictSublevel (M := M) (t ∘ r) c) :
    (cyclicDiscreteEnergyInsertMap ht r h0 hlast c γ hγ hcont x : Fin (n + 1) → M) =
      cyclicDiscreteEnergyInsert t r h0 hlast (γ x) := (rfl)

/-- Forgetting the newly inserted vertices recovers the original sublevel point. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_cyclicDiscreteEnergyInsertMap
    (x : cyclicDiscreteEnergyStrictSublevel (M := M) (t ∘ r) c) :
    cyclicDiscreteEnergyForgetMap ht r h0 hlast c
      (cyclicDiscreteEnergyInsertMap ht r h0 hlast c γ hγ hcont x) = x :=
  Subtype.ext <| by
    rw [cyclicDiscreteEnergyForgetMap_apply, cyclicDiscreteEnergyInsertMap_apply]
    exact cyclicDiscreteEnergyForget_cyclicDiscreteEnergyInsert ht r h0 hlast x (γ x)
      (fun i ↦ (hγ x i).source) (fun i ↦ (hγ x i).target)

/-- Forgetting the newly inserted vertices is a left inverse to continuous geodesic insertion of
closed tuples. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_comp_cyclicDiscreteEnergyInsertMap :
    (cyclicDiscreteEnergyForgetMap ht r h0 hlast c).comp
        (cyclicDiscreteEnergyInsertMap ht r h0 hlast c γ hγ hcont) =
      ContinuousMap.id (cyclicDiscreteEnergyStrictSublevel (M := M) (t ∘ r) c) := by
  ext x : 1
  simp

end Sublevel

end Insert

end TauCeti
