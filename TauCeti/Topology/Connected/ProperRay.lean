/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.FilledHull

/-!
# Locally finite proper rays

Let `X` be a locally compact, σ-compact Hausdorff space which is locally path-connected and has
no compact connected component; for instance a second-countable manifold none of whose components
is compact. Then every point of `X` starts a ray, given as a sequence of paths, which leaves
every compact set, and these rays can be chosen locally finitely: for a locally finite family of
points `p i` there are paths `q i k` from `z i k` to `z i (k + 1)` with `z i 0 = p i` such that
the whole family of path images, indexed by `i` and `k`, is locally finite.

This is the topological input for the vanishing of degree-zero Borel–Moore homology on spaces
with no compact connected component. Each path `q i k` is a singular `1`-simplex with boundary
`[z i (k + 1)] - [z i k]`, and the paths of all the rays form a locally finite `1`-chain. Taking
every path with coefficient `-1`, the boundary telescopes along each ray to the starting point
`[p i]`.

The construction goes through the relatively compact connected components of the complement of a
compact set `K`. Their union with `K` is the filled hull of `K` for the bornology of relatively
compact sets, and it is again compact
(`IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl`, in
`TauCeti/Topology/FilledHull.lean`). Along a compact exhaustion `K n` one then chooses nested
components of the complements `(K n)ᶜ` with noncompact closure, and joins successive points by
paths inside them.

## Main results

* `TauCeti.exists_locallyFinite_range_path`: a locally finite family of points starts a locally
  finite family of subdivided proper rays.

## References

* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V
  (Borel–Moore homology of noncompact spaces).
* H. Freudenthal, *Über die Enden topologischer Räume und Gruppen*, Math. Z. 33 (1931), 692–713
  (ends of a space and the components of complements of compact sets).
-/

public section

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]

namespace TauCeti

section Rays

variable [LocallyPathConnectedSpace X] [SigmaCompactSpace X]

/-- Along the chosen compact exhaustion, the component of `y` in the complement of the `n`-th
compact set has noncompact closure. -/
private def Escapes (n : ℕ) (y : X) : Prop :=
  ¬IsCompact (closure (connectedComponentIn (CompactExhaustion.choice X n)ᶜ y))

omit [T2Space X] [LocallyPathConnectedSpace X] in
private lemma Escapes.mono {m n : ℕ} {y : X} (h : Escapes n y) (hmn : m ≤ n) : Escapes m y :=
  fun hc ↦ h <| hc.of_isClosed_subset isClosed_closure <| closure_mono <|
    connectedComponentIn_mono _ <| compl_subset_compl.2 <| (CompactExhaustion.choice X).subset hmn

/-- From a point escaping past the `m`-th compact set, a ray leaves every compact set, staying
past the `(m + k)`-th compact set along its `k`-th path. -/
private lemma exists_path_seq (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) {m : ℕ}
    {y : X} (hy : Escapes m y) :
    ∃ z : ℕ → X, z 0 = y ∧ ∀ k, ∃ γ : Path (z k) (z (k + 1)),
      range γ ⊆ (CompactExhaustion.choice X (m + k))ᶜ := by
  set K := CompactExhaustion.choice X
  obtain ⟨z, hz0, hz⟩ := exists_seq_not_isCompact_closure_connectedComponentIn_compl hX
    (K := fun k ↦ K (m + k)) (fun k ↦ K.isCompact _) hy
  refine ⟨z, hz0, fun k ↦ ?_⟩
  have hjoin : JoinedIn (connectedComponentIn (K (m + k))ᶜ (z k)) (z k) (z (k + 1)) :=
    (K.isCompact _).isClosed.isOpen_compl.joinedIn_of_mem_connectedComponentIn
      (notMem_of_not_isCompact_closure_connectedComponentIn_compl (hz k).1) (hz k).2
  exact ⟨hjoin.somePath, range_subset_iff.2 fun t ↦
    connectedComponentIn_subset _ _ (hjoin.somePath_mem t)⟩

/-- Every point starts a subdivided ray whose `k`-th path avoids the `n`-th compact set of the
exhaustion whenever `n < k`, and avoids it from the start whenever the point itself escapes past
it. -/
private lemma exists_path_seq_of_mem (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) (x : X) :
    ∃ z : ℕ → X, z 0 = x ∧ ∀ k, ∃ γ : Path (z k) (z (k + 1)), ∀ n, (Escapes n x ∨ n < k) →
      range γ ⊆ (CompactExhaustion.choice X n)ᶜ := by
  set K := CompactExhaustion.choice X
  by_cases hx : ∃ n, Escapes n x
  · -- Start at `x` itself, past the last compact set it escapes.
    classical
    have hbound : ∀ n, Escapes n x → n ≤ K.find x := fun n hn ↦
      le_of_lt <| not_le.1 fun h ↦
        notMem_of_not_isCompact_closure_connectedComponentIn_compl hn (K.mem_iff_find_le.2 h)
    obtain ⟨n₀, hn₀⟩ := hx
    set m := Nat.findGreatest (Escapes · x) (K.find x)
    have hm : Escapes m x := Nat.findGreatest_spec (P := (Escapes · x)) (hbound n₀ hn₀) hn₀
    obtain ⟨z, hz0, hz⟩ := exists_path_seq hX hm
    refine ⟨z, hz0, fun k ↦ ?_⟩
    obtain ⟨γ, hγ⟩ := hz k
    refine ⟨γ, fun n hn ↦ hγ.trans (compl_subset_compl.2 (K.subset ?_))⟩
    rcases hn with hn | hn
    · exact (Nat.le_findGreatest (hbound n hn) hn).trans (Nat.le_add_right _ _)
    · exact hn.le.trans (Nat.le_add_left _ _)
  · -- Otherwise first join `x` to an escaping point of its connected component.
    simp only [not_exists] at hx
    obtain ⟨y, hyx, hy⟩ := exists_mem_not_isCompact_closure_connectedComponentIn_compl hX
      (S := connectedComponent x) (by rw [isClosed_connectedComponent.closure_eq]; exact hX x)
      (K.isCompact 0)
    obtain ⟨z, hz0, hz⟩ := exists_path_seq hX (m := 0) hy
    have hxy : Joined x (z 0) := by
      rw [hz0, ← mem_pathComponent_iff, pathComponent_eq_connectedComponent,
        connectedComponent_eq hyx]
      exact mem_connectedComponent
    refine ⟨fun k ↦ Nat.casesOn k x z, rfl, fun k ↦ ?_⟩
    cases k with
    | zero => exact ⟨hxy.somePath, fun n hn ↦ by simp [hx n] at hn⟩
    | succ k =>
      obtain ⟨γ, hγ⟩ := hz k
      refine ⟨γ, fun n hn ↦ hγ.trans (compl_subset_compl.2 (K.subset ?_))⟩
      rcases hn with hn | hn
      · exact absurd hn (hx n)
      · simpa using Nat.lt_succ_iff.1 hn

/-- **Locally finite proper rays.** In a locally compact, σ-compact Hausdorff, locally
path-connected space with no compact connected component, every locally finite family of points
`p i` starts a locally finite family of subdivided rays: there are points `z i k` with
`z i 0 = p i` and paths `q i k` from `z i k` to `z i (k + 1)` whose images form a locally finite
family indexed by `(i, k)`. In particular every compact set meets only finitely many of these
paths, so each ray `k ↦ q i k` eventually leaves every compact set. -/
theorem exists_locallyFinite_range_path (hX : ∀ x : X, ¬IsCompact (connectedComponent x))
    {ι : Type*} (p : ι → X)
    (hp : LocallyFinite fun i ↦ ({p i} : Set X)) :
    ∃ z : ι → ℕ → X, ∃ q : ∀ i k, Path (z i k) (z i (k + 1)), (∀ i, z i 0 = p i) ∧
      LocallyFinite fun ik : ι × ℕ ↦ range (q ik.1 ik.2) := by
  set K := CompactExhaustion.choice X
  choose z hz0 hz using fun i ↦ exists_path_seq_of_mem hX (p i)
  choose q hq using hz
  refine ⟨z, q, hz0, fun w ↦ ?_⟩
  obtain ⟨N, hN⟩ := K.exists_mem_nhds w
  refine ⟨K N, hN, ?_⟩
  -- A path meeting `K N` lies on a ray starting in the compact filled hull of `K N`, and is
  -- among the first `N + 1` paths of that ray.
  have hfin := hp.finite_nonempty_inter_compact
    ((K.isCompact N).isCompact_setOf_isCompact_closure_connectedComponentIn_compl hX)
  refine ((hfin.prod (Set.finite_le_nat N)).subset fun ⟨i, k⟩ ⟨y, hyq, hyK⟩ ↦ ?_)
  have hmeet : ¬range (q i k) ⊆ (K N)ᶜ := fun h ↦ h hyq hyK
  refine ⟨⟨p i, rfl, not_not.1 fun h ↦ hmeet (hq i k N (Or.inl h))⟩, ?_⟩
  exact not_lt.1 fun h ↦ hmeet (hq i k N (Or.inr h))

end Rays

end TauCeti
