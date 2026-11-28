/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Topology.Sym.Disjoint
import TauCeti.Topology.Covering.Graph

/-!
# The incidence correspondence of a map into a symmetric power

A map `v : Y → Sym α n` assigns to every point `y` an unordered `n`-tuple of points of `α`. Its
*incidence correspondence* is the set of pairs `(y, z)` with `z` a point of the tuple `v y`, that is
the preimage under `v × id` of the universal divisor `{(s, z) | z ∈ s}` of `Sym α n × α`. It comes
with the projection `(y, z) ↦ y`, whose fibre over `y` is the set of points of `v y`. This file
shows that over the tuples without repeated points, the *reduced* tuples, this projection is an
`n`-sheeted covering.

For a branched cover `f : S → Y` of degree `n` and a map `u : S → α`, the map
`y ↦ u_* (f^* y)` (`TauCeti.RiemannSurface.FiniteHolomorphicMap.fiberSym`) sends `y` to the images
of the points over `y`. Going back from a map `v : Y → Sym α n` to a cover of `Y` starts from the
incidence correspondence of `v`, the pulled-back universal divisor. Over the reduced tuples it is
itself an unbranched cover of `Y`, carrying the map `(y, z) ↦ z` to `α`; at tuples with repeated
points it has to be normalized.

* **Moving points.** Near a reduced tuple `s₀` the points of a tuple can be labelled continuously:
  there are an open neighbourhood `W` of `s₀` and maps `σ i : Sym α n → α`, continuous on `W`, such
  that every `s ∈ W` is the tuple of the pairwise distinct points `σ 0 s, …, σ (n - 1) s`
  (`Sym.exists_isOpen_continuousOn_ofFn_eq`). They are the inverse of the open embedding of a
  product of pairwise disjoint neighbourhoods of the points of `s₀`
  (`Sym.isOpenEmbedding_ofFn_map`). In particular the reduced tuples form an open set
  (`Sym.isOpen_setOf_nodup`).
* **The incidence correspondence is closed** in `Y × α` for continuous `v`
  (`Sym.isClosed_setOf_snd_mem`).
* **Covering.** For continuous `v`, the projection from the incidence correspondence to `Y` is
  evenly covered, with fibre `Fin n`, near every `y` at which `v y` is reduced
  (`Sym.isEvenlyCovered_fst_mem`), so it is a covering map over the set of such `y`
  (`Sym.isCoveringMapOn_fst_mem`), with exactly `n` points in each fibre there
  (`Sym.natCard_preimage_fst_mem`).

At a tuple with a repeated point the points cannot be labelled continuously in general: on the
symmetric square of `ℂ`, read in elementary-symmetric coordinates as the monic quadratics, the two
roots of `z² - y` are exchanged by a loop of `y` around `0`. There the incidence correspondence is
branched, and recovering a branched cover requires its normalization.

## References

* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), 955–1097, §13 (holomorphic curves in `Σ × [0, 1] × ℝ` and disks in `Sym^g(Σ)`).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004), 1027–1158, §2.
-/

public section

open Topology Set

namespace Sym

variable {α : Type*} [TopologicalSpace α] [T2Space α] {n : ℕ}

/-- **Near a reduced tuple the points move continuously.** If the unordered tuple `s₀` has no
repeated point, there are an open neighbourhood `W` of `s₀` and labels `σ i`, continuous on `W`,
such that every tuple `s ∈ W` consists of the pairwise distinct points `σ i s`. -/
theorem exists_isOpen_continuousOn_ofFn_eq {s₀ : Sym α n} (hs₀ : (s₀ : Multiset α).Nodup) :
    ∃ W : Set (Sym α n), IsOpen W ∧ s₀ ∈ W ∧ ∃ σ : Fin n → Sym α n → α,
      (∀ i, ContinuousOn (σ i) W) ∧
        ∀ s ∈ W, ofFn (fun i => σ i s) = s ∧ Function.Injective fun i => σ i s := by
  obtain ⟨p, rfl⟩ := ofFn_surjective s₀
  have hp : Function.Injective p := nodup_coe_ofFn_iff.1 hs₀
  -- pairwise disjoint open neighbourhoods `V i` of the points `p i`
  obtain ⟨U, hU, hdisj⟩ := (finite_range p).t2_separation
  let V : Fin n → Set α := fun i => U (p i)
  have hVdisj : Pairwise (Function.onFun Disjoint V) := fun i j hij =>
    hdisj (mem_range_self i) (mem_range_self j) (hp.ne hij)
  -- their product is an open subspace of the symmetric power
  have hE : IsOpenEmbedding fun x : ∀ i, V i => ofFn fun i => (x i : α) :=
    isOpenEmbedding_ofFn_map (fun i => ((↑) : V i → α))
      (fun i => (hU (p i)).2.isOpenEmbedding_subtypeVal)
      (by simpa only [Subtype.range_coe] using hVdisj)
  have : Nonempty (∀ i, V i) := ⟨fun i => ⟨p i, (hU (p i)).1⟩⟩
  let e := hE.toOpenPartialHomeomorph _
  have htarget : e.target = range fun x : ∀ i, V i => ofFn fun i => (x i : α) :=
    hE.toOpenPartialHomeomorph_target
  refine ⟨e.target, e.open_target, htarget ▸ ⟨fun i => ⟨p i, (hU (p i)).1⟩, rfl⟩,
    fun i s => (e.symm s i : α), fun i => ?_, fun s hs => ⟨e.right_inv hs, fun i j hij => ?_⟩⟩
  · exact (continuous_subtypeVal.comp (continuous_apply i)).comp_continuousOn e.continuousOn_symm
  · by_contra hne
    have hij' : (e.symm s i : α) = e.symm s j := hij
    exact disjoint_left.1 (hVdisj hne) (e.symm s i).property (hij' ▸ (e.symm s j).property)

/-- **The reduced tuples form an open set.** In a Hausdorff space, the unordered `n`-tuples without
repeated points form an open subset of the symmetric power. -/
theorem isOpen_setOf_nodup : IsOpen {s : Sym α n | (s : Multiset α).Nodup} := by
  refine isOpen_iff_mem_nhds.2 fun s₀ hs₀ => ?_
  obtain ⟨W, hW, hs₀W, σ, -, hσ⟩ := exists_isOpen_continuousOn_ofFn_eq hs₀
  filter_upwards [hW.mem_nhds hs₀W] with s hs
  have h := nodup_coe_ofFn_iff.2 (hσ s hs).2
  rwa [(hσ s hs).1] at h

/-- **The universal divisor is closed.** In a Hausdorff space, the pairs `(y, z)` with `z` a point
of the tuple `v y` form a closed set, for every continuous map `v` into the symmetric power. -/
theorem isClosed_setOf_snd_mem {Y : Type*} [TopologicalSpace Y] {v : Y → Sym α n}
    (hv : Continuous v) : IsClosed {q : Y × α | q.2 ∈ v q.1} := by
  -- it is the preimage of the universal divisor `{(s, z) | z ∈ s}`
  suffices h : IsClosed {q : Sym α n × α | q.2 ∈ q.1} from
    h.preimage (hv.prodMap continuous_id)
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun q (hq : q.2 ∉ q.1) => ?_)
  obtain ⟨p, hp⟩ := ofFn_surjective q.1
  have hne (i : Fin n) : p i ≠ q.2 := fun h => hq (by rw [← hp]; exact mem_ofFn.2 ⟨i, h⟩)
  -- separate each point of the tuple from `z`
  choose u w hu hw hpu hzw hdisj using fun i => t2_separation (hne i)
  have hN : ofFn '' univ.pi u ∈ 𝓝 q.1 :=
    hp ▸ (isOpenMap_ofFn _ (isOpen_set_pi finite_univ fun i _ => hu i)).mem_nhds
      ⟨p, fun i _ => hpu i, rfl⟩
  have hW : ⋂ i, w i ∈ 𝓝 q.2 := (isOpen_iInter_of_finite hw).mem_nhds (mem_iInter.2 hzw)
  filter_upwards [prod_mem_nhds hN hW] with q' ⟨⟨p', hp', hq'⟩, hz'⟩ hmem
  rw [mem_ofPred_eq, ← hq', mem_ofFn] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact disjoint_left.1 (hdisj i) (hp' i (mem_univ i)) (hi ▸ mem_iInter.1 hz' i)

/-- **The incidence correspondence is evenly covered near a reduced tuple.** For a continuous map
`v` into the symmetric power, the projection `(y, z) ↦ y` from the pairs with `z` a point of
`v y` is evenly covered, with fibre `Fin n`, near every `y₀` at which `v y₀` has no repeated
point. -/
theorem isEvenlyCovered_fst_mem {Y : Type*} [TopologicalSpace Y] {v : Y → Sym α n}
    (hv : Continuous v) {y₀ : Y} (hy₀ : (v y₀ : Multiset α).Nodup) :
    IsEvenlyCovered (fun q : {q : Y × α // q.2 ∈ v q.1} => q.val.1) y₀ (Fin n) := by
  obtain ⟨W, hW, hy₀W, σ, hσc, hσ⟩ := exists_isOpen_continuousOn_ofFn_eq hy₀
  -- over `v ⁻¹' W` the points of `v y` are labelled by the continuous maps `σ i ∘ v`
  refine IsEvenlyCovered.subtype_fst_of_continuousOn (P := fun y z => z ∈ v y) (U := v ⁻¹' W)
    (σ := fun i y => σ i (v y)) (hW.preimage hv) hy₀W
    (fun i => (hσc i).comp hv.continuousOn fun _ hy => hy) fun y hy => ⟨(hσ _ hy).2, fun z => ?_⟩
  rw [← mem_ofFn (f := fun i => σ i (v y)), (hσ _ hy).1]

/-- **The incidence correspondence is a covering over the reduced tuples.** For a continuous map `v`
into the symmetric power, the projection `(y, z) ↦ y` from the pairs with `z` a point of `v y` is a
covering map over the set of `y` at which `v y` has no repeated point. -/
theorem isCoveringMapOn_fst_mem {Y : Type*} [TopologicalSpace Y] {v : Y → Sym α n}
    (hv : Continuous v) :
    IsCoveringMapOn (fun q : {q : Y × α // q.2 ∈ v q.1} => q.val.1)
      {y | (v y : Multiset α).Nodup} :=
  fun _ hy => (isEvenlyCovered_fst_mem hv hy).to_isEvenlyCovered_preimage

/-- **A map to the reduced tuples has a covering as incidence correspondence.** If the continuous
map `v` only takes tuples without repeated points as values, the projection `(y, z) ↦ y` from the
pairs with `z` a point of `v y` is a covering map. -/
theorem isCoveringMap_fst_mem {Y : Type*} [TopologicalSpace Y] {v : Y → Sym α n}
    (hv : Continuous v) (hnodup : ∀ y, (v y : Multiset α).Nodup) :
    IsCoveringMap (fun q : {q : Y × α // q.2 ∈ v q.1} => q.val.1) :=
  isCoveringMap_iff_isCoveringMapOn_univ.2 <|
    (isCoveringMapOn_fst_mem hv).mono fun y _ => hnodup y

omit [TopologicalSpace α] [T2Space α] in
/-- **The incidence correspondence has `n` points over a reduced tuple.** The fibre of the
projection `(y, z) ↦ y` over `y` consists of the points of `v y`, so there are `n` of them when
`v y` has no repeated point. -/
theorem natCard_preimage_fst_mem {Y : Type*} {v : Y → Sym α n} {y : Y}
    (hy : (v y : Multiset α).Nodup) :
    Nat.card ((fun q : {q : Y × α // q.2 ∈ v q.1} => q.val.1) ⁻¹' {y}) = n := by
  classical
  -- a point of the fibre over `y` is a point of `v y`
  let e : (fun q : {q : Y × α // q.2 ∈ v q.1} => q.val.1) ⁻¹' {y} ≃ {z // z ∈ v y} :=
    { toFun q := ⟨q.val.val.2, by obtain ⟨⟨⟨y', z⟩, hz⟩, rfl : y' = y⟩ := q; exact hz⟩
      invFun z := ⟨⟨(y, z.val), z.property⟩, rfl⟩
      left_inv q := by obtain ⟨⟨⟨y', z⟩, hz⟩, rfl : y' = y⟩ := q; rfl
      right_inv _ := rfl }
  rw [Nat.card_congr (e.trans (Equiv.subtypeEquivRight fun z =>
      (Multiset.mem_toFinset (s := (v y : Multiset α))).symm)),
    Nat.card_eq_fintype_card, Fintype.card_coe, Multiset.toFinset_card_of_nodup hy, Sym.card_coe]

end Sym
