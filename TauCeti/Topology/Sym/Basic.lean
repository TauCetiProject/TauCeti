/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Separation.Hausdorff
public import TauCeti.Data.Sym.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The symmetric power of a topological space

The `n`-th symmetric power `Sym α n` of a type is the type of unordered `n`-tuples of points of
`α`. It is the quotient of the space `Fin n → α` of ordered tuples by the permutation action, and
this file gives it the corresponding quotient topology, together with the API that a quotient
topology is used through: the quotient map is continuous, and a map out of `Sym α n` is continuous
exactly when its composition with the quotient map is.

The quotient map is `Sym.ofFn` of `TauCeti/Data/Sym/Basic.lean`, which reads an ordered
tuple as an unordered one; the `Fin n → α` form is the one that carries a product topology, so it
is what the quotient topology is defined against. Its surjectivity and the description
`Sym.ofFn_eq_ofFn_iff` of its fibres as the orbits of the permutation action are the two
facts about it used below.

## Main declarations

* `Sym.preimage_image_ofFn`: the saturation of a set of ordered tuples under `ofFn` is the
  union of its reindexings.
* `Sym.instTopologicalSpace`: the quotient topology on `Sym α n`, coinduced along `ofFn`.
* `Sym.isQuotientMap_ofFn`, `Sym.continuous_ofFn` and
  `Sym.continuous_iff_comp_ofFn`: the resulting quotient-map API.
* `Sym.isOpenMap_ofFn`, `Sym.isClosedMap_ofFn` and
  `Sym.isOpenQuotientMap_ofFn`: the quotient map is open and closed, the permutation group
  being finite.
* `Sym.frequently_ofFn_eq_ofFn_and_ne`: in a space without isolated points, the quotient map is
  not injective near a tuple with two equal points.
* `Sym.continuous_map`, `Sym.isOpenMap_map` and
  `Sym.isOpenEmbedding_map`: the `n`-th symmetric power of a continuous, open, or open
  embedding map is again one; in particular the symmetric power of an open subspace is an open
  subspace of the symmetric power.
* `Sym.isOpen_setOf_forall_mem`: the tuples with all their points in an open set form an
  open set.
* `Sym.continuous_append` and `Sym.isOpenMap_append`: concatenation of symmetric
  powers is continuous and open.
* `Sym.continuous_sum_map`: the sum of a continuous function over the points of an unordered
  tuple, counted with multiplicity, is continuous.
* `Sym.instCompactSpace` and `Sym.instT2Space`: the symmetric power of a compact
  space is compact, and that of a Hausdorff space is Hausdorff.

The symmetric power `Sym^g(Σ)` of a surface must be a space before it can be given a complex
structure; this file supplies the underlying topology, and
`TauCeti/Analysis/Polynomial/SymmetricPower.lean` identifies it, over an algebraically closed
normed field, with affine space through the elementary symmetric functions.
-/

public section

open Topology

namespace Sym

variable {α β : Type*} {m n : ℕ}

/-! ### The fibres of the quotient map -/

/-- The saturation of a set of ordered tuples under `Sym.ofFn` is the union of its reindexings. -/
theorem preimage_image_ofFn (s : Set (Fin n → α)) :
    ofFn ⁻¹' (ofFn '' s) = ⋃ σ : Equiv.Perm (Fin n), (· ∘ σ) ⁻¹' s := by
  ext g
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨f, hf, hfg⟩
    obtain ⟨σ, rfl⟩ := ofFn_eq_ofFn_iff.1 hfg
    exact ⟨σ.symm, by simpa [Function.comp_assoc] using hf⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨g ∘ σ, hσ, ofFn_comp_perm σ g⟩

/-! ### The quotient topology -/

variable [TopologicalSpace α] [TopologicalSpace β]

/-- The `n`-th symmetric power of a topological space carries the quotient topology of the
permutation action on ordered `n`-tuples, presented as the topology coinduced along
`Sym.ofFn`. -/
instance instTopologicalSpace : TopologicalSpace (Sym α n) :=
  .coinduced ofFn inferInstance

/-- The quotient map onto the symmetric power is continuous. -/
@[continuity, fun_prop]
theorem continuous_ofFn : Continuous (ofFn : (Fin n → α) → Sym α n) :=
  continuous_coinduced_rng

/-- `Sym.ofFn` presents `Sym α n` as a topological quotient of `Fin n → α`. -/
theorem isQuotientMap_ofFn : IsQuotientMap (ofFn : (Fin n → α) → Sym α n) :=
  ⟨⟨rfl⟩, ofFn_surjective⟩

/-- A map out of a symmetric power is continuous exactly when the associated map on ordered
tuples is; this is the universal property of the quotient topology. -/
theorem continuous_iff_comp_ofFn {g : Sym α n → β} : Continuous g ↔ Continuous (g ∘ ofFn) :=
  isQuotientMap_ofFn.continuous_iff

/-- The quotient map onto the symmetric power is open: the saturation of an open set is the union
of its reindexings, each of them open. -/
theorem isOpenMap_ofFn : IsOpenMap (ofFn : (Fin n → α) → Sym α n) := fun s hs => by
  rw [← isQuotientMap_ofFn.isCoinducing.isOpen_preimage, preimage_image_ofFn]
  exact isOpen_iUnion fun σ => hs.preimage (Pi.continuous_precomp σ)

/-- The quotient map onto the symmetric power is closed: the saturation of a closed set is the
union of its reindexings, a *finite* union of closed sets. -/
theorem isClosedMap_ofFn : IsClosedMap (ofFn : (Fin n → α) → Sym α n) := fun s hs => by
  rw [← isQuotientMap_ofFn.isCoinducing.isClosed_preimage, preimage_image_ofFn]
  exact isClosed_iUnion_of_finite fun σ => hs.preimage (Pi.continuous_precomp σ)

/-- The quotient map onto the symmetric power is an open quotient map. -/
theorem isOpenQuotientMap_ofFn : IsOpenQuotientMap (ofFn : (Fin n → α) → Sym α n) :=
  .of_isOpenMap_isQuotientMap isOpenMap_ofFn isQuotientMap_ofFn

open Filter Function in
/-- In a space without isolated points, such as a manifold, if two points of a tuple `p` coincide,
then the quotient map onto the symmetric power is not injective on any neighbourhood of `p`:
arbitrarily close to `p` there are two different tuples with the same underlying unordered tuple,
obtained by moving one of the two coinciding points and then exchanging them. -/
theorem frequently_ofFn_eq_ofFn_and_ne [PerfectSpace α] {p : Fin n → α} {i j : Fin n}
    (hij : i ≠ j) (hp : p i = p j) :
    ∃ᶠ w : (Fin n → α) × (Fin n → α) in 𝓝 (p, p), Sym.ofFn w.1 = Sym.ofFn w.2 ∧ w.1 ≠ w.2 := by
  classical
  -- move the `i`-th point to a nearby `q ≠ p i`, and swap the `i`-th and `j`-th points
  set w : α → Fin n → α := fun q => update p i q
  have hw : Tendsto (fun q => (w q, w q ∘ Equiv.swap i j)) (𝓝[≠] (p i)) (𝓝 (p, p)) := by
    have h₁ : Tendsto w (𝓝[≠] (p i)) (𝓝 p) := by
      simpa [w] using
        ((continuous_const.update (f := fun _ : α => p) i continuous_id).tendsto (p i)).mono_left
          nhdsWithin_le_nhds
    have hswap : (fun k => p (Equiv.swap i j k)) = p := funext (Equiv.apply_swap_eq_self hp)
    have h₂ : Tendsto (fun q => w q ∘ Equiv.swap i j) (𝓝[≠] (p i)) (𝓝 p) := by
      have h := ((continuous_pi fun k => continuous_apply (Equiv.swap i j k)).tendsto p).comp h₁
      rw [hswap] at h
      exact h
    exact h₁.prodMk_nhds h₂
  refine hw.frequently (Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin] with q hq
  refine ⟨(ofFn_comp_perm _ _).symm, fun h => hq ?_⟩
  -- the two tuples differ at `i`, where they are `q` and `p j = p i`
  simpa [w, update_of_ne hij.symm, ← hp] using congrFun h i

/-! ### Functoriality -/

/-- The symmetric power of a continuous map is continuous. -/
@[continuity, fun_prop]
theorem continuous_map {f : α → β} (hf : Continuous f) :
    Continuous (Sym.map f : Sym α n → Sym β n) := by
  rw [continuous_iff_comp_ofFn, map_comp_ofFn]
  exact continuous_ofFn.comp (Continuous.piMap fun _ => hf)

/-- The symmetric power of an open map is open. -/
theorem isOpenMap_map {f : α → β} (hf : IsOpenMap f) :
    IsOpenMap (Sym.map f : Sym α n → Sym β n) := by
  rw [isOpenQuotientMap_ofFn.isOpenMap_iff, map_comp_ofFn]
  exact isOpenMap_ofFn.comp (IsOpenMap.piMap (fun _ => hf) (by simp))

/-- The symmetric power of an open embedding is an open embedding: the `n`-th symmetric power of
an open subspace is an open subspace of the `n`-th symmetric power. -/
theorem isOpenEmbedding_map {f : α → β} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (Sym.map f : Sym α n → Sym β n) :=
  .of_continuous_injective_isOpenMap (continuous_map hf.continuous)
    (Sym.map_injective hf.injective n) (isOpenMap_map hf.isOpenMap)

/-- The unordered tuples all of whose points lie in an open set form an open subset of the
symmetric power: the range of the symmetric power of the inclusion of that open set. -/
theorem isOpen_setOf_forall_mem {V : Set α} (hV : IsOpen V) :
    IsOpen {s : Sym α n | ∀ a ∈ s, a ∈ V} := by
  convert (isOpenEmbedding_map (n := n) hV.isOpenEmbedding_subtypeVal).isOpen_range using 1
  ext s
  rw [Set.mem_ofPred_eq, mem_range_map, Subtype.range_coe]

omit [TopologicalSpace α] in
/-- Concatenation of unordered tuples read on ordered ones: it is presented by `Fin.append`, as an
equality of maps out of pairs of ordered tuples. -/
private theorem append_comp_prodMap_ofFn :
    (fun p : Sym α n × Sym α m => p.1.append p.2) ∘ Prod.map ofFn ofFn =
      ofFn ∘ fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2 := by
  funext p
  obtain ⟨f, g⟩ := p
  exact (ofFn_fin_append f g).symm

/-- Concatenation of two symmetric-power points is continuous. -/
@[continuity, fun_prop]
theorem continuous_append :
    Continuous fun p : Sym α n × Sym α m => p.1.append p.2 := by
  rw [← (isOpenQuotientMap_ofFn.prodMap isOpenQuotientMap_ofFn).continuous_comp_iff,
    append_comp_prodMap_ofFn]
  exact continuous_ofFn.comp (Fin.continuous_append n m)

/-- Concatenation of two symmetric-power points is an open map. -/
theorem isOpenMap_append :
    IsOpenMap fun p : Sym α n × Sym α m => p.1.append p.2 := by
  have hcoe : ⇑(Fin.appendHomeomorph (X := α) n m) =
      fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2 := by
    funext q i
    simp
  rw [(isOpenQuotientMap_ofFn.prodMap isOpenQuotientMap_ofFn).isOpenMap_iff,
    append_comp_prodMap_ofFn, ← hcoe]
  exact isOpenMap_ofFn.comp (Fin.appendHomeomorph n m).isOpenMap

/-! ### Sums over the points of a tuple -/

/-- Summing a continuous function over the points of an unordered tuple, counted with
multiplicity, is continuous on the symmetric power: read on ordered tuples it is
`f ↦ ∑ i, g (f i)`. -/
@[continuity, fun_prop]
theorem continuous_sum_map {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    {g : α → M} (hg : Continuous g) :
    Continuous fun s : Sym α n => ((s : Multiset α).map g).sum := by
  rw [continuous_iff_comp_ofFn]
  have h : (fun s : Sym α n => ((s : Multiset α).map g).sum) ∘ ofFn =
      fun f : Fin n → α => ∑ i, g (f i) := by
    funext f
    simp [Fin.sum_ofFn]
  rw [h]
  exact continuous_finsetSum _ fun i _ => hg.comp (continuous_apply i)

/-! ### The first symmetric power -/

/-- **The first symmetric power of a space is the space itself**: `Sym.oneEquiv`, sending a
point to the singleton, is a homeomorphism `α ≃ₜ Sym α 1`. -/
def oneHomeomorph : α ≃ₜ Sym α 1 where
  toEquiv := oneEquiv
  continuous_toFun := (continuous_ofFn.comp (continuous_pi fun _ => continuous_id)).congr
    fun a => ofFn_eq_oneEquiv fun _ => a
  continuous_invFun := by
    rw [continuous_iff_comp_ofFn]
    exact (continuous_apply 0).congr fun f => by
      rw [Function.comp_apply, ofFn_eq_oneEquiv]
      exact (oneEquiv.left_inv (f 0)).symm

@[simp]
theorem oneHomeomorph_apply (a : α) : oneHomeomorph a = oneEquiv a :=
  (rfl)

@[simp]
theorem oneHomeomorph_symm_apply (s : Sym α 1) : oneHomeomorph.symm s = oneEquiv.symm s :=
  (rfl)

/-! ### Separation and compactness -/

/-- The symmetric power of a compact space is compact, being a continuous image of a finite power
of that space. -/
instance instCompactSpace [CompactSpace α] : CompactSpace (Sym α n) :=
  ⟨by
    rw [← Set.image_univ_of_surjective (ofFn_surjective (α := α) (n := n))]
    exact isCompact_univ.image continuous_ofFn⟩

/-- The symmetric power of a Hausdorff space is Hausdorff: `ofFn` is an open quotient map, and the
relation it induces is the finite union, over permutations, of the graphs of the reindexing maps,
hence closed. -/
instance instT2Space [T2Space α] : T2Space (Sym α n) := by
  rw [t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_ofFn]
  have hrel : {q : (Fin n → α) × (Fin n → α) | ofFn q.1 = ofFn q.2} =
      ⋃ σ : Equiv.Perm (Fin n), {q : (Fin n → α) × (Fin n → α) | q.1 ∘ σ = q.2} := by
    ext q
    simpa using ofFn_eq_ofFn_iff
  rw [hrel]
  exact isClosed_iUnion_of_finite fun σ =>
    isClosed_eq ((Pi.continuous_precomp σ).comp continuous_fst) continuous_snd

end Sym
