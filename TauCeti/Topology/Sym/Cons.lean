/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sym.Basic

/-!
# The unordered tuples through a fixed point

For a point `a` of a topological space `α`, adjoining `a` is a map `Sym α n → Sym α (n + 1)` whose
range is the set `TauCeti.Sym.basepointDivisor a` of unordered tuples containing `a`
(`TauCeti.Sym.range_cons`). This
file shows that the map is continuous and, as soon as the points of `α` are closed, a closed
embedding. The unordered `(n + 1)`-tuples through `a` therefore form a closed subset of the
symmetric power, homeomorphic to `Sym α n`.

For a surface `Σ` with a basepoint `z` this subset of `Sym^g(Σ)` is the divisor
`V_z = {z} × Sym^{g-1}(Σ)` of Ozsváth--Szabó, through which the basepoint enters Heegaard Floer
homology: the multiplicity `n_z(φ)` of a Whitney disk `φ` is its intersection number with `V_z`.
That `V_z` misses the tori of a Heegaard diagram when `z` lies off the attaching curves is
`TauCeti.Sym.disjoint_basepointDivisor_pi`. It is cut out by a single affine equation in every
elementary symmetric chart it meets, as shown by
`TauCeti.exists_continuousLinearMap_ne_zero_mem_iff_symChartAt`.

## Main declarations

* `TauCeti.Sym.continuous_cons`: adjoining a point is continuous.
* `TauCeti.Sym.isClosedMap_cons` and `TauCeti.Sym.isClosedEmbedding_cons`: in a `T₁` space it is
  a closed map, hence a closed embedding.
* `TauCeti.Sym.isClosed_basepointDivisor`: in a `T₁` space the unordered tuples through a point
  form a closed set.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004), [arXiv:math/0101206](
  https://arxiv.org/abs/math/0101206), §2.1 and §2.4.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {α : Type*} [TopologicalSpace α] {n : ℕ}

/-- Adjoining a point to an unordered tuple is continuous. -/
@[continuity, fun_prop]
theorem continuous_cons (a : α) : Continuous (Sym.cons a : Sym α n → Sym α (n + 1)) := by
  have h : (Sym.cons a : Sym α n → Sym α (n + 1)) ∘ ofFn = ofFn ∘ Fin.cons a :=
    funext fun f => (ofFn_cons a f).symm
  rw [continuous_iff_comp_ofFn, h]
  exact continuous_ofFn.comp (continuous_const.finCons continuous_id)

/-- In a space whose points are closed, adjoining a point to an unordered tuple is a closed map. -/
theorem isClosedMap_cons [T1Space α] (a : α) :
    IsClosedMap (Sym.cons a : Sym α n → Sym α (n + 1)) := by
  intro C hC
  -- on ordered tuples, the image is the set of tuples starting with `a` whose tail presents a
  -- point of `C`, which is closed; its image under the closed map `ofFn` is the image of `C`
  have himage : Sym.cons a '' C =
      ofFn '' ({f : Fin (n + 1) → α | f 0 = a} ∩ Fin.tail ⁻¹' (ofFn ⁻¹' C)) := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨g, rfl⟩ := ofFn_surjective t
      exact ⟨Fin.cons a g, ⟨by simp, by simpa using ht⟩, ofFn_cons a g⟩
    · rintro ⟨f, ⟨hf0, hft⟩, rfl⟩
      refine ⟨ofFn (Fin.tail f), hft, ?_⟩
      rw [← ofFn_cons, ← hf0, Fin.cons_self_tail]
  rw [himage]
  refine isClosedMap_ofFn _ ((isClosed_singleton.preimage (continuous_apply 0)).inter ?_)
  exact (hC.preimage continuous_ofFn).preimage (continuous_pi fun i => continuous_apply i.succ)

/-- In a space whose points are closed, adjoining a point is a closed embedding of `Sym α n` into
`Sym α (n + 1)`, with range the unordered tuples through that point (`TauCeti.Sym.range_cons`). -/
theorem isClosedEmbedding_cons [T1Space α] (a : α) :
    IsClosedEmbedding (Sym.cons a : Sym α n → Sym α (n + 1)) :=
  .of_continuous_injective_isClosedMap (continuous_cons a)
    (fun s t h => (Sym.cons_inj_right a s t).1 h) (isClosedMap_cons a)

/-- In a space whose points are closed, the unordered tuples through a given point form a closed
subset of the symmetric power. -/
theorem isClosed_basepointDivisor [T1Space α] (a : α) :
    IsClosed (basepointDivisor a : Set (Sym α n)) := by
  cases n with
  | zero =>
    rw [basepointDivisor_zero]
    exact isClosed_empty
  | succ n =>
    rw [← range_cons a]
    exact (isClosedEmbedding_cons a).isClosed_range

end Sym

end TauCeti
