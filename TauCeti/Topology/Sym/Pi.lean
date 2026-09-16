/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Data.Sym.Pi
public import TauCeti.Topology.Sym.Basic

/-!
# The subspace of unordered tuples with one point in each member of a family

`TauCeti.Sym.pi A` is the set of unordered `n`-tuples having one point in each member of a family
`A : Fin n → Set α` of subsets. This file gives it its topology, as a subspace of the symmetric
power `Sym α n`: it is closed when the members of the family are, compact when they are, and, for a
pairwise disjoint family of compact sets in a Hausdorff space, homeomorphic to the product
`∀ i, ↥(A i)` of its members.

The case to keep in mind is the torus `T_α = α₁ × ⋯ × α_g ⊆ Sym^g(Σ)` attached to the `g`
pairwise disjoint attaching circles of a Heegaard diagram on a surface `Σ` (Ozsváth--Szabó,
*Holomorphic disks and topological invariants for closed three-manifolds*, §2.1). The circles are
compact and pairwise disjoint, so `T_α` really is an embedded `g`-torus and not merely a continuous
image of one. The companion open-range statement, where the members of the family are open rather
than compact and the product is an open subspace, is
`TauCeti.Sym.isOpenEmbedding_ofFn_map`.

## Main declarations

* `TauCeti.Sym.isClosed_pi` and `TauCeti.Sym.isCompact_pi`: the subspace is closed, respectively
  compact, when the members of the family are.
* `TauCeti.Sym.isClosedEmbedding_ofFn_coe`: for a pairwise disjoint family of compact sets in a
  Hausdorff space, the parametrization by ordered tuples is a closed embedding.
* `TauCeti.Sym.piHomeomorph`: the resulting homeomorphism with the product of the members.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004), [arXiv:math/0101206](
  https://arxiv.org/abs/math/0101206), §2.1.
-/

public section

namespace TauCeti

open Topology

namespace Sym

variable {α : Type*} [TopologicalSpace α] {n : ℕ} {A : Fin n → Set α}

/-- The parametrization of `TauCeti.Sym.pi A` by ordered tuples is continuous. -/
@[continuity, fun_prop]
theorem continuous_ofFn_coe :
    Continuous fun x : ∀ i, ↥(A i) => ofFn fun i => (x i : α) :=
  continuous_ofFn.comp (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))

/-- The unordered tuples with one point in each member of a family of closed sets form a closed
subspace of the symmetric power: the quotient map onto a symmetric power is closed. -/
theorem isClosed_pi (hA : ∀ i, IsClosed (A i)) : IsClosed (pi A) := by
  rw [pi_eq_image_univ_pi]
  exact isClosedMap_ofFn _ (isClosed_set_pi fun i _ => hA i)

/-- The unordered tuples with one point in each member of a family of compact sets form a compact
subspace of the symmetric power. -/
theorem isCompact_pi (hA : ∀ i, IsCompact (A i)) : IsCompact (pi A) := by
  rw [pi_eq_image_univ_pi]
  exact (isCompact_univ_pi hA).image continuous_ofFn

variable [T2Space α]

/-- **The tuples with one point in each member of a pairwise disjoint family of compact sets are
an embedded product.** For the attaching circles of a Heegaard diagram this says that the torus
`T_α` is embedded, and closed, in the symmetric power of the surface. -/
theorem isClosedEmbedding_ofFn_coe (hA : ∀ i, IsCompact (A i))
    (h : Pairwise (Function.onFun Disjoint A)) :
    IsClosedEmbedding fun x : ∀ i, ↥(A i) => ofFn fun i => (x i : α) :=
  haveI (i : Fin n) : CompactSpace ↥(A i) := isCompact_iff_compactSpace.1 (hA i)
  continuous_ofFn_coe.isClosedEmbedding (ofFn_coe_injective h)

/-- **The subspace `TauCeti.Sym.pi A` is the product of the members of the family**, for a pairwise
disjoint family of compact sets in a Hausdorff space: the topological refinement of
`TauCeti.Sym.piEquiv`. -/
noncomputable def piHomeomorph (hA : ∀ i, IsCompact (A i))
    (h : Pairwise (Function.onFun Disjoint A)) : (∀ i, ↥(A i)) ≃ₜ ↥(pi A) :=
  ((isClosedEmbedding_ofFn_coe hA h).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (pi_eq_range A).symm)

/-- The homeomorphism underlying `TauCeti.Sym.piHomeomorph` is the parametrization by ordered
tuples. -/
@[simp]
theorem coe_piHomeomorph (hA : ∀ i, IsCompact (A i)) (h : Pairwise (Function.onFun Disjoint A))
    (x : ∀ i, ↥(A i)) : (piHomeomorph hA h x : Sym α n) = ofFn fun i => (x i : α) := by
  -- unfold the chain of Mathlib equivalences out of which the homeomorphism is assembled
  simp [piHomeomorph, Topology.IsEmbedding.toHomeomorph, Homeomorph.setCongr, Set.equivOfEq,
    Equiv.subtypeEquivProp]

end Sym

end TauCeti
