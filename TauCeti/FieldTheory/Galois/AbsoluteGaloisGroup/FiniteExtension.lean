/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension

/-!
# The absolute Galois group of a finite separable extension as an open subgroup

Let `L/K` be a finite separable extension and `σ : L →ₐ[K] Kˢ` a `K`-embedding of `L` into a
separable closure `Kˢ` of `K`. The automorphisms of `Kˢ` that fix `σ(L)` pointwise form an open
subgroup

```text
galoisSubgroup K L σ ≤ G_K = AbsoluteGaloisGroup K
```

of index `[L : K]`, and it is the absolute Galois group of `L`: the isomorphism of topological
groups `absoluteGaloisGroupEquivFixingSubgroup K L σ : G_L ≃ₜ* σ.fieldRange.fixingSubgroup` of
`TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension`, read at the open subgroup, is an
isomorphism `G_L ≃ₜ* galoisSubgroup K L σ` for the Krull topologies, which is what continuous
cohomology depends on.

The embedding is genuine data. Without one there is no homomorphism `G_L → G_K` induced by the
extension `L/K`, hence no realization of `G_L` as a subgroup of `G_K`, and two embeddings cut out
conjugate subgroups. Restriction, corestriction and the other subgroup-indexed operations of
Galois cohomology along `L/K` are the operations at `galoisSubgroup K L σ`, read through
`galoisSubgroupEquiv K L σ`, and their independence of `σ` is a statement about those operations
rather than about the subgroup. The index formula is what discharges the finite-index and
index-two hypotheses those operations carry.

Finiteness of `L/K` enters in three places: it makes the fixing subgroup open, so that it can be
packaged as the `OpenSubgroup` `galoisSubgroup K L σ`; it is the hypothesis of the finite-degree
index formula `galoisSubgroup_index`; and, through the packaging, it is carried by
`galoisSubgroupEquiv K L σ` and its application lemmas. The identification of separable closures
and the isomorphism of Galois groups themselves need no finiteness and live in the imported
module. Separability of `L/K` is a consequence of the existence of `σ` and is not assumed.

## Main definitions

* `TauCeti.galoisSubgroup K L σ`: the open subgroup of `G_K` fixing `σ(L)` pointwise, for a
  finite `L/K`.
* `TauCeti.galoisSubgroupEquiv K L σ`: the isomorphism of topological groups
  `G_L ≃ₜ* galoisSubgroup K L σ`.

## Main results

* `TauCeti.galoisSubgroup_index`: the index of `galoisSubgroup K L σ` in `G_K` is `[L : K]`.
* `TauCeti.galoisSubgroupEquiv_apply_separableClosureRingEquiv`: the isomorphism intertwines the
  actions of `G_L` on `Lˢ` and of `G_K` on `Kˢ` through `separableClosureRingEquiv K L σ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §5 for
  restriction and corestriction along a finite extension, and Ch. VI §1 for the absolute Galois
  group at the separable closure.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-! ### The open subgroup -/

/-- **The open subgroup of `G_K` cut out by a `K`-embedding of `L` into `Kˢ`**: the automorphisms
of `Kˢ` fixing `σ(L)` pointwise. It is open because `L/K` is finite, and `galoisSubgroupEquiv`
identifies it with the absolute Galois group of `L`. -/
def galoisSubgroup : OpenSubgroup (AbsoluteGaloisGroup K) where
  toSubgroup := σ.fieldRange.fixingSubgroup
  isOpen' :=
    haveI : FiniteDimensional K σ.fieldRange := σ.toLinearMap.finiteDimensional_range
    σ.fieldRange.fixingSubgroup_isOpen

/-- The subgroup underlying `galoisSubgroup K L σ` is the fixing subgroup of the image of `σ`. -/
@[simp]
theorem galoisSubgroup_toSubgroup :
    (galoisSubgroup K L σ).toSubgroup = σ.fieldRange.fixingSubgroup :=
  (rfl)

/-- An automorphism of `Kˢ` lies in `galoisSubgroup K L σ` exactly when it fixes `σ x` for every
`x : L`. -/
@[simp]
theorem mem_galoisSubgroup_iff {g : AbsoluteGaloisGroup K} :
    g ∈ galoisSubgroup K L σ ↔ ∀ x : L, g (σ x) = σ x := by
  rw [← OpenSubgroup.mem_toSubgroup, galoisSubgroup_toSubgroup,
    IntermediateField.mem_fixingSubgroup_iff]
  simp

/-- **The index of `galoisSubgroup K L σ` is the degree `[L : K]`.** -/
theorem galoisSubgroup_index : (galoisSubgroup K L σ).toSubgroup.index = Module.finrank K L := by
  rw [galoisSubgroup_toSubgroup, ← finrank_eq_fixingSubgroup_index]
  exact (AlgEquiv.ofInjectiveField σ).toLinearEquiv.finrank_eq.symm

/-- `galoisSubgroup K L σ` is all of `G_K` exactly when `L/K` is trivial, that is `[L : K] = 1`. -/
theorem galoisSubgroup_eq_top_iff : galoisSubgroup K L σ = ⊤ ↔ Module.finrank K L = 1 := by
  rw [← galoisSubgroup_index, Subgroup.index_eq_one, ← OpenSubgroup.toSubgroup_top,
    OpenSubgroup.toSubgroup_injective.eq_iff]

/-! ### The isomorphism with the absolute Galois group of `L` -/

/-- **The absolute Galois group of `L` is the open subgroup of `G_K` cut out by `σ`**, as
topological groups: conjugation by the identification `separableClosureRingEquiv K L σ` of separable
closures is an isomorphism `G_L ≃ₜ* galoisSubgroup K L σ` for the Krull topologies. It is
`absoluteGaloisGroupEquivFixingSubgroup K L σ` read at the open subgroup. -/
def galoisSubgroupEquiv : AbsoluteGaloisGroup L ≃ₜ* ↥(galoisSubgroup K L σ).toSubgroup :=
  absoluteGaloisGroupEquivFixingSubgroup K L σ

/-- `galoisSubgroupEquiv K L σ` conjugates by the identification of separable closures. -/
@[simp]
theorem galoisSubgroupEquiv_apply (g : AbsoluteGaloisGroup L) (y : SeparableClosure K) :
    (galoisSubgroupEquiv K L σ g : AbsoluteGaloisGroup K) y =
      separableClosureRingEquiv K L σ (g ((separableClosureRingEquiv K L σ).symm y)) :=
  absoluteGaloisGroupEquivFixingSubgroup_apply K L σ g y

/-- **The isomorphism intertwines the Galois actions**: the image of `g : G_L` acts on
`e x ∈ Kˢ` as `g` acts on `x ∈ Lˢ`, where `e = separableClosureRingEquiv K L σ`. -/
theorem galoisSubgroupEquiv_apply_separableClosureRingEquiv (g : AbsoluteGaloisGroup L)
    (x : SeparableClosure L) :
    (galoisSubgroupEquiv K L σ g : AbsoluteGaloisGroup K) (separableClosureRingEquiv K L σ x) =
      separableClosureRingEquiv K L σ (g x) := by
  rw [galoisSubgroupEquiv_apply, RingEquiv.symm_apply_apply]

/-- The inverse of `galoisSubgroupEquiv K L σ` conjugates back by the identification of separable
closures. -/
@[simp]
theorem galoisSubgroupEquiv_symm_apply (h : ↥(galoisSubgroup K L σ).toSubgroup)
    (x : SeparableClosure L) :
    (galoisSubgroupEquiv K L σ).symm h x =
      (separableClosureRingEquiv K L σ).symm
        ((h : AbsoluteGaloisGroup K) (separableClosureRingEquiv K L σ x)) :=
  absoluteGaloisGroupEquivFixingSubgroup_symm_apply K L σ h x

end TauCeti
