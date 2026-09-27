/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.Normal.Embeddings
public import TauCeti.GroupTheory.GroupAction.Transitive

/-!
# The norm of a finite subextension as a product over the absolute Galois group

Let `K` be a field, `Kˢ` a separable closure, `L/K` a finite extension and `σ : L →ₐ[K] Kˢ` a
`K`-embedding. Composing with `σ` identifies the coset space of the open subgroup
`Gal(Kˢ/σ(L))` cut out by `σ` with the set of `K`-embeddings of `L` into `Kˢ`,

```text
G_K ⧸ Gal(Kˢ/σ(L)) ≃ (L →ₐ[K] Kˢ),    g ↦ g ∘ σ,
```

and under that identification the classical formula "the norm is the product of the conjugates"
becomes a product over a system `t` of coset representatives:

```text
algebraMap K Kˢ (N_{L/K} b) = ∏ u : G_K ⧸ Gal(Kˢ/σ(L)), t u (σ b).
```

This is the shape in which the norm of a finite extension meets the cohomology of `G_K`, where a
sum `x ↦ ∑ u, t u • x` over a transversal is the standard degree-zero corestriction: on units of
`Kˢ` fixed by `Gal(Kˢ/σ(L))`, that sum is the norm of `L/K`.

Separability of `L/K` is not assumed. An embedding of `L` into a separable closure of `K` forces
it by Mathlib's `Algebra.IsSeparable.of_algHom`. Finiteness of `L/K` is used twice: it bounds the
index of `Gal(Kˢ/σ(L))` by `[L : K]`, so that the coset space is a finite index set, and it is the
hypothesis of Mathlib's product formula for the norm.

## Main definitions

* `TauCeti.fixingSubgroupQuotientEquivAlgHom`: the bijection between the cosets of
  `Gal(Kˢ/σ(L))` and the `K`-embeddings of `L` into `Kˢ`.

## Main results

* `TauCeti.algebraMap_norm_eq_prod_transversal`: the norm of `L/K` is the product of the
  conjugates of `σ`, indexed by a transversal of `Gal(Kˢ/σ(L))`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §5, where
  the degree-zero corestriction along a finite extension of fields is the norm.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

include σ

/-! ### The cosets of the subgroup cut out by `σ` -/

private theorem stabilizer_algHom_eq_fixingSubgroup :
    MulAction.stabilizer (AbsoluteGaloisGroup K) σ = σ.fieldRange.fixingSubgroup := by
  ext g
  rw [MulAction.mem_stabilizer_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro h _ ⟨x, rfl⟩
    exact AlgEquiv.apply_of_smul_eq h x
  · intro h
    ext x
    exact congrArg Subtype.val (h (σ x) ⟨x, rfl⟩)

/-- **The cosets of `Gal(Kˢ/σ(L))` are the `K`-embeddings of `L` into `Kˢ`**, the coset of
`g` corresponding to `g ∘ σ`. Composed with `galoisSubgroup_index` it is the statement that a
finite separable extension of degree `d` has exactly `d` embeddings into a separable closure. -/
def fixingSubgroupQuotientEquivAlgHom :
    AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup ≃ (L →ₐ[K] SeparableClosure K) :=
  (Subgroup.quotientEquivOfEq (stabilizer_algHom_eq_fixingSubgroup K L σ).symm).trans
    (quotientStabilizerEquiv (AbsoluteGaloisGroup K) σ)

/-- `fixingSubgroupQuotientEquivAlgHom` sends the coset of `g` to `g ∘ σ`. -/
@[simp]
theorem fixingSubgroupQuotientEquivAlgHom_mk (g : AbsoluteGaloisGroup K) :
    fixingSubgroupQuotientEquivAlgHom K L σ (QuotientGroup.mk g) = g.toAlgHom.comp σ :=
  by
    rw [fixingSubgroupQuotientEquivAlgHom, Equiv.trans_apply,
      Subgroup.quotientEquivOfEq_mk, quotientStabilizerEquiv_mk,
      AlgEquiv.smul_algHom_def]

variable [FiniteDimensional K L]

/-! ### The norm as a product of conjugates -/

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The norm of `L/K` is the product of the conjugates of `σ`** (NSW, Ch. I §5): for any system
`t` of representatives of the cosets of `Gal(Kˢ/σ(L))`, the image of `N_{L/K} b` in `Kˢ`
is `∏ u, t u (σ b)`. The cosets index the `K`-embeddings of `L` into `Kˢ` through
`fixingSubgroupQuotientEquivAlgHom`, and `L/K` is separable, so Mathlib's
`Algebra.norm_eq_prod_embeddings` computes the product. -/
theorem algebraMap_norm_eq_prod_transversal
    (t : AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup → AbsoluteGaloisGroup K)
    (ht : ∀ u, (QuotientGroup.mk (t u) :
      AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup) = u) (b : L) :
    algebraMap K (SeparableClosure K) (Algebra.norm K b) = ∏ u, t u (σ b) := by
  have := Algebra.IsSeparable.of_algHom K (SeparableClosure K) σ
  have hsplits : ∀ x : L, ((minpoly K x).map
      (algebraMap K (SeparableClosure K))).Splits := fun x =>
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)
  refine (algebraMap (SeparableClosure K) (AlgebraicClosure K)).injective ?_
  rw [map_prod, ← IsScalarTower.algebraMap_apply K (SeparableClosure K) (AlgebraicClosure K),
    Algebra.norm_eq_prod_embeddings (K := K) (L := L) (E := AlgebraicClosure K) b]
  refine (Fintype.prod_equiv ((fixingSubgroupQuotientEquivAlgHom K L σ).trans
    (IntermediateField.algHomEquivAlgHomOfSplits (AlgebraicClosure K)
      (separableClosure K (AlgebraicClosure K)) hsplits)) _ _ fun u => ?_).symm
  have hu : fixingSubgroupQuotientEquivAlgHom K L σ u = (t u).toAlgHom.comp σ := by
    conv_lhs => rw [← ht u]
    rw [fixingSubgroupQuotientEquivAlgHom_mk]
  rw [Equiv.trans_apply, hu, IntermediateField.algHomEquivAlgHomOfSplits_apply_apply,
    AlgHom.comp_apply]
  -- `SeparableClosure K` is by definition `separableClosure K (AlgebraicClosure K)`, and only
  -- that abbreviation separates the two sides.
  rfl

end TauCeti
