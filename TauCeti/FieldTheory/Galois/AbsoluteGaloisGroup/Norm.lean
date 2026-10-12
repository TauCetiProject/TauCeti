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

/-!
# The norm of a finite subextension as a product over the absolute Galois group

Let `K` be a field, `Kˢ` a separable closure, `L/K` a finite extension and `σ : L →ₐ[K] Kˢ` a
`K`-embedding. Composing with `σ` identifies the coset space of the open subgroup
`Gal(Kˢ/σ(L))` cut out by `σ` with the set of `K`-embeddings of `L` into `Kˢ`,

```text
G_K ⧸ Gal(Kˢ/σ(L)) ≃ (L →ₐ[K] Kˢ),    g ↦ g ∘ σ,
```

which is `TauCeti.FieldTheory.fixingSubgroupQuotientEquivAlgHom` for the normal extension
`Kˢ / K`. Under that identification the classical formula "the norm is the product of the
conjugates" becomes a product over a system `t` of coset representatives:

```text
algebraMap K Kˢ (N_{L/K} b) = ∏ u : G_K ⧸ Gal(Kˢ/σ(L)), t u (σ b).
```

This is the shape in which the norm of a finite extension meets the cohomology of `G_K`, where a
sum `x ↦ ∑ u, t u • x` over a transversal is the standard degree-zero corestriction: on units of
`Kˢ` fixed by `Gal(Kˢ/σ(L))`, that sum is the norm of `L/K`.

Separability of `L/K` is not assumed. An embedding of `L` into a separable closure of `K` forces
it by Mathlib's `Algebra.IsSeparable.of_algHom`. Finiteness of `L/K` is used twice: it bounds the
index of `Gal(Kˢ/σ(L))` by `[L : K]`, so that the coset space is a finite index set, and it is the
hypothesis of Mathlib's product formula for the norm, `Algebra.norm_eq_prod_embeddings`.

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

variable [FiniteDimensional K L]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The norm of `L/K` is the product of the conjugates of `σ`** (NSW, Ch. I §5): for any system
`t` of representatives of the cosets of `Gal(Kˢ/σ(L))`, the image of `N_{L/K} b` in `Kˢ`
is `∏ u, t u (σ b)`. -/
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
  refine (Fintype.prod_equiv ((FieldTheory.fixingSubgroupQuotientEquivAlgHom σ).trans
    (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (AlgebraicClosure K) (SeparableClosure K)
      hsplits)) _ _ fun u => ?_).symm
  have hu : FieldTheory.fixingSubgroupQuotientEquivAlgHom σ u = (t u).toAlgHom.comp σ := by
    conv_lhs => rw [← ht u]
    rw [FieldTheory.fixingSubgroupQuotientEquivAlgHom_mk]
  rw [Equiv.trans_apply, hu, Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

end TauCeti
