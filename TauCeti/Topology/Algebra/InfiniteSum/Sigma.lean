/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import TauCeti.Order.Filter.AtTopBot.Finset

/-!
# Regrouping a series along finite fibres

Mathlib's `HasSum.sigma` regroups a series over a sigma type into the sums of its fibres, which
needs a regular topology and continuous addition to take the fibre sums. When every fibre is
finite the fibre sums are finite sums, and the regrouping holds in any topological additive monoid.
Applying this to `Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd` regroups a double sum over
`A × A` into finite antidiagonal sums over `Finset.antidiagonal d` without regularity or continuity
of addition.

## Main results

* `HasSum.sigma_of_finite`: a series over `Σ b, γ b` with finite fibres sums to the same value
  when grouped by `b`.
* `HasProd.prod_mulAntidiagonal`, `HasSum.sum_antidiagonal`: regrouping a convergent double product
  or series over `A × A` along finite antidiagonals.
* `Multipliable.tprod_prod_eq_tprod_prod_mulAntidiagonal`,
  `Summable.tsum_prod_eq_tsum_sum_antidiagonal`: the corresponding `tprod`/`tsum` identities in a
  Hausdorff space.
-/

public section

open Finset Filter

/-- **Regrouping along finite fibres.** If a family over a sigma type with finite fibres sums to
`a`, then so does the family of its fibre sums. No regularity of the topology is needed. -/
@[to_additive]
theorem HasProd.sigma_of_finite {α β : Type*} {γ : β → Type*} [CommMonoid α] [TopologicalSpace α]
    [∀ b, Fintype (γ b)] {f : (Σ b, γ b) → α} {a : α} (ha : HasProd f a) :
    HasProd (fun b ↦ ∏ c, f ⟨b, c⟩) a := by
  classical
  -- the partial products over finite sets of `b` are partial products of `ha`
  exact (ha.comp TauCeti.tendsto_finset_sigma_univ_atTop).congr fun s ↦ by
    simp [Finset.prod_sigma]

/-- **Regrouping a double product by antidiagonals.** If a family `f : A × A → α` has product `a`
on a type with multiplicative antidiagonals, then the family of finite products over
`Finset.mulAntidiagonal d` also has product `a`. No separation axiom or continuity of multiplication
is needed. -/
@[to_additive
/-- **Regrouping a double sum by antidiagonals.** If a family `f : A × A → α` sums to `a` on a
type with additive antidiagonals, then the family of finite sums over `Finset.antidiagonal d` also
sums to `a`. No separation axiom or continuity of addition is needed. -/]
theorem HasProd.prod_mulAntidiagonal {A α : Type*} [Mul A] [Finset.HasMulAntidiagonal A]
    [CommMonoid α] [TopologicalSpace α] {f : A × A → α} {a : α} (hf : HasProd f a) :
    HasProd (fun d : A ↦ ∏ kl ∈ Finset.mulAntidiagonal d, f kl) a := by
  simpa [Finset.prod_coe_sort, Finset.prod_attach] using
    (Finset.HasMulAntidiagonal.sigmaMulAntidiagonalEquivProd.hasProd_iff.2 hf).sigma_of_finite

/-- **Regrouping a multipliable double product by antidiagonals.** In a Hausdorff space, the
product of a multipliable family `f : A × A → α` equals the product over `d : A` of the finite
products over `Finset.mulAntidiagonal d`. -/
@[to_additive Summable.tsum_prod_eq_tsum_sum_antidiagonal
/-- **Regrouping a summable double series by antidiagonals.** In a Hausdorff space, the sum of a
summable family `f : A × A → α` equals the sum over `d : A` of the finite sums over
`Finset.antidiagonal d`. -/]
theorem Multipliable.tprod_prod_eq_tprod_prod_mulAntidiagonal {A α : Type*} [Mul A]
    [Finset.HasMulAntidiagonal A] [CommMonoid α] [TopologicalSpace α] [T2Space α]
    {f : A × A → α} (hf : Multipliable f) :
    (∏' x : A × A, f x) = ∏' d : A, ∏ kl ∈ Finset.mulAntidiagonal d, f kl :=
  hf.hasProd.prod_mulAntidiagonal.tprod_eq.symm
