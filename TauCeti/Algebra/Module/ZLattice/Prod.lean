/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Products of lattices

The product `L.prod L'` of discrete subgroups `L ⊆ E` and `L' ⊆ E'` of two topological modules is
a discrete subgroup of `E × E'`, and the product of two full lattices in normed spaces over a
normed field `K` is a full lattice in the product space. For complex tori, this makes the
quotient of `E × E'` by `L.prod L'` the complex torus of the product lattice, which is the product
of the complex tori `E / L` and `E' / L'`.

## Main results

* `Submodule.instDiscreteTopologyProd`: the product of two discrete submodules is discrete.
* `Submodule.instIsZLatticeProd`: the product of two full lattices is a full lattice.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1.
-/

public section

/-- The product of two discrete submodules is a discrete submodule of the product module. -/
instance Submodule.instDiscreteTopologyProd {R M M₂ : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] [AddCommMonoid M₂] [Module R M₂] [TopologicalSpace M₂]
    (p : Submodule R M) (q : Submodule R M₂) [DiscreteTopology p] [DiscreteTopology q] :
    DiscreteTopology (p.prod q) :=
  DiscreteTopology.of_continuous_injective (f := p.prodEquiv q)
    ((continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _))
    (p.prodEquiv q).injective

/-- The product of two full lattices is a full lattice in the product space. -/
instance Submodule.instIsZLatticeProd {K E E₂ : Type*} [NormedField K] [NormedAddCommGroup E]
    [NormedSpace K E] [NormedAddCommGroup E₂] [NormedSpace K E₂] (L : Submodule ℤ E)
    (L₂ : Submodule ℤ E₂) [DiscreteTopology L] [DiscreteTopology L₂] [IsZLattice K L]
    [IsZLattice K L₂] : IsZLattice K (L.prod L₂) where
  span_top := by
    rw [Submodule.prod_coe, Submodule.span_prod_eq K L.zero_mem L₂.zero_mem, IsZLattice.span_top,
      IsZLattice.span_top, Submodule.prod_top]
