/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Zero

/-!
# The augmentation of zeroth singular homology on elements

For a ring `k`, Mathlib's augmentation `TopCat.singularHomology₀ε : H₀(X; k) ⟶ k` is defined on
homology through the components of the singular simplicial set. This file computes it on the class
of an explicit `0`-chain: it is the sum of the coefficients of the chain, the augmentation
`TauCeti.singularAugment` of the chain level (`TauCeti.singularHomology₀ε_homologyπ_cyclesMk`).
This is the form in which a degree-zero class produced by a chain-level construction, such as the
connecting morphism of a short exact sequence of singular chains, is evaluated.

## Main results

* `TauCeti.singularHomology₀ε_homologyπ_cyclesMk`: the augmentation of the class of a `0`-chain is
  the sum of its coefficients.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial

universe u

namespace TauCeti

variable {k : Type u} [Ring k]

/-- **The augmentation of the class of a `0`-chain.** The class in zeroth singular homology of a
`0`-chain `c` has augmentation the sum `singularAugment k X c` of the coefficients of `c`: on
homology, `singularAugment` induces Mathlib's augmentation `TopCat.singularHomology₀ε`. -/
theorem singularHomology₀ε_homologyπ_cyclesMk {X : TopCat.{u}}
    (c : ((singularChains k).obj X).X 0) (hc : ((singularChains k).obj X).d 0 0 c = 0) :
    X.singularHomology₀ε (ModuleCat.of k k) (((singularChains k).obj X).homologyπ 0
      (((singularChains k).obj X).cyclesMk c 0 ChainComplex.next_nat_zero hc)) =
      singularAugment k X c := by
  let K := (singularChains k).obj X
  -- Every `0`-chain is a cycle, through `cycles₀Iso`.
  have hmk : K.cyclesMk c 0 ChainComplex.next_nat_zero hc = K.cycles₀Iso.inv c :=
    (ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance
      ((HomologicalComplex.i_cyclesMk (C := ModuleCat k) _ _ _ _ _).trans
        (by rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCyclesIso_inv_hom_id]; rfl))
  rw [hmk]
  -- Both sides are linear in `c`, and on a simplex the augmentation of the vertex class is `1`.
  have := singularChains_linearMap_ext (n := 0) (V := k)
    (L := (K.cycles₀Iso.inv ≫ K.homologyπ 0 ≫ X.singularHomology₀ε (ModuleCat.of k k)).hom)
    (L' := singularAugment k X) fun σ ↦ by
      rw [singularAugment_simplexChain]
      exact ConcreteCategory.congr_hom
        ((SSet.ιChainComplex_cycles₀Iso_inv_homologyπ_assoc (X := TopCat.toSSet.obj X)
          (ModuleCat.of k k) σ _).trans (SSet.ιHomology₀_homology₀ε (ModuleCat.of k k) σ)) (1 : k)
  exact LinearMap.congr_fun this c

end TauCeti
