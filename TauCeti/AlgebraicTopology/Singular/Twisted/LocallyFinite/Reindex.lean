/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Reindex

/-!
# Simplicial reindexing of locally finite twisted chains

A simplicial structure map only replaces a singular simplex by one whose image is contained
in the original image. Thus it extends to locally finite chains, including degeneracy maps.
The extensions preserve identities and composition. This is the support control needed when
using simplicial identities to fill locally finite cycles.

## References

* G. E. Bredon, *Sheaf Theory*, 2nd ed., Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits SimplexCategory

open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X) {a b c : ℕ}

/-- Simplicial structure maps of twisted chains are properly supported: reindexing never
enlarges the image of a simplex. -/
theorem isProperlySupported_twistedChainReindex (α : ⦋a⦌ ⟶ ⦋b⦌) :
    IsProperlySupported (twistedChainReindex L α) := by
  apply IsProperlySupported.of_movesAlong (g := 𝟙 X) isProperMap_id
  rw [movesAlong_iff]
  intro ρ σ x hx
  have hρ : (TopCat.toSSet.obj X).map α.op σ = ρ := by
    by_contra hne
    apply hx
    have hzero : ιTwistedChainComplex L b σ ≫ twistedChainReindex L α ≫
        twistedChainComplexCoeff L ρ = 0 := by
      rw [← Category.assoc, ιTwistedChainComplex_reindex, Category.assoc,
        ιTwistedChainComplex_twistedChainComplexCoeff_of_ne L hne, comp_zero]
    simpa only [matrixCoeff_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply] using congrArg (fun f ↦ f.hom x) hzero
  subst ρ
  rw [TopCat.hom_id, ContinuousMap.coe_id, Set.image_id]
  exact TopCat.range_simplexMap_map_subset _ σ

/-- Reindex a locally finite twisted chain along a simplex-category morphism. As for
simplicial objects, this is contravariant in the simplex-category morphism. -/
def locallyFiniteReindex (α : ⦋a⦌ ⟶ ⦋b⦌) :
    locallyFiniteChains L b →ₗ[R] locallyFiniteChains L a :=
  extendLocallyFinite (isProperlySupported_twistedChainReindex L α)

/-- Reindexing is the properly supported extension of the finite-chain structure map. -/
theorem locallyFiniteReindex_def (α : ⦋a⦌ ⟶ ⦋b⦌) :
    locallyFiniteReindex L α =
      extendLocallyFinite (isProperlySupported_twistedChainReindex L α) := (rfl)

/-- Coefficients of reindexing are obtained by extending the corresponding finite-chain map. -/
@[simp]
theorem coe_locallyFiniteReindex (α : ⦋a⦌ ⟶ ⦋b⦌) (z : locallyFiniteChains L b) :
    (locallyFiniteReindex L α z : ∀ σ, L.obj (initialVertex σ)) =
      extendLocallyFiniteFun (twistedChainReindex L α) z :=
  coe_extendLocallyFinite _ z

/-- Reindexing by the identity fixes a locally finite chain. -/
@[simp]
theorem locallyFiniteReindex_id : locallyFiniteReindex L (𝟙 ⦋a⦌) = LinearMap.id := by
  unfold locallyFiniteReindex
  simp only [twistedChainReindex_id, extendLocallyFinite_id]

/-- Reindexing locally finite chains respects composition. -/
theorem locallyFiniteReindex_comp (α : ⦋a⦌ ⟶ ⦋b⦌) (β : ⦋b⦌ ⟶ ⦋c⦌) :
    locallyFiniteReindex L (α ≫ β) =
      locallyFiniteReindex L α ∘ₗ locallyFiniteReindex L β := by
  unfold locallyFiniteReindex
  rw [extendLocallyFinite_comp]
  simp only [twistedChainReindex_comp]

end TauCeti.LocalCoefficientSystem
