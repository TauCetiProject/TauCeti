/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.House

/-!
# Basic lemmas on the mixed embedding of a number field

For a number field `K`, the sup norm of `mixedEmbedding K x` on `mixedSpace K` equals the house of
`x` (`TauCeti.NumberField.norm_mixedEmbedding`), and `mixedEmbedding K` embeds `𝓞 K` injectively
onto `NumberField.mixedEmbedding.integerLattice K ⊆ mixedSpace K`, packaged here as a `ℤ`-linear
equivalence `TauCeti.NumberField.mixedEmbedding.integerLatticeEquiv K`.

## Main definitions

* `TauCeti.NumberField.mixedEmbedding.integerLatticeEquiv K`: the `ℤ`-linear equivalence
  `𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K` induced by `mixedEmbedding K`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.normAtPlace_le_norm`: `normAtPlace w x ≤ ‖x‖`.
* `TauCeti.NumberField.norm_mixedEmbedding`: `‖mixedEmbedding K x‖ = house x`.
* `TauCeti.NumberField.mixedEmbedding.coe_integerLatticeEquiv`: coercing
  `integerLatticeEquiv K x` to `mixedSpace K` gives `mixedEmbedding K (x : K)`.
-/

public section

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

open scoped Classical in
/-- At every infinite place `w`, the local norm `normAtPlace w x` is at most the sup norm `‖x‖` on
`mixedSpace K`. -/
theorem normAtPlace_le_norm {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K)
    (x : mixedSpace K) :
    normAtPlace w x ≤ ‖x‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun u ↦ normAtPlace u x) (Finset.mem_univ w)

/-- The `ℤ`-linear equivalence `𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K` induced by
`mixedEmbedding K`. -/
def integerLatticeEquiv (K : Type*) [Field K] [NumberField K] :
    𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K :=
  LinearEquiv.ofInjective
    ((mixedEmbedding K).toIntAlgHom.toLinearMap.comp
      ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ))
    (fun _ _ hxy ↦ RingOfIntegers.ext <| mixedEmbedding_injective K (by simpa using hxy))

/-- Coercing `integerLatticeEquiv K x` to `mixedSpace K` evaluates `mixedEmbedding K` at `x`. -/
@[simp]
theorem coe_integerLatticeEquiv {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
    (integerLatticeEquiv K x : mixedSpace K) = mixedEmbedding K (x : K) :=
  (rfl)

end TauCeti.NumberField.mixedEmbedding

namespace TauCeti.NumberField

open Classical in
/-- On `mixedSpace K`, the sup norm of `mixedEmbedding K x` is the house of `x`. -/
@[simp]
theorem norm_mixedEmbedding {K : Type*} [Field K] [NumberField K] (x : K) :
    ‖mixedEmbedding K x‖ = house x := by
  refine le_antisymm ?_ ?_
  · rw [norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ ↦ ?_
    rw [normAtPlace_apply, ← norm_embedding_eq]
    exact norm_embedding_le_house x w.embedding
  · rw [house, canonicalEmbedding.norm_le_iff]
    intro φ
    rw [← InfinitePlace.apply, ← normAtPlace_apply]
    exact mixedEmbedding.normAtPlace_le_norm (InfinitePlace.mk φ) (mixedEmbedding K x)

end TauCeti.NumberField
end
