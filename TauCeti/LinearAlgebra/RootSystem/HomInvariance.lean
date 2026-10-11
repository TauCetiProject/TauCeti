/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Invariance under homomorphisms of root pairings

A homomorphism `f : P.Hom P₂` of root pairings consists of a linear map of weight spaces,
its transpose on coweight spaces, and a bijection `f.indexEquiv` of the indexing sets, subject to
`f.weightMap (P.root i) = P₂.root (f.indexEquiv i)`. The index bijection preserves Cartan pairings
and commutes with root reflections. When the weight map is injective, it also preserves and
reflects root membership, additive relations between roots, linear independence, and the
root-string coefficients `RootPairing.chainTopCoeff` and `RootPairing.chainBotCoeff`.

The weight map need not be surjective: these results also apply when the target has extra toral
directions outside the span of its roots. An equivalence of root pairings supplies the injectivity
hypothesis through `g.bijective_weightMap.injective`.

Mathlib's `RootPairing.Hom.pairing` gives the pairing in the coefficient ring. The invariance
lemmas here also apply to combinatorial expressions in the index bijection, without introducing
weight-space vectors.

## Main results

* `RootPairing.Hom.weightMap_mem_range_root_iff`: the weight map carries roots to roots and
  nothing else to a root.
* `RootPairing.Hom.pairingIn_indexEquiv`: the index bijection preserves pairings valued in a
  coefficient subring.
* `RootPairing.Hom.indexEquiv_reflectionPerm`: it commutes with `RootPairing.reflectionPerm`, and
  therefore with the negation of an index, which is `RootPairing.reflectionPerm i i` by definition
  and is rewritten to that form by the `simp` lemma `RootPairing.indexNeg_neg`.
* `RootPairing.Hom.root_indexEquiv_eq_add_iff` and
  `RootPairing.Hom.root_indexEquiv_eq_sub_iff`: it preserves and reflects the relations
  `α = β + γ` and `α = β - γ` between roots.
* `RootPairing.Hom.linearIndependent_root_indexEquiv_iff`: it preserves and reflects linear
  independence of a pair of roots.
* `RootPairing.Hom.chainTopCoeff_indexEquiv` and `RootPairing.Hom.chainBotCoeff_indexEquiv`: it
  preserves the two root-string coefficients.

These invariance facts show that an automorphism of a root system permutes the matrices of Geck's
construction, as developed in `TauCeti.LinearAlgebra.RootSystem.GeckConstruction.Symmetry`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing

open Function Set

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}

namespace Hom

/-- The index bijection of a homomorphism of root pairings preserves the pairing valued in a
coefficient subring. -/
@[simp]
theorem pairingIn_indexEquiv (f : P.Hom P₂) (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [P.IsValuedIn S] [P₂.IsValuedIn S] (i j : ι) :
    P₂.pairingIn S (f.indexEquiv i) (f.indexEquiv j) = P.pairingIn S i j := by
  refine FaithfulSMul.algebraMap_injective S R ?_
  rw [algebraMap_pairingIn, algebraMap_pairingIn, f.pairing]

/-- The index bijection of a homomorphism of root pairings commutes with root reflections. -/
@[simp]
theorem indexEquiv_reflectionPerm (f : P.Hom P₂) (i j : ι) :
    f.indexEquiv (P.reflectionPerm i j) =
      P₂.reflectionPerm (f.indexEquiv i) (f.indexEquiv j) := by
  refine P₂.root.injective ?_
  rw [← Hom.root_weightMap_apply P P₂ _ f, root_reflectionPerm, root_reflectionPerm,
    reflection_apply_root, reflection_apply_root, map_sub, map_smul, f.pairing,
    Hom.root_weightMap_apply, Hom.root_weightMap_apply]

variable (f : P.Hom P₂) (hf : Injective f.weightMap)
include hf

/-- A homomorphism of root pairings with injective weight map carries roots to roots, and carries
nothing else to a root. -/
theorem weightMap_mem_range_root_iff {m : M} :
    f.weightMap m ∈ range P₂.root ↔ m ∈ range P.root := by
  refine ⟨fun ⟨l, hl⟩ => ⟨f.indexEquiv.symm l, hf ?_⟩,
    fun ⟨i, hi⟩ => ⟨f.indexEquiv i, ?_⟩⟩
  · rw [Hom.root_weightMap_apply, Equiv.apply_symm_apply, hl]
  · rw [← hi, Hom.root_weightMap_apply]

/-- The index bijection of a homomorphism with injective weight map preserves and reflects
the relation `α = β + γ` between roots. -/
@[simp]
theorem root_indexEquiv_eq_add_iff (k i j : ι) :
    P₂.root (f.indexEquiv k) = P₂.root (f.indexEquiv i) + P₂.root (f.indexEquiv j) ↔
      P.root k = P.root i + P.root j := by
  rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply,
    ← map_add]
  exact hf.eq_iff

/-- The index bijection of a homomorphism with injective weight map preserves and reflects
the relation `α = β - γ` between roots. -/
@[simp]
theorem root_indexEquiv_eq_sub_iff (k j i : ι) :
    P₂.root (f.indexEquiv k) = P₂.root (f.indexEquiv j) - P₂.root (f.indexEquiv i) ↔
      P.root k = P.root j - P.root i := by
  rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply,
    ← map_sub]
  exact hf.eq_iff

/-- The index bijection of a homomorphism with injective weight map preserves and reflects linear
independence of a pair of roots. -/
@[simp]
theorem linearIndependent_root_indexEquiv_iff (i j : ι) :
    LinearIndependent R ![P₂.root (f.indexEquiv i), P₂.root (f.indexEquiv j)] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  have key : ![P₂.root (f.indexEquiv i), P₂.root (f.indexEquiv j)] =
      f.weightMap ∘ ![P.root i, P.root j] := by
    ext k
    fin_cases k <;> simp [Hom.root_weightMap_apply]
  rw [key]
  exact f.weightMap.linearIndependent_iff
    (LinearMap.ker_eq_bot_of_injective hf)

section Chain

variable [Finite ι] [Finite ι₂] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P₂.IsCrystallographic]

/-- The index bijection of a homomorphism with injective weight map preserves the number of steps
one may add `α` to `β` and stay among the roots. -/
@[simp]
theorem chainTopCoeff_indexEquiv (i j : ι) :
    P₂.chainTopCoeff (f.indexEquiv i) (f.indexEquiv j) = P.chainTopCoeff i j := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' := (f.linearIndependent_root_indexEquiv_iff hf i j).mpr h
    have key : ∀ n : ℕ, P₂.root (f.indexEquiv j) + n • P₂.root (f.indexEquiv i) ∈ range P₂.root ↔
        P.root j + n • P.root i ∈ range P.root := fun n => by
      rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, ← map_nsmul, ← map_add]
      exact f.weightMap_mem_range_root_iff hf
    refine le_antisymm ?_ ?_
    · rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h, ← key]
      exact (P₂.root_add_nsmul_mem_range_iff_le_chainTopCoeff h').mpr le_rfl
    · rw [← P₂.root_add_nsmul_mem_range_iff_le_chainTopCoeff h', key]
      exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr le_rfl
  · rw [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent
      fun hc => h ((f.linearIndependent_root_indexEquiv_iff hf i j).mp hc)]

/-- The index bijection of a homomorphism with injective weight map preserves the number of steps
one may subtract `α` from `β` and stay among the roots. -/
@[simp]
theorem chainBotCoeff_indexEquiv (i j : ι) :
    P₂.chainBotCoeff (f.indexEquiv i) (f.indexEquiv j) = P.chainBotCoeff i j := by
  rw [← P₂.chainTopCoeff_reflectionPerm_left, ← P.chainTopCoeff_reflectionPerm_left,
    ← f.indexEquiv_reflectionPerm, f.chainTopCoeff_indexEquiv hf]

end Chain

end Hom

end RootPairing
