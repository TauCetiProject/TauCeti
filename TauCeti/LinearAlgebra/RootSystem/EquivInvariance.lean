/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# What an equivalence of root pairings preserves

An equivalence `g : P.Equiv P₂` of root pairings consists of a linear equivalence of weight spaces,
its transpose on coweight spaces, and a bijection `g.indexEquiv` of the indexing sets, subject to
`g.weightMap (P.root i) = P₂.root (g.indexEquiv i)`. This file collects the combinatorial data that
the index bijection therefore preserves: which elements of the weight space are roots, the integral
Cartan pairings, the negation of an index, additive relations between roots, and the root-string
coefficients `RootPairing.chainTopCoeff` and `RootPairing.chainBotCoeff`.

Mathlib's `RootPairing.Hom.pairing` gives the pairing in the coefficient ring. The invariance
lemmas here also apply to combinatorial expressions in the index bijection, without introducing
weight-space vectors.

## Main results

* `RootPairing.Equiv.weightMap_mem_range_root_iff`: the weight map carries roots to roots and
  nothing else to a root.
* `RootPairing.Hom.pairingIn_indexEquiv`: the index bijection preserves pairings valued in a
  coefficient subring.
* `RootPairing.Hom.indexEquiv_reflectionPerm`: it commutes with `RootPairing.reflectionPerm`, and
  therefore with the negation of an index, which is `RootPairing.reflectionPerm i i` by definition
  and is rewritten to that form by the `simp` lemma `RootPairing.indexNeg_neg`.
* `RootPairing.Equiv.root_indexEquiv_eq_add_iff` and
  `RootPairing.Equiv.root_indexEquiv_eq_sub_iff`: it preserves and reflects the relations
  `α = β + γ` and `α = β - γ` between roots.
* `RootPairing.Equiv.linearIndependent_root_indexEquiv_iff`: it preserves and reflects linear
  independence of a pair of roots.
* `RootPairing.Equiv.chainTopCoeff_indexEquiv` and `RootPairing.Equiv.chainBotCoeff_indexEquiv`: it
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

end Hom

namespace Equiv

variable (g : P.Equiv P₂)

/-- An equivalence of root pairings carries roots to roots, and carries nothing else to a root. -/
theorem weightMap_mem_range_root_iff {m : M} :
    g.toHom.weightMap m ∈ range P₂.root ↔ m ∈ range P.root := by
  refine ⟨fun ⟨l, hl⟩ => ⟨g.indexEquiv.symm l, g.bijective_weightMap.injective ?_⟩,
    fun ⟨i, hi⟩ => ⟨g.indexEquiv i, ?_⟩⟩
  · rw [Hom.root_weightMap_apply, Equiv.apply_symm_apply, hl]
  · rw [← hi, Hom.root_weightMap_apply]

/-- The index bijection of an equivalence of root pairings preserves and reflects the relation
`α = β + γ` between roots. -/
@[simp]
theorem root_indexEquiv_eq_add_iff (k i j : ι) :
    P₂.root (g.indexEquiv k) = P₂.root (g.indexEquiv i) + P₂.root (g.indexEquiv j) ↔
      P.root k = P.root i + P.root j := by
  rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply,
    ← map_add]
  exact g.bijective_weightMap.injective.eq_iff

/-- The index bijection of an equivalence of root pairings preserves and reflects the relation
`α = β - γ` between roots. -/
@[simp]
theorem root_indexEquiv_eq_sub_iff (k j i : ι) :
    P₂.root (g.indexEquiv k) = P₂.root (g.indexEquiv j) - P₂.root (g.indexEquiv i) ↔
      P.root k = P.root j - P.root i := by
  rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply,
    ← map_sub]
  exact g.bijective_weightMap.injective.eq_iff

/-- The index bijection of an equivalence of root pairings preserves and reflects linear
independence of a pair of roots. -/
@[simp]
theorem linearIndependent_root_indexEquiv_iff (i j : ι) :
    LinearIndependent R ![P₂.root (g.indexEquiv i), P₂.root (g.indexEquiv j)] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  have key : ![P₂.root (g.indexEquiv i), P₂.root (g.indexEquiv j)] =
      g.toHom.weightMap ∘ ![P.root i, P.root j] := by
    ext k
    fin_cases k <;> simp [Hom.root_weightMap_apply]
  rw [key]
  exact g.toHom.weightMap.linearIndependent_iff
    (LinearMap.ker_eq_bot_of_injective g.bijective_weightMap.injective)

section Chain

variable [Finite ι] [Finite ι₂] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P₂.IsCrystallographic]

/-- The index bijection of an equivalence of root pairings preserves the number of steps one may
add `α` to `β` and stay among the roots. -/
@[simp]
theorem chainTopCoeff_indexEquiv (i j : ι) :
    P₂.chainTopCoeff (g.indexEquiv i) (g.indexEquiv j) = P.chainTopCoeff i j := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' := (g.linearIndependent_root_indexEquiv_iff i j).mpr h
    have key : ∀ n : ℕ, P₂.root (g.indexEquiv j) + n • P₂.root (g.indexEquiv i) ∈ range P₂.root ↔
        P.root j + n • P.root i ∈ range P.root := fun n => by
      rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, ← map_nsmul, ← map_add]
      exact g.weightMap_mem_range_root_iff
    refine le_antisymm ?_ ?_
    · rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h, ← key]
      exact (P₂.root_add_nsmul_mem_range_iff_le_chainTopCoeff h').mpr le_rfl
    · rw [← P₂.root_add_nsmul_mem_range_iff_le_chainTopCoeff h', key]
      exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr le_rfl
  · rw [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent
      fun hc => h ((g.linearIndependent_root_indexEquiv_iff i j).mp hc)]

/-- The index bijection of an equivalence of root pairings preserves the number of steps one may
subtract `α` from `β` and stay among the roots. -/
@[simp]
theorem chainBotCoeff_indexEquiv (i j : ι) :
    P₂.chainBotCoeff (g.indexEquiv i) (g.indexEquiv j) = P.chainBotCoeff i j := by
  rw [← P₂.chainTopCoeff_reflectionPerm_left, ← P.chainTopCoeff_reflectionPerm_left,
    ← g.toHom.indexEquiv_reflectionPerm, chainTopCoeff_indexEquiv]

end Chain

end Equiv

end RootPairing
