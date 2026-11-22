/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom
public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
public import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# Invariance under homomorphisms of root pairings

A homomorphism `f : P.Hom P₂` of root pairings consists of a linear map of weight spaces,
its transpose on coweight spaces, and a bijection `f.indexEquiv` of the indexing sets, subject to
`f.weightMap (P.root i) = P₂.root (f.indexEquiv i)`. The index bijection preserves Cartan pairings
and commutes with root reflections. When the weight map is injective, it also preserves and reflects
root membership, additive relations between roots, and linear independence.

The weight map need not be surjective: these results also apply when the target has extra toral
directions outside the span of its roots. An equivalence of root pairings supplies the injectivity
hypothesis through `g.bijective_weightMap.injective`. Coefficient-valuedness is transported by
`RootPairing.Hom.isValuedIn`.

Mathlib's `RootPairing.Hom.pairing` gives the pairing in the coefficient ring. The invariance
lemmas here also apply to combinatorial expressions in the index bijection, without introducing
weight-space vectors.

## Main results

* `RootPairing.Hom.weightMap_mem_range_root_iff`: the weight map carries roots to roots and
  nothing else to a root.
* `RootPairing.Hom.isValuedIn`: the target root pairing takes values in any coefficient ring in
  which the source root pairing takes values.
* `RootPairing.Hom.pairingIn_indexEquiv`: the index bijection preserves pairings valued in a
  coefficient subring.
* `RootPairing.Hom.indexEquiv_reflectionPerm`: it commutes with `RootPairing.reflectionPerm`, and
  therefore with the negation of an index, which is `RootPairing.reflectionPerm i i` by definition
  and is rewritten to that form by the `simp` lemma `RootPairing.indexNeg_neg`.
* `RootPairing.Hom.root_indexEquiv_eq_add_iff` and
  `RootPairing.Hom.root_indexEquiv_eq_sub_iff`: it preserves and reflects the relations
  `α = β + γ` and `α = β - γ` between roots.
* `RootPairing.Hom.linearIndependent_root_indexEquiv_iff`: it preserves and reflects linear
  independence of a pair of roots; consequently `RootPairing.Hom.isReduced` and
  `RootPairing.Equiv.isReduced` transport reducedness to the target pairing.
* `RootPairing.Equiv.isRootSystem`: an equivalence of root pairings transports `IsRootSystem`.
* `RootPairing.Hom.coroot'_weightMap` and `RootPairing.Hom.weightMap_reflection`: the weight map
  preserves coroot values and intertwines the reflection at a root with the reflection at its
  image. These generalise Mathlib's `RootPairing.Equiv.coroot'_weightEquiv` and
  `RootPairing.Equiv.weightEquiv_reflection` from equivalences to morphisms.

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

/-- A homomorphism of root pairings transports the property that all root-coroot pairings take
values in a given coefficient ring. -/
theorem isValuedIn (f : P.Hom P₂) (S : Type*) [CommRing S] [Algebra S R]
    [P.IsValuedIn S] : P₂.IsValuedIn S where
  exists_value i j := by
    obtain ⟨i, rfl⟩ := f.indexEquiv.surjective i
    obtain ⟨j, rfl⟩ := f.indexEquiv.surjective j
    rw [f.pairing]
    exact P.exists_value i j

/-- The index bijection of a homomorphism of root pairings preserves the pairing valued in a
coefficient subring. -/
@[simp]
theorem pairingIn_indexEquiv (f : P.Hom P₂) (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) :
    letI := f.isValuedIn S
    P₂.pairingIn S (f.indexEquiv i) (f.indexEquiv j) = P.pairingIn S i j := by
  let := f.isValuedIn S
  refine FaithfulSMul.algebraMap_injective S R ?_
  rw [algebraMap_pairingIn, algebraMap_pairingIn, f.pairing]

/-- The index bijection of a homomorphism of root pairings commutes with root reflections. -/
@[simp]
theorem indexEquiv_reflectionPerm (f : P.Hom P₂) (i j : ι) :
    f.indexEquiv (P.reflectionPerm i j) =
      P₂.reflectionPerm (f.indexEquiv i) (f.indexEquiv j) := by
  refine P₂.root.injective ?_
  rw [← Hom.root_weightMap_apply]
  simp [root_reflectionPerm, reflection_apply_root, Hom.root_weightMap_apply]

/-- The weight map of a homomorphism of root pairings preserves coroot values: pulling the coroot
functional at `f.indexEquiv i` back along `f.weightMap` gives the coroot functional at `i`. This
generalises Mathlib's `RootPairing.Equiv.coroot'_weightEquiv` from equivalences to morphisms. -/
@[grind =]
theorem coroot'_weightMap (f : P.Hom P₂) (i : ι) (x : M) :
    P₂.coroot' (f.indexEquiv i) (f.weightMap x) = P.coroot' i x := by
  simpa [coroot', Hom.coroot_coweightMap_apply] using
    congrArg (fun g : Module.Dual R M ↦ g x)
      (f.weight_coweight_transpose_apply P P₂ (P₂.coroot (f.indexEquiv i)))

/-- The weight map of a homomorphism of root pairings intertwines the reflection at a root with
the reflection at its image. This generalises Mathlib's `RootPairing.Equiv.weightEquiv_reflection`
from equivalences to morphisms, with the same proof. -/
theorem weightMap_reflection (f : P.Hom P₂) (i : ι) (x : M) :
    f.weightMap (P.reflection i x) = P₂.reflection (f.indexEquiv i) (f.weightMap x) := by
  rw [reflection_apply, reflection_apply, map_sub, map_smul, Hom.root_weightMap_apply,
    coroot'_weightMap]

section Injective

variable (f : P.Hom P₂) (hf : Injective f.weightMap)
include hf

/-- A homomorphism of root pairings with injective weight map carries roots to roots, and carries
nothing else to a root. -/
theorem weightMap_mem_range_root_iff {m : M} :
    f.weightMap m ∈ range P₂.root ↔ m ∈ range P.root := by
  rw [← hf.mem_set_image, ← range_comp, f.root_weightMap, EquivLike.range_comp]

/-- The index bijection of a homomorphism with injective weight map preserves and reflects
the relation `α = β + γ` between roots. -/
@[simp]
theorem root_indexEquiv_eq_add_iff (k i j : ι) :
    P₂.root (f.indexEquiv k) = P₂.root (f.indexEquiv i) + P₂.root (f.indexEquiv j) ↔
      P.root k = P.root i + P.root j := by
  simp only [← Hom.root_weightMap_apply, ← map_add, hf.eq_iff]

/-- The index bijection of a homomorphism with injective weight map preserves and reflects
the relation `α = β - γ` between roots. -/
@[simp]
theorem root_indexEquiv_eq_sub_iff (k j i : ι) :
    P₂.root (f.indexEquiv k) = P₂.root (f.indexEquiv j) - P₂.root (f.indexEquiv i) ↔
      P.root k = P.root j - P.root i := by
  simp only [← Hom.root_weightMap_apply, ← map_sub, hf.eq_iff]

/-- The index bijection of a homomorphism with injective weight map preserves and reflects linear
independence of a pair of roots. -/
@[simp]
theorem linearIndependent_root_indexEquiv_iff (i j : ι) :
    LinearIndependent R ![P₂.root (f.indexEquiv i), P₂.root (f.indexEquiv j)] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  rw [← f.weightMap.linearIndependent_iff_of_injOn hf.injOn]
  congr!
  ext k
  fin_cases k <;> simp [Hom.root_weightMap_apply]

/-- A homomorphism with injective weight map transports reducedness to the target. -/
theorem isReduced [P.IsReduced] : P₂.IsReduced := by
  rw [isReduced_iff']; intro i₂ j₂ hij hdep
  obtain ⟨i, rfl⟩ := f.indexEquiv.surjective i₂
  obtain ⟨j, rfl⟩ := f.indexEquiv.surjective j₂
  rcases IsReduced.eq_or_eq_neg i j (mt (f.linearIndependent_root_indexEquiv_iff hf i j).mpr hdep)
    with hroot | hroot
  · exact absurd (congrArg f.indexEquiv (P.root.injective hroot)) hij
  · rw [← Hom.root_weightMap_apply P P₂ i f, hroot, map_neg, Hom.root_weightMap_apply P P₂ j f]

end Injective

end Hom

/-- An equivalence of root pairings transports `IsRootSystem` from the source to the target. -/
theorem Equiv.isRootSystem (e : P.Equiv P₂) [P.IsRootSystem] : P₂.IsRootSystem where
  span_root_eq_top := by
    have h := congrArg (Submodule.map e.weightEquiv.toLinearMap)
      (IsRootSystem.span_root_eq_top (P := P))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    convert h using 2
    rw [← Set.range_comp]
    have hcomp : (e.weightEquiv.toLinearMap : M → M₂) ∘ P.root = P₂.root ∘ e.indexEquiv := by
      ext i
      exact Hom.root_weightMap_apply P P₂ i e.toHom
    rw [hcomp, EquivLike.range_comp]
  span_coroot_eq_top := by
    have h := congrArg (Submodule.map e.coweightEquiv.symm.toLinearMap)
      (IsRootSystem.span_coroot_eq_top (P := P))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    convert h using 2
    rw [← Set.range_comp]
    have hcomp : (e.coweightEquiv.symm.toLinearMap : N → N₂) ∘ P.coroot =
        P₂.coroot ∘ e.indexEquiv := by
      ext i
      simp [← Equiv.inv_coweightMap, Hom.coroot_coweightMap_apply]
    rw [hcomp, EquivLike.range_comp]

/-- An equivalence of root pairings transports reducedness from the source to the target. -/
theorem Equiv.isReduced (e : P.Equiv P₂) [P.IsReduced] : P₂.IsReduced :=
  e.toHom.isReduced e.bijective_weightMap.injective

end RootPairing
