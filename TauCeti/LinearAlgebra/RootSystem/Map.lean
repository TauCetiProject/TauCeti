/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Pushforward of a root pairing along linear equivalences

Mathlib's `RootPairing.map` pushes a root pairing `P : RootPairing ι R M N` forward along a
bijection `e : ι ≃ ι₂` of root indices and linear equivalences `f : M ≃ₗ[R] M₂` and
`g : N ≃ₗ[R] N₂` of the weight and coweight modules, and transports `RootPairing.IsRootSystem`.
This file supplies the evaluation API of `RootPairing.map`, packages `(e, f, g⁻¹)` as the canonical
root-pairing equivalence `RootPairing.equivMap : P.Equiv (P.map e f g)`, and transports
coefficient-valuedness (in particular `RootPairing.IsCrystallographic`) and
`RootPairing.IsReduced` to `P.map e f g`.

## Main definitions

* `RootPairing.equivMap`: the canonical equivalence `P.Equiv (P.map e f g)` between a root pairing
  and its pushforward along `(e, f, g)`.

## Main results

* `RootPairing.toLinearMap_map`, `RootPairing.root_map`, `RootPairing.coroot_map`,
  `RootPairing.reflectionPerm_map`, and `RootPairing.coroot'_map`: evaluation rules for the
  pushforward pairing.
* `RootPairing.Hom.coroot'_indexEquiv_weightMap`: a homomorphism intertwines coroot functionals
  with its weight map and index bijection.
* `RootPairing.Hom.isReduced`: a homomorphism of root pairings with injective weight map transports
  `RootPairing.IsReduced` from source to target.
* `RootPairing.instIsValuedInMap` and `RootPairing.instIsReducedMap`: `P.map e f g` inherits
  `IsValuedIn S` (hence `IsCrystallographic`) and `IsReduced` from `P`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing

open Function

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]

/-- Evaluating the coroot functional at `h.indexEquiv j` on `h.weightMap x` agrees with evaluating
the source coroot functional at `j` on `x`. -/
theorem Hom.coroot'_indexEquiv_weightMap {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}
    (h : P.Hom P₂) (j : ι) (x : M) :
    P₂.coroot' (h.indexEquiv j) (h.weightMap x) = P.coroot' j x := by
  have hj : h.coweightMap (P₂.coroot (h.indexEquiv j)) = P.coroot j := by
    simpa using Hom.coroot_coweightMap_apply P P₂ (h.indexEquiv j) h
  simpa [coroot', hj] using congr($h.weight_coweight_transpose (P₂.coroot (h.indexEquiv j)) x)

/-- A homomorphism of root pairings with injective weight map transports reducedness from the
source pairing to the target pairing. -/
theorem Hom.isReduced {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}
    (h : P.Hom P₂) (hinj : Injective h.weightMap) [P.IsReduced] : P₂.IsReduced where
  eq_or_eq_neg i₂ j₂ hdep := by
    obtain ⟨i, rfl⟩ := h.indexEquiv.surjective i₂
    obtain ⟨j, rfl⟩ := h.indexEquiv.surjective j₂
    rw [h.linearIndependent_root_indexEquiv_iff hinj] at hdep
    rcases IsReduced.eq_or_eq_neg (P := P) i j hdep with heq | hneg
    · refine Or.inl ?_
      have himg := congrArg h.weightMap heq
      rwa [Hom.root_weightMap_apply, Hom.root_weightMap_apply] at himg
    · refine Or.inr ?_
      have himg := congrArg h.weightMap hneg
      rwa [Hom.root_weightMap_apply, map_neg, Hom.root_weightMap_apply] at himg

section Map

variable (P : RootPairing ι R M N) (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂)

/-- The bilinear pairing of `P.map e f g` pulls back along `f.symm` and `g.symm`. -/
@[simp]
theorem toLinearMap_map (x : M₂) (y : N₂) :
    (P.map e f g).toLinearMap x y = P.toLinearMap (f.symm x) (g.symm y) :=
  (rfl)

/-- Each root of `P.map e f g` is the image under `f` of the preimage root of `P`. -/
@[simp]
theorem root_map (i : ι₂) :
    (P.map e f g).root i = f (P.root (e.symm i)) :=
  (rfl)

/-- Each coroot of `P.map e f g` is the image under `g` of the preimage coroot of `P`. -/
@[simp]
theorem coroot_map (i : ι₂) :
    (P.map e f g).coroot i = g (P.coroot (e.symm i)) :=
  (rfl)

/-- Reflections of `P.map e f g` conjugate the reflection permutations of `P` by `e`. -/
@[simp]
theorem reflectionPerm_map (i j : ι₂) :
    (P.map e f g).reflectionPerm i j = e (P.reflectionPerm (e.symm i) (e.symm j)) :=
  (rfl)

/-- Coroot functionals of `P.map e f g` pull back along `e.symm` and `f.symm`. -/
theorem coroot'_map (i : ι₂) (x : M₂) :
    (P.map e f g).coroot' i x = P.coroot' (e.symm i) (f.symm x) := by
  simp [coroot']

/-- The canonical equivalence `P.Equiv (P.map e f g)` carrying roots along `f`, coroots
contravariantly along `g.symm`, and indices along `e`. -/
def equivMap : P.Equiv (P.map e f g) where
  weightMap := f.toLinearMap
  coweightMap := g.symm.toLinearMap
  indexEquiv := e
  weight_coweight_transpose := by
    ext y x
    simp
  root_weightMap := by
    ext i
    simp
  coroot_coweightMap := by
    ext i
    simp
  bijective_weightMap := f.bijective
  bijective_coweightMap := g.symm.bijective

/-- The weight map of `equivMap` applies `f`. -/
@[simp]
theorem weightMap_equivMap_apply (x : M) :
    (P.equivMap e f g).weightMap x = f x :=
  (rfl)

/-- The weight equivalence of `equivMap` is `f`. -/
@[simp]
theorem weightEquiv_equivMap :
    (P.equivMap e f g).weightEquiv = f :=
  LinearEquiv.ext fun _ ↦ rfl

/-- The contravariant coweight map of `equivMap` applies `g.symm`. -/
@[simp]
theorem coweightMap_equivMap_apply (y : N₂) :
    (P.equivMap e f g).coweightMap y = g.symm y :=
  (rfl)

/-- The contravariant coweight equivalence of `equivMap` is `g.symm`. -/
@[simp]
theorem coweightEquiv_equivMap :
    (P.equivMap e f g).coweightEquiv = g.symm :=
  LinearEquiv.ext fun _ ↦ rfl

/-- The index equivalence of `equivMap` is `e`. -/
@[simp]
theorem indexEquiv_equivMap :
    (P.equivMap e f g).indexEquiv = e :=
  (rfl)

/-- Pushing a root pairing forward along linear equivalences preserves coefficient-valuedness, and
in particular `RootPairing.IsCrystallographic`. -/
instance instIsValuedInMap (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    (P.map e f g).IsValuedIn S :=
  (P.equivMap e f g).toHom.isValuedIn S

/-- Pushing a reduced root pairing forward along linear equivalences preserves reducedness. -/
instance instIsReducedMap [P.IsReduced] : (P.map e f g).IsReduced :=
  (P.equivMap e f g).toHom.isReduced f.injective

end Map

end RootPairing
