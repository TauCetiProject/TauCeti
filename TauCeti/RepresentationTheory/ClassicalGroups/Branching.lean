/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard

/-!
# Branching of the standard representation along the block inclusion

The block inclusion `TauCeti.glBlockSucc : GL (Fin n) k →* GL (Fin (n + 1)) k` puts a matrix in the
upper-left block and fixes the last basis vector, so restricting the standard representation of
`GL (Fin (n + 1)) k` along it leaves the last coordinate alone.  This file proves that, in the form

`Res (stdRep k (n + 1)) ≅ stdRep k n ⊕ 1`,

as `TauCeti.stdRepBlockSuccEquiv`, and records the resulting character identity
`TauCeti.char_stdRep_glBlockSucc`.

This is the first instance of the branching rule `GL n ↓ GL (n-1)`.  The standard representation is
the irreducible of highest weight `(1, 0, …, 0)`, the two sequences interlacing that weight are
`(1, 0, …, 0)` and `(0, …, 0)`, and those are the highest weights of the standard and the trivial
representation of the smaller group; so the decomposition below is multiplicity-free, as the
branching rule predicts.  The decomposition of a general `V_λ` needs the highest-weight
classification and is not proved here.  What is proved here is the case of the first fundamental
weight, together with the restriction formula `TauCeti.stdRep_glBlockSucc_apply` that any such
computation starts from.

The splitting is written against `Fin.snoc` and `Fin.init`: a vector of `Fin (n + 1) → k` is its
first `n` coordinates together with its last, and that linear isomorphism is what carries the
restricted representation onto `Representation.prod`.

## Main definitions

* `TauCeti.stdRepBlockSuccEquiv`: the branching isomorphism, an equivalence of representations of
  `GL (Fin n) k`.

## Main results

* `TauCeti.stdRep_glBlockSucc_apply`: the restricted standard action multiplies the first `n`
  coordinates by `g` and fixes the last.
* `TauCeti.char_stdRep_glBlockSucc`: the character of the restriction is the character of the
  standard representation plus one.
* `TauCeti.stdRep_comp_glBlockSucc_injective`: the restriction is still faithful.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "`GLₙ ↓ GLₙ₋₁`".
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- A vector of length `n + 1` split into its first `n` coordinates and its last one.  This is the
linear isomorphism along which the restricted standard representation becomes a product, so it is
the underlying linear equivalence of `TauCeti.stdRepBlockSuccEquiv` and is kept private;
`TauCeti.stdRepBlockSuccEquiv_apply` records its formula. -/
private def initLastLinearEquiv : (Fin (n + 1) → k) ≃ₗ[k] (Fin n → k) × k where
  toFun v := (Fin.init v, v (Fin.last n))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := Fin.snoc p.1 p.2
  left_inv v := Fin.snoc_init_self v
  right_inv p := Prod.ext (by simp) (by simp)

private theorem initLastLinearEquiv_apply (v : Fin (n + 1) → k) :
    initLastLinearEquiv k n v = (Fin.init v, v (Fin.last n)) :=
  (rfl)

/-- **The standard action, restricted along the block inclusion**: `g` multiplies the first `n`
coordinates and the last one is fixed. -/
theorem stdRep_glBlockSucc_apply (g : GL (Fin n) k) (v : Fin (n + 1) → k) :
    stdRep k (n + 1) (glBlockSucc k n g) v =
      Fin.snoc ((g : Matrix (Fin n) (Fin n) k) *ᵥ Fin.init v) (v (Fin.last n)) := by
  rw [stdRep_apply_apply, coe_glBlockSucc, blockSucc_mulVec]

/-- **Branching of the standard representation of `GL (Fin (n + 1)) k` to `GL (Fin n) k`.**  The
restriction along the block inclusion is the standard representation of the smaller group plus a
trivial summand, carried by the splitting of a vector into its first `n` coordinates and its last
one.  This is the multiplicity-free branching `GL (n + 1) ↓ GL n` for the first fundamental weight:
the two dominant weights interlacing `(1, 0, …, 0)` are `(1, 0, …, 0)` and `(0, …, 0)`. -/
noncomputable def stdRepBlockSuccEquiv :
    Representation.Equiv
      ((stdRep k (n + 1)).comp (glBlockSucc k n) :
        Representation k (GL (Fin n) k) (Fin (n + 1) → k))
      ((stdRep k n).prod (Representation.trivial k (GL (Fin n) k) k)) :=
  Representation.Equiv.mk (initLastLinearEquiv k n) fun g => LinearMap.ext fun v =>
    Prod.ext (by simp [initLastLinearEquiv_apply, blockSucc_mulVec])
      (by simp [initLastLinearEquiv_apply, blockSucc_mulVec])

@[simp]
theorem stdRepBlockSuccEquiv_apply (v : Fin (n + 1) → k) :
    stdRepBlockSuccEquiv k n v = (Fin.init v, v (Fin.last n)) :=
  (rfl)

/-- The standard representation stays faithful after restriction along the block inclusion, both
maps being injective. -/
theorem stdRep_comp_glBlockSucc_injective :
    Function.Injective ((stdRep k (n + 1)).comp (glBlockSucc k n)) :=
  (stdRep_injective k (n + 1)).comp (glBlockSucc_injective k n)

end CommRing

section Field

variable [Field k]

/-- The character of the restricted standard representation is the character of the standard
representation of the smaller group plus one, the dimension of the trivial summand. -/
theorem char_stdRep_glBlockSucc (g : GL (Fin n) k) :
    (stdRep k (n + 1)).character (glBlockSucc k n g) = (stdRep k n).character g + 1 := by
  rw [char_stdRep, char_stdRep, coe_glBlockSucc, trace_blockSucc]

/-- The character identity for the bundled standard representation. -/
theorem char_stdFDRep_glBlockSucc (g : GL (Fin n) k) :
    (stdFDRep k (n + 1)).character (glBlockSucc k n g) = (stdFDRep k n).character g + 1 := by
  rw [char_stdFDRep, char_stdFDRep, coe_glBlockSucc, trace_blockSucc]

end Field

end TauCeti
