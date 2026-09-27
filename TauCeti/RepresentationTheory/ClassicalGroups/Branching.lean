/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard

/-!
# Branching of the standard representation along the block inclusion

The block inclusion `TauCeti.glBlockSucc : GL (Fin n) k →* GL (Fin (n + 1)) k` puts a matrix in the
upper-left block and fixes the last basis vector, so restricting the standard representation of
`GL (Fin (n + 1)) k` along it leaves the last coordinate alone.  This file proves that, in the form

`Res (stdRep k (n + 1)) ≅ stdRep k n ⊕ 1`,

as `TauCeti.stdRepBlockSuccEquiv`, and records the resulting character identity
`TauCeti.char_stdRep_glBlockSucc`.

This is the branching problem `GL (n + 1) ↓ GL n` for the standard representation: the restriction
of the standard representation splits off a trivial summand and leaves the standard representation
of the smaller group.  The corresponding decomposition of the other irreducible representations
needs the highest-weight classification and is not proved here; what is proved here is the
restriction formula `TauCeti.stdRep_glBlockSucc_apply` that any such computation starts from,
together with this one splitting.

The splitting is `LinearEquiv.piFinSnoc`: a vector of `Fin (n + 1) → k` is its first `n`
coordinates together with its last, and that linear isomorphism is what carries the restricted
representation onto `Representation.prod`.

## Main definitions

* `TauCeti.stdRepBlockSuccEquiv`: the branching isomorphism, an equivalence of representations of
  `GL (Fin n) k`.

## Main results

* `TauCeti.stdRep_glBlockSucc_apply`: the restricted standard action multiplies the first `n`
  coordinates by `g` and fixes the last.
* `TauCeti.char_stdRep_glBlockSucc`: the character of the restriction is the character of the
  standard representation plus one.
* `TauCeti.stdRep_comp_glBlockSucc_injective`: the restriction is still faithful.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- **The standard action, restricted along the block inclusion**: `g` multiplies the first `n`
coordinates and the last one is fixed. -/
theorem stdRep_glBlockSucc_apply (g : GL (Fin n) k) (v : Fin (n + 1) → k) :
    stdRep k (n + 1) (glBlockSucc k n g) v =
      Fin.snoc ((g : Matrix (Fin n) (Fin n) k) *ᵥ Fin.init v) (v (Fin.last n)) := by
  rw [stdRep_apply_apply, coe_glBlockSucc, blockSucc_mulVec]

/-- **Branching of the standard representation of `GL (Fin (n + 1)) k` to `GL (Fin n) k`.**  The
restriction along the block inclusion is the standard representation of the smaller group plus a
trivial summand, carried by the splitting of a vector into its first `n` coordinates and its last
one. -/
noncomputable def stdRepBlockSuccEquiv :
    Representation.Equiv
      ((stdRep k (n + 1)).comp (glBlockSucc k n) :
        Representation k (GL (Fin n) k) (Fin (n + 1) → k))
      ((stdRep k n).prod (Representation.trivial k (GL (Fin n) k) k)) :=
  Representation.Equiv.mk (LinearEquiv.piFinSnoc k fun _ => k) fun g => LinearMap.ext fun v =>
    Prod.ext (by simp [blockSucc_mulVec]) (by simp [blockSucc_mulVec])

@[simp]
theorem stdRepBlockSuccEquiv_apply (v : Fin (n + 1) → k) :
    stdRepBlockSuccEquiv k n v = (Fin.init v, v (Fin.last n)) :=
  LinearEquiv.piFinSnoc_apply k (fun _ => k) v

@[simp]
theorem stdRepBlockSuccEquiv_symm_apply (p : (Fin n → k) × k) :
    (stdRepBlockSuccEquiv k n).symm p = Fin.snoc p.1 p.2 :=
  LinearEquiv.piFinSnoc_symm_apply k (fun _ => k) p

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
