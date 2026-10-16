/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.End
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linear duality preserves indecomposability

A reflexive right module is indecomposable exactly when its scalar dual, with the left
action by precomposition, is indecomposable. This applies in particular to finite-dimensional
modules over an arbitrary algebra over a field. The result supplies the duality step in
passing from indecomposable transposes to indecomposable Auslander–Reiten translates.

The dual action is specified by an equivariant linear identification. No finiteness of the
algebra, algebraic closedness, or choice of a global module structure on scalar duals is needed.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section I.3.
-/

public section

namespace LinearEquiv

open TauCeti

universe u v w z

variable {k : Type u} [CommSemiring k] {A : Type v} [Ring A] [Algebra k A]
  {N : Type w} [AddCommGroup N] [Module Aᵐᵒᵖ N] [Module k N]
  [IsScalarTower k Aᵐᵒᵖ N] [Module.IsReflexive k N]
  {Q : Type z} [AddCommGroup Q] [Module A Q] [Module k Q]

/-- A reflexive right module is indecomposable exactly when its left scalar dual is.
Finite-dimensional modules over a field satisfy the reflexivity hypothesis automatically. -/
theorem isIndecomposableModule_iff_of_dual (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x)) :
    IsIndecomposableModule A Q ↔ IsIndecomposableModule Aᵐᵒᵖ N := by
  have hnon : Nontrivial Q ↔ Nontrivial N := by
    rw [← not_subsingleton_iff_nontrivial, ← not_subsingleton_iff_nontrivial]
    apply not_congr
    constructor
    · intro h
      let _ := h
      let _ : Subsingleton (Module.Dual k N) := e.symm.toEquiv.subsingleton
      exact (Module.evalEquiv k N).toEquiv.subsingleton
    · intro h
      let _ := h
      exact e.toEquiv.subsingleton
  rw [isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem,
    isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  refine and_congr hnon ?_
  let d := e.dualEndRingEquiv he
  constructor
  · intro h f hf
    have hop : IsIdempotentElem (MulOpposite.op f) :=
      congrArg MulOpposite.op hf
    have hd := h (d (MulOpposite.op f)) (hop.map d)
    simpa using hd.imp (fun h ↦ congrArg (fun g ↦ (d.symm g).unop) h)
      (fun h ↦ congrArg (fun g ↦ (d.symm g).unop) h)
  · intro h f hf
    have hop := hf.map d.symm
    have hunop : IsIdempotentElem (d.symm f).unop :=
      congrArg MulOpposite.unop hop
    have hd := h (d.symm f).unop hunop
    simpa using hd.imp (fun h ↦ congrArg (fun g ↦ d (MulOpposite.op g)) h)
      (fun h ↦ congrArg (fun g ↦ d (MulOpposite.op g)) h)

end LinearEquiv
