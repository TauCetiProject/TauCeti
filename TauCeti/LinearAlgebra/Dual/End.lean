/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Tower

/-!
# Endomorphisms under left–right linear duality

Let `N` be a right module and identify a left module `Q` with its scalar dual, with the
action given by precomposition. Transposition gives a ring homomorphism from the opposite
endomorphism ring of `N` to the endomorphism ring of `Q`. When `N` is reflexive over the
base, this is a ring equivalence. In particular, finite-dimensional linear duality preserves
the idempotents that detect decompositions of modules.

The action is specified through an equivariant linear identification, so these constructions
apply to a dual carrying a chosen action without introducing competing global instances.
The inverse equivalence is characterized by the same evaluation pairing as transposition.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section I.3.
-/

public section

namespace LinearEquiv

universe u v w z

variable {k : Type u} [CommSemiring k] {A : Type v} [Semiring A] [Algebra k A]
  {N : Type w} [AddCommMonoid N] [Module Aᵐᵒᵖ N] [Module k N]
  [IsScalarTower k Aᵐᵒᵖ N]
  {Q : Type z} [AddCommMonoid Q] [Module A Q] [Module k Q]

/-- Transposition along an equivariant identification with the scalar dual reverses
multiplication of endomorphisms. No reflexivity assumption is needed for this map. -/
def dualEndRingHom (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x)) :
    (Module.End Aᵐᵒᵖ N)ᵐᵒᵖ →+* Module.End A Q where
  toFun f :=
    { __ := e.symm.conjRingEquiv (f.unop.restrictScalars k).dualMap
      map_smul' := fun a q ↦ by
        apply e.injective
        ext x
        simp [he] }
  map_one' := by ext q; apply e.injective; ext x; simp
  map_mul' := by intros; ext q; apply e.injective; ext x; simp
  map_zero' := by ext q; apply e.injective; ext x; simp
  map_add' := by intros; ext q; apply e.injective; ext x; simp

/-- Transposition is precomposition, expressed through the identifying pairing. -/
@[simp]
theorem dualEndRingHom_apply_apply (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x))
    (f : (Module.End Aᵐᵒᵖ N)ᵐᵒᵖ) (q : Q) (x : N) :
    e (e.dualEndRingHom he f q) x = e q (f.unop x) := by
  simp [dualEndRingHom]

/-- Over a reflexive scalar module, every endomorphism of the left dual is the transpose
of a unique right-module endomorphism. -/
theorem dualEndRingHom_bijective [Module.IsReflexive k N]
    (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x)) :
    Function.Bijective (e.dualEndRingHom he) := by
  -- Equivariance forces the given scalar action on `Q` to be restriction along `k → A`.
  let : IsScalarTower k A Q := IsScalarTower.of_algebraMap_smul fun c q ↦ by
    apply e.injective
    ext x
    simp [he, ← MulOpposite.algebraMap_apply]
  constructor
  · intro f g h
    apply MulOpposite.unop_injective
    ext x
    apply (Module.bijective_dual_eval k N).injective
    ext φ
    obtain ⟨q, rfl⟩ := e.surjective φ
    simpa using congrArg (fun F ↦ e (F q) x) h
  · intro g
    let gk := e.conjRingEquiv (g.restrictScalars k)
    let t := (Module.evalEquiv k N).symm.toLinearMap.comp
      (gk.dualMap.comp (Module.Dual.eval k N))
    have ht (φ : Module.Dual k N) (x : N) : φ (t x) = gk φ x := by
      simp [t]
    let f : Module.End Aᵐᵒᵖ N :=
      { __ := t
        map_smul' := fun a x ↦ by
          apply (Module.bijective_dual_eval k N).injective
          ext φ
          obtain ⟨q, rfl⟩ := e.surjective φ
          calc
            e q (t (a • x)) = e (g q) (a • x) := by simp [ht, gk]
            _ = e (a.unop • g q) x := (he a.unop (g q) x).symm
            _ = e (g (a.unop • q)) x := by rw [g.map_smul]
            _ = e (a.unop • q) (t x) := by simp [ht, gk]
            _ = e q (a • t x) := by simp [he] }
    refine ⟨MulOpposite.op f, ?_⟩
    ext q
    apply e.injective
    ext x
    simp [f, ht, gk]

/-- Linear duality identifies the endomorphism ring of a reflexive right module,
with multiplication reversed, with the endomorphism ring of its left dual. -/
noncomputable def dualEndRingEquiv [Module.IsReflexive k N]
    (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x)) :
    (Module.End Aᵐᵒᵖ N)ᵐᵒᵖ ≃+* Module.End A Q :=
  RingEquiv.ofBijective (e.dualEndRingHom he) (e.dualEndRingHom_bijective he)

/-- The endomorphism-ring equivalence acts by precomposition on the pairing. -/
@[simp]
theorem dualEndRingEquiv_apply_apply [Module.IsReflexive k N]
    (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x))
    (f : (Module.End Aᵐᵒᵖ N)ᵐᵒᵖ) (q : Q) (x : N) :
    e (e.dualEndRingEquiv he f q) x = e q (f.unop x) :=
  e.dualEndRingHom_apply_apply he f q x

/-- The inverse transposition is characterized by moving the endomorphism across the
evaluation pairing. -/
@[simp]
theorem dualEndRingEquiv_symm_apply_apply [Module.IsReflexive k N]
    (e : Q ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (q : Q) (x : N), e (a • q) x = e q (MulOpposite.op a • x))
    (g : Module.End A Q) (q : Q) (x : N) :
    e q (((e.dualEndRingEquiv he).symm g).unop x) = e (g q) x := by
  rw [← e.dualEndRingEquiv_apply_apply he, RingEquiv.apply_symm_apply]

end LinearEquiv
