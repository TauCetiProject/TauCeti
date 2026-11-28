/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Aut

/-!
# Permutations of ring homomorphisms by postcomposition

`RingAut.toPermRingHom` turns the action of the target ring's automorphisms on ring
homomorphisms into a monoid homomorphism. Its range gives a finite quotient of the
automorphism group whenever there are finitely many ring homomorphisms.
-/

public section

namespace RingAut

variable (R S : Type*) [NonAssocSemiring R] [NonAssocSemiring S]

/-- Automorphisms of `S` permute the homomorphisms from `R` to `S` by postcomposition. -/
def toPermRingHom : RingAut S →* Equiv.Perm (R →+* S) where
  toFun σ :=
    { toFun f := σ.toRingHom.comp f
      invFun f := σ.symm.toRingHom.comp f
      left_inv f := by simp only [← RingHom.comp_assoc,
        σ.symm_toRingHom_comp_toRingHom, RingHom.id_comp]
      right_inv f := by simp only [← RingHom.comp_assoc,
        σ.toRingHom_comp_symm_toRingHom, RingHom.id_comp] }
  map_one' := Equiv.ext fun f ↦ RingHom.ext fun x ↦ by simp
  map_mul' σ τ := Equiv.ext fun f ↦ RingHom.ext fun x ↦ (rfl)

/-- Evaluating the permutation associated to `σ` postcomposes the input homomorphism with `σ`. -/
@[simp]
theorem toPermRingHom_apply (σ : RingAut S) (f : R →+* S) :
    toPermRingHom R S σ f = σ.toRingHom.comp f := (rfl)

end RingAut
