/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic

/-!
# Intertwining Lie algebra homomorphisms

Intertwining homomorphisms compose, and the inverse of an intertwining equivalence
intertwines the endomorphisms in the opposite direction.
-/

public section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

variable {M N : Type*} [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N]

namespace LieHom

variable {f : L →ₗ⁅R⁆ L} {g : M →ₗ⁅R⁆ M} {k : N →ₗ⁅R⁆ N}

/-- Intertwining homomorphisms compose to an intertwining homomorphism. -/
theorem comp_intertwines (u : L →ₗ⁅R⁆ M) (v : M →ₗ⁅R⁆ N)
    (hu : g.comp u = u.comp f) (hv : k.comp v = v.comp g) :
    k.comp (v.comp u) = (v.comp u).comp f := by
  ext x
  exact (congr_fun hv (u x)).trans (congrArg v (congr_fun hu x))

end LieHom

namespace LieEquiv

variable {f : L →ₗ⁅R⁆ L} {g : M →ₗ⁅R⁆ M} {k : N →ₗ⁅R⁆ N}

/-- The inverse of an intertwining equivalence intertwines in the opposite direction. -/
theorem symm_intertwines (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f) :
    f.comp e.symm.toLieHom = e.symm.toLieHom.comp g := by
  ext y
  apply e.injective
  simpa using (LieHom.congr_fun h (e.symm y)).symm

/-- The composite of intertwining equivalences intertwines. -/
theorem trans_intertwines (e₁ : L ≃ₗ⁅R⁆ M) (e₂ : M ≃ₗ⁅R⁆ N)
    (h₁ : g.comp e₁.toLieHom = e₁.toLieHom.comp f)
    (h₂ : k.comp e₂.toLieHom = e₂.toLieHom.comp g) :
    k.comp (e₁.trans e₂).toLieHom = (e₁.trans e₂).toLieHom.comp f :=
  LieHom.comp_intertwines e₁.toLieHom e₂.toLieHom h₁ h₂

end LieEquiv
