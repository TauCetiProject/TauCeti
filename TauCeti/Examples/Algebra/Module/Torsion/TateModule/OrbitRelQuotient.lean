/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Basic.Real.Basic
import TauCeti.Algebra.Module.Torsion.TateModule.OrbitRelQuotient

/-!
# Checks for the Tate module of a torus

Checks for the torsion of a torus `E / f(Λ)`: for `n = 1` the killed-by-`n` subgroup is zero, and
for `n = ℓ ^ r` multiplication by `ℓ` on torus torsion corresponds to reduction of lattice classes
modulo `ℓ ^ (r - 1)`. For the circle `ℝ / ℤ` the
`2`-adic Tate module is the `2`-adic completion of `ℤ`.
-/

open Function Submodule TauCeti

namespace TauCeti.Examples.TateModuleOrbitRelQuotient

variable {Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E] (f : Λ →ₗ[ℤ] E) (hf : Injective f)

/-- For `n = 1` the killed-by-`n` subgroup `T[p ^ 0]` of the torus is zero. -/
example (p : ℕ) (x : TateModuleLevel p (AddAction.orbitRel.Quotient (LinearMap.range f) E) 0) :
    x = 0 := by
  ext
  simpa using (Submodule.mem_torsionBy_iff _ _).1 x.property

/-- Multiplication by `ℓ` on `T[ℓ ^ (r + 1)] → T[ℓ ^ r]` is reduction modulo `ℓ ^ r` of lattice
classes. -/
example (ℓ r : ℕ)
    (x : TateModuleLevel ℓ (AddAction.orbitRel.Quotient (LinearMap.range f) E) (r + 1)) :
    f.orbitRelQuotientTateModuleLevelδ hf ℓ r
        (tateModuleTransition ℓ (AddAction.orbitRel.Quotient (LinearMap.range f) E) r x) =
      factorPow (Ideal.span {(ℓ : ℤ)}) Λ r.le_succ
        (f.orbitRelQuotientTateModuleLevelδ hf ℓ (r + 1) x) :=
  f.orbitRelQuotientTateModuleLevelδ_transition hf ℓ r x

/-- The `2`-adic Tate module of the circle `ℝ / ℤ` is the `2`-adic completion of `ℤ`. -/
noncomputable example :
    TateModule 2
        (AddAction.orbitRel.Quotient (LinearMap.range (Int.castAddHom ℝ).toIntLinearMap) ℝ) ≃+
      AdicCompletion (Ideal.span {((2 : ℕ) : ℤ)}) ℤ :=
  (Int.castAddHom ℝ).toIntLinearMap.orbitRelQuotientTateModuleδEquiv Int.cast_injective 2
    ⟨fun a b h ↦ by simpa using h,
      fun v ↦ ⟨v / 2, by simp only [Nat.cast_ofNat, two_zsmul, add_halves]⟩⟩

end TauCeti.Examples.TateModuleOrbitRelQuotient
