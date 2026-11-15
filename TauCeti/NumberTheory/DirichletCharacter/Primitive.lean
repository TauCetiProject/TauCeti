/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# Comparing primitive characters at different levels

Primitive Dirichlet characters are identified by their lifts to a common nonzero level. Equality
of the lifts forces equality of the original levels, because changing level preserves the
conductor. This gives an equality criterion without choosing representatives at prime arguments.

For primitive quadratic characters, their product at the least common multiple level is principal
exactly when the original characters coincide, including their levels. This separates the
exceptional equal-character case in two-character arguments for real Dirichlet L-functions.
Only one of the two characters needs to be quadratic.
-/

public section

namespace DirichletCharacter

variable {R : Type*} {N M L : ℕ}

/-- Two primitive characters have equal lifts to a common nonzero level exactly when their levels
and characters agree. The existential equality transports the first character to the second
level. -/
theorem IsPrimitive.changeLevel_eq_changeLevel_iff [CommMonoidWithZero R] [NeZero L]
    {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hN : N ∣ L) (hM : M ∣ L) :
    changeLevel hN χ = changeLevel hM ψ ↔ ∃ h : N = M, h ▸ χ = ψ := by
  constructor
  · intro h
    have hlevel : N = M := by
      simpa only [conductor_changeLevel, (isPrimitive_def χ).mp hχ,
        (isPrimitive_def ψ).mp hψ] using congrArg conductor h
    subst M
    exact ⟨rfl, changeLevel_injective hN h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

section Quadratic

variable [CommRing R]

/-- The common-level product of two primitive characters, one of them quadratic, is principal
exactly when they are the same primitive character. In particular, different primitive levels
cannot give a principal product. -/
theorem IsPrimitive.mul_eq_one_iff {χ : DirichletCharacter R N}
    {ψ : DirichletCharacter R M} [NeZero N] [NeZero M]
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψq : ψ.IsQuadratic) :
    χ.mul ψ = 1 ↔ ∃ h : N = M, h ▸ χ = ψ := by
  have : NeZero (Nat.lcm N M) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne M)⟩
  have hq := hψq.changeLevel (Nat.dvd_lcm_right N M)
  rw [DirichletCharacter.mul, mul_eq_one_iff_eq_inv, hq.inv]
  exact hχ.changeLevel_eq_changeLevel_iff hψ _ _

end Quadratic

end DirichletCharacter
