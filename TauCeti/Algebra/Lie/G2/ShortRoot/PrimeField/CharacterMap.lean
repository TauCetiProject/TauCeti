/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.SpecialIsogeny
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullbacks of the short-root G₂ special isogeny

The signed-minor special isogeny of `TauCeti.G2ShortRoot.PrimeField.points` sends the
fundamental-weight torus parameter `(s₀, s₁)` to `(s₁, s₀³)`. Its character pullback is therefore
`TauCeti.DynkinType.g2SpecialIsogeny.weightMap`, not its transpose. This file identifies the
independently constructed point endomorphism with that lattice map, and computes the pullback
of every odd power used in the Ree construction.

The equations hold over every commutative `𝔽₃`-algebra. They concern the explicit prime-field
carrier and do not identify it with the canonical simply connected group scheme.

The central formal inputs are `specialIsogeny_weightTorusPoints`,
`specialIsogeny_comp_specialIsogeny` and `frobenius_weightTorusPoints`; character maps compose
by `TauCeti.IsCharacterMap.comp`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the odd-power construction.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

variable (A : Type*) [CommRing A] [Algebra (ZMod 3) A]

/-- Frobenius pulls back characters of the weight torus by multiplication by `3 ^ m`. -/
theorem isCharacterMap_frobenius (m : ℕ) :
    IsCharacterMap (weightTorusPoints A) (frobenius m A)
      ((3 ^ m : ℕ) • (1 : Module.End ℤ (Fin 2 → ℤ))) := by
  rw [isCharacterMap_iff]
  intro s
  rw [frobenius_weightTorusPoints, torusPointMap_nsmul, torusPointMap_one]
  rfl

/-- The signed-minor special isogeny pulls back characters by the pinned G₂ special
root-datum isogeny's weight map, in fundamental-weight coordinates. -/
theorem isCharacterMap_specialIsogeny :
    IsCharacterMap (weightTorusPoints A) (specialIsogeny A)
      DynkinType.g2SpecialIsogeny.weightMap := by
  rw [isCharacterMap_iff]
  intro s
  rw [specialIsogeny_weightTorusPoints]
  congr 1
  funext i
  fin_cases i <;>
    simp [torusPointMap_apply, DynkinType.g2SpecialIsogeny_weightMap,
      DynkinType.g2SpecialIsogenyMatrix_def, torusCharacter_def, Fin.prod_univ_succ]

/-- The character pullback of the odd special-isogeny power is `3 ^ m` times the pinned
special weight map. The scalar factor does not remove the length exchange. -/
theorem isCharacterMap_specialIsogeny_pow_odd (m : ℕ) :
    IsCharacterMap (weightTorusPoints A)
      (HPow.hPow (α := Monoid.End (points A)) (specialIsogeny A) (2 * m + 1))
      ((3 ^ m : ℕ) • DynkinType.g2SpecialIsogeny.weightMap) := by
  rw [specialIsogeny_pow_odd]
  have hchar : DynkinType.g2SpecialIsogeny.weightMap *
        ((3 ^ m : ℕ) • (1 : Module.End ℤ (Fin 2 → ℤ))) =
      (3 ^ m : ℕ) • DynkinType.g2SpecialIsogeny.weightMap := by
    rw [Module.End.mul_eq_comp, LinearMap.comp_smul]
    rfl
  exact hchar ▸ (isCharacterMap_frobenius A m).comp (isCharacterMap_specialIsogeny A)

end TauCeti.G2ShortRoot.PrimeField
