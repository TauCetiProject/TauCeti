/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.Basic
import Mathlib.GroupTheory.Nilpotent

/-!
# Congruence kernels of `SL₂(ℤ/p^kℤ) →* SL₂(𝔽_p)`

For a prime `p` and `1 ≤ k`, the kernel of reduction modulo `p` on `SL₂(ℤ/p^kℤ)` has order
`p^{3(k - 1)}` (`card_ker_map_zmod_prime_pow` in
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.Basic`). Consequently it is a finite
`p`-group (`isPGroup_ker_map_zmod_prime_pow`), hence nilpotent and solvable
(`isSolvable_ker_map_zmod_prime_pow`).
-/

public section

namespace Matrix.SpecialLinearGroup

open scoped MatrixGroups

/-- For prime `p` and `1 ≤ k`, the kernel of `SL₂(ℤ/p^kℤ) →* SL₂(𝔽_p)` is a `p`-group. -/
theorem isPGroup_ker_map_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    IsPGroup p (map (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) :
      SL(2, ZMod (p ^ k)) →* SL(2, ZMod p)).ker :=
  IsPGroup.of_card (card_ker_map_zmod_prime_pow hp hk)

/-- For prime `p` and `1 ≤ k`, the kernel of `SL₂(ℤ/p^kℤ) →* SL₂(𝔽_p)` is solvable. -/
theorem isSolvable_ker_map_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Group.IsSolvable (map (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) :
      SL(2, ZMod (p ^ k)) →* SL(2, ZMod p)).ker := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  exact (isPGroup_ker_map_zmod_prime_pow hp hk).isNilpotent.to_isSolvable

end Matrix.SpecialLinearGroup
