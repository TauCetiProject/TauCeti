/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi

/-!
# Rational functions and the symplectic Levi embedding

The Levi embedding `TauCeti.GLSymplecticFin.leviHom` sends `A : GL (Fin m) k` to the symplectic
matrix `diag(A, (A⁻¹)ᵀ)` in the `Fin (m + m)` coordinates. Each of its entries is an entry of `A`,
an entry of `A⁻¹`, or zero, so each is a rational function of `A`. This is what makes the
restriction of a rational representation of the symplectic group to its Levi subgroup rational.

## Main results

* `TauCeti.GLSymplecticFin.entry_leviHom_mem_rationalFunctions`: every matrix entry of the Levi
  embedding is a rational function on `GL (Fin m) k`.
-/

public section

open TauCeti.Matrix.GeneralLinearGroup

universe u

namespace TauCeti

namespace GLSymplecticFin

variable {k : Type u} [CommRing k] {m : ℕ}

/-- **Every matrix entry of the Levi embedding `A ↦ diag(A, (A⁻¹)ᵀ)` is a rational function of
`A`**: it is an entry of `A`, an entry of `A⁻¹`, or zero. -/
theorem entry_leviHom_mem_rationalFunctions (p : Fin (m + m) × Fin (m + m)) :
    (fun A : GL (Fin m) k => (((leviHom A : GLSymplecticFin m k) :
      GL (Fin (m + m)) k) : _root_.Matrix (Fin (m + m)) (Fin (m + m)) k) p.1 p.2)
      ∈ rationalFunctions k m := by
  obtain ⟨a, b⟩ := p
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective b
  simp only [coe_leviHom, _root_.Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with i | i <;> rcases y with j | j
  · exact polynomialFunctions_le_rationalFunctions (entry_mem_polynomialFunctions i j)
  · exact zero_mem _
  · exact zero_mem _
  · exact entry_inv_mem_rationalFunctions j i

end GLSymplecticFin

end TauCeti
