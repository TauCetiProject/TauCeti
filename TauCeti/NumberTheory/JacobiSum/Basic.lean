/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Transport of Jacobi sums

Mathlib's `jacobiSum_ringHomComp` moves a Jacobi sum `J(χ, ψ) = ∑ x, χ x * ψ (1 - x)` along a
homomorphism of the coefficient ring. Here we also change the domain: if a ring isomorphism
`e : R ≃+* S` of finite rings and a coefficient homomorphism `f` carry `χ` to `χ'` and `ψ` to
`ψ'`, in the sense that `f (χ a) = χ' (e a)` and `f (ψ a) = ψ' (e a)`, then
`f (J(χ, ψ)) = J(χ', ψ')`. This is how a ring isomorphism of rings of integers acts on Jacobi
sums of characters of their residue fields, such as power residue symbols.
-/

public section

namespace TauCeti

variable {R S R' R'' F : Type*} [CommRing R] [Fintype R] [CommRing S] [Fintype S] [CommRing R']
  [CommRing R''] [FunLike F R' R''] [RingHomClass F R' R'']

/-- **Transport of Jacobi sums.** If a ring isomorphism `e` of the domains and a homomorphism
`f` of the coefficients carry `χ` to `χ'` and `ψ` to `ψ'`, then `f (J(χ, ψ)) = J(χ', ψ')`. -/
theorem map_jacobiSum {f : F} {e : R ≃+* S} {χ ψ : MulChar R R'} {χ' ψ' : MulChar S R''}
    (hχ : ∀ a, f (χ a) = χ' (e a)) (hψ : ∀ a, f (ψ a) = ψ' (e a)) :
    f (jacobiSum χ ψ) = jacobiSum χ' ψ' := by
  simp only [jacobiSum, map_sum, map_mul, hχ, hψ, map_sub, map_one]
  exact e.toEquiv.sum_comp fun x => χ' x * ψ' (1 - x)

end TauCeti
