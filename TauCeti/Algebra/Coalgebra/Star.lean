/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Star coalgebras

A star coalgebra is a coalgebra `A` over a commutative star ring `R`, carrying a
conjugate-linear involution `star`, whose comultiplication is a star map:
`Δ(a*) = Δ(a)*`, where the tensor square carries the star structure `(x ⊗ y)* = x* ⊗ y*`.
Together with a compatible star algebra structure this is the defining condition of a Hopf star
algebra, the algebraic shadow of a compact quantum group.

The counit is then automatically a star map, `ε(a*) = conj (ε a)`: starring the counit law
for `a*` exhibits `a ↦ conj (ε (a*))` as a left counit, and a left counit agrees with the right
counit `ε`.

## Main declarations

* `TauCeti.StarCoalgebra`: the comultiplication commutes with the star operation.
* `Coalgebra.Repr.star`: starring both legs of a representation of `Δ a` represents `Δ (a*)`.
* `TauCeti.StarCoalgebra.counit_star`: the counit of a star coalgebra is a star map.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 1.2.7.
-/

public section

open scoped TensorProduct
open Coalgebra

namespace TauCeti

/-- A star coalgebra: a coalgebra over a commutative star ring, with a conjugate-linear star
operation, whose comultiplication commutes with star, `Δ(a*) = Δ(a)*`. -/
class StarCoalgebra (R A : Type*) [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [CoalgebraStruct R A] : Prop where
  /-- The comultiplication commutes with the star operation. -/
  comul_star (a : A) : comul (R := R) (star a) = star (comul (R := R) a)

attribute [simp] StarCoalgebra.comul_star

end TauCeti

variable {R A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
  [Module R A] [StarModule R A]

/-- Starring both legs of a representation `Δ a = ∑ xᵢ ⊗ yᵢ` gives the representation
`Δ (a*) = ∑ xᵢ* ⊗ yᵢ*`. -/
def Coalgebra.Repr.star [CoalgebraStruct R A] [TauCeti.StarCoalgebra R A] {a : A} {ι : Type*}
    (𝓡 : Coalgebra.Repr R a ι) : Coalgebra.Repr R (Star.star a) ι where
  index := 𝓡.index
  left i := Star.star (𝓡.left i)
  right i := Star.star (𝓡.right i)
  eq := by
    rw [TauCeti.StarCoalgebra.comul_star, ← 𝓡.eq, star_sum]
    simp

section

variable [CoalgebraStruct R A] [TauCeti.StarCoalgebra R A] {a : A} {ι : Type*}
  (𝓡 : Coalgebra.Repr R a ι)

@[simp]
theorem Coalgebra.Repr.star_index : 𝓡.star.index = 𝓡.index := (rfl)

@[simp]
theorem Coalgebra.Repr.star_left (i : ι) : 𝓡.star.left i = Star.star (𝓡.left i) := (rfl)

@[simp]
theorem Coalgebra.Repr.star_right (i : ι) : 𝓡.star.right i = Star.star (𝓡.right i) := (rfl)

end

namespace TauCeti.StarCoalgebra

variable [Coalgebra R A] [StarCoalgebra R A]

/-- The counit of a star coalgebra is a star map: `ε(a*) = conj (ε a)`. -/
@[simp]
theorem counit_star (a : A) : counit (R := R) (star a) = star (counit (R := R) a) := by
  let 𝓡 := ℛ R a
  -- Starring the counit law for `a*` gives `∑ (ε (xᵢ*))* • yᵢ = a` for `Δ a = ∑ xᵢ ⊗ yᵢ`.
  have hl : ∑ i ∈ 𝓡.index, star (counit (R := R) (star (𝓡.left i))) • 𝓡.right i = a := by
    simpa [star_sum, star_smul] using congr(star $(sum_counit_smul 𝓡.star))
  -- The other counit law reads `∑ ε(yᵢ) • xᵢ = a`.
  have hr : ∑ i ∈ 𝓡.index, counit (R := R) (𝓡.right i) • 𝓡.left i = a := by
    simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using
      congr(TensorProduct.rid R A $(sum_tmul_counit_eq 𝓡))
  conv_lhs => rw [← hr]
  conv_rhs => rw [← hl]
  simp [star_sum, mul_comm]

end TauCeti.StarCoalgebra
