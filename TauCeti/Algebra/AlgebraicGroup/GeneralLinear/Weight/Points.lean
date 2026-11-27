/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Points
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus

/-!
# Points and powers of the weight cocharacters of the general linear group

An integer weight `w i` on each coordinate of `GL_N` defines the cocharacter
`TauCeti.GeneralLinear.weightCocharacter w`, `t ↦ diag(t ^ w 0, ..., t ^ w (N - 1))`. This file
reads it through the abstract action `TauCeti.Cocharacter.pointsHom` of a cocharacter on unit
points, and computes its powers: the `m`-th power `t ↦ λ(t ^ m)`
(`BialgHom.powCocharacter`) of the weight cocharacter with weights `w` is the weight cocharacter
with weights `w i * m`.

## Main declarations

* `TauCeti.GeneralLinear.pointsMulEquiv_pointsHom_weightCocharacter`: the cocharacter with weights
  `w` sends a unit `t` to `diag(t ^ w i)`.
* `TauCeti.GeneralLinear.powCocharacter_weightCocharacter`: the `m`-th power of the weight
  cocharacter with weights `w` is the weight cocharacter with weights `w i * m`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {N : ℕ}

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The abstract cocharacter action agrees with the concrete weight cocharacter on points. -/
theorem pointsHom_weightCocharacter (w : Fin N → ℤ) (t : Aˣ) :
    Cocharacter.pointsHom A (weightCocharacter (R := R) w) t =
      weightCocharacterPoints w
        ((MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm t) := by
  rw [Cocharacter.pointsHom_apply, mapDomain_weightCocharacter,
    ← MultiplicativeGroup.pointsMulEquiv_symm_apply]

/-- The cocharacter with weights `w` sends `t` to `diag(t ^ w i)`. -/
theorem pointsMulEquiv_pointsHom_weightCocharacter (w : Fin N → ℤ) (t : Aˣ) :
    pointsMulEquiv N (Cocharacter.pointsHom A (weightCocharacter (R := R) w) t) =
      diagGL (weightDiagonalUnits w t) := by
  rw [pointsHom_weightCocharacter, pointsMulEquiv_weightCocharacterPoints,
    MulEquiv.apply_symm_apply]

end Points

/-- The `m`-th power `t ↦ λ(t ^ m)` of the weight cocharacter with weights `w` is the weight
cocharacter with weights `w i * m`. -/
@[simp]
theorem powCocharacter_weightCocharacter (w : Fin N → ℤ) (m : ℤ) :
    (weightCocharacter (R := R) w).powCocharacter m = weightCocharacter (fun i ↦ w i * m) := by
  -- Both cocharacters send a unit `u` to the diagonal point with entries `u ^ (w i * m)`.
  have hpts : ∀ u : (LaurentPolynomial R)ˣ,
      Cocharacter.pointsHom (LaurentPolynomial R)
          ((weightCocharacter (R := R) w).powCocharacter m) u =
        Cocharacter.pointsHom (LaurentPolynomial R)
          (weightCocharacter (R := R) (fun i ↦ w i * m)) u := by
    intro u
    apply (pointsMulEquiv (R := R) (A := LaurentPolynomial R) N).injective
    rw [BialgHom.pointsHom_powCocharacter, pointsMulEquiv_pointsHom_weightCocharacter,
      pointsMulEquiv_pointsHom_weightCocharacter]
    congr 1
    funext i
    rw [weightDiagonalUnits_apply, weightDiagonalUnits_apply, ← zpow_mul, mul_comm]
  -- A cocharacter is determined by its value at the generic point `T` of `𝔾ₘ`.
  apply Cocharacter.genericPoint_injective
  rw [Cocharacter.genericPoint_eq_pointsHom, Cocharacter.genericPoint_eq_pointsHom]
  exact hpts _

end TauCeti.GeneralLinear
