/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic

/-!
# Manin symbols and the modular relations

The unimodular divisor of `g ∈ SL₂(ℤ)` is the divisor `{g · 0} - {g · ∞}` of the oriented path
from `g · ∞` to `g · 0`. Right multiplication by `S` reverses this path, and the three paths
permuted by `U = TS` around an ideal triangle sum to zero: these are the two-term and three-term
Manin relations, here proved among the degree-zero divisors themselves. The unimodular divisors
span the degree-zero divisors by Manin's lemma, so an additive map on them is determined by its
values on the unimodular divisors.

A Manin symbol is the modular symbol on the oriented edge from `g · ∞` to `g · 0`,
for `g ∈ SL₂(ℤ)`. These edges generate the modular-symbol module. Reversing an edge
by `S` gives the two-term relation, and the three edges of the triangle permuted by
`U = TS` give the three-term relation. These and invariance under `-1` hold with every
homogeneous coefficient polynomial, and follow from the same relations among unimodular
divisors. They are the relations used in a finite Manin-symbol
presentation and in the comparison with period polynomials.

## References

* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, 1972.
* W. Stein, *Modular Forms: A Computational Approach*, §8.2.
-/

public noncomputable section

open Matrix.SpecialLinearGroup ModularGroup OnePoint MvPolynomial Representation TensorProduct
  MulOpposite
open scoped MatrixGroups

namespace TauCeti.ModularSymbols

/-! ### Unimodular divisors -/

section UnimodularDivisor

variable (R : Type*) [Ring R]

/-- The unimodular divisor `{g 0} - {g ∞}` of `g ∈ SL(2, ℤ)`: the divisor of the path from
`g ∞` to `g 0`, the translate by `g` of the path from `∞` to `0`. -/
def unimodularDivisor (g : SL(2, ℤ)) : degreeZero R :=
  divisor R (mapGL ℚ g • ∞) (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ))

variable {R}

/-- The unimodular divisor of `g` is the divisor of the path from `g ∞` to `g 0`. -/
theorem unimodularDivisor_def (g : SL(2, ℤ)) :
    unimodularDivisor R g =
      divisor R (mapGL ℚ g • ∞) (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ)) :=
  (rfl)

/-- `SL(2, ℤ)` permutes the unimodular divisors by left multiplication. -/
@[simp]
theorem degreeZeroGLRep_mapGL_unimodularDivisor (h g : SL(2, ℤ)) :
    degreeZeroGLRep R (mapGL ℚ h) (unimodularDivisor R g) = unimodularDivisor R (h * g) := by
  simp [unimodularDivisor_def, mul_smul]

/-- The two-term Manin relation: right multiplication by `S` reverses the path. -/
@[simp]
theorem unimodularDivisor_mul_S (g : SL(2, ℤ)) :
    unimodularDivisor R (g * S) = -unimodularDivisor R g := by
  simp [unimodularDivisor_def, mul_smul]

/-- The unimodular divisor is unchanged when its matrix is multiplied by the central element
`-1`. -/
@[simp]
theorem unimodularDivisor_neg (g : SL(2, ℤ)) :
    unimodularDivisor R (-g) = unimodularDivisor R g := by
  have hg : -g = g * S * S := by rw [mul_assoc, S_mul_S_eq, mul_neg_one]
  rw [hg, unimodularDivisor_mul_S, unimodularDivisor_mul_S, neg_neg]

/-- The three-term Manin relation: the paths `g ∞ → g 0`, `g 0 → g 1` and `g 1 → g ∞` around
the ideal triangle with vertices `g 0`, `g 1`, `g ∞` sum to zero. The element `T * S` cycles the
vertices `0`, `1`, `∞` of the base triangle, and its conjugate `g * (T * S) * g⁻¹` cycles the
vertices of the translated triangle. -/
theorem unimodularDivisor_add_mul_T_mul_S_add_mul_T_mul_S_sq (g : SL(2, ℤ)) :
    unimodularDivisor R g + unimodularDivisor R (g * (T * S)) +
      unimodularDivisor R (g * (T * S) ^ 2) = 0 := by
  simp only [unimodularDivisor_def, map_mul, map_pow, mul_smul (mapGL ℚ g),
    mapGL_T_mul_S_smul_infty, mapGL_T_mul_S_smul_zero, mapGL_T_mul_S_sq_smul_infty,
    mapGL_T_mul_S_sq_smul_zero]
  rw [add_right_comm, divisor_add_divisor, divisor_add_divisor, divisor_self]

/-- An additive map on the integral degree-zero divisors is determined by its values on the
unimodular divisors `{g 0} - {g ∞}`, which span by Manin's lemma. -/
theorem addMonoidHom_ext_unimodular {V : Type*} [AddCommGroup V] {φ ψ : degreeZero ℤ →+ V}
    (h : ∀ g : SL(2, ℤ), φ (unimodularDivisor ℤ g) = ψ (unimodularDivisor ℤ g)) : φ = ψ := by
  refine AddMonoidHom.toIntLinearMap_injective
    (LinearMap.ext_on_range span_degreeZeroRep_eq_top fun g ↦ ?_)
  -- The translate `g ({∞} - {0})` is the reversed unimodular divisor of `g`.
  have hg : degreeZeroRep ℤ g (divisor ℤ ((0 : ℚ) : OnePoint ℚ) ∞) = -unimodularDivisor ℤ g := by
    rw [degreeZeroRep_apply, degreeZeroGLRep_divisor, unimodularDivisor_def, neg_divisor]
  simp only [AddMonoidHom.coe_toIntLinearMap, hg, map_neg, h g]

end UnimodularDivisor

/-! ### Manin symbols -/

variable {R : Type*} [CommRing R] (Γ : Subgroup SL(2, ℤ)) {w : ℕ}

/-- The Manin symbol represented by the oriented unimodular edge `g · ∞ → g · 0`,
linear in the homogeneous coefficient polynomial. -/
def maninSymbol (g : SL(2, ℤ)) :
    homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w :=
  symbol Γ (mapGL ℚ g • ∞) (mapGL ℚ g • (0 : ℚ))

@[simp]
theorem maninSymbol_apply (g : SL(2, ℤ))
    (P : homogeneousSubmodule (Fin 2) R w) :
    maninSymbol Γ g P = symbol Γ (mapGL ℚ g • ∞) (mapGL ℚ g • (0 : ℚ)) P :=
  by unfold maninSymbol; rfl

/-- A Manin symbol is the coinvariant class of the translate of `[∞] - [0]` tensored with
its coefficient polynomial. -/
theorem maninSymbol_eq_mk (g : SL(2, ℤ))
    (P : homogeneousSubmodule (Fin 2) R w) :
    maninSymbol Γ g P = Coinvariants.mk _
      (degreeZeroRep R g (divisor R ((0 : ℚ) : OnePoint ℚ) ∞) ⊗ₜ[R] P) := by
  rw [maninSymbol_apply, symbol_apply, degreeZeroRep_apply, degreeZeroGLRep_divisor]

/-- A Manin symbol is the image of the reversed unimodular divisor under the linear map
`D ↦ [D ⊗ P]` into the coinvariants, so the relations among unimodular divisors give relations
among Manin symbols. -/
theorem maninSymbol_eq_mk_neg_unimodularDivisor (g : SL(2, ℤ))
    (P : homogeneousSubmodule (Fin 2) R w) :
    maninSymbol Γ g P =
      (Coinvariants.mk _ ∘ₗ (TensorProduct.mk R _ _).flip P) (-unimodularDivisor R g) := by
  rw [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, maninSymbol_apply,
    symbol_apply, unimodularDivisor_def, neg_divisor]

private theorem maninSymbol_mul (g h : SL(2, ℤ))
    (P : homogeneousSubmodule (Fin 2) R w) :
    maninSymbol Γ (g * h) P =
      symbol Γ (mapGL ℚ g • (mapGL ℚ h • ∞))
        (mapGL ℚ g • (mapGL ℚ h • (0 : ℚ))) P := by
  rw [maninSymbol_apply, map_mul, mul_smul, mul_smul]

/-- The subgroup relation for Manin symbols. Left multiplication of an edge by an element of
`Γ` can be transferred to the right action on its coefficient polynomial. -/
theorem maninSymbol_mul_of_mem {h : SL(2, ℤ)} (hh : h ∈ Γ) (g : SL(2, ℤ))
    (P : homogeneousSubmodule (Fin 2) R w) :
    maninSymbol Γ (h * g) P =
      maninSymbol Γ g (binaryFormRep R w (op (h : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
  rw [maninSymbol_mul, maninSymbol_apply]
  exact symbol_mapGL_smul Γ hh _ _ P

/-- The two-term Manin relation: right multiplication by `S` reverses the edge. -/
@[simp]
theorem maninSymbol_mul_S (g : SL(2, ℤ)) :
    maninSymbol Γ (g * S) = -(maninSymbol Γ g :
      homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w) := by
  ext P
  rw [LinearMap.neg_apply, maninSymbol_eq_mk_neg_unimodularDivisor,
    maninSymbol_eq_mk_neg_unimodularDivisor, unimodularDivisor_mul_S, map_neg]

/-- The Manin symbol is unchanged when its matrix is multiplied by the central element `-1`. -/
@[simp]
theorem maninSymbol_neg (g : SL(2, ℤ)) :
    maninSymbol Γ (-g) = (maninSymbol Γ g :
      homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w) := by
  ext P
  rw [maninSymbol_eq_mk_neg_unimodularDivisor, maninSymbol_eq_mk_neg_unimodularDivisor,
    unimodularDivisor_neg]

/-- The three-term Manin relation for the oriented triangle with vertices
`g · ∞`, `g · 1`, and `g · 0`. -/
theorem maninSymbol_add_mul_T_mul_S_add_mul_T_mul_S_sq (g : SL(2, ℤ)) :
    maninSymbol Γ g + maninSymbol Γ (g * (T * S)) +
      maninSymbol Γ (g * (T * S) ^ 2) =
        (0 : homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w) := by
  ext P
  simp only [LinearMap.add_apply, LinearMap.zero_apply, maninSymbol_eq_mk_neg_unimodularDivisor,
    ← map_add, ← neg_add, unimodularDivisor_add_mul_T_mul_S_add_mul_T_mul_S_sq, neg_zero, map_zero]

/-- The Manin symbols `maninSymbol Γ g P`, for `g ∈ SL(2, ℤ)` and homogeneous binary forms
`P` of degree `w`, span `𝕄_w(Γ; R)`. -/
theorem span_maninSymbol_eq_top :
    Submodule.span R
      (Set.range fun x : SL(2, ℤ) × homogeneousSubmodule (Fin 2) R w ↦
        maninSymbol Γ x.1 x.2) = ⊤ := by
  refine eq_top_iff.2 ((span_mk_degreeZeroRep_tmul_eq_top Γ).symm.le.trans
    (Submodule.span_mono ?_))
  rintro _ ⟨_, ⟨g, rfl⟩, P, -, rfl⟩
  exact ⟨(g, P), maninSymbol_eq_mk Γ g P⟩

end TauCeti.ModularSymbols
