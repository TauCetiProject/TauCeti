/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic

/-!
# Manin symbols and the modular relations

A Manin symbol is the modular symbol on the oriented edge from `g · ∞` to `g · 0`,
for `g ∈ SL₂(ℤ)`. These edges generate the modular-symbol module. Reversing an edge
by `S` gives the two-term relation, and the three edges of the triangle permuted by
`U = TS` give the three-term relation. These and invariance under `-1` hold with every
homogeneous coefficient polynomial. They are the relations used in a finite Manin-symbol
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
      (degreeZeroRep R g
        ⟨_, single_sub_single_mem_degreeZero ∞ ((0 : ℚ) : OnePoint ℚ)⟩ ⊗ₜ[R] P) := by
  rw [maninSymbol_apply, symbol_apply, degreeZeroRep_apply,
    degreeZeroGLRep_single_sub_single]

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
  rw [maninSymbol_mul, mapGL_S_smul_infty, mapGL_S_smul_zero, LinearMap.neg_apply,
    maninSymbol_apply]
  exact LinearMap.congr_fun (symbol_swap Γ (mapGL ℚ g • ∞) (mapGL ℚ g • (0 : ℚ))) P

/-- The Manin symbol is unchanged when its matrix is multiplied by the central element `-1`. -/
@[simp]
theorem maninSymbol_neg (g : SL(2, ℤ)) :
    maninSymbol Γ (-g) = (maninSymbol Γ g :
      homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w) := by
  have hS : S * S = (-1 : SL(2, ℤ)) := by
    apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_mul, coe_neg, Matrix.SpecialLinearGroup.coe_one]
      using S_mul_S_eq
  have hg : -g = g * S * S := by rw [mul_assoc, hS]; simp
  rw [hg, maninSymbol_mul_S, maninSymbol_mul_S, neg_neg]

/-- The three-term Manin relation for the oriented triangle with vertices
`g · ∞`, `g · 1`, and `g · 0`. -/
theorem maninSymbol_add_mul_T_mul_S_add_mul_T_mul_S_sq (g : SL(2, ℤ)) :
    maninSymbol Γ g + maninSymbol Γ (g * (T * S)) +
      maninSymbol Γ (g * (T * S) ^ 2) =
        (0 : homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w) := by
  ext P
  simp only [LinearMap.add_apply, LinearMap.zero_apply]
  rw [maninSymbol_apply, maninSymbol_mul, maninSymbol_mul, map_pow, map_mul,
    mapGL_T_mul_S_smul_infty, mapGL_T_mul_S_smul_zero,
    mapGL_T_mul_S_sq_smul_infty, mapGL_T_mul_S_sq_smul_zero]
  calc
    _ = (symbol Γ (mapGL ℚ g • ∞) (mapGL ℚ g • (0 : ℚ)) P +
          symbol Γ (mapGL ℚ g • (0 : ℚ)) (mapGL ℚ g • (1 : ℚ)) P) +
          symbol Γ (mapGL ℚ g • (1 : ℚ)) (mapGL ℚ g • ∞) P := by abel
    _ = symbol Γ (mapGL ℚ g • ∞) (mapGL ℚ g • (1 : ℚ)) P +
          symbol Γ (mapGL ℚ g • (1 : ℚ)) (mapGL ℚ g • ∞) P := by
      rw [← LinearMap.add_apply, symbol_add_symbol]
    _ = 0 := by rw [← LinearMap.add_apply, symbol_add_symbol, symbol_self]; simp

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
