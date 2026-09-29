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
`U = TS` give the three-term relation. Both hold with every homogeneous coefficient
polynomial. They are the relations used in a finite Manin-symbol presentation and in
the comparison with period polynomials.

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

private theorem maninSymbol_mul (g h : SL(2, ℤ))
    (P : homogeneousSubmodule (Fin 2) R w) :
    maninSymbol Γ (g * h) P =
      symbol Γ (mapGL ℚ g • (mapGL ℚ h • ∞))
        (mapGL ℚ g • (mapGL ℚ h • (0 : ℚ))) P := by
  rw [maninSymbol_apply, map_mul, mul_smul, mul_smul]

private theorem S_smul_infty : (mapGL ℚ S • (∞ : OnePoint ℚ)) = (0 : ℚ) := by
  simp [OnePoint.smul_infty_eq_ite]

private theorem S_smul_zero : (mapGL ℚ S • ((0 : ℚ) : OnePoint ℚ)) = ∞ := by
  simp [OnePoint.smul_some_eq_ite]

private theorem TS_smul_infty : (mapGL ℚ (T * S) • (∞ : OnePoint ℚ)) = (1 : ℚ) := by
  rw [map_mul, mul_smul]
  simp [OnePoint.smul_infty_eq_ite, OnePoint.smul_some_eq_ite]

private theorem TS_smul_zero : (mapGL ℚ (T * S) • ((0 : ℚ) : OnePoint ℚ)) = ∞ := by
  rw [map_mul, mul_smul]
  simp [OnePoint.smul_infty_eq_ite, OnePoint.smul_some_eq_ite]

private theorem TS_smul_one : (mapGL ℚ (T * S) • ((1 : ℚ) : OnePoint ℚ)) = (0 : ℚ) := by
  rw [map_mul, mul_smul]
  simp [OnePoint.smul_some_eq_ite]

/-- The subgroup relation for Manin symbols. Left multiplication of an edge by an element of
`Γ` can be transferred to the right action on its coefficient polynomial. -/
theorem maninSymbol_mul_of_mem {h : SL(2, ℤ)} (hh : h ∈ Γ) (g : SL(2, ℤ))
    (P : homogeneousSubmodule (Fin 2) R w) :
    maninSymbol Γ (h * g) P =
      maninSymbol Γ g (binaryFormRep R w (op (h : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
  rw [maninSymbol_mul, maninSymbol_apply]
  exact symbol_mapGL_smul Γ hh _ _ P

/-- The two-term Manin relation: right multiplication by `S` reverses the edge. -/
theorem maninSymbol_mul_S (g : SL(2, ℤ)) :
    maninSymbol Γ (g * S) = -(maninSymbol Γ g :
      homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w) := by
  ext P
  rw [maninSymbol_mul, S_smul_infty, S_smul_zero, LinearMap.neg_apply,
    maninSymbol_apply]
  exact congrArg (fun F : homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w ↦ F P)
    (symbol_swap Γ (mapGL ℚ g • ∞) (mapGL ℚ g • (0 : ℚ)))

/-- The three-term Manin relation for the oriented triangle with vertices
`g · ∞`, `g · 1`, and `g · 0`. -/
theorem maninSymbol_add_mul_TS_add_mul_TS_sq (g : SL(2, ℤ)) :
    maninSymbol Γ g + maninSymbol Γ (g * (T * S)) +
      maninSymbol Γ (g * (T * S) ^ 2) =
        (0 : homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R Γ w) := by
  ext P
  simp only [LinearMap.add_apply, LinearMap.zero_apply]
  have hcycle :
      (mapGL ℚ ((T * S) ^ 2) • (∞ : OnePoint ℚ)) = (0 : ℚ) := by
    rw [map_pow, pow_two, mul_smul, TS_smul_infty, TS_smul_one]
  have hcycle' :
      (mapGL ℚ ((T * S) ^ 2) • ((0 : ℚ) : OnePoint ℚ)) = (1 : ℚ) := by
    rw [map_pow, pow_two, mul_smul, TS_smul_zero, TS_smul_infty]
  rw [maninSymbol_apply, maninSymbol_mul, maninSymbol_mul,
    TS_smul_infty, TS_smul_zero, hcycle, hcycle']
  calc
    _ = (symbol Γ (mapGL ℚ g • ∞) (mapGL ℚ g • (0 : ℚ)) P +
          symbol Γ (mapGL ℚ g • (0 : ℚ)) (mapGL ℚ g • (1 : ℚ)) P) +
          symbol Γ (mapGL ℚ g • (1 : ℚ)) (mapGL ℚ g • ∞) P := by abel
    _ = symbol Γ (mapGL ℚ g • ∞) (mapGL ℚ g • (1 : ℚ)) P +
          symbol Γ (mapGL ℚ g • (1 : ℚ)) (mapGL ℚ g • ∞) P := by
      rw [← LinearMap.add_apply, symbol_add_symbol]
    _ = 0 := by rw [← LinearMap.add_apply, symbol_add_symbol, symbol_self]; simp

/-- Manin symbols span the modular-symbol module: every degree-zero divisor is a sum of
unimodular edges, before passing to the coinvariants. -/
theorem span_maninSymbol_eq_top :
    Submodule.span R
      (Set.range fun x : SL(2, ℤ) × homogeneousSubmodule (Fin 2) R w ↦
        maninSymbol Γ x.1 x.2) = ⊤ := by
  refine eq_top_iff.2 ((span_mk_degreeZeroRep_tmul_eq_top Γ).symm.le.trans
    (Submodule.span_mono ?_))
  rintro _ ⟨_, ⟨g, rfl⟩, P, -, rfl⟩
  refine ⟨(g, P), ?_⟩
  dsimp only
  rw [maninSymbol_apply, symbol_apply]
  congr 2
  ext1
  simp

end TauCeti.ModularSymbols
