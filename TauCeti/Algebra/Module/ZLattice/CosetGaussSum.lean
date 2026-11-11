/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.GaussSum

/-!
# Gauss sums over translates of an even lattice

For an even lattice `L`, and `γ, m ∈ L^∨`, this file constructs the finite sum

`∑_{y ∈ L/cL} exp (2πi (a ‖γ + y‖² / 2 + ⟪γ + y, m⟫) / c)`.

The quotient is parametrized by `L/cL`, not by a choice of representatives in the affine
coset. Expanding the square identifies the sum with a constant phase times the existing
twisted Gauss sum with twisting vector `a • γ + m`. In particular, when the level divides
`c`, it vanishes unless `a • γ + m ∈ L`. This is the finite-algebra input to splitting a
coset theta series under a modular substitution; the surviving dual vectors lie in the
class `-a • γ`, rather than in the zero class.

Both the summand and the sum are independent of the representative of `γ` modulo `L`,
the former after translating its quotient argument. Completing the square evaluates the
surviving sum in terms of the untwisted Gauss sum.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
* W. Ebeling, *Lattices and Codes*, Chapter 3.
-/

public section

open Complex Submodule
open scoped Pointwise Real RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (L : Submodule ℤ E)

/-- The Gauss summand over `γ + L`, indexed by `L/cL`. The offset and twisting vector
belong to the dual lattice; evenness and these memberships ensure descent to the quotient. -/
noncomputable def cosetGaussTerm (hL : IsEven L) (a : ℤ) (c : ℕ) (γ m : dual L)
    (y : L ⧸ ((c : ℝ) • L).submoduleOf L) : ℂ :=
  cexp (2 * π * I * (((a * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
    gaussTerm L hL a c (a • γ + m) y

/-- The Gauss sum over the translate `γ + L`, with twisting vector `m ∈ L^∨`. -/
noncomputable def cosetGaussSum (hL : IsEven L) (a : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (γ m : dual L) : ℂ :=
  ∑ y, cosetGaussTerm L hL a c γ m y

variable {L} (hL : IsEven L)

theorem cosetGaussSum_def (a : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (γ m : dual L) :
    cosetGaussSum L hL a c γ m = ∑ y, cosetGaussTerm L hL a c γ m y :=
  (rfl)

/-- On a representative `v ∈ L`, the coset Gauss summand is
`exp (2πi (a ‖γ + v‖² / 2 + ⟪γ + v, m⟫) / c)`. -/
@[simp]
theorem cosetGaussTerm_mk (a : ℤ) (c : ℕ) (γ m : dual L) (v : L) :
    cosetGaussTerm L hL a c γ m (Submodule.Quotient.mk v) =
      cexp (2 * π * I *
        (((a * ‖(γ : E) + v‖ ^ 2 / 2 + ⟪(γ : E) + v, (m : E)⟫) / c : ℝ) : ℂ)) := by
  rw [cosetGaussTerm, gaussTerm_mk, ← exp_add]
  congr 1
  simp only [coe_add, Submodule.coe_smul, inner_add_right, ← Int.cast_smul_eq_zsmul ℝ,
    inner_smul_right, inner_add_left, norm_add_sq_real, real_inner_comm (v : E) (γ : E)]
  push_cast
  ring

/-- At the zero offset the summand is the existing twisted Gauss summand. -/
@[simp]
theorem cosetGaussTerm_zero (a : ℤ) (c : ℕ) (m : dual L)
    (y : L ⧸ ((c : ℝ) • L).submoduleOf L) :
    cosetGaussTerm L hL a c 0 m y = gaussTerm L hL a c m y := by
  simp [cosetGaussTerm]

/-- Changing the representative of the offset translates the quotient argument. -/
theorem cosetGaussTerm_eq_of_sub_mem (a : ℤ) (c : ℕ) (γ γ' m : dual L)
    (h : (γ' : E) - γ ∈ L) (y : L ⧸ ((c : ℝ) • L).submoduleOf L) :
    cosetGaussTerm L hL a c γ' m y =
      cosetGaussTerm L hL a c γ m (y + Submodule.Quotient.mk ⟨(γ' : E) - γ, h⟩) := by
  induction y using Submodule.Quotient.induction_on with | H v
  rw [← Submodule.Quotient.mk_add, cosetGaussTerm_mk, cosetGaussTerm_mk]
  have heq : (γ' : E) + v = (γ : E) + ((v : E) + ((γ' : E) - γ)) := by abel
  simp only [coe_add, heq]

/-- Expanding the square reduces a coset Gauss sum to a twisted Gauss sum on `L`.
The new twisting vector is `a • γ + m`. -/
theorem cosetGaussSum_eq_mul (a : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (γ m : dual L) :
    cosetGaussSum L hL a c γ m =
      cexp (2 * π * I * (((a * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
        gaussSumTwisted L hL a c (a • γ + m) := by
  simp only [cosetGaussSum, cosetGaussTerm, gaussSumTwisted_def, Finset.mul_sum]

/-- At the zero offset the coset Gauss sum is the twisted Gauss sum. -/
@[simp]
theorem cosetGaussSum_zero (a : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (m : dual L) :
    cosetGaussSum L hL a c 0 m = gaussSumTwisted L hL a c m := by
  simp [cosetGaussSum, gaussSumTwisted_def]

/-- The sum over a coset is independent of its representative modulo `L`. -/
theorem cosetGaussSum_eq_of_sub_mem (a : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (γ γ' m : dual L)
    (h : (γ' : E) - γ ∈ L) :
    cosetGaussSum L hL a c γ' m = cosetGaussSum L hL a c γ m := by
  simp only [cosetGaussSum, cosetGaussTerm_eq_of_sub_mem hL a c γ γ' m h]
  exact Equiv.sum_comp (Equiv.addRight (Submodule.Quotient.mk (⟨(γ' : E) - γ, h⟩ : L))) _

/-- If the level divides `c`, the coset Gauss sum vanishes unless the twisting vector
`m` lies in the class `-a • γ` modulo `L`. -/
theorem cosetGaussSum_eq_zero [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]
    (a : ℤ) {c : ℕ} [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)]
    (hc : level L ∣ c) (γ m : dual L) (hm : ((a • γ + m : dual L) : E) ∉ L) :
    cosetGaussSum L hL a c γ m = 0 := by
  rw [cosetGaussSum_eq_mul, gaussSumTwisted_eq_zero hL a hc hm, mul_zero]

/-- For `a ≡ 1` modulo the level, the surviving twisting vectors lie in the class `-γ`.
This is the support condition for a principal-congruence modular substitution. -/
theorem cosetGaussSum_eq_zero_of_modEq [FiniteDimensional ℝ E] [DiscreteTopology L]
    [IsZLattice ℝ L] {a : ℤ} {c : ℕ}
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)]
    (ha : a ≡ 1 [ZMOD level L]) (hc : level L ∣ c) (γ m : dual L)
    (hm : ((γ + m : dual L) : E) ∉ L) :
    cosetGaussSum L hL a c γ m = 0 := by
  apply cosetGaussSum_eq_zero hL a hc γ m
  intro hmem
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp ha.symm
  have hN : (level L : ℤ) • (γ : E) ∈ L := by
    simpa only [natCast_zsmul] using level_nsmul_mem γ.2
  have heq : ((γ + m : dual L) : E) =
      ((a • γ + m : dual L) : E) - t • ((level L : ℤ) • (γ : E)) := by
    simp only [coe_add, Submodule.coe_smul, ht]
    module
  apply hm
  rw [heq]
  exact L.sub_mem hmem (L.smul_mem t hN)

/-- Completing the square evaluates the coset Gauss sum when `a d ≡ 1 (mod c)` and
`a • γ + m ∈ L`. No level hypothesis is needed for this identity. -/
theorem cosetGaussSum_eq_of_mem {a d : ℤ} {c : ℕ}
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (had : a * d ≡ 1 [ZMOD c])
    (γ m : dual L) (hm : ((a • γ + m : dual L) : E) ∈ L) :
    cosetGaussSum L hL a c γ m =
      cexp (2 * π * I *
        ((((a * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c -
          a * d ^ 2 * ‖((a • γ + m : dual L) : E)‖ ^ 2 / (2 * c) : ℝ)) : ℂ)) *
        gaussSum L hL a c := by
  rw [cosetGaussSum_eq_mul, gaussSumTwisted_eq_of_mem hL had hm, ← mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

end ZLattice
