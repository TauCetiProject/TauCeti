/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification
-- Proof-only: symmetry of the coefficients of commutative formal group laws and of symmetric
-- polynomials, coefficients of substitutions into two-variable series, and substitution modulo
-- an ideal annihilated by the coefficients.
import TauCeti.RingTheory.FormalGroup.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Defs
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Formal group laws with square-zero coefficients

Write a formal group law over a commutative ring `A` as `F(X, Y) = X + Y + G(X, Y)`. If the
coefficients of `G` pairwise multiply to zero — for instance, if they lie in an ideal of square
zero — then substituting into `G` only sees the linear part `X + Y` of `F`, and associativity of
`F` says exactly that `G` is an additive 2-cocycle:

  `G(X, Y) + G(X + Y, Z) = G(X, Y + Z) + G(Y, Z)`.

When `F` is commutative, `G` is moreover symmetric. Conversely, a polynomial additive 2-cocycle
`f` with no constant term and square-zero coefficients gives the formal group law `X + Y + f`, a
first-order deformation of the additive formal group law, which is commutative when `f` is
symmetric.

This is how the symmetric 2-cocycle lemma computes the indecomposables of the Lazard ring: modulo
the square of its augmentation ideal, the nonlinear part of the universal formal group law has
square-zero coefficients, so they satisfy the symmetric cocycle equations
(`FormalGroup.isSymmetricCocycleCoeff_coeff`) and `TauCeti.IsSymmetricCocycleCoeff.exists_eq_nsmul`
applies to them.

## Main definitions

* `MvPolynomial.IsAddCocycle₂.formalGroup`: the formal group law `X + Y + f(X, Y)` attached to an
  additive 2-cocycle `f` without constant term whose coefficients pairwise multiply to zero.

## Main results

* `FormalGroup.subst_add_subst_eq`: if the coefficients of `G = F - X - Y` pairwise multiply to
  zero, then `G` satisfies the additive 2-cocycle identity.
* `FormalGroup.choose_mul_coeff_eq`: the cocycle identity at the coefficient of `XⁱYʲZᵏ` with
  `i, k ≥ 1`, `(i + j).choose i * a_{i+j,k} = (j + k).choose j * a_{i,j+k}`.
* `FormalGroup.isSymmetricCocycleCoeff_coeff`: for a commutative such `F`, the coefficients of
  the monomials of each total degree `n` satisfy the coefficient equations of a symmetric additive
  2-cocycle of degree `n`.
* `MvPolynomial.IsAddCocycle₂.isComm_formalGroup`: the formal group law `X + Y + f(X, Y)` is
  commutative when `f` is symmetric.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

open MvPowerSeries Finsupp

variable {A : Type*} [CommRing A]

namespace TauCeti

/-- For `F = X + Y + G` with the coefficients of `G` pairwise multiplying to zero,
`F(F(X, Y), Z) = X + Y + Z + G(X, Y) + G(X + Y, Z)`. -/
private theorem subst_subst_left {G : MvPowerSeries (Fin 2) A}
    (hG : ∀ d e, coeff d G * coeff e G = 0) (hG0 : constantCoeff G = 0) :
    (X 0 + X 1 + G).subst ![(X 0 + X 1 + G).subst ![X 0, X 1], X 2] =
      (X 0 + X 1 + X 2 + (G.subst ![X 0, X 1] + G.subst ![X 0 + X 1, X 2]) :
        MvPowerSeries (Fin 3) A) := by
  have h01 : HasSubst ![(X 0 : MvPowerSeries (Fin 3) A), X 1] :=
    hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp
  have hc : constantCoeff (G.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1]) = 0 :=
    constantCoeff_subst_eq_zero h01 (fun s ↦ by fin_cases s <;> simp) hG0
  rw [subst_X_add_X_add_eq hG h01 h01 (by simp) (by simp),
    subst_X_add_X_add_eq hG (u := X 0 + X 1) (v := X 2)
      (hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp [hc])
      (hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp)
      (fun e ↦ by simpa using coeff_subst_mem_span h01 e) (by simp)]
  ring

/-- For `F = X + Y + G` with the coefficients of `G` pairwise multiplying to zero,
`F(X, F(Y, Z)) = X + Y + Z + G(Y, Z) + G(X, Y + Z)`. -/
private theorem subst_subst_right {G : MvPowerSeries (Fin 2) A}
    (hG : ∀ d e, coeff d G * coeff e G = 0) (hG0 : constantCoeff G = 0) :
    (X 0 + X 1 + G).subst ![X 0, (X 0 + X 1 + G).subst ![X 1, X 2]] =
      (X 0 + X 1 + X 2 + (G.subst ![X 1, X 2] + G.subst ![X 0, X 1 + X 2]) :
        MvPowerSeries (Fin 3) A) := by
  have h12 : HasSubst ![(X 1 : MvPowerSeries (Fin 3) A), X 2] :=
    hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp
  have hc : constantCoeff (G.subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2]) = 0 :=
    constantCoeff_subst_eq_zero h12 (fun s ↦ by fin_cases s <;> simp) hG0
  rw [subst_X_add_X_add_eq hG h12 h12 (by simp) (by simp),
    subst_X_add_X_add_eq hG (u := X 0) (v := X 1 + X 2)
      (hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp [hc])
      (hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp)
      (by simp) (fun e ↦ by simpa using coeff_subst_mem_span h12 e)]
  ring

end TauCeti

namespace FormalGroup

/-- **The nonlinear part of a formal group law with square-zero coefficients is an additive
2-cocycle.** If the coefficients of `G = F(X, Y) - X - Y` pairwise multiply to zero, then
`G(X, Y) + G(X + Y, Z) = G(X, Y + Z) + G(Y, Z)`. -/
theorem subst_add_subst_eq (F : FormalGroup A)
    (hF : ∀ d e, coeff d (F.toPowerSeries - (X 0 + X 1)) *
      coeff e (F.toPowerSeries - (X 0 + X 1)) = 0) :
    ((F.toPowerSeries - (X 0 + X 1)).subst ![X 0, X 1] +
        (F.toPowerSeries - (X 0 + X 1)).subst ![X 0 + X 1, X 2] : MvPowerSeries (Fin 3) A) =
      (F.toPowerSeries - (X 0 + X 1)).subst ![X 0, X 1 + X 2] +
        (F.toPowerSeries - (X 0 + X 1)).subst ![X 1, X 2] := by
  have hG0 : constantCoeff (F.toPowerSeries - (X 0 + X 1)) = 0 := by
    simp [F.zero_constantCoeff]
  have h := F.assoc
  rw [← add_sub_cancel (X 0 + X 1) F.toPowerSeries, TauCeti.subst_subst_left hF hG0,
    TauCeti.subst_subst_right hF hG0] at h
  rw [add_comm (subst ![X 0, X 1 + X 2] _)]
  exact add_left_cancel h

/-- The additive 2-cocycle identity for the nonlinear part of a formal group law with
square-zero coefficients, at the coefficient of `XⁱYʲZᵏ` with `i, k ≥ 1`: writing `a_{i,j}` for
the coefficient of `XⁱYʲ`, `(i + j).choose i * a_{i+j,k} = (j + k).choose j * a_{i,j+k}`. -/
theorem choose_mul_coeff_eq (F : FormalGroup A)
    (hF : ∀ d e, coeff d (F.toPowerSeries - (X 0 + X 1)) *
      coeff e (F.toPowerSeries - (X 0 + X 1)) = 0) {i k : ℕ} (hi : i ≠ 0) (hk : k ≠ 0)
    (j : ℕ) :
    ((i + j).choose i : A) * coeff (single 0 (i + j) + single 1 k) F.toPowerSeries =
      (j + k).choose j * coeff (single 0 i + single 1 (j + k)) F.toPowerSeries := by
  have h := congrArg (coeff (single 0 i + single 1 j + single 2 k)) (F.subst_add_subst_eq hF)
  simp only [map_add, coeff_subst_X_add_X_X, coeff_subst_X_X_add_X, coeff_subst_X_zero_X_one,
    coeff_subst_X_one_X_two] at h
  simpa [hi, hk, coeff_X, Finsupp.single_apply, Finsupp.ext_iff, Fin.forall_fin_two] using h

/-- For a commutative formal group law whose nonlinear coefficients pairwise multiply to zero, the
coefficients `bᵢ` of `XⁱYⁿ⁻ⁱ` satisfy the coefficient equations of a symmetric additive 2-cocycle
of degree `n`. -/
theorem isSymmetricCocycleCoeff_coeff (F : FormalGroup A) [F.IsComm]
    (hF : ∀ d e, coeff d (F.toPowerSeries - (X 0 + X 1)) *
      coeff e (F.toPowerSeries - (X 0 + X 1)) = 0) (n : ℕ) :
    TauCeti.IsSymmetricCocycleCoeff n fun i ↦ coeff (single 0 i + single 1 (n - i))
      F.toPowerSeries where
  symm i hi := by rw [Nat.sub_sub_self hi, F.coeff_comm]
  rel i j k hi hj hk hn := by
    rw [nsmul_eq_mul, nsmul_eq_mul, show n - (i + j) = k by omega, show n - i = j + k by omega]
    exact F.choose_mul_coeff_eq hF hi.ne' hk.ne' j

end FormalGroup

namespace MvPolynomial.IsAddCocycle₂

variable {f : MvPolynomial (Fin 2) A}

/-- The power series `X + Y + f(X, Y)` of a polynomial `f` without constant term which is an
additive 2-cocycle has constant coefficient `0` and linear coefficients `1`. -/
private theorem coeff_X_add_X_add_coe (hf : f.IsAddCocycle₂) (h0 : constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 +
        (f : MvPowerSeries (Fin 2) A)) = 0 ∧
      MvPowerSeries.coeff (single 0 1) (MvPowerSeries.X 0 + MvPowerSeries.X 1 +
        (f : MvPowerSeries (Fin 2) A)) = 1 ∧
      MvPowerSeries.coeff (single 1 1) (MvPowerSeries.X 0 + MvPowerSeries.X 1 +
        (f : MvPowerSeries (Fin 2) A)) = 1 := by
  -- The cocycle identity at `X` says that the coefficient of `X` in `f` vanishes.
  have h1 : f.coeff (single 0 1) = 0 := by simpa using hf.coeff_eq 1 0 0
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_add, MvPowerSeries.constantCoeff_X, zero_add]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      ← MvPolynomial.constantCoeff_eq, h0]
  · rw [map_add, map_add, MvPolynomial.coeff_coe, h1]
    simp [MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]
  · rw [map_add, map_add, MvPolynomial.coeff_coe, hf.coeff_single_one_eq_zero one_ne_zero]
    simp [MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]

/-- The formal group law `X + Y + f(X, Y)` attached to an additive 2-cocycle `f` without
constant term whose coefficients pairwise multiply to zero: a first-order deformation of the
additive formal group law. -/
def formalGroup (hf : f.IsAddCocycle₂) (h0 : constantCoeff f = 0)
    (hff : ∀ d e, f.coeff d * f.coeff e = 0) : FormalGroup A where
  toPowerSeries := MvPowerSeries.X 0 + MvPowerSeries.X 1 + (f : MvPowerSeries (Fin 2) A)
  zero_constantCoeff := (coeff_X_add_X_add_coe hf h0).1
  lin_coeff_X := (coeff_X_add_X_add_coe hf h0).2.1
  lin_coeff_Y := (coeff_X_add_X_add_coe hf h0).2.2
  assoc := by
    have hG : ∀ d e, MvPowerSeries.coeff d (f : MvPowerSeries (Fin 2) A) *
        MvPowerSeries.coeff e (f : MvPowerSeries (Fin 2) A) = 0 := by
      simpa [MvPolynomial.coeff_coe] using hff
    have hG0 : MvPowerSeries.constantCoeff (f : MvPowerSeries (Fin 2) A) = 0 := by
      simpa using (coeff_X_add_X_add_coe hf h0).1
    rw [TauCeti.subst_subst_left hG hG0, TauCeti.subst_subst_right hG hG0]
    -- Both sides are polynomials, and the cocycle identity of `f` identifies them.
    simp only [← coe_X, ← coe_add, subst_coe_pair_eq_coe_aeval]
    rw [isAddCocycle₂_iff.1 hf, add_comm (aeval ![X 0, X 1 + X 2] f)]

/-- The underlying power series of `hf.formalGroup h0 hff` is `X + Y + f(X, Y)`. -/
@[simp]
theorem toPowerSeries_formalGroup (hf : f.IsAddCocycle₂) (h0 : constantCoeff f = 0)
    (hff : ∀ d e, f.coeff d * f.coeff e = 0) :
    (hf.formalGroup h0 hff).toPowerSeries =
      MvPowerSeries.X 0 + MvPowerSeries.X 1 + (f : MvPowerSeries (Fin 2) A) :=
  (rfl)

/-- The formal group law `X + Y + f(X, Y)` is commutative when `f` is symmetric. -/
theorem isComm_formalGroup (hf : f.IsAddCocycle₂) (h0 : constantCoeff f = 0)
    (hff : ∀ d e, f.coeff d * f.coeff e = 0) (hs : f.IsSymmetric) :
    (hf.formalGroup h0 hff).IsComm where
  comm := by
    ext d
    have hd : d = single 0 (d 0) + single 1 (d 1) := by ext i; fin_cases i <;> simp
    rw [coeff_subst_X_one_X_zero, toPowerSeries_formalGroup]
    simp only [map_add, MvPolynomial.coeff_coe]
    rw [hs.coeff_single_add_single, ← hd]
    simp only [MvPowerSeries.coeff_X, Finsupp.ext_iff, Fin.forall_fin_two]
    simp [add_comm, and_comm]

end MvPolynomial.IsAddCocycle₂
