/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification
-- Proof-only: symmetry of the coefficients of commutative formal group laws and of symmetric
-- polynomials, coefficients of substitutions into two-variable series, and substitution modulo
-- an ideal annihilated by the coefficients.
import TauCeti.RingTheory.FormalGroup.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Defs
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Ideal
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

* `FormalGroup.assocDefect_add_eq`: first-order expansion of the associativity defect of
  `F + Δ` when `Δ` has coefficients in a square-zero ideal.
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

namespace FormalGroup

/-- First-order expansion of `(F + Δ)((F + Δ)(X₀, X₁), X₂) - (F + Δ)(X₀, (F + Δ)(X₁, X₂))` when `Δ`
has coefficients in a square-zero ideal `I`. -/
theorem assocDefect_add_eq {I : Ideal A} (hI : I * I = ⊥) (F : FormalGroup A)
    (Δ : MvPowerSeries (Fin 2) A) (hΔI : ∀ d, coeff d Δ ∈ I) :
    let S := F.toPowerSeries + Δ
    let F₀₁ := F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1]
    let F₁₂ := F.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2]
    S.subst ![S.subst ![X 0, X 1], X 2] - S.subst ![X 0, S.subst ![X 1, X 2]] =
      Δ.subst ![X 0, X 1] * (pderiv 0 F.toPowerSeries).subst ![F₀₁, X 2] + Δ.subst ![F₀₁, X 2] -
        Δ.subst ![X 0, F₁₂] -
        Δ.subst ![X 1, X 2] * (pderiv 1 F.toPowerSeries).subst ![X 0, F₁₂] := by
  intro S F₀₁ F₁₂
  have haL : HasSubst ![F₀₁, X 2] := .cons_subst_zero_left 0 1 2 F.zero_constantCoeff
  have haR : HasSubst ![X 0, F₁₂] := .cons_subst_zero_right 0 1 2 F.zero_constantCoeff
  set δL : Fin 2 → MvPowerSeries (Fin 3) A := ![Δ.subst ![X 0, X 1], 0]
  set δR : Fin 2 → MvPowerSeries (Fin 3) A := ![0, Δ.subst ![X 1, X 2]]
  have hδLI : ∀ s d, coeff d (δL s) ∈ I
    | 0, d => coeff_subst_mem_of_coeff_mem .X_X hΔI d
    | 1, _ => by simp [δL]
  have hδRI : ∀ s d, coeff d (δR s) ∈ I
    | 0, _ => by simp [δR]
    | 1, d => coeff_subst_mem_of_coeff_mem .X_X hΔI d
  have hhL i j := mul_eq_zero_of_coeff_mem hI (hδLI i) (hδLI j)
  have hhR i j := mul_eq_zero_of_coeff_mem hI (hδRI i) (hδRI j)
  have heqL : (![S.subst ![X 0, X 1], X 2] : Fin 2 → MvPowerSeries (Fin 3) A) =
      ![F₀₁, X 2] + δL := by
    dsimp only [S, F₀₁, δL]; rw [subst_add .X_X, Matrix.vec2_add, _root_.add_zero]
  have heqR : (![X 0, S.subst ![X 1, X 2]] : Fin 2 → MvPowerSeries (Fin 3) A) =
      ![X 0, F₁₂] + δR := by
    dsimp only [S, F₁₂, δR]; rw [subst_add .X_X, Matrix.vec2_add, _root_.add_zero]
  rw [heqL, heqR, subst_add (haL.add (.of_sq_eq_zero fun i ↦ by rw [sq, hhL])),
    subst_add (haR.add (.of_sq_eq_zero fun i ↦ by rw [sq, hhR])),
    subst_add_of_mul_eq_zero haL hhL F.toPowerSeries,
    subst_add_eq_of_coeff_mem hI haL hδLI hΔI,
    subst_add_of_mul_eq_zero haR hhR F.toPowerSeries,
    subst_add_eq_of_coeff_mem hI haR hδRI hΔI, Fin.sum_univ_two, Fin.sum_univ_two, ← F.assoc]
  simp only [δL, δR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zero_mul, _root_.add_zero]
  ring

/-- Specialization of `FormalGroup.assocDefect_add_eq` to `F := 𝔾ₐ` when the coefficients of `G`
pairwise multiply to zero, taking the ideal spanned by the coefficients of `G`. -/
private theorem assocDefect_add_𝔾ₐ_eq {G : MvPowerSeries (Fin 2) A}
    (hG : ∀ d e, coeff d G * coeff e G = 0) :
    (X 0 + X 1 + G).subst ![(X 0 + X 1 + G).subst ![X 0, X 1], X 2] -
        (X 0 + X 1 + G).subst ![X 0, (X 0 + X 1 + G).subst ![X 1, X 2]] =
      (G.subst ![X 0, X 1] + G.subst ![X 0 + X 1, X 2] - G.subst ![X 0, X 1 + X 2] -
        G.subst ![X 1, X 2] : MvPowerSeries (Fin 3) A) := by
  have hI : Ideal.span (Set.range fun d ↦ coeff d G) *
      Ideal.span (Set.range fun d ↦ coeff d G) = ⊥ := by
    rw [Ideal.span_mul_span, Ideal.span_eq_bot]
    rintro _ ⟨_, ⟨d, rfl⟩, _, ⟨e, rfl⟩, rfl⟩
    exact hG d e
  have h := assocDefect_add_eq hI (𝔾ₐ : FormalGroup A) G fun d ↦ Ideal.subset_span ⟨d, rfl⟩
  dsimp only at h
  have h01 : (𝔾ₐ : FormalGroup A).toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1] =
      X 0 + X 1 := by
    rw [𝔾ₐ_toPowerSeries, subst_add .X_X, subst_X .X_X, subst_X .X_X]; rfl
  have h12 : (𝔾ₐ : FormalGroup A).toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) A), X 2] =
      X 1 + X 2 := by
    rw [𝔾ₐ_toPowerSeries, subst_add .X_X, subst_X .X_X, subst_X .X_X]; rfl
  have hp0 : pderiv 0 (𝔾ₐ : FormalGroup A).toPowerSeries = 1 := by
    rw [𝔾ₐ_toPowerSeries]; simp
  have hp1 : pderiv 1 (𝔾ₐ : FormalGroup A).toPowerSeries = 1 := by
    rw [𝔾ₐ_toPowerSeries]; simp
  have hs0 : (1 : MvPowerSeries (Fin 2) A).subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) A), X 2] =
      1 := by
    rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp),
      map_one]
  have hs1 : (1 : MvPowerSeries (Fin 2) A).subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1 + X 2] =
      1 := by
    rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp),
      map_one]
  rw [h01, h12, hp0, hp1, 𝔾ₐ_toPowerSeries] at h
  rw [hs0, hs1, mul_one, mul_one] at h
  exact h

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
  have h := assocDefect_add_𝔾ₐ_eq hF
  rw [add_sub_cancel, F.assoc, sub_self, sub_sub, eq_comm, sub_eq_zero] at h
  exact h

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
    have hk' : n - (i + j) = k := by omega
    have hjk : n - i = j + k := by omega
    rw [nsmul_eq_mul, nsmul_eq_mul, hk', hjk]
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
    have hcoc : ((f : MvPowerSeries (Fin 2) A).subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] +
        (f : MvPowerSeries (Fin 2) A).subst
          ![MvPowerSeries.X 0 + MvPowerSeries.X 1, MvPowerSeries.X 2] :
          MvPowerSeries (Fin 3) A) =
        (f : MvPowerSeries (Fin 2) A).subst
          ![MvPowerSeries.X 0, MvPowerSeries.X 1 + MvPowerSeries.X 2] +
        (f : MvPowerSeries (Fin 2) A).subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] := by
      simp only [← coe_X, ← coe_add, subst_coe_pair_eq_coe_aeval]
      rw [isAddCocycle₂_iff.1 hf, add_comm (aeval ![X 0, X 1 + X 2] f)]
    have h := FormalGroup.assocDefect_add_𝔾ₐ_eq hG
    rw [hcoc, add_sub_cancel_left, sub_self] at h
    exact sub_eq_zero.mp h

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
