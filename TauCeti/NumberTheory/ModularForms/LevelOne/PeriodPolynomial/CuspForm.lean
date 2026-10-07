/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Basic
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Map
import TauCeti.NumberTheory.Modular.Relations
import TauCeti.NumberTheory.ModularForms.ModularSymbols.Manin
import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Injective

/-!
# The period polynomial of a level-one cusp form

Let `f` be a cusp form of weight `k = w + 2` on `SL(2, ℤ)`. Its **period polynomial** is the
binary form of degree `w`

`r_f(X, Y) = ∫₀^{i∞} f(τ) (X - τY)ʷ dτ`,

whose coefficients are, up to binomial coefficients and signs, the periods
`∫₀^{i∞} f(τ) τʲ dτ`, `0 ≤ j ≤ w`. Here it is built from the period map on modular symbols of
level one: the functional `P ↦ ∫₀^{i∞} f(τ) P(τ, 1) dτ` on binary forms is the period map of `f`
evaluated on the symbols `{∞, 0} ⊗ P`, and `r_f` is the binary form attached to this functional
by `TauCeti.binaryFormDual`.

The relations among modular symbols become relations among period polynomials. Since the period
map of `f` sends the symbol `{g∞, g0} ⊗ P` to the period of `P ∣ g`, the two-term and three-term
Manin relations say that `r_f` is killed by `1 + S` and by `1 + U + U²`: the period polynomial lies
in the period-polynomial space `W_w`. Since the symbols `{g∞, g0} ⊗ P` span the modular symbols,
`r_f` determines all the periods of `f`, so the injectivity of the period map makes `f ↦ r_f`
injective. This is the map `S_k(SL(2, ℤ)) → W_w` of the Eichler–Shimura theory, and
`TauCeti.periodPolynomial` is stated with codomain `W_w`. Its even and odd
parts, together with the dimension count `dim W_w = dim M_k + dim S_k` of
`TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Finrank`, are what compare `W_w` with
the spaces of modular forms in the period-polynomial approach to the Eichler–Selberg trace
formula.

## Main definitions

* `TauCeti.periodPolynomial hk`: the `ℂ`-linear map `f ↦ r_f` from cusp forms of weight
  `k = w + 2` on `SL(2, ℤ)` to the period-polynomial space `W_w`.

## Main results

* `TauCeti.eval_periodPolynomial`: `r_f(x, y) = ∫₀^{i∞} f(τ) (x - τy)ʷ dτ`.
* `TauCeti.periodPolynomial_injective`: `f ↦ r_f` is injective.

## References

* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular Forms*
  (R. A. Rankin, ed.), Ellis Horwood, 1984, 197–249, §1.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2.
* Y. I. Manin, *Periods of parabolic forms and p-adic Hecke series*, Mat. Sb. **92** (1973),
  378–401, §1.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup MulOpposite MvPolynomial ModularGroup OnePoint
  TauCeti.ModularSymbols
open scoped MatrixGroups

namespace TauCeti

variable {k : ℤ} {w : ℕ}

/-- A level-one cusp form, viewed as a cusp form for the image of `⊤ : Subgroup SL(2, ℤ)`, the
group for which `TauCeti.ModularSymbols.periodMap` is stated. -/
private def toTop : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) k where
  toFun f := CuspForm.mcast rfl f (MonoidHom.range_eq_map _).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem toTop_apply (f : CuspForm 𝒮ℒ k) (z : UpperHalfPlane) : toTop f z = f z :=
  (rfl)

private theorem toTop_injective : Function.Injective (toTop (k := k)) :=
  fun f g h ↦ CuspForm.ext fun z ↦ by rw [← toTop_apply, h, toTop_apply]

/-- The period polynomial as a binary form of degree `w`, before restricting the codomain to
`W_w`: the binary form attached by `TauCeti.binaryFormDual` to the functional
`P ↦ ∫₀^{i∞} f(τ) P(τ, 1) dτ`, the period map of `f` on the modular symbols `{∞, 0} ⊗ P`. -/
private def periodForm (hk : k = w + 2) :
    CuspForm 𝒮ℒ k →ₗ[ℂ] homogeneousSubmodule (Fin 2) ℂ w :=
  binaryFormDual ℂ w ∘ₗ LinearMap.lcomp ℂ ℂ (symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ)) ∘ₗ
    periodMap ℂ ⊤ hk ∘ₗ toTop

private theorem periodForm_apply (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) :
    periodForm hk f = binaryFormDual ℂ w
      (periodMap ℂ ⊤ hk (toTop f) ∘ₗ symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ)) :=
  (rfl)

private theorem eval_periodForm (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) (x y : ℂ) :
    eval ![x, y] (periodForm hk f : MvPolynomial (Fin 2) ℂ) =
      cuspIntegral (fun τ ↦ f τ * (x - τ * y) ^ w) ((0 : ℚ) : OnePoint ℚ) ∞ := by
  rw [periodForm_apply, eval_binaryFormDual, LinearMap.comp_apply, periodMap_symbol]
  congr 1
  ext τ
  simp [periodIntegrand_apply, toTop_apply, mul_comm]

/-- The period functional of `f` at `P ∣ g` is the period map of `f` on the Manin symbol of `g`. -/
private theorem periodMap_symbol_binaryFormRep (hk : k = w + 2) (f : CuspForm 𝒮ℒ k)
    (g : SL(2, ℤ)) (P : homogeneousSubmodule (Fin 2) ℂ w) :
    periodMap ℂ ⊤ hk (toTop f)
        (symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ)
          (binaryFormRep ℂ w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) P)) =
      periodMap ℂ ⊤ hk (toTop f) (maninSymbol ⊤ g P) := by
  have h := maninSymbol_mul_of_mem (R := ℂ) ⊤ (Subgroup.mem_top g) 1 P
  rw [mul_one] at h
  rw [h, maninSymbol_apply, map_one, one_smul, one_smul]

/-- `S⁻¹ = -S`, written so that the two-term Manin relation applies. -/
private theorem S_inv_eq : (S⁻¹ : SL(2, ℤ)) = -1 * S := by
  have hS : S * S = (-1 : SL(2, ℤ)) := Subtype.ext <| by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, coe_neg, Matrix.SpecialLinearGroup.coe_one]
      using S_mul_S_eq
  exact inv_eq_of_mul_eq_one_right (by rw [neg_one_mul, mul_neg, hS, neg_neg])

/-- `U⁻¹ = -U²`, written so that the three-term Manin relation applies. -/
private theorem U_inv_eq : ((T * S)⁻¹ : SL(2, ℤ)) = -(1 * (T * S) ^ 2) :=
  inv_eq_of_mul_eq_one_right <| by
    rw [one_mul, mul_neg, ← pow_succ', ModularGroup.T_mul_S_pow_three, neg_neg]

/-- `U⁻² = -U`, written so that the three-term Manin relation applies. -/
private theorem U_inv_mul_U_inv_eq : ((T * S)⁻¹ * (T * S)⁻¹ : SL(2, ℤ)) = -(1 * (T * S)) := by
  rw [U_inv_eq, neg_mul_neg, one_mul, one_mul, ← pow_add, pow_succ,
    ModularGroup.T_mul_S_pow_three, neg_one_mul]

/-- **The period polynomial lies in `W_w`**: `r_f` is killed by `1 + S` and by `1 + U + U²`, the
two-term and three-term Manin relations. -/
private theorem periodForm_mem_periodPolynomials (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) :
    periodForm hk f ∈ periodPolynomials ℂ w := by
  -- the period functional, after the adjugate action of `g`, is the period map on the Manin
  -- symbol of `g⁻¹`
  have hφ (g : SL(2, ℤ)) :
      periodMap ℂ ⊤ hk (toTop f) ∘ₗ symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ) ∘ₗ
          binaryFormAdjugateRep ℂ w (g : Matrix (Fin 2) (Fin 2) ℤ) =
        periodMap ℂ ⊤ hk (toTop f) ∘ₗ maninSymbol ⊤ g⁻¹ := by
    ext P
    simp only [LinearMap.comp_apply, binaryFormAdjugateRep_apply,
      ← Matrix.SpecialLinearGroup.coe_inv, periodMap_symbol_binaryFormRep]
  have h₁ : symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ) =
      (maninSymbol ⊤ 1 : homogeneousSubmodule (Fin 2) ℂ w →ₗ[ℂ] ModularSymbols ℂ ⊤ w) := by
    ext P
    rw [maninSymbol_apply, map_one, one_smul, one_smul]
  -- the two-term relation, through `S⁻¹ = -S`
  have h₂ : maninSymbol ⊤ 1 + maninSymbol ⊤ S⁻¹ =
      (0 : homogeneousSubmodule (Fin 2) ℂ w →ₗ[ℂ] ModularSymbols ℂ ⊤ w) := by
    rw [S_inv_eq, maninSymbol_mul_S, maninSymbol_neg, add_neg_cancel]
  -- the three-term relation, through `U⁻¹ = -U²` and `U⁻² = -U`
  have h₃ : maninSymbol ⊤ 1 + maninSymbol ⊤ (T * S)⁻¹ + maninSymbol ⊤ ((T * S)⁻¹ * (T * S)⁻¹) =
      (0 : homogeneousSubmodule (Fin 2) ℂ w →ₗ[ℂ] ModularSymbols ℂ ⊤ w) := by
    rw [U_inv_mul_U_inv_eq, U_inv_eq, maninSymbol_neg, maninSymbol_neg, add_right_comm,
      maninSymbol_add_mul_T_mul_S_add_mul_T_mul_S_sq]
  rw [mem_periodPolynomials_iff, periodForm_apply]
  simp only [binaryFormRep_binaryFormDual, ← map_add]
  constructor
  · rw [LinearMap.comp_assoc, hφ, h₁, ← LinearMap.comp_add, h₂]
    simp
  · have hUU : binaryFormAdjugateRep ℂ w ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ∘ₗ
          binaryFormAdjugateRep ℂ w ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        binaryFormAdjugateRep ℂ w ((T * S * (T * S) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← Module.End.mul_eq_comp, ← map_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    simp only [LinearMap.comp_assoc, hUU]
    rw [hφ, hφ, _root_.mul_inv_rev (T * S) (T * S), h₁, ← LinearMap.comp_add,
      ← LinearMap.comp_add, h₃]
    simp

private theorem periodForm_injective (hk : k = w + 2) : Function.Injective (periodForm hk) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  rw [periodForm_apply, ← map_zero (binaryFormDual ℂ w)] at hf
  have hφ := binaryFormDual_injective
    (fun j _ ↦ .of_ne_zero (Nat.cast_ne_zero.2 (Nat.choose_pos ‹_›).ne')) hf
  refine toTop_injective (periodMap_injective (R := ℂ) hk ?_)
  rw [map_zero, map_zero]
  refine LinearMap.ext_on (span_maninSymbol_eq_top (R := ℂ) (w := w) ⊤) ?_
  rintro _ ⟨⟨g, P⟩, rfl⟩
  dsimp only
  rw [← periodMap_symbol_binaryFormRep, ← LinearMap.comp_apply, hφ, LinearMap.zero_apply,
    LinearMap.zero_apply]

/-- **The period polynomial** `r_f(X, Y) = ∫₀^{i∞} f(τ) (X - τY)ʷ dτ` of a cusp form `f` of weight
`k = w + 2` on `SL(2, ℤ)` (`TauCeti.eval_periodPolynomial`), as a `ℂ`-linear map to the
period-polynomial space `W_w`. It is the binary form attached by `TauCeti.binaryFormDual` to the
functional `P ↦ ∫₀^{i∞} f(τ) P(τ, 1) dτ`, the period map of `f` on the modular symbols
`{∞, 0} ⊗ P`; it lies in `W_w` because of the two-term and three-term Manin relations. -/
def periodPolynomial (hk : k = w + 2) : CuspForm 𝒮ℒ k →ₗ[ℂ] periodPolynomials ℂ w :=
  (periodForm hk).codRestrict _ (periodForm_mem_periodPolynomials hk)

/-- **The values of the period polynomial**: `r_f(x, y) = ∫₀^{i∞} f(τ) (x - τy)ʷ dτ`. -/
@[simp]
theorem eval_periodPolynomial (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) (x y : ℂ) :
    eval ![x, y] ((periodPolynomial hk f : homogeneousSubmodule (Fin 2) ℂ w) :
        MvPolynomial (Fin 2) ℂ) =
      cuspIntegral (fun τ ↦ f τ * (x - τ * y) ^ w) ((0 : ℚ) : OnePoint ℚ) ∞ :=
  eval_periodForm hk f x y

/-- **The period polynomial determines the cusp form**: `f ↦ r_f` is injective. -/
theorem periodPolynomial_injective (hk : k = w + 2) :
    Function.Injective (periodPolynomial hk) :=
  fun _ _ h ↦ periodForm_injective hk (congrArg Subtype.val h)

end TauCeti
