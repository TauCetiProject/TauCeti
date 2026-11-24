/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.QExpansion
public import TauCeti.Analysis.Fourier.ZMod

/-!
# Cyclotomic conjugation of weight-two division values

After division by `(2πi)²`, the Fourier coefficients of weighted weight-two Eisenstein
series transform algebraically under cyclotomic coefficient maps. Multiplication of the
second residue coordinate by `d` corresponds to the coefficient map `ζ_N ↦ ζ_N^d`.
The constant coefficient is included by its finite Bernoulli formula; no continuity of
the coefficient map, or interchange with an infinite sum, is used.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §6.1.
-/

public noncomputable section

open Complex ZMod
open UpperHalfPlane hiding I
open scoped Real Matrix

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- Cyclotomic conjugation acts on normalized weight-two Fourier coefficients by
multiplying the second residue coordinate. This includes the constant coefficient. -/
theorem map_qExpansion_weightedG2MF_coeff_div {σ : ℂ →+* ℂ} {d : (ZMod N)ˣ}
    (hσ : ∀ j : ZMod N, σ (stdAddChar j) = stdAddChar ((d : ZMod N) * j))
    {W W' : (Fin 2 → ZMod N) → ℂ}
    (hW : ∀ x y, W' ![x, (d : ZMod N) * y] = σ (W ![x, y])) (n : ℕ) :
    σ ((qExpansion N (weightedG2MF W)).coeff n / (2 * π * I) ^ 2) =
      (qExpansion N (weightedG2MF W')).coeff n / (2 * π * I) ^ 2 := by
  have hsum : ∑ b, W' b = σ (∑ b, W b) := by
    rw [map_sum, ← (piFinTwoEquiv fun _ ↦ ZMod N).symm.sum_comp,
      ← (piFinTwoEquiv fun _ ↦ ZMod N).symm.sum_comp, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    conv_lhs => rw [← Equiv.sum_comp d.mulLeft]
    simp only [Units.mulLeft_apply, piFinTwoEquiv_symm_apply]
    exact Finset.sum_congr rfl fun y _ ↦ hW x y
  let V := fun a ↦ W a - ((N : ℂ) ^ 2)⁻¹ * ∑ b, W b
  let V' := fun a ↦ W' a - ((N : ℂ) ^ 2)⁻¹ * ∑ b, W' b
  have hV (x y) : V' ![x, (d : ZMod N) * y] = σ (V ![x, y]) := by
    simp only [V, V', hW, hsum, map_sub, map_mul, map_inv₀, map_pow, map_natCast]
  have hzero (j) : σ (𝓕 (fun y ↦ V ![0, y]) j) = 𝓕 (fun y ↦ V' ![0, y]) j :=
    map_dft_of_mul hσ (hV 0) j
  have hrow (x : ZMod N) (j) :
      σ (𝓕 (fun y ↦ V ![x, y] + V ![-x, -y]) j) =
        𝓕 (fun y ↦ V' ![x, y] + V' ![-x, -y]) j := by
    apply map_dft_of_mul hσ
    intro y
    rw [← mul_neg, hV, hV, map_add]
  rw [qExpansion_weightedG2MF_coeff_div, qExpansion_weightedG2MF_coeff_div]
  dsimp only
  split_ifs <;>
    simp only [map_div₀, map_neg, map_sum, map_mul, map_pow, map_natCast, map_ofNat,
      map_ratCast, hzero, hrow, V, V']

/-- On a single-residue division value, cyclotomic coefficient conjugation sends
`(a,b)` to `(a,db)`. -/
theorem map_qExpansion_single_weightedG2MF_coeff_div {σ : ℂ →+* ℂ} {d : (ZMod N)ˣ}
    (hσ : ∀ j : ZMod N, σ (stdAddChar j) = stdAddChar ((d : ZMod N) * j))
    (a : Fin 2 → ZMod N) (n : ℕ) :
    σ ((qExpansion N (weightedG2MF (Pi.single a (1 : ℂ)))).coeff n /
      (2 * π * I) ^ 2) =
    (qExpansion N (weightedG2MF (Pi.single ![a 0, (d : ZMod N) * a 1] (1 : ℂ)))).coeff n /
      (2 * π * I) ^ 2 := by
  classical
  apply map_qExpansion_weightedG2MF_coeff_div hσ
  intro x y
  have heq : (![x, (d : ZMod N) * y] : Fin 2 → ZMod N) =
      ![a 0, (d : ZMod N) * a 1] ↔ ![x, y] = a := by
    constructor
    · intro h
      ext i
      fin_cases i
      · exact congrFun h 0
      · exact d.mulLeft.injective (congrFun h 1)
    · intro h
      ext i
      fin_cases i
      · exact congrFun h 0
      · exact congrArg (fun z : ZMod N ↦ (d : ZMod N) * z) (congrFun h 1)
  simp only [Pi.single_apply, heq, apply_ite σ, map_one, map_zero]

end TauCeti.EisensteinSeries
