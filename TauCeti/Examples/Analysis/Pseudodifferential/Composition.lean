/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion
public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Checks of the composition and adjoint expansions

The composition expansion `a # b ∼ ∑ₖ sharpTerm a b k`, with
`sharpTerm a b k = ((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`, and the adjoint expansion
`a* ∼ ∑ₖ adjointTerm a k`, with `adjointTerm a k = ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†`
(`TauCeti.Symbol.sharpTerm`, `TauCeti.Symbol.adjointTerm`), are computed here on three
model symbols whose expansions terminate. Each pins down a convention that a sign or a missing
factor would get wrong.

* **The canonical commutator.** For the frequency coordinate `ξⱼ`
  (`TauCeti.Symbol.ofInner (EuclideanSpace.single j 1)`, the symbol of `Dⱼ = -i ∂ⱼ`) and the
  position coordinate `xₖ` (`TauCeti.Symbol.coordSubSymbol 0 k`), the expansion of `ξⱼ # xₖ` is
  `xₖ ξⱼ - i δⱼₖ` (`sum_coefficient_ofInner_sharpTerm_coordSubSymbol`), with leading term
  `xₖ ξⱼ`, first correction `-i δⱼₖ` and no further terms, whereas `xₖ # ξⱼ = xₖ ξⱼ`
  (`coordSubSymbol_sharpTerm_ofInner_succ`). Hence `[Dⱼ, xₖ]` has symbol `-i δⱼₖ`
  (`sum_coefficient_sharpTerm_sub_sharpTerm`), and on Schwartz functions the operators satisfy
  `Dⱼ (xₖ u) - xₖ Dⱼ u = -i δⱼₖ u` (`quantizeSchwartzValue_ofInner_smulLeftCLM_sub`). In one
  dimension: `ξ # x = x ξ - i`, `x # ξ = x ξ` and `[D, x] = -i`.
* **Matrix units.** For the constant symbols of the matrix units `eᵢₖ` on `ℂ²`, the expansion of
  `eᵢₖ # eₖᵢ` is the matrix product `eᵢᵢ` (`sum_coefficient_single_sharpTerm_single`), so
  `e₁₂ # e₂₁ = e₁₁` and `e₂₁ # e₁₂ = e₂₂`. Their commutator `diag(1, -1)`
  (`sum_coefficient_single_sharpTerm_single_sub`) is a nonzero constant, which in positive
  dimension is a symbol of no negative order (`not_exists_coefficient_eq_diagonal`): since the
  leading symbols do not commute, the commutator of these two operators of order `0` is not of
  lower order.
* **A position-dependent adjoint.** For `p(x, ξ) = e^{i xⱼ} ξⱼ` (`expMulFreq j`), the adjoint
  expansion is `e^{-i xⱼ} (ξⱼ - 1)` (`sum_coefficient_adjointTerm_expMulFreq`): besides the
  pointwise adjoint `e^{-i xⱼ} ξⱼ` it has the correction `-i (∂_{xⱼ} ∂_{ξⱼ} p)† = -e^{-i xⱼ}`, so
  the formal adjoint is not the pointwise adjoint
  (`sum_coefficient_adjointTerm_expMulFreq_ne`). In one dimension this is the symbol of
  `(e^{i x} D)* = D e^{-i x} = e^{-i x} D - e^{-i x}`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3) for
  the adjoint expansion and (2.5)–(2.7) for the composition expansion.
-/

public section

noncomputable section

open Finset
open scoped ContDiff SchwartzMap

namespace TauCeti.CompositionExample

open Symbol

variable {n : ℕ}

/-! ### Coordinate derivatives of the model coefficients -/

/-- The coordinate derivative of `y ↦ exp (i yⱼ) • c` in the direction `eₗ`. -/
private theorem coordinateDeriv_cexp_smul {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (c : B) (j l : Fin n) (x : CoordinateSpace n) :
    coordinateDeriv [l] (fun y : CoordinateSpace n ↦ Complex.exp (Complex.I * (y j : ℂ)) • c) x =
      ((if l = j then Complex.I else 0) * Complex.exp (Complex.I * (x j : ℂ))) • c := by
  rw [coordinateDeriv_cons, coordinateDeriv_nil]
  have hf : HasFDerivAt (fun y : CoordinateSpace n ↦ Complex.I * (y j : ℂ))
      (Complex.I • (Complex.ofRealCLM.comp (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ)))
      x := by
    have := ((Complex.ofRealCLM.comp
      (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ)).hasFDerivAt (x := x)).const_smul
        Complex.I
    convert this using 1
    funext y
    simp
  rw [(hf.cexp.smul_const c).fderiv]
  by_cases h : l = j
  · subst h
    simp [mul_comm]
  · simp [h, Ne.symm h]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### The position and frequency coordinates -/

section Coordinates

/-- The derivative `∂_{xₗ} xₖ` is `(eₗ)ₖ`. -/
private theorem coefficient_spatialDeriv_coordSubSymbol_zero (k l : Fin n)
    (x ξ : CoordinateSpace n) :
    (spatialDeriv l (coordSubSymbol (W := V) 0 k)).coefficient (x, ξ) =
      (EuclideanSpace.single l (1 : ℝ) : CoordinateSpace n) k • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_spatialDeriv]
  simp only [coefficient_coordSubSymbol, sub_zero]
  exact congrFun (coordinateDeriv_singleton_coord_smul _ k l) x

/-- **The leading term of `ξⱼ # xₖ`** is the product `ξⱼ xₖ`. -/
theorem coefficient_ofInner_sharpTerm_coordSubSymbol_zero (j k : Fin n)
    (x ξ : CoordinateSpace n) :
    ((ofInner (EuclideanSpace.single j 1) : Symbol n V V 1).sharpTerm
        (coordSubSymbol 0 k) 0).coefficient (x, ξ) =
      (x k * ξ j) • ContinuousLinearMap.id ℂ V := by
  simp [EuclideanSpace.inner_single_right, smul_smul]

/-- **The first correction term of `ξⱼ # xₖ`** is `-i (∂_{ξ} ξⱼ) (∂_{x} xₖ) = -i δⱼₖ`. -/
theorem coefficient_ofInner_sharpTerm_coordSubSymbol_one (j k : Fin n)
    (x ξ : CoordinateSpace n) :
    ((ofInner (EuclideanSpace.single j 1) : Symbol n V V 1).sharpTerm
        (coordSubSymbol 0 k) 1).coefficient (x, ξ) =
      (if j = k then -Complex.I else 0) • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_sharpTerm_one]
  simp only [coefficient_frequencyDeriv_ofInner,
    coefficient_spatialDeriv_coordSubSymbol_zero,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp,
    PiLp.single_apply]
  split_ifs with h
  · subst h
    simp
  · simp [ite_smul, Ne.symm h]

/-- The terms of `ξⱼ # xₖ` of order `-1` and below vanish: `ξⱼ` has no second frequency
derivatives. -/
theorem ofInner_sharpTerm_coordSubSymbol_add_two (j k : Fin n) (N : ℕ) :
    (ofInner (EuclideanSpace.single j 1) : Symbol n V V 1).sharpTerm (coordSubSymbol 0 k)
      (N + 2) = 0 := by
  ext1
  funext ⟨x, ξ⟩
  have h (w : Fin (N + 2) → Fin n) :
      mixedDeriv [] (List.ofFn w) (ofInner (EuclideanSpace.single j 1) : Symbol n V V 1).coefficient
        x ξ = 0 := by
    simp only [mixedDeriv_def, coordinateDeriv_nil, coefficient_ofInner_single]
    exact congrFun (coordinateDeriv_coord_smul_eq_zero_of_two_le_length _ j (by simp)) ξ
  rw [coefficient_sharpTerm]
  simp only [h, ContinuousLinearMap.zero_comp, Finset.sum_const_zero, smul_zero, coefficient_zero,
    Pi.zero_apply]

/-- **The composition expansion of `ξⱼ # xₖ` is `xₖ ξⱼ - i δⱼₖ`**: every partial sum with at least
two terms is exact. -/
theorem sum_coefficient_ofInner_sharpTerm_coordSubSymbol (j k : Fin n) {N : ℕ} (hN : 2 ≤ N)
    (x ξ : CoordinateSpace n) :
    ∑ i ∈ range N, ((ofInner (EuclideanSpace.single j 1) : Symbol n V V 1).sharpTerm
        (coordSubSymbol 0 k) i).coefficient (x, ξ) =
      (x k * ξ j) • ContinuousLinearMap.id ℂ V -
        (if j = k then Complex.I else 0) • ContinuousLinearMap.id ℂ V := by
  rw [Finset.eventually_constant_sum (fun i hi ↦ ?_) hN]
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      coefficient_ofInner_sharpTerm_coordSubSymbol_zero,
      coefficient_ofInner_sharpTerm_coordSubSymbol_one]
    split_ifs <;> simp [sub_eq_add_neg]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
    rw [ofInner_sharpTerm_coordSubSymbol_add_two, coefficient_zero, Pi.zero_apply]

/-- **The leading term of `xₖ # ξⱼ`** is the product `xₖ ξⱼ`. -/
theorem coefficient_coordSubSymbol_sharpTerm_ofInner_zero (j k : Fin n)
    (x ξ : CoordinateSpace n) :
    ((coordSubSymbol 0 k).sharpTerm
        (ofInner (EuclideanSpace.single j 1) : Symbol n V V 1) 0).coefficient (x, ξ) =
      (x k * ξ j) • ContinuousLinearMap.id ℂ V := by
  simp [EuclideanSpace.inner_single_right, smul_smul, mul_comm]

/-- **`xₖ # ξⱼ = xₖ ξⱼ`**: the later terms vanish, since `ξⱼ` does not depend on the position. -/
theorem coordSubSymbol_sharpTerm_ofInner_succ (j k : Fin n) (N : ℕ) :
    (coordSubSymbol 0 k).sharpTerm (ofInner (EuclideanSpace.single j 1) : Symbol n V V 1)
      (N + 1) = 0 :=
  sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero (spatialDeriv_ofInner _) _ N

/-- **The commutator `[Dⱼ, xₖ]` has symbol `-i δⱼₖ`**: the composition expansions of `ξⱼ # xₖ` and
`xₖ # ξⱼ` differ by `-i δⱼₖ` as soon as they have at least two terms. -/
theorem sum_coefficient_sharpTerm_sub_sharpTerm (j k : Fin n) {N : ℕ} (hN : 2 ≤ N)
    (x ξ : CoordinateSpace n) :
    ∑ i ∈ range N, ((ofInner (EuclideanSpace.single j 1) : Symbol n V V 1).sharpTerm
        (coordSubSymbol 0 k) i).coefficient (x, ξ) -
      ∑ i ∈ range N, ((coordSubSymbol 0 k).sharpTerm
        (ofInner (EuclideanSpace.single j 1) : Symbol n V V 1) i).coefficient (x, ξ) =
      (if j = k then -Complex.I else 0) • ContinuousLinearMap.id ℂ V := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' (one_le_two.trans hN)
  rw [sum_coefficient_ofInner_sharpTerm_coordSubSymbol j k hN, Finset.sum_range_succ']
  simp only [coordSubSymbol_sharpTerm_ofInner_succ, coefficient_zero, Pi.zero_apply,
    Finset.sum_const_zero, zero_add, coefficient_coordSubSymbol_sharpTerm_ofInner_zero]
  split_ifs <;> simp

/-- **The commutator `[Dⱼ, xₖ] = -i δⱼₖ` of the operators.** With `Dⱼ = Op(ξⱼ) = -i ∂ⱼ`,
`Dⱼ (xₖ u) - xₖ Dⱼ u = -i δⱼₖ u` for every Schwartz function `u`. -/
theorem quantizeSchwartzValue_ofInner_smulLeftCLM_sub [CompleteSpace V] (j k : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofInner (EuclideanSpace.single j 1) : Symbol n V V 1).coefficient
        (SchwartzMap.smulLeftCLM V (EuclideanSpace.proj k : CoordinateSpace n →L[ℝ] ℝ) u) x -
      x k • quantizeSchwartzValue
        (ofInner (EuclideanSpace.single j 1) : Symbol n V V 1).coefficient u x =
      (if j = k then -Complex.I else 0) • u x := by
  rw [quantizeSchwartzValue_ofInner, quantizeSchwartzValue_ofInner,
    SchwartzMap.lineDerivOp_smulLeftCLM_clm]
  have hg : (fun y : CoordinateSpace n ↦ y k).HasTemperateGrowth :=
    (EuclideanSpace.proj k).hasTemperateGrowth
  simp only [add_apply]
  simp [SchwartzMap.smulLeftCLM_apply_apply hg, PiLp.single_apply, smul_comm (x k) Complex.I,
    eq_comm (a := k), apply_ite (fun f : 𝓢(CoordinateSpace n, V) ↦ f x)]

end Coordinates

/-! ### Matrix units -/

section MatrixUnits

open Matrix

/-- **`eᵢₖ # eₖᵢ = eᵢᵢ`**: the composition expansion of the constant matrix units `eᵢₖ` and `eₖᵢ` is
`eᵢᵢ`. In particular `e₁₂ # e₂₁ = e₁₁` and `e₂₁ # e₁₂ = e₂₂`. -/
theorem sum_coefficient_single_sharpTerm_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i k : ι)
    (N : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    ∑ l ∈ range (N + 1), ((const (n := n) (toEuclideanCLM (𝕜 := ℂ) (single i k 1))).sharpTerm
      (const (toEuclideanCLM (𝕜 := ℂ) (single k i 1))) l).coefficient p =
      toEuclideanCLM (𝕜 := ℂ) (single i i 1) := by
  rw [sum_coefficient_const_sharpTerm_const, ← ContinuousLinearMap.mul_def, ← map_mul,
    single_mul_single_same, one_mul]

/-- **The commutator of `e₁₂` and `e₂₁` is `diag(1, -1)`**: the difference of the composition
expansions `e₁₂ # e₂₁` and `e₂₁ # e₁₂`. -/
theorem sum_coefficient_single_sharpTerm_single_sub (N : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    ∑ l ∈ range (N + 1), ((const (n := n) (toEuclideanCLM (𝕜 := ℂ) (single 0 1 1))).sharpTerm
        (const (toEuclideanCLM (𝕜 := ℂ) (single 1 0 1))) l).coefficient p -
      ∑ l ∈ range (N + 1), ((const (n := n) (toEuclideanCLM (𝕜 := ℂ) (single 1 0 1))).sharpTerm
        (const (toEuclideanCLM (𝕜 := ℂ) (single 0 1 1))) l).coefficient p =
      toEuclideanCLM (𝕜 := ℂ) (diagonal ![1, -1]) := by
  rw [sum_coefficient_single_sharpTerm_single, sum_coefficient_single_sharpTerm_single,
    ← map_sub]
  congr 1
  ext i k
  fin_cases i <;> fin_cases k <;> simp

/-- **The commutator of `e₁₂` and `e₂₁` keeps order `0`**: in positive dimension no symbol of
negative order has the constant coefficient `diag(1, -1)`. -/
theorem not_exists_coefficient_eq_diagonal [NeZero n] {μ : ℝ} (hμ : μ < 0) :
    ¬∃ a : Symbol n (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2)) μ,
      ∀ p, a.coefficient p = toEuclideanCLM (𝕜 := ℂ) (diagonal ![1, -1]) := by
  have hD : toEuclideanCLM (𝕜 := ℂ) (diagonal ![(1 : ℂ), -1]) ≠ 0 := by
    intro h
    have h' := congrArg (fun T ↦ T (EuclideanSpace.single 0 1) 0) h
    simp at h'
  exact not_exists_coefficient_eq_const hD hμ

end MatrixUnits

/-! ### The adjoint of `e^{i xⱼ} Dⱼ` -/

section Adjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem contDiff_cexp_smul_id (j : Fin n) :
    ContDiff ℝ ∞ fun y : CoordinateSpace n ↦
      Complex.exp (Complex.I * (y j : ℂ)) • ContinuousLinearMap.id ℂ H :=
  (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).contDiff))).smul contDiff_const

/-- The symbol `e^{i xⱼ} ξⱼ` of order `1`, the symbol of the operator `e^{i xⱼ} Dⱼ`. -/
def expMulFreq (j : Fin n) : Symbol n H H 1 :=
  inclusion (zero_add 1).le
    ((ofSpatial _ (contDiff_cexp_smul_id j)).comp (ofInner (EuclideanSpace.single j 1)))

omit [CompleteSpace H] in
@[simp]
theorem coefficient_expMulFreq (j : Fin n) (p : CoordinateSpace n × CoordinateSpace n) :
    (expMulFreq j : Symbol n H H 1).coefficient p =
      p.2 j • Complex.exp (Complex.I * (p.1 j : ℂ)) • ContinuousLinearMap.id ℂ H := by
  simp only [expMulFreq, coefficient_inclusion, coefficient_comp, coefficient_ofSpatial,
    coefficient_ofInner_single, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp]

omit [CompleteSpace H] in
/-- The mixed derivative `∂_{xₗ} ∂_{ξₗ} (e^{i xⱼ} ξⱼ)` is `i δₗⱼ e^{i xⱼ}`. -/
private theorem coefficient_spatialDeriv_frequencyDeriv_expMulFreq (j l : Fin n)
    (x ξ : CoordinateSpace n) :
    (spatialDeriv l (frequencyDeriv l (expMulFreq j : Symbol n H H 1))).coefficient (x, ξ) =
      (if l = j then Complex.I * Complex.exp (Complex.I * (x j : ℂ)) else 0) •
        ContinuousLinearMap.id ℂ H := by
  have hξ (y : CoordinateSpace n) :
      (frequencyDeriv l (expMulFreq j : Symbol n H H 1)).coefficient (y, ξ) =
        Complex.exp (Complex.I * (y j : ℂ)) •
          ((EuclideanSpace.single l (1 : ℝ) : CoordinateSpace n) j •
            ContinuousLinearMap.id ℂ H) := by
    rw [coefficient_frequencyDeriv]
    simp only [coefficient_expMulFreq]
    rw [smul_comm]
    exact congrFun (coordinateDeriv_singleton_coord_smul _ j l) ξ
  rw [coefficient_spatialDeriv]
  simp only [hξ]
  rw [coordinateDeriv_cexp_smul]
  by_cases h : l = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- **The leading term of the formal adjoint** of `e^{i xⱼ} ξⱼ` is the pointwise adjoint
`e^{-i xⱼ} ξⱼ`. -/
theorem coefficient_adjointTerm_expMulFreq_zero (j : Fin n) (x ξ : CoordinateSpace n) :
    ((expMulFreq j : Symbol n H H 1).adjointTerm 0).coefficient (x, ξ) =
      ξ j • Complex.exp (-(Complex.I * (x j : ℂ))) • ContinuousLinearMap.id ℂ H := by
  rw [coefficient_adjointTerm_zero, coefficient_expMulFreq, ← Complex.coe_smul, smul_smul,
    map_smulₛₗ, ContinuousLinearMap.adjoint_id]
  simp [← Complex.exp_conj, mul_smul]

/-- **The first correction term of the formal adjoint** of `e^{i xⱼ} ξⱼ` is
`-i (∂_{xⱼ} ∂_{ξⱼ} (e^{i xⱼ} ξⱼ))† = -i (i e^{i xⱼ})† = -e^{-i xⱼ}`. -/
theorem coefficient_adjointTerm_expMulFreq_one (j : Fin n) (x ξ : CoordinateSpace n) :
    ((expMulFreq j : Symbol n H H 1).adjointTerm 1).coefficient (x, ξ) =
      -(Complex.exp (-(Complex.I * (x j : ℂ))) • ContinuousLinearMap.id ℂ H) := by
  rw [coefficient_adjointTerm_succ, Finset.sum_eq_single j (fun l _ hl ↦ by
      rw [coefficient_adjointTerm_zero, coefficient_spatialDeriv_frequencyDeriv_expMulFreq]
      simp [hl]) (by simp),
    coefficient_adjointTerm_zero, coefficient_spatialDeriv_frequencyDeriv_expMulFreq]
  simp [map_smulₛₗ, ContinuousLinearMap.adjoint_id, ← Complex.exp_conj, smul_smul, ← mul_assoc]

/-- The terms of the formal adjoint of `e^{i xⱼ} ξⱼ` of order `-1` and below vanish: `ξⱼ` has no
second frequency derivatives. -/
theorem adjointTerm_expMulFreq_add_two (j : Fin n) (N : ℕ) :
    (expMulFreq j : Symbol n H H 1).adjointTerm (N + 2) = 0 := by
  ext1
  funext ⟨x, ξ⟩
  have h (w : Fin (N + 2) → Fin n) :
      mixedDeriv (List.ofFn w) (List.ofFn w) (expMulFreq j : Symbol n H H 1).coefficient x ξ =
        0 := by
    simp only [mixedDeriv_def, coefficient_expMulFreq]
    have h0 : (fun y : CoordinateSpace n ↦ coordinateDeriv (List.ofFn w) (fun η ↦
        η j • Complex.exp (Complex.I * (y j : ℂ)) • ContinuousLinearMap.id ℂ H) ξ) = 0 :=
      funext fun _ ↦ congrFun (coordinateDeriv_coord_smul_eq_zero_of_two_le_length _ j (by simp)) ξ
    rw [h0, coordinateDeriv_zero, Pi.zero_apply]
  rw [coefficient_adjointTerm]
  simp only [h, map_zero, Finset.sum_const_zero, smul_zero, coefficient_zero, Pi.zero_apply]

/-- **The formal adjoint of `e^{i xⱼ} ξⱼ` is `e^{-i xⱼ} (ξⱼ - 1)`**: every partial sum of the
adjoint expansion with at least two terms is exact. -/
theorem sum_coefficient_adjointTerm_expMulFreq (j : Fin n) {N : ℕ} (hN : 2 ≤ N)
    (x ξ : CoordinateSpace n) :
    ∑ i ∈ range N, ((expMulFreq j : Symbol n H H 1).adjointTerm i).coefficient (x, ξ) =
      (ξ j - 1) • Complex.exp (-(Complex.I * (x j : ℂ))) • ContinuousLinearMap.id ℂ H := by
  rw [Finset.eventually_constant_sum (fun i hi ↦ ?_) hN]
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      coefficient_adjointTerm_expMulFreq_zero, coefficient_adjointTerm_expMulFreq_one]
    rw [sub_smul, one_smul, sub_eq_add_neg]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
    rw [adjointTerm_expMulFreq_add_two, coefficient_zero, Pi.zero_apply]

/-- **The formal adjoint of `e^{i xⱼ} ξⱼ` is not just its pointwise adjoint `e^{-i xⱼ} ξⱼ`**: the
expansion has the nonzero correction `-e^{-i xⱼ}`. -/
theorem sum_coefficient_adjointTerm_expMulFreq_ne [Nontrivial H] (j : Fin n) {N : ℕ}
    (hN : 2 ≤ N) (x ξ : CoordinateSpace n) :
    ∑ i ∈ range N, ((expMulFreq j : Symbol n H H 1).adjointTerm i).coefficient (x, ξ) ≠
      ξ j • Complex.exp (-(Complex.I * (x j : ℂ))) • ContinuousLinearMap.id ℂ H := by
  rw [sum_coefficient_adjointTerm_expMulFreq j hN, sub_smul, one_smul, Ne, sub_eq_self]
  rw [← ContinuousLinearMap.one_def]
  exact smul_ne_zero (Complex.exp_ne_zero _) one_ne_zero

end Adjoint

end TauCeti.CompositionExample
