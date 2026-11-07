/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Evaluating modular symbols at the cusps

Every cusp `α ∈ ℙ¹(ℚ)` is represented by a primitive integral vector `v_α`, unique up to sign:
`(1, 0)` for `∞` and `(num q, den q)` for `q ∈ ℚ`. For `g ∈ SL(2, ℤ)` the cusp `g∞` is represented
by the first column of `g`. A binary form `P` of even degree `w` takes the same value at `v` and
`-v`, so `P(v_α)` is a well-defined function of the cusp (`TauCeti.ModularSymbols.evalCusp`), and
it is invariant under `SL(2, ℤ)`: `(P ∣ g⁻¹)(v_{gα}) = P(v_α)`.

Consequently the functional `([α] - [β]) ⊗ P ↦ P(v_α) - P(v_β)` on degree-zero divisors tensored
with binary forms descends to the modular symbols `𝕄_w(Γ; R)` for every `Γ ≤ SL(2, ℤ)`
(`TauCeti.ModularSymbols.boundaryEval`). It is the boundary map of modular symbols, sending
`{α, β} ⊗ P` to `[α] ⊗ P - [β] ⊗ P`, followed by the evaluation `[α] ⊗ P ↦ P(v_α)` on the
`SL(2, ℤ)`-coinvariants of the cusp divisors tensored with binary forms. At level one, the binary
form attached to its values on the symbols `{∞, 0} ⊗ P` is `-(X^w - Y^w)`, the negative of the
Eisenstein period polynomial
(`TauCeti.binaryFormDual_evalCusp_infty_sub_evalCusp_zero`, in
`TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Eisenstein`).

## Main definitions

* `TauCeti.ModularSymbols.evalCusp R w α`: the value `P ↦ P(v_α)` of binary forms at a cusp.
* `TauCeti.ModularSymbols.boundaryEval Γ hw`: the functional `{α, β} ⊗ P ↦ P(v_α) - P(v_β)` on
  `𝕄_w(Γ; R)`, for even `w`.

## Main results

* `TauCeti.ModularSymbols.evalCusp_infty`, `TauCeti.ModularSymbols.evalCusp_coe`: the values at
  `∞` and at `q ∈ ℚ` are the values at `(1, 0)` and at `(num q, den q)`.
* `TauCeti.ModularSymbols.evalCusp_mapGL_smul_infty`: for even `w`, the value at `g∞` is the value
  at the first column of `g`.
* `TauCeti.ModularSymbols.evalCusp_mapGL_smul`: for even `w`, `(P ∣ g⁻¹)(v_{gα}) = P(v_α)`.
* `TauCeti.ModularSymbols.boundaryEval_mk`: the value of the functional on the class of `D ⊗ P`.
* `TauCeti.ModularSymbols.boundaryEval_symbol`: the value of the functional on `{α, β} ⊗ P`.

## References

* W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics **79**,
  American Mathematical Society, 2007, §8.4 (boundary modular symbols).
-/

public section

open MonoidAlgebra MvPolynomial Representation TensorProduct
open Matrix.SpecialLinearGroup OnePoint
open scoped MatrixGroups

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] {w : ℕ}

/-! ### The primitive vector of a cusp -/

/-- The primitive integral vector representing a cusp: `(1, 0)` for `∞`, and `(num q, den q)` for
`q ∈ ℚ`. Every primitive vector representing the cusp is `±` this one. -/
private def cuspVector (α : OnePoint ℚ) : Fin 2 → ℤ :=
  α.elim ![1, 0] fun q ↦ ![q.num, q.den]

@[simp]
private theorem cuspVector_infty : cuspVector ∞ = ![1, 0] :=
  (rfl)

@[simp]
private theorem cuspVector_coe (q : ℚ) : cuspVector q = ![q.num, q.den] :=
  (rfl)

/-- **The cusp `g∞` is represented by the first column of `g`**, up to sign: for `g ∈ SL(2, ℤ)`
with first column `(a, c)`, the vector `cuspVector (g∞)` is `(a, c)` or `(-a, -c)`. -/
private theorem cuspVector_mapGL_smul_infty (g : SL(2, ℤ)) :
    cuspVector (mapGL ℚ g • ∞) = (fun i ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) i 0) ∨
      cuspVector (mapGL ℚ g • ∞) = -fun i ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) i 0 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  have he (i j : Fin 2) : (mapGL ℚ g : Matrix (Fin 2) (Fin 2) ℚ) i j = (g i j : ℚ) := by simp
  simp only [smul_infty_eq_ite, he, Int.cast_eq_zero]
  by_cases hc : g 1 0 = 0
  · -- `g` fixes `∞`, so its first column is `(±1, 0)`
    simp only [hc, ↓reduceIte, cuspVector_infty]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (by simpa [hc] using hdet : g 0 0 * g 1 1 = 1)
      with h | h
    · left
      ext i
      fin_cases i <;> simp [h, hc]
    · right
      ext i
      fin_cases i <;> simp [h, hc]
  · -- otherwise `g∞ = a / c` with `a` and `c` coprime
    simp only [hc, ↓reduceIte, cuspVector_coe]
    have hcop : Nat.Coprime (g 0 0).natAbs (g 1 0).natAbs := by
      have h := Int.isCoprime_iff_gcd_eq_one.mp (⟨g 1 1, -g 0 1, by linarith⟩ :
        IsCoprime (g 0 0) (g 1 0))
      rwa [Int.gcd_eq_natAbs] at h
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · right
      have hpos' : 0 < -g 1 0 := neg_pos.mpr hneg
      have hcop' : Nat.Coprime (-g 0 0).natAbs (-g 1 0).natAbs := by simpa using hcop
      have hq : ((g 0 0 : ℤ) : ℚ) / (g 1 0 : ℤ) = ((-g 0 0 : ℤ) : ℚ) / (-g 1 0 : ℤ) := by
        push_cast
        rw [neg_div_neg_eq]
      have hnum : (((g 0 0 : ℤ) : ℚ) / (g 1 0 : ℤ)).num = -g 0 0 := by
        rw [hq, Rat.num_div_eq_of_coprime hpos' hcop']
      have hden : ((((g 0 0 : ℤ) : ℚ) / (g 1 0 : ℤ)).den : ℤ) = -g 1 0 := by
        rw [hq, Rat.den_div_eq_of_coprime hpos' hcop']
      ext i
      fin_cases i
      · simp [hnum]
      · simp [hden]
    · left
      ext i
      fin_cases i
      · simp [Rat.num_div_eq_of_coprime hpos hcop]
      · simpa using Rat.den_div_eq_of_coprime hpos hcop

/-! ### Binary forms evaluated at the cusps -/

variable (R w) in
/-- **The value of a binary form at a cusp**: `P ↦ P(v_α)`, where `v_α = cuspVector α` is the
primitive integral vector representing `α`: `(1, 0)` for `∞` and `(num q, den q)` for `q ∈ ℚ`
(`TauCeti.ModularSymbols.evalCusp_infty`, `TauCeti.ModularSymbols.evalCusp_coe`). For even `w` it
equals the value at any primitive
vector representing `α`, in particular at the first column of any `g ∈ SL(2, ℤ)` with `g∞ = α`
(`TauCeti.ModularSymbols.evalCusp_mapGL_smul_infty`). -/
noncomputable def evalCusp (α : OnePoint ℚ) : homogeneousSubmodule (Fin 2) R w →ₗ[R] R :=
  (aeval fun i ↦ (cuspVector α i : R)).toLinearMap.domRestrict _

private theorem evalCusp_apply (α : OnePoint ℚ) (P : homogeneousSubmodule (Fin 2) R w) :
    evalCusp R w α P = eval (fun i ↦ (cuspVector α i : R)) (P : MvPolynomial (Fin 2) R) := by
  simp [evalCusp]

/-- The value at `∞` is the value at `(1, 0)`, the coefficient of `Xʷ`. -/
@[simp]
theorem evalCusp_infty (P : homogeneousSubmodule (Fin 2) R w) :
    evalCusp R w ∞ P = eval ![1, 0] (P : MvPolynomial (Fin 2) R) := by
  have hv : (fun i ↦ (cuspVector ∞ i : R)) = ![1, 0] := by
    ext i
    fin_cases i <;> simp
  rw [evalCusp_apply, hv]

/-- The value at `q ∈ ℚ` is the value at `(num q, den q)`. -/
@[simp]
theorem evalCusp_coe (q : ℚ) (P : homogeneousSubmodule (Fin 2) R w) :
    evalCusp R w q P = eval ![(q.num : R), (q.den : R)] (P : MvPolynomial (Fin 2) R) := by
  have hv : (fun i ↦ (cuspVector q i : R)) = ![(q.num : R), (q.den : R)] := by
    ext i
    fin_cases i <;> simp
  rw [evalCusp_apply, hv]

/-- **The value at `g∞` is the value at the first column of `g`**, for even `w`. -/
theorem evalCusp_mapGL_smul_infty (hw : Even w) (g : SL(2, ℤ))
    (P : homogeneousSubmodule (Fin 2) R w) :
    evalCusp R w (mapGL ℚ g • ∞) P =
      eval (fun i ↦ ((g : Matrix (Fin 2) (Fin 2) ℤ) i 0 : R)) (P : MvPolynomial (Fin 2) R) := by
  rw [evalCusp_apply]
  rcases cuspVector_mapGL_smul_infty g with h | h
  · rw [h]
  · have hv : (fun i ↦ (cuspVector (mapGL ℚ g • ∞) i : R)) =
        (-1 : R) • fun i ↦ ((g : Matrix (Fin 2) (Fin 2) ℤ) i 0 : R) := by
      ext i
      simp [h]
    rw [hv, ((mem_homogeneousSubmodule _ _).1 P.2).eval_smul, hw.neg_one_pow, one_smul]

/-- **`SL(2, ℤ)`-invariance of the values at the cusps.** For even `w` and `g ∈ SL(2, ℤ)`,
`(P ∣ g⁻¹)(v_{gα}) = P(v_α)`. -/
theorem evalCusp_mapGL_smul (hw : Even w) (g : SL(2, ℤ)) (α : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    evalCusp R w (mapGL ℚ g • α) (binaryFormSLRep R w g P) = evalCusp R w α P := by
  obtain ⟨h, rfl⟩ := exists_mem_SL2 ℤ α
  -- the first column of `g h` is `g` applied to the first column of `h`
  have hcol (M N : Matrix (Fin 2) (Fin 2) ℤ) : (fun i ↦ ((M * N) i 0 : R)) =
      Matrix.mulVec (M.map (Int.cast : ℤ → R)) fun i ↦ (N i 0 : R) := by
    ext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hinv : ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) *
      (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) = 1 := by
    have h1 : ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * g = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 := congrArg (Int.castRingHom R).mapMatrix h1
    rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h2
    exact h2
  simp only [smul_smul, ← map_mul, evalCusp_mapGL_smul_infty hw, binaryFormSLRep_apply,
    coe_binaryFormRep_apply, eval_linearSubst, Matrix.SpecialLinearGroup.coe_mul, hcol,
    Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

/-! ### The functional on modular symbols -/

variable (R w) in
/-- The linear extension `∑ rₐ [α] ↦ ∑ rₐ evalCusp α` of the values at the cusps to the
`R`-divisors on the cusps. -/
private noncomputable def divisorEval :
    R[OnePoint ℚ] →ₗ[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] R :=
  Finsupp.linearCombination R (evalCusp R w) ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp]
private theorem divisorEval_single (α : OnePoint ℚ) (r : R) :
    divisorEval R w (single α r) = r • evalCusp R w α := by
  simp [divisorEval]

private theorem divisorEval_divisorRep (hw : Even w) (g : SL(2, ℤ)) (D : R[OnePoint ℚ])
    (P : homogeneousSubmodule (Fin 2) R w) :
    divisorEval R w (divisorRep R g D) (binaryFormSLRep R w g P) = divisorEval R w D P := by
  induction D using MonoidAlgebra.induction_linear with
  | zero => simp
  | add D E hD hE => simp only [map_add, LinearMap.add_apply, hD, hE]
  | single α r =>
    rw [divisorRep_single, divisorEval_single, divisorEval_single, LinearMap.smul_apply,
      LinearMap.smul_apply, evalCusp_mapGL_smul hw]

/-- The values at the cusps make up an `SL(2, ℤ)`-invariant functional on
`Div⁰(ℙ¹(ℚ)) ⊗_R Sym^w(R²)`. -/
private theorem lift_divisorEval_comp_symbolRep (hw : Even w) (g : SL(2, ℤ)) :
    TensorProduct.lift (divisorEval R w ∘ₗ (degreeZero R).subtype) ∘ₗ symbolRep R w g =
      TensorProduct.lift (divisorEval R w ∘ₗ (degreeZero R).subtype) := by
  refine TensorProduct.ext' fun D P ↦ ?_
  simp only [LinearMap.comp_apply, symbolRep_tmul, TensorProduct.lift.tmul, Submodule.coe_subtype,
    coe_degreeZeroRep_apply, divisorEval_divisorRep hw]

variable (Γ : Subgroup SL(2, ℤ))

/-- The invariance of `lift_divisorEval_comp_symbolRep`, stated for the representation of `Γ`
whose coinvariants are `𝕄_w(Γ; R)`. -/
private theorem lift_divisorEval_comp_symbolRep_subtype (hw : Even w) (γ : Γ) :
    TensorProduct.lift (divisorEval R w ∘ₗ (degreeZero R).subtype) ∘ₗ
        ((symbolRep R w).comp Γ.subtype) γ =
      TensorProduct.lift (divisorEval R w ∘ₗ (degreeZero R).subtype) :=
  lift_divisorEval_comp_symbolRep hw γ

/-- **Evaluation of modular symbols at the cusps.** For even `w`, the functional on `𝕄_w(Γ; R)`
sending `{α, β} ⊗ P` to `P(v_α) - P(v_β)`, where `v_α` is the primitive integral vector
representing `α` (`TauCeti.ModularSymbols.boundaryEval_symbol`). It is well defined on the
`Γ`-coinvariants because the values at the cusps are `SL(2, ℤ)`-invariant
(`TauCeti.ModularSymbols.evalCusp_mapGL_smul`). -/
noncomputable def boundaryEval (hw : Even w) : ModularSymbols R Γ w →ₗ[R] R :=
  Coinvariants.lift _ (TensorProduct.lift (divisorEval R w ∘ₗ (degreeZero R).subtype)) 
    (lift_divisorEval_comp_symbolRep_subtype Γ hw)

/-- On the class of `D ⊗ P`, the functional `boundaryEval` is `∑_α D(α) P(v_α)`. -/
@[simp]
theorem boundaryEval_mk (hw : Even w) (D : degreeZero R) (P : homogeneousSubmodule (Fin 2) R w) :
    boundaryEval Γ hw (Coinvariants.mk _ (D ⊗ₜ[R] P)) =
      Finsupp.linearCombination R (fun α ↦ evalCusp R w α P) (MonoidAlgebra.coeff D.1) := by
  simp [boundaryEval, divisorEval, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply]

/-- The functional `boundaryEval` sends `{α, β} ⊗ P` to `P(v_α) - P(v_β)`. -/
theorem boundaryEval_symbol (hw : Even w) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    boundaryEval Γ hw (symbol Γ α β P) = evalCusp R w α P - evalCusp R w β P := by
  simp [symbol_apply, Finsupp.linearCombination_single]

/-- On the symbols `{α, β} ⊗ P`, as a linear map in `P`, the functional `boundaryEval` is
`evalCusp α - evalCusp β`. -/
theorem boundaryEval_comp_symbol (hw : Even w) (α β : OnePoint ℚ) :
    boundaryEval Γ hw ∘ₗ symbol Γ α β = evalCusp R w α - evalCusp R w β :=
  LinearMap.ext (boundaryEval_symbol Γ hw α β)

end TauCeti.ModularSymbols
