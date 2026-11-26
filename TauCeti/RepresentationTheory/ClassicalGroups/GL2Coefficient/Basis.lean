/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GL2Coefficient
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basis

/-!
# The monomial basis of the coefficients `V_(a,b)` of `GL₂`

For integers `a ≥ b` the coefficient `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` of `GL₂`
(`TauCeti.gl2CoefficientRep k a b`) has the monomial basis `x^i y^{a-b-i} ⊗ 1`,
`0 ≤ i ≤ a - b`, where `x, y` is the standard basis of `k²`
(`TauCeti.gl2CoefficientBasis k a b`). The monomial `x^i y^{a-b-i} ⊗ 1` is a weight vector of
weight `(b + i, a - i)`: the diagonal matrix `diag(t₁, t₂)` scales it by `t₁^{b+i} t₂^{a-i}`.
When the weight characters of `k` separate weights (for instance over an infinite field), the
weight space of weight `(b + i, a - i)` is the line through `x^i y^{a-b-i} ⊗ 1`.

## Main definitions

* `TauCeti.gl2CoefficientBasis k a b`: the monomial basis of `V_(a,b)`, indexed by
  `Fin ((a - b).toNat + 1)`.

## Main results

* `TauCeti.gl2CoefficientBasis_apply`: the basis vector `i` is `x^i y^{a-b-i} ⊗ 1`.
* `TauCeti.gl2CoefficientBasis_mem_weightSpace`: it has weight `(b + i, a - i)`.
* `TauCeti.gl2CoefficientRep_diagGL_apply_basis`: `diag(t₁, t₂)` acts on it by
  `t₁^{b+i} t₂^{a-i}`.
* `TauCeti.weightSpace_gl2CoefficientRep_eq_span`: the weight space of weight `(b + i, a - i)` is
  the line through it, when weights are separated by their characters.
-/

public section

noncomputable section

open Matrix Module
open scoped TensorProduct

namespace TauCeti

variable (k : Type) [CommRing k] (a b : ℤ)

/-- The **monomial basis** of `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b`: the vector `i` is
`x^i y^{a-b-i} ⊗ 1`, where `x, y` is the standard basis of `k²`. -/
def gl2CoefficientBasis : Basis (Fin ((a - b).toNat + 1)) k (GL2CoefficientSpace k a b) :=
  ((((Pi.basisFun k (Fin 2)).symmetricPower (a - b).toNat).reindex
    (symFinTwoEquiv (a - b).toNat)).tensorProduct (Basis.singleton Unit k)).reindex
      (Equiv.prodPUnit _)

variable {k a b}

/-- The monomial basis vector `i` is `x^i y^{a-b-i} ⊗ 1`. -/
@[simp]
theorem gl2CoefficientBasis_apply (i : Fin ((a - b).toNat + 1)) :
    gl2CoefficientBasis k a b i =
      (Pi.basisFun k (Fin 2)).symmetricPower (a - b).toNat ((symFinTwoEquiv _).symm i) ⊗ₜ 1 := by
  simp [gl2CoefficientBasis]

/-- **The monomial `x^i y^{a-b-i} ⊗ 1` has weight `(b + i, a - i)`.** -/
theorem gl2CoefficientBasis_mem_weightSpace (hab : b ≤ a) (i : Fin ((a - b).toNat + 1)) :
    gl2CoefficientBasis k a b i ∈
      weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) ![b + i, a - i] := by
  have hw := tmul_mem_weightSpace_tprod
    (basis_mem_weightSpace_symPowerRep (k := k) ((symFinTwoEquiv (a - b).toNat).symm i))
    ((weightSpace_detPowerRep (k := k) (n := 2) b).symm ▸ Submodule.mem_top (x := (1 : k)))
  rw [weightOfMultiset_symFinTwoEquiv_symm] at hw
  have hi : (i : ℕ) ≤ (a - b).toNat := Nat.lt_succ_iff.mp i.isLt
  have hd : ((a - b).toNat : ℤ) = a - b := Int.toNat_of_nonneg (by omega)
  have hl : (![b + i, a - i] : Fin 2 → ℤ) =
      ![(i : ℤ), (((a - b).toNat - i : ℕ) : ℤ)] + fun _ ↦ b := by
    ext j
    fin_cases j <;> simp [Nat.cast_sub hi] <;> omega
  rw [gl2CoefficientBasis_apply, hl]
  exact hw

/-- **The diagonal matrix `diag(t₁, t₂)` acts on `x^i y^{a-b-i} ⊗ 1` by `t₁^{b+i} t₂^{a-i}`.** -/
theorem gl2CoefficientRep_diagGL_apply_basis (hab : b ≤ a) (t : Fin 2 → kˣ)
    (i : Fin ((a - b).toNat + 1)) :
    gl2CoefficientRep k a b (diagGL t) (gl2CoefficientBasis k a b i : GL2CoefficientSpace k a b) =
      ((t 0 ^ (b + i) * t 1 ^ (a - i) : kˣ) : k) • gl2CoefficientBasis k a b i := by
  rw [apply_of_mem_weightSpace (W := GL2CoefficientSpace k a b)
    (gl2CoefficientBasis_mem_weightSpace hab i)]
  rw [weightChar_apply, torusCharacter_def, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The weight space of weight `(b + i, a - i)` is the line through `x^i y^{a-b-i} ⊗ 1`**,
when the weight characters of `k` separate weights (for instance over an infinite field,
`TauCeti.weightChar_injective`). -/
theorem weightSpace_gl2CoefficientRep_eq_span [IsCancelMulZero k]
    (hchar : Function.Injective (weightChar k (κ := Fin 2))) (hab : b ≤ a)
    (i : Fin ((a - b).toNat + 1)) :
    weightSpace (W := GL2CoefficientSpace k a b) (gl2CoefficientRep k a b) ![b + i, a - i] =
      Submodule.span k {gl2CoefficientBasis k a b i} := by
  have hwt : Function.Injective
      fun i : Fin ((a - b).toNat + 1) ↦ (![b + (i : ℕ), a - (i : ℕ)] : Fin 2 → ℤ) :=
    fun _ _ h ↦ Fin.ext (by simpa using congrFun h 0)
  exact Basis.weightSpace_eq_span (W := GL2CoefficientSpace k a b) (ρ := gl2CoefficientRep k a b)
    (gl2CoefficientBasis k a b)
    (gl2CoefficientBasis_mem_weightSpace (k := k) hab) hchar hwt i

end TauCeti
