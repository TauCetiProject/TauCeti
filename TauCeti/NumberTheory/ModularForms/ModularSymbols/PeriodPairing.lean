/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.PeriodIntegral

/-!
# The raw period pairing

Let `f` be a cusp form of weight `w + 2`. Its raw period pairing sends a degree-zero divisor on
the rational cusps, tensored with a homogeneous binary form `P` of degree `w`, to the
corresponding period of `f`. On the generators it is

`([α] - [β]) ⊗ P ↦ ∫_β^α f(z) P(z, 1) dz`.

The construction first pairs a divisor with the cusp values `∫_∞^α f(z) P(z, 1) dz`. Additivity
of periods shows that the difference of two such values is the integral from `β` to `α`. This
produces an integral bilinear pairing on
`Div⁰(ℙ¹(ℚ)) × Sym^w(ℤ²)`, which is then lifted through the tensor product. The next stage of the
period-map construction proves invariance under the diagonal modular-group action and descends
this pairing to modular symbols.

## Main definitions

* `TauCeti.ModularSymbols.rawPairing`: the raw period functional on
  `Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(ℤ²)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2, (8.2.15)–(8.2.16).
* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, Izv. Akad. Nauk SSSR
  Ser. Mat. **36** (1972), 19–66, §1.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup MonoidAlgebra MvPolynomial OnePoint TensorProduct
open scoped MatrixGroups ModularForm

namespace TauCeti.ModularSymbols

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ} {w : ℕ}
variable {F : Type*} [hF : FunLike F UpperHalfPlane ℂ]

/-- The period of `f(z) P(z, 1) dz` from `∞` to the cusp `α`, as a `ℤ`-linear functional in
the integral binary form `P`. -/
private def periodAtCusp [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (α : OnePoint ℚ) :
    homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] ℂ where
  toFun P := cuspIntegral (periodIntegrand f P) ∞ α
  map_add' P Q := by
    rw [periodIntegrand_add_right]
    rcases eq_or_ne (∞ : OnePoint ℚ) α with hα | hα
    · subst α
      simp
    · obtain ⟨g, hg, hzero, hinf⟩ := exists_smul_zero_smul_infty hα
      rw [← hzero, ← hinf]
      exact cuspIntegral_add hg
        (integrableOn_resToImagAxis_periodIntegrand_slash f hk P hg)
        (integrableOn_resToImagAxis_periodIntegrand_slash f hk Q hg)
  map_smul' c P := by
    rw [periodIntegrand_smul_right, ← Int.cast_smul_eq_zsmul ℂ, cuspIntegral_smul]
    simp

/-- Evaluating `periodAtCusp` gives the integral from `∞` to the chosen cusp. -/
@[simp]
private theorem periodAtCusp_apply [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (α : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) ℤ w) :
    periodAtCusp f hk α P = cuspIntegral (periodIntegrand f P) ∞ α :=
  (rfl)

/-- Pair a degree-zero divisor with an integral binary form by taking the coefficient-weighted
sum of the periods from `∞` to its cusps. -/
private def periodDivisorPairing [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2) :
    degreeZero ℤ →ₗ[ℤ] homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] ℂ :=
  (((Finsupp.linearCombination ℤ (periodAtCusp f hk)) :
      (OnePoint ℚ →₀ ℤ) →ₗ[ℤ]
        (homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] ℂ)).comp
      (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap).comp (degreeZero ℤ).subtype

/-- The **raw period pairing** of a cusp form of weight `w + 2`. It is the `ℤ`-linear
functional on `Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(ℤ²)` induced by integrating against binary forms. -/
def rawPairing [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2) :
    degreeZero ℤ ⊗[ℤ] homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] ℂ :=
  TensorProduct.lift (periodDivisorPairing f hk)

/-- On a pure tensor, the raw pairing is the coefficient-weighted sum of periods from `∞` to
the cusps in the divisor. -/
theorem rawPairing_tmul [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (D : degreeZero ℤ)
    (P : homogeneousSubmodule (Fin 2) ℤ w) :
    rawPairing f hk (D ⊗ₜ[ℤ] P) =
      Finsupp.linearCombination ℤ
        (fun α ↦ cuspIntegral (periodIntegrand f P) ∞ α)
        (MonoidAlgebra.coeff D.1) := by
  -- `change` avoids ambiguity between the two definitionally equal canonical `ℤ`-module
  -- instances on a tensor product, which prevents `rw [TensorProduct.lift.tmul]` from matching.
  change periodDivisorPairing f hk D P = _
  simp [periodDivisorPairing, Finsupp.linearCombination_apply, periodAtCusp_apply]

/-- The raw pairing sends `([α] - [β]) ⊗ P` to the period from `β` to `α`. This is the
characteristic formula relating the analytic pairing to the generators of modular symbols. -/
@[simp]
theorem rawPairing_single_sub_single_tmul [CuspFormClass F 𝒢 k] (f : F)
    (hk : k = w + 2)
    (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) ℤ w) :
    rawPairing f hk
        (⟨single α (1 : ℤ) - single β 1, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ[ℤ] P) =
      cuspIntegral (periodIntegrand f P) β α := by
  rw [rawPairing_tmul]
  rw [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, map_sub,
    Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul]
  have hadd := cuspIntegral_periodIntegrand_add_adjacent f hk P ∞ β α
  rw [sub_eq_iff_eq_add]
  simpa only [add_comm, one_smul] using hadd.symm

end TauCeti.ModularSymbols

end
