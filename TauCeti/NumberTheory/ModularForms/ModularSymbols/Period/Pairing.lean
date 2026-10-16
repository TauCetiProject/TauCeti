/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Integral

/-!
# The raw period pairing

Let `f` be a cusp form of weight `w + 2` and `R` a commutative ring with an algebra map to `ℂ`
(typically `ℤ`). The raw period pairing of `f` sends a degree-zero `R`-divisor on the rational
cusps, tensored with a homogeneous binary form `P` of degree `w` with coefficients in `R`, to the
corresponding period of `f`. On the generators it is

`([α] - [β]) ⊗ P ↦ ∫_β^α f(z) P(z, 1) dz`.

The construction first pairs a divisor with the cusp values `∫_∞^α f(z) P(z, 1) dz`. Additivity
of periods shows that the difference of two such values is the integral from `β` to `α`. This
produces an `R`-bilinear pairing on
`Div⁰(ℙ¹(ℚ)) × Sym^w(R²)`, which is then lifted through the tensor product. The pairing is
`ℂ`-linear in `f`. Its invariance under the diagonal modular-group action and its descent to
modular symbols are in `TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Map`.

## Main definitions

* `TauCeti.ModularSymbols.rawPairing`: the raw period functional on
  `Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)`.

## Main results

* `TauCeti.ModularSymbols.rawPairing_single_sub_single_tmul`: the raw pairing sends
  `([α] - [β]) ⊗ P` to `∫_β^α f(z) P(z, 1) dz`.
* `TauCeti.ModularSymbols.rawPairing_add`, `TauCeti.ModularSymbols.rawPairing_smul`: the raw
  pairing is `ℂ`-linear in the cusp form.

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

variable {R : Type*} [CommRing R] [Algebra R ℂ]
variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ} {w : ℕ}
variable {F : Type*} [hF : FunLike F UpperHalfPlane ℂ]

variable (R) in
/-- The period of `f(z) P(z, 1) dz` from `∞` to the cusp `α`, as an `R`-linear functional in
the binary form `P` with coefficients in `R`. -/
private def periodAtCusp [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (α : OnePoint ℚ) :
    homogeneousSubmodule (Fin 2) R w →ₗ[R] ℂ where
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
    rw [periodIntegrand_smul_right, ← algebraMap_smul ℂ, cuspIntegral_smul, RingHom.id_apply,
      Algebra.smul_def]

/-- Evaluating `periodAtCusp` gives the integral from `∞` to the chosen cusp. -/
@[simp]
private theorem periodAtCusp_apply [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (α : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    periodAtCusp R f hk α P = cuspIntegral (periodIntegrand f P) ∞ α :=
  (rfl)

variable (R) in
/-- Pair a degree-zero divisor with a binary form by taking the coefficient-weighted sum of the
periods from `∞` to its cusps. -/
private def periodDivisorPairing [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2) :
    degreeZero R →ₗ[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] ℂ :=
  (((Finsupp.linearCombination R (periodAtCusp R f hk)) :
      (OnePoint ℚ →₀ R) →ₗ[R]
        (homogeneousSubmodule (Fin 2) R w →ₗ[R] ℂ)).comp
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap).comp (degreeZero R).subtype

variable (R) in
/-- The **raw period pairing** of a cusp form of weight `w + 2`. It is the `R`-linear
functional on `Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)` induced by integrating against binary forms. -/
def rawPairing [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2) :
    degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] ℂ :=
  TensorProduct.lift (periodDivisorPairing R f hk)

/-- On a pure tensor, the raw pairing is the coefficient-weighted sum of periods from `∞` to
the cusps in the divisor. -/
theorem rawPairing_tmul [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (D : degreeZero R)
    (P : homogeneousSubmodule (Fin 2) R w) :
    rawPairing R f hk (D ⊗ₜ[R] P) =
      Finsupp.linearCombination R
        (fun α ↦ cuspIntegral (periodIntegrand f P) ∞ α)
        (MonoidAlgebra.coeff D.1) := by
  simp [rawPairing, periodDivisorPairing, Finsupp.linearCombination_apply, periodAtCusp_apply]

/-- The raw pairing sends `([α] - [β]) ⊗ P` to the period from `β` to `α`. This is the
characteristic formula relating the analytic pairing to the generators of modular symbols. -/
@[simp]
theorem rawPairing_single_sub_single_tmul [CuspFormClass F 𝒢 k] (f : F)
    (hk : k = w + 2)
    (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    rawPairing R f hk
        (⟨single α (1 : R) - single β 1, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ[R] P) =
      cuspIntegral (periodIntegrand f P) β α := by
  rw [rawPairing_tmul]
  rw [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, map_sub,
    Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, one_smul]
  have hadd := cuspIntegral_periodIntegrand_add_adjacent f hk P ∞ β α
  rw [sub_eq_iff_eq_add]
  simpa only [add_comm] using hadd.symm

/-- The raw pairing is additive in the cusp form. -/
theorem rawPairing_add (f g : CuspForm 𝒢 k) (hk : k = w + 2) :
    rawPairing R (f + g) hk = rawPairing R f hk + rawPairing R g hk := by
  refine hom_ext_unimodular fun γ P ↦ ?_
  have hγ : 0 < ((mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact one_pos
  rw [LinearMap.add_apply, rawPairing_single_sub_single_tmul, rawPairing_single_sub_single_tmul,
    rawPairing_single_sub_single_tmul, FunLike.coe_add, periodIntegrand_add_left]
  exact cuspIntegral_add hγ (integrableOn_resToImagAxis_periodIntegrand_slash f hk P hγ)
    (integrableOn_resToImagAxis_periodIntegrand_slash g hk P hγ)

/-- The raw pairing is `ℂ`-homogeneous in the cusp form. -/
theorem rawPairing_smul [𝒢.HasDetOne] (c : ℂ) (f : CuspForm 𝒢 k) (hk : k = w + 2) :
    rawPairing R (c • f) hk = c • rawPairing R f hk := by
  refine hom_ext_unimodular fun γ P ↦ ?_
  rw [LinearMap.smul_apply, rawPairing_single_sub_single_tmul, rawPairing_single_sub_single_tmul,
    FunLike.coe_smul, periodIntegrand_smul_left, cuspIntegral_smul, smul_eq_mul]

end TauCeti.ModularSymbols

end
