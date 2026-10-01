/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Pairing

/-!
# The period map

Let `Γ ≤ SL(2, ℤ)` be a subgroup of finite index, `R` a commutative ring with an algebra map to
`ℂ` (typically `ℤ`), and `f` a cusp form of weight `k = w + 2` on `Γ`. The raw period pairing
`TauCeti.ModularSymbols.rawPairing R f` sends `([α] - [β]) ⊗ P` in `Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)` to
the period `∫_β^α f(z) P(z, 1) dz`. This file shows that it is invariant under the diagonal
action of `Γ`, and hence descends to the module of modular symbols `𝕄_w(Γ; R)`, the
`Γ`-coinvariants. The invariance is the substitution `z ↦ γz` in the period integral together
with the slash invariance `f ∣[k] γ = f` for `γ ∈ Γ`
(`TauCeti.ModularSymbols.cuspIntegral_periodIntegrand_mapGL_smul_of_mem`).

The descended functionals are `ℂ`-linear in `f`, so they assemble into the **period map**
`S_k(Γ) →ₗ[ℂ] (𝕄_w(Γ; R) →ₗ[R] ℂ)`. It sends a cusp form to an `R`-linear functional on the
modular symbols, rather than a form to a symbol: symbols are cycles and forms are integrated over
them, so for `R = ℤ` the integral structure stays on the source of the functionals. On the
symbol `{α, β} ⊗ P` the functional of `f` is the period `∫_β^α f(z) P(z, 1) dz`.

## Main definitions

* `TauCeti.ModularSymbols.periodMap R Γ hk`: the period map
  `S_k(Γ) →ₗ[ℂ] (𝕄_w(Γ; R) →ₗ[R] ℂ)`, for `k = w + 2`.

## Main results

* `TauCeti.ModularSymbols.rawPairing_comp_symbolRep`: the raw pairing of a cusp form on `Γ` is
  invariant under the diagonal action of `Γ` on `Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)`.
* `TauCeti.ModularSymbols.periodMap_mk`: on the class of `x`, the functional of `f` is the raw
  pairing of `f` with `x`.
* `TauCeti.ModularSymbols.periodMap_symbol`: the period map sends the symbol `{α, β} ⊗ P` to
  `∫_β^α f(z) P(z, 1) dz`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2, (8.2.15)–(8.2.16).
* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, Izv. Akad. Nauk SSSR
  Ser. Mat. **36** (1972), 19–66, §1.
* W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics **79**,
  American Mathematical Society, 2007, §8.5.
-/

public noncomputable section

open Matrix.SpecialLinearGroup MonoidAlgebra MvPolynomial OnePoint Representation TensorProduct
open scoped MatrixGroups ModularForm

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] [Algebra R ℂ]
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {w : ℕ}

/-- **Invariance of the raw pairing.** For a cusp form `f` of weight `w + 2` on `Γ` and `γ ∈ Γ`,
the raw pairing of `f` is invariant under the diagonal action of `γ` on
`Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)`: `⟪f, {γα, γβ} ⊗ (P ∣ γ⁻¹)⟫ = ⟪f, {α, β} ⊗ P⟫`. -/
theorem rawPairing_comp_symbolRep {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (Γ.map (mapGL ℝ)) k] (f : F) (hk : k = w + 2) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    rawPairing R f hk ∘ₗ symbolRep R w γ = rawPairing R f hk := by
  refine hom_ext_unimodular fun g P ↦ ?_
  rw [LinearMap.comp_apply, symbolRep_tmul, degreeZeroRep_apply,
    degreeZeroGLRep_single_sub_single, rawPairing_single_sub_single_tmul,
    rawPairing_single_sub_single_tmul, cuspIntegral_periodIntegrand_mapGL_smul_of_mem f hk _ hγ,
    binaryFormRep_binaryFormSLRep]

/-- The descent of the raw pairing of `f` to `𝕄_w(Γ; R)`, the underlying function of the period
map. -/
private def periodFunctional (hk : k = w + 2) (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    ModularSymbols R Γ w →ₗ[R] ℂ :=
  Coinvariants.lift _ (rawPairing R f hk) fun γ ↦ by
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, rawPairing_comp_symbolRep f hk γ.2]

-- Stated through `periodFunctional` so that it can be rewritten with: the linear maps produced by
-- `Coinvariants.lift` carry the additive structure of `ℂ` as an `AddCommGroup`, which does not
-- match `rawPairing` up to reducible defeq.
private theorem periodFunctional_mk (hk : k = w + 2) (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    periodFunctional hk f (Coinvariants.mk _ x) = rawPairing R f hk x :=
  Coinvariants.lift_mk _ _ _ x

variable (R Γ) in
/-- The **period map** `S_k(Γ) →ₗ[ℂ] (𝕄_w(Γ; R) →ₗ[R] ℂ)` for `k = w + 2`: a cusp form `f` on
`Γ` is sent to the `R`-linear functional on the modular symbols induced by its raw period
pairing, so that `{α, β} ⊗ P ↦ ∫_β^α f(z) P(z, 1) dz` (`periodMap_symbol`). For `R = ℤ` this is
the pairing of cusp forms with the integral modular symbols. -/
def periodMap (hk : k = w + 2) :
    CuspForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ] ModularSymbols R Γ w →ₗ[R] ℂ where
  toFun := periodFunctional hk
  map_add' f g := Coinvariants.hom_ext <| LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply, periodFunctional_mk,
      periodFunctional_mk, periodFunctional_mk, rawPairing_add, LinearMap.add_apply]
  map_smul' c f := Coinvariants.hom_ext <| LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, RingHom.id_apply, LinearMap.smul_apply,
      periodFunctional_mk, periodFunctional_mk, rawPairing_smul, LinearMap.smul_apply]

/-- On the class of `x ∈ Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)`, the period map is the raw pairing. -/
@[simp]
theorem periodMap_mk (hk : k = w + 2) (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    periodMap R Γ hk f (Coinvariants.mk _ x) = rawPairing R f hk x :=
  periodFunctional_mk hk f x

/-- **The period map on symbols**: the functional of `f` sends the modular symbol `{α, β} ⊗ P` to
the period `∫_β^α f(z) P(z, 1) dz`. Not `@[simp]`: simp proves it from `symbol_apply`,
`periodMap_mk` and `rawPairing_single_sub_single_tmul`. -/
theorem periodMap_symbol (hk : k = w + 2) (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (α β : OnePoint ℚ) (P : homogeneousSubmodule (Fin 2) R w) :
    periodMap R Γ hk f (symbol Γ α β P) = cuspIntegral (periodIntegrand f P) β α := by
  rw [symbol_apply, periodMap_mk, rawPairing_single_sub_single_tmul]

end TauCeti.ModularSymbols

end
