/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AddChar.SelfDualMeasure
public import TauCeti.NumberTheory.NumberField.Global.Adeles.AddChar
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place

import TauCeti.NumberTheory.LocalField.Topology

/-!
# The standard additive characters of the completions of a number field at finite places

Let `K` be a number field, `v` a finite place of `K`, `K_v` the completion, `𝒪_v` its ring of
integers and `𝔇` the different of `K / ℚ`, with `d_v = ord_v 𝔇`. The standard additive character
`ψ_f` of the finite adeles (`TauCeti.GlobalNumberFields.finiteAdeleAddChar`) restricts to `K_v`,
placed in the finite adeles as the adeles supported at `v`. This restriction is the **standard
character** `ψ_v = adicCompletionAddChar K v` of `K_v`. This file proves:

* `ψ_f` is the product of the `ψ_v`: `ψ_f (a) = ∏_{v ∈ S} ψ_v (a_v)` for every finite set `S` of
  places outside which `a` is integral (`finiteAdeleAddChar_eq_prod`).
* The annihilator of `𝒪_v` under `(x, y) ↦ ψ_v (x y)` is the local inverse different
  `𝔇_v⁻¹ = {y | Valued.v y ≤ exp d_v}` (`forall_adicCompletionAddChar_mul_eq_one_iff`). This is
  the local form of the adelic statement `forall_finiteAdeleAddChar_mul_eq_one_iff`, from which it
  is deduced. In particular `ψ_v` is nontrivial and its conductor exponent is `d_v`
  (`conductorExponent_adicCompletionAddChar`): the largest fractional ideal on which `ψ_v` is
  trivial is `𝔇_v⁻¹`.
* The self-dual Haar measure of `ψ_v` (`AddChar.selfDualMeasure`) is `N(𝔇_v)^(-1/2) dx_v`, where
  `dx_v` gives `𝒪_v` mass one and `N(𝔇_v) = N(v)^(d_v)`
  (`selfDualMeasure_adicCompletionAddChar`); it gives `𝒪_v` the mass `N(𝔇_v)^(-1/2)`, which is
  `1` for all but finitely many `v` (`eventually_selfDualMeasure_adicCompletionAddChar_eq`).

## Sign convention

On `K` the finite part `ψ_f` is `exp (2πi Tr_{K/ℚ} ·)`, and the infinite part of the standard
adelic character carries the opposite sign. Tate's local character `exp (-2πi {x}_p)` (Tate, §2.2)
at the finite places is the inverse `ψ_v⁻¹`. A character and its inverse have the same
annihilators, conductor exponent (`AddChar.conductorExponent_inv`) and self-dual measure
(`AddChar.selfDualMeasure_inv`), so the annihilator, conductor-exponent and self-dual-measure
statements here hold verbatim for `ψ_v⁻¹`.

## Main definitions

* `TauCeti.GlobalNumberFields.adicCompletionAddChar`: the standard character of `K_v`.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleAddChar_eq_prod`: `ψ_f = ∏_v ψ_v`.
* `TauCeti.GlobalNumberFields.forall_adicCompletionAddChar_mul_eq_one_iff`: the annihilator of
  `𝒪_v` is the local inverse different.
* `TauCeti.GlobalNumberFields.conductorExponent_adicCompletionAddChar`: `ν(ψ_v) = d_v`.
* `TauCeti.GlobalNumberFields.selfDualMeasure_adicCompletionAddChar`,
  `TauCeti.GlobalNumberFields.selfDualMeasure_adicCompletionAddChar_adicCompletionIntegers`: the
  self-dual measure is `N(𝔇_v)^(-1/2) dx_v`.

## References

The statements at finite places are adapted from `finiteLocalStandardCharacter`,
`finiteLocalStandardCharacter_annihilator_integers`, `finiteLocalAdditiveTamagawaMeasure` and
`finiteLocalAdditiveTamagawaMeasure_selfDual` in `RiemannMasullo/AppA_AlgebraicNT/Sec3.lean` of
the Riemann–Masullo formalization (https://github.com/mccorvie/riemann-masullo). There the local
annihilator is computed through local traces; here it is read off the adelic annihilator.

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory* (1967), §2.2.
* A. Weil, *Basic Number Theory*, Chapter VII, §2.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing IsDedekindDomain.HeightOneSpectrum
  NumberField MeasureTheory Measure ValuativeRel TauCeti
open scoped NumberField nonZeroDivisors ENNReal

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **The standard additive character `ψ_v` of the completion `K_v`** of a number field at a
finite place `v`: the restriction of the standard character `ψ_f` of the finite adeles to the
adeles supported at `v`. It is trivial on `𝒪_v`, the annihilator of `𝒪_v` under
`(x, y) ↦ ψ_v (x y)` is the local inverse different
(`forall_adicCompletionAddChar_mul_eq_one_iff`), and `ψ_f` is the product of the `ψ_v`
(`finiteAdeleAddChar_eq_prod`). -/
def adicCompletionAddChar : AddChar (v.adicCompletion K) Circle :=
  (finiteAdeleAddChar K).compAddMonoidHom (single K v).toLinearMap.toAddMonoidHom

variable {K v}

/-- `ψ_v (x)` is `ψ_f` of the finite adele supported at `v` with `v`-component `x`. -/
theorem adicCompletionAddChar_apply (x : v.adicCompletion K) :
    adicCompletionAddChar K v x = finiteAdeleAddChar K (single K v x) :=
  (rfl)

/-- `ψ_v` is trivial on the local integers `𝒪_v`. -/
theorem adicCompletionAddChar_apply_of_mem {x : v.adicCompletion K}
    (hx : x ∈ v.adicCompletionIntegers K) : adicCompletionAddChar K v x = 1 :=
  finiteAdeleAddChar_apply_of_mem_integralAdeles <|
    mem_integralAdeles.2 ((single_mem_integralAdeles_iff v).2 hx)

/-- `ψ_v` is locally constant, being trivial on the open subgroup `𝒪_v`. -/
theorem isLocallyConstant_adicCompletionAddChar :
    IsLocallyConstant (adicCompletionAddChar K v) :=
  isLocallyConstant_finiteAdeleAddChar.comp_continuous (single K v).continuous

/-- `ψ_v` is continuous. -/
@[continuity, fun_prop]
theorem continuous_adicCompletionAddChar : Continuous (adicCompletionAddChar K v) :=
  isLocallyConstant_adicCompletionAddChar.continuous

/-- **`ψ_f` is the product of the local characters `ψ_v`.** If the finite adele `a` is integral at
every place outside the finite set `S`, then `ψ_f (a) = ∏_{v ∈ S} ψ_v (a_v)`. -/
theorem finiteAdeleAddChar_eq_prod (a : FiniteAdeleRing (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w ∉ S, a w ∈ w.adicCompletionIntegers K) :
    finiteAdeleAddChar K a = ∏ u ∈ S, adicCompletionAddChar K u (a u) := by
  classical
  -- `a` differs from the sum of its components at `S` by an integral finite adele
  have hint : a - ∑ u ∈ S, single K u (a u) ∈ integralAdeles (𝓞 K) K := by
    refine mem_integralAdeles.2 fun w ↦ ?_
    rw [FiniteAdeleRing.sub_apply, sum_single_apply]
    split_ifs with hw
    · rw [sub_self]
      exact zero_mem _
    · rw [sub_zero]
      exact hS w hw
  calc finiteAdeleAddChar K a
      = finiteAdeleAddChar K (∑ u ∈ S, single K u (a u) + (a - ∑ u ∈ S, single K u (a u))) := by
        rw [add_sub_cancel]
    _ = ∏ u ∈ S, adicCompletionAddChar K u (a u) := by
        rw [finiteAdeleAddChar_add_of_mem_integralAdeles hint, AddChar.map_sum_eq_prod]
        simp only [adicCompletionAddChar_apply]

/-- In `𝔸ᶠ`, the products of the finite adele supported at `v` with `y` by integral finite adeles
are the finite adeles supported at `v` with component in `y 𝒪_v`. -/
private theorem forall_single_mul_iff (y : v.adicCompletion K) :
    (∀ x ∈ v.adicCompletionIntegers K, adicCompletionAddChar K v (x * y) = 1) ↔
      ∀ u ∈ integralAdeles (𝓞 K) K, finiteAdeleAddChar K (single K v y * u) = 1 := by
  refine ⟨fun h u hu ↦ ?_, fun h x hx ↦ ?_⟩
  · rw [← single_mul, mul_comm]
    exact h _ (mem_integralAdeles.1 hu v)
  · have hu := h (single K v x) (mem_integralAdeles.2 ((single_mem_integralAdeles_iff v).2 hx))
    rwa [← single_mul, single_apply_self, mul_comm] at hu

/-- The `v`-adic order of the inverse different is `-d_v`, minus the order of the different. -/
private theorem count_dual_one :
    FractionalIdeal.count K v (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) =
      -FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coeIdeal_differentIdeal ℤ ℚ, FractionalIdeal.count_inv, neg_neg]

/-- **The annihilator of `𝒪_v` is the local inverse different.** For `y ∈ K_v`, `ψ_v (x y) = 1`
for every `x ∈ 𝒪_v` exactly when `y ∈ 𝔇_v⁻¹`, that is, `Valued.v y ≤ exp d_v` where `d_v` is the
`v`-adic order of the different `𝔇` of `K / ℚ`. -/
theorem forall_adicCompletionAddChar_mul_eq_one_iff (y : v.adicCompletion K) :
    (∀ x ∈ v.adicCompletionIntegers K, adicCompletionAddChar K v (x * y) = 1) ↔
      Valued.v y ≤ WithZero.exp
        (FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [forall_single_mul_iff, forall_finiteAdeleAddChar_mul_eq_one_iff,
    single_mem_finiteAdelicIdeal_iff, Units.val_mk0, count_dual_one, neg_neg]

/-- The standard character `ψ_v` is nontrivial. -/
theorem adicCompletionAddChar_ne_one : adicCompletionAddChar K v ≠ 1 := by
  intro h
  set d := FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)
  obtain ⟨y, hy⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (d + 1))
  have := (forall_adicCompletionAddChar_mul_eq_one_iff y).1 fun x _ ↦ by rw [h, _root_.one_apply]
  rw [hy, WithZero.exp_le_exp] at this
  omega

/-- **The conductor exponent of `ψ_v` is the order `d_v` of the different at `v`**: the largest
fractional ideal of `K_v` on which `ψ_v` is trivial is the local inverse different
`𝔇_v⁻¹ = 𝓂 ^ (-d_v)`. -/
theorem conductorExponent_adicCompletionAddChar :
    (adicCompletionAddChar K v).conductorExponent =
      FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by
  set d := FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)
  set ψ := adicCompletionAddChar K v
  have h0 := AddChar.setOf_eq_one_mem_nhds_zero (continuous_adicCompletionAddChar (K := K) (v := v))
  -- both descriptions of the annihilator of `𝒪_v` give the same balls `Valued.v y ≤ exp n`
  have key (y : v.adicCompletion K) :
      Valued.v y ≤ WithZero.exp ψ.conductorExponent ↔ Valued.v y ≤ WithZero.exp d := by
    rw [← forall_adicCompletionAddChar_mul_eq_one_iff, ← neg_neg ψ.conductorExponent,
      ← valuation_le_uniformizer_zpow_iff_valued_le, ← sub_zero (-ψ.conductorExponent),
      ← AddChar.forall_mul_eq_one_iff_valuation_le h0 adicCompletionAddChar_ne_one 0]
    simp only [zpow_zero, ← mem_adicCompletionIntegers_iff_valuation_le_one]
  obtain ⟨y, hy⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp d)
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp ψ.conductorExponent)
  have h₁ := (key y).2 (by rw [hy])
  have h₂ := (key z).1 (by rw [hz])
  rw [hy, WithZero.exp_le_exp] at h₁
  rw [hz, WithZero.exp_le_exp] at h₂
  omega

/-! ### The self-dual measure -/

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

/-- **The self-dual measure of `ψ_v` is `N(𝔇_v)^(-1/2) dx_v`**, where `dx_v` is the Haar measure
giving `𝒪_v` mass one and `N(𝔇_v) = N(v)^(d_v)` is the absolute norm of the local different. -/
theorem selfDualMeasure_adicCompletionAddChar :
    (adicCompletionAddChar K v).selfDualMeasure =
      ((Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (-(FractionalIdeal.count K v
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) : ℝ) / 2)) •
        addHaarMeasure (integerPositiveCompacts (v.adicCompletion K)) := by
  rw [addHaarMeasure_unique (adicCompletionAddChar K v).selfDualMeasure
      (integerPositiveCompacts (v.adicCompletion K)), coe_integerPositiveCompacts,
    AddChar.selfDualMeasure_integer, conductorExponent_adicCompletionAddChar,
    natCard_residueField_adicCompletion_eq_absNorm]

/-- **The self-dual mass of `𝒪_v`.** The self-dual measure of `ψ_v` gives `𝒪_v` the mass
`N(𝔇_v)^(-1/2) = N(v)^(-d_v / 2)`. -/
theorem selfDualMeasure_adicCompletionAddChar_adicCompletionIntegers :
    (adicCompletionAddChar K v).selfDualMeasure (v.adicCompletionIntegers K) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (-(FractionalIdeal.count K v
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) : ℝ) / 2) := by
  have h : ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) = 𝒪[v.adicCompletion K] := by
    rw [integer_eq_adicCompletionIntegers]
    rfl
  rw [h, AddChar.selfDualMeasure_integer, conductorExponent_adicCompletionAddChar,
    natCard_residueField_adicCompletion_eq_absNorm]

variable (K) in
/-- **The self-dual measures are almost all normalized.** For all but finitely many finite places
`v`, namely those not dividing the different, `ψ_v` has conductor exponent `0` and its self-dual
measure is the Haar measure `dx_v` giving `𝒪_v` mass one. This is the condition needed for the
restricted product of the self-dual measures to be defined. -/
theorem eventually_selfDualMeasure_adicCompletionAddChar_eq
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (adicCompletionAddChar K v).conductorExponent = 0 ∧
        (adicCompletionAddChar K v).selfDualMeasure =
          addHaarMeasure (integerPositiveCompacts (v.adicCompletion K)) := by
  filter_upwards [FractionalIdeal.finite_factors
    (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)] with v hv
  refine ⟨conductorExponent_adicCompletionAddChar.trans hv, ?_⟩
  rw [selfDualMeasure_adicCompletionAddChar, hv, Int.cast_zero, neg_zero, zero_div,
    ENNReal.rpow_zero, one_smul]

end TauCeti.GlobalNumberFields
