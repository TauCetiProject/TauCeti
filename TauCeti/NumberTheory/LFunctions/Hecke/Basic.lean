/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.LFunctions.Hecke.Primitive
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight

/-!
# Presented Hecke L-functions of ray class characters

For a ray class character `χ` of a modulus `𝔪`, `TauCeti.LFunctions.heckeLFunctionC χ` is the
canonical meromorphic continuation (`TauCeti.meromorphicContinuation`) of the L-series
`L(χ, s) = ∑_𝔞 χ(𝔞) N𝔞 ^ (-s)`, summed over the ideals prime to the finite part of `𝔪`, with
the coefficients of the unitary weight `RayClassCharacter.toUnitaryIdealWeight`. The series
depends on the presentation and not only on the character: presenting `χ` at a multiple `𝔫` of
`𝔪` deletes the Euler factors at the primes dividing `𝔫` but not `𝔪`. Those factors are
`TauCeti.LFunctions.eulerCorrection χ 𝔫 s = ∏_{𝔭 ∣ 𝔫, 𝔭 ∤ 𝔪} (1 - χ(𝔭) N𝔭 ^ (-s))`, an entire
function without zeros on `Re s > 0`.

The comparison of presentations holds on `Re s > 1`, where the series converge absolutely, and as
an equality of punctured germs at every point of the plane. The germ statements make no assertion
about the values at the point itself: where a zero of the correction factor meets a pole, the
normal form of the product need not be the product of the values, so no identity of values on the
whole plane is claimed. The comparison holds whether or not a continuation to the plane exists,
because dividing by the correction factor turns a continuation of one series into a continuation of
the other. Every presented series is in particular the series of the primitive character
`PrimitiveRayClassCharacter.of χ` times the Euler factors at the primes dividing `𝔪` but not the
conductor.

## Main definitions

* `TauCeti.LFunctions.heckeLFunctionC`: the continued L-series of a ray class character at its
  presentation modulus.
* `TauCeti.LFunctions.eulerCorrection`: the Euler factors deleted by presenting a character at a
  larger modulus.

## Main results

* `TauCeti.LFunctions.LSeries_toUnitaryIdealWeight_induced`: on `Re s > 1`, inducing multiplies
  the L-series by the deleted Euler factors.
* `TauCeti.LFunctions.heckeLFunctionC_induced` and
  `TauCeti.LFunctions.heckeLFunctionC_induced_eventuallyEq`: the same for the continued
  functions, on `Re s > 1` and as germs everywhere.
* `TauCeti.LFunctions.heckeLFunctionC_eq_primitive` and
  `TauCeti.LFunctions.heckeLFunctionC_eventuallyEq_primitive`: the comparison with the primitive
  character.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section
noncomputable section

open Filter Set IsDedekindDomain
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-! ### The deleted Euler factors -/

open Classical in
/-- **The Euler factors deleted by a larger presentation**:
`∏_{𝔭 ∣ 𝔫, 𝔭 ∤ 𝔪} (1 - χ(𝔭) N𝔭 ^ (-s))` for a ray class character `χ` of `𝔪`. The value
`χ(𝔭)` is read through the ideal weight `RayClassCharacter.toMultiplicativeIdealWeight`, which is
total, so no ray class is read off a prime dividing `𝔪`. -/
def eulerCorrection (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K) (s : ℂ) : ℂ :=
  ∏ 𝔭 ∈ 𝔫.support \ 𝔪.support,
    (1 - χ.toMultiplicativeIdealWeight 𝔭.asIdeal * (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))

/-- The deleted Euler factors may be taken over all primes dividing `𝔫`: the factor at a prime
dividing `𝔪` is `1`, since the weight vanishes there. -/
theorem eulerCorrection_eq_prod_support (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K) (s : ℂ) :
    eulerCorrection χ 𝔫 s = ∏ 𝔭 ∈ 𝔫.support,
      (1 - χ.toMultiplicativeIdealWeight 𝔭.asIdeal * (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) := by
  classical
  rw [eulerCorrection]
  refine Finset.prod_subset Finset.sdiff_subset fun 𝔭 h𝔭 h𝔭' ↦ ?_
  have hbad : 𝔭 ∈ χ.toMultiplicativeIdealWeight.badPrimes := by
    rw [RayClassCharacter.badPrimes_toMultiplicativeIdealWeight]
    by_contra h
    exact h𝔭' (Finset.mem_sdiff.mpr ⟨h𝔭, h⟩)
  rw [MultiplicativeIdealWeight.mem_badPrimes.mp hbad, zero_mul, sub_zero]

/-- No Euler factor is deleted when the primes dividing `𝔫` already divide `𝔪`. -/
theorem eulerCorrection_of_support_subset (χ : RayClassCharacter 𝔪) (h : 𝔫.support ⊆ 𝔪.support)
    (s : ℂ) : eulerCorrection χ 𝔫 s = 1 := by
  classical
  rw [eulerCorrection, Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.prod_empty]

/-- No Euler factor is deleted at the presentation modulus itself. -/
@[simp]
theorem eulerCorrection_self (χ : RayClassCharacter 𝔪) (s : ℂ) : eulerCorrection χ 𝔪 s = 1 :=
  eulerCorrection_of_support_subset χ subset_rfl s

/-- For the trivial character of the trivial modulus, presenting at `𝔫` deletes the Euler factors
`∏_{𝔭 ∣ 𝔫} (1 - N𝔭 ^ (-s))` of the Dedekind zeta function. -/
theorem eulerCorrection_one (𝔫 : Modulus K) (s : ℂ) :
    eulerCorrection (1 : RayClassCharacter (Modulus.one K)) 𝔫 s =
      ∏ 𝔭 ∈ 𝔫.support, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) := by
  rw [eulerCorrection_eq_prod_support]
  refine Finset.prod_congr rfl fun 𝔭 _ ↦ ?_
  simp [MultiplicativeIdealWeight.ofBadPrimes_apply, 𝔭.ne_bot]

/-- The deleted Euler factors form an entire function of `s`. -/
theorem differentiable_eulerCorrection (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K) :
    Differentiable ℂ (eulerCorrection χ 𝔫) := by
  classical
  refine Differentiable.fun_finsetProd fun 𝔭 _ ↦ (differentiable_const 1).sub
    ((differentiable_const _).mul (differentiable_neg.const_cpow (.inl ?_)))
  exact 𝔭.natCast_absNorm_ne_zero

/-- The deleted Euler factors have no zero on `Re s > 0`: there `|χ(𝔭) N𝔭 ^ (-s)| < 1`. -/
theorem eulerCorrection_ne_zero (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K) {s : ℂ}
    (hs : 0 < s.re) : eulerCorrection χ 𝔫 s ≠ 0 := by
  classical
  refine Finset.prod_ne_zero_iff.mpr fun 𝔭 _ h ↦ ?_
  have hlt : ‖χ.toMultiplicativeIdealWeight 𝔭.asIdeal * (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)‖ <
      1 := by
    rw [norm_mul, Complex.cpow_neg, norm_inv]
    have hnorm := 𝔭.one_lt_norm_absNorm_cpow hs
    have hχ : ‖χ.toMultiplicativeIdealWeight 𝔭.asIdeal‖ ≤ 1 := by
      simpa using χ.toUnitaryIdealWeight.norm_le_one 𝔭.asIdeal
    calc _ ≤ 1 * ‖(Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖⁻¹ := by gcongr
      _ < 1 := by rw [one_mul]; exact inv_lt_one_of_one_lt₀ hnorm
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-! ### The presented series and its continuation -/

/-- **Inducing deletes Euler factors, on `Re s > 1`.** Presenting a ray class character `χ` of `𝔪`
at a multiple `𝔫` of `𝔪` multiplies its L-series by `eulerCorrection χ 𝔫 s`. -/
theorem LSeries_toUnitaryIdealWeight_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (normCoeff K (χ.induced h).toUnitaryIdealWeight.toIdealArithmeticFunction) s =
      LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s *
        eulerCorrection χ 𝔫 s := by
  rw [RayClassCharacter.toUnitaryIdealWeight_induced,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_restrictAway,
    MultiplicativeIdealWeight.LSeries_restrictAway _ _ (by
      simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using
        summable_idealTerm_of_unitary_of_one_lt_re χ.toUnitaryIdealWeight hs),
    eulerCorrection_eq_prod_support]
  simp only [RayClassCharacter.val_toUnitaryIdealWeight, Complex.cpow_neg, div_eq_mul_inv]

/-- **The presented Hecke L-function** of a ray class character `χ` of `𝔪`: the canonical
meromorphic continuation from `Re s > 1` of the L-series of `χ`, summed over the ideals prime to
the finite part of `𝔪`. It depends on the presentation and not only on the character
(`heckeLFunctionC_induced`). It agrees with the L-series on `Re s > 1` once a continuation to the
plane exists (`meromorphicContinuation_eqOn`), and is `0` otherwise. -/
def heckeLFunctionC (χ : RayClassCharacter 𝔪) : ℂ → ℂ :=
  meromorphicContinuation 1 (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))

/-- The defining equation of the presented Hecke L-function, through which the general results on
`meromorphicContinuation` apply to it. -/
theorem heckeLFunctionC_def (χ : RayClassCharacter 𝔪) :
    heckeLFunctionC χ = meromorphicContinuation 1
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) := (rfl)

/-- The presented Hecke L-function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_heckeLFunctionC (χ : RayClassCharacter 𝔪) :
    MeromorphicNFOn (heckeLFunctionC χ) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The presented Hecke L-function is holomorphic on `Re s > 1`. -/
theorem analyticOnNhd_heckeLFunctionC (χ : RayClassCharacter 𝔪) :
    AnalyticOnNhd ℂ (heckeLFunctionC χ) {s | 1 < s.re} :=
  analyticOnNhd_meromorphicContinuation (analyticOnNhd_LSeries_of_unitary χ.toUnitaryIdealWeight)

/-- The presented Hecke L-function of an induced character is the canonical continuation of the
L-series of the original character times the deleted Euler factors. -/
private theorem heckeLFunctionC_induced_eq_meromorphicContinuation (h : 𝔪 ∣ 𝔫)
    (χ : RayClassCharacter 𝔪) :
    heckeLFunctionC (χ.induced h) = meromorphicContinuation 1 (eulerCorrection χ 𝔫 •
      LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) :=
  meromorphicContinuation_congr fun s hs ↦ by
    rw [LSeries_toUnitaryIdealWeight_induced h χ hs, Pi.smul_apply', smul_eq_mul, mul_comm]

/-- **Inducing deletes Euler factors, for the continued functions on `Re s > 1`.** -/
theorem heckeLFunctionC_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeLFunctionC (χ.induced h) s = heckeLFunctionC χ s * eulerCorrection χ 𝔫 s := by
  rw [heckeLFunctionC_induced_eq_meromorphicContinuation, meromorphicContinuation_smul_apply
    (fun z ↦ ((differentiable_eulerCorrection χ 𝔫).analyticAt z).meromorphicAt)
    (fun z _ ↦ (differentiable_eulerCorrection χ 𝔫).analyticAt z)
    (fun z hz ↦ eulerCorrection_ne_zero χ 𝔫 (zero_lt_one.trans hz))
    (analyticOnNhd_LSeries_of_unitary χ.toUnitaryIdealWeight) hs, smul_eq_mul, mul_comm,
    heckeLFunctionC_def]

/-- **Inducing deletes Euler factors, as germs.** At every point of the plane, the presented
Hecke L-function of `χ.induced h` has the punctured germ of that of `χ` times the deleted Euler
factors. This says nothing about the values at `s` itself: where a zero of the correction factor
meets a pole, the normal form of the product need not be the product of the values. -/
theorem heckeLFunctionC_induced_eventuallyEq (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) (s : ℂ) :
    heckeLFunctionC (χ.induced h) =ᶠ[𝓝[≠] s]
      fun z ↦ heckeLFunctionC χ z * eulerCorrection χ 𝔫 z := by
  rw [heckeLFunctionC_induced_eq_meromorphicContinuation]
  filter_upwards [meromorphicContinuation_smul_eventuallyEq
    (fun z ↦ ((differentiable_eulerCorrection χ 𝔫).analyticAt z).meromorphicAt)
    (fun z _ ↦ (differentiable_eulerCorrection χ 𝔫).analyticAt z)
    (fun z hz ↦ eulerCorrection_ne_zero χ 𝔫 (zero_lt_one.trans hz))
    (analyticOnNhd_LSeries_of_unitary χ.toUnitaryIdealWeight) s] with z hz
  rw [hz, Pi.smul_apply', smul_eq_mul, mul_comm, heckeLFunctionC_def]

/-- **The presented series is the primitive series times the deleted Euler factors**, on
`Re s > 1`. The conductor is supplied by `PrimitiveRayClassCharacter.of`, not by the
presentation. -/
theorem heckeLFunctionC_eq_primitive (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeLFunctionC χ s = heckeLFunctionC (PrimitiveRayClassCharacter.of χ).character s *
      eulerCorrection (PrimitiveRayClassCharacter.of χ).character 𝔪 s := by
  conv_lhs => rw [← PrimitiveRayClassCharacter.induced_character_of χ
    (PrimitiveRayClassCharacter.conductor_of_dvd χ)]
  exact heckeLFunctionC_induced _ _ hs

/-- **The presented series is the primitive series times the deleted Euler factors**, as germs at
every point of the plane. -/
theorem heckeLFunctionC_eventuallyEq_primitive (χ : RayClassCharacter 𝔪) (s : ℂ) :
    heckeLFunctionC χ =ᶠ[𝓝[≠] s]
      fun z ↦ heckeLFunctionC (PrimitiveRayClassCharacter.of χ).character z *
        eulerCorrection (PrimitiveRayClassCharacter.of χ).character 𝔪 z := by
  conv_lhs => rw [← PrimitiveRayClassCharacter.induced_character_of χ
    (PrimitiveRayClassCharacter.conductor_of_dvd χ)]
  exact heckeLFunctionC_induced_eventuallyEq _ _ s

end TauCeti.LFunctions
