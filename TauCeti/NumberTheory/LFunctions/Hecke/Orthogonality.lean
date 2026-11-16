/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta
public import TauCeti.NumberTheory.LFunctions.Hecke.Primitive
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Partial zeta functions and ray class L-series: orthogonality

For a modulus `𝔪` of a number field `K`, the class indicators `rayClassCoeff 𝔪 c` and the ideal
weights `χ.toUnitaryIdealWeight` of the ray class characters `χ` of `𝔪` are two bases of the same
space of coefficient functions, related by a finite Fourier transform on the ray class group
`Cl_𝔪`. In one direction the weight of `χ` is `∑_c χ(c) 1_c`; in the other, by column
orthogonality of the characters,

`#Cl_𝔪 · 1_c = ∑_χ χ(c)⁻¹ χ`.

Regrouped by norm and summed as Dirichlet series on `Re s > 1`, this says

`L(s, χ) = ∑_c χ(c) ζ(s, c)`  and  `#Cl_𝔪 · ζ(s, c) = ∑_χ χ(c)⁻¹ L(s, χ)`,

where `ζ(s, c)` is the partial zeta function of the ray class `c` and `L(s, χ)` the L-series of
`χ`, both summed over the ideals prime to the finite part of `𝔪`. Neither identity carries a
finite Euler correction: the correction appears only when the series of the trivial character is
rewritten as the Dedekind zeta function (`sum_LSeries_rayClassCoeff`). Since `χ` takes values in
the roots of unity, `χ(c)⁻¹` is the complex conjugate of `χ(c)`.

The second identity recovers each partial zeta function from the character L-series; the first
expresses each character L-series through the partial zeta functions, whose individual
continuation across `Re s = 1` is `exists_differentiableOn_eq_LSeries_rayClassCoeff_sub`.

Across a change of modulus `𝔪 ∣ 𝔫`, the same two identities relate the characters of `𝔪` to the
partial zeta functions of `𝔫`. Inducing `χ` to `𝔫` multiplies its L-series by the Euler factors
`E_χ(s) = ∏_{𝔭 ∣ 𝔫₀, 𝔭 ∤ 𝔪₀} (1 - χ(𝔭) N𝔭 ^ (-s))` (`RayClassCharacter.eulerCorrection`), and
the induced character is constant on the fibres of `classMap : Cl_𝔫 → Cl_𝔪`, so

`L(s, χ) E_χ(s) = ∑_d χ(d) Z(s, d)`  and  `#Cl_𝔪 · Z(s, c) = ∑_χ χ(c)⁻¹ L(s, χ) E_χ(s)`,

where `Z(s, c) = ∑_{c' ↦ c} ζ(s, c')` sums the partial zeta functions of the classes of `𝔫` over
`c`. When `𝔫₀` has no prime outside `𝔪₀` every `E_χ` is `1` and `Z(s, c) = ζ(s, c)`
(`sum_LSeries_rayClassCoeff_classMap`).

## Main results

* `TauCeti.LFunctions.sum_smul_rayClassCoeff`: the weight of a ray class character is the
  `χ`-weighted sum of the class indicators.
* `TauCeti.LFunctions.sum_inv_smul_toUnitaryIdealWeight`: the class indicator of `c`, scaled by
  `#Cl_𝔪`, is the `χ(c)⁻¹`-weighted sum of the character weights.
* `TauCeti.LFunctions.sum_mul_LSeries_rayClassCoeff`: on `Re s > 1`,
  `L(s, χ) = ∑_c χ(c) ζ(s, c)`.
* `TauCeti.LFunctions.sum_inv_mul_LSeries_toUnitaryIdealWeight`: on `Re s > 1`,
  `#Cl_𝔪 · ζ(s, c) = ∑_χ χ(c)⁻¹ L(s, χ)`.
* `TauCeti.LFunctions.sum_mul_sum_LSeries_rayClassCoeff_classMap` and
  `TauCeti.LFunctions.sum_inv_mul_LSeries_toUnitaryIdealWeight_mul_eulerCorrection`: the two
  identities across a change of modulus `𝔪 ∣ 𝔫`, with the deleted Euler factors.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8.
-/

public section

namespace TauCeti.LFunctions

open NumberField TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-! ### Coefficients -/

/-- **A ray class character weight in terms of the class indicators.** The ideal weight of a ray
class character `χ` of `𝔪` is `∑_c χ(c) 1_c`: at an ideal prime to the finite part of `𝔪` only
the indicator of its own class is nonzero, and at any other ideal both sides vanish. -/
theorem sum_smul_rayClassCoeff [Fintype (RayClassGroup 𝔪)] (χ : RayClassCharacter 𝔪) :
    ∑ c : RayClassGroup 𝔪, ((χ c : ℂˣ) : ℂ) • rayClassCoeff 𝔪 c =
      χ.toUnitaryIdealWeight.toIdealArithmeticFunction := by
  classical
  funext I
  rw [Finset.sum_apply, UnitaryIdealWeight.toIdealArithmeticFunction_apply,
    RayClassCharacter.val_toUnitaryIdealWeight]
  by_cases hI : 𝔪.IsCoprimeTo (I : Ideal (𝓞 K))
  · simp [rayClassCoeff_apply_of_isCoprimeTo _ hI,
      Ideal.isPrimeTo_iff.mpr (Modulus.isCoprimeTo_iff.mp hI)]
  · have hI' : ¬ Ideal.IsPrimeTo (I : Ideal (𝓞 K)) 𝔪.support :=
      fun h ↦ hI (Modulus.isCoprimeTo_iff.mpr (Ideal.isPrimeTo_iff.mp h))
    simp [rayClassCoeff_apply_of_not_isCoprimeTo _ hI, hI']

/-- **Orthogonality: a class indicator in terms of the character weights.** Summing `χ(c)⁻¹`
against the ideal weights of all ray class characters `χ` of `𝔪` gives `#Cl_𝔪` times the
indicator of the ray class `c`. The inverse sits on the class `c`; summing `χ(c)` instead gives
the indicator of `c⁻¹`. -/
theorem sum_inv_smul_toUnitaryIdealWeight (c : RayClassGroup 𝔪) :
    ∑ χ : RayClassCharacter 𝔪,
        (((χ c)⁻¹ : ℂˣ) : ℂ) • χ.toUnitaryIdealWeight.toIdealArithmeticFunction =
      (Nat.card (RayClassGroup 𝔪) : ℂ) • rayClassCoeff 𝔪 c := by
  have := Fintype.ofFinite (RayClassGroup 𝔪)
  have : NeZero (Monoid.exponent (RayClassGroup 𝔪) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  simp_rw [← sum_smul_rayClassCoeff]
  exact CommGroup.sum_inv_smul_sum_smul _ c

/-! ### Dirichlet series -/

/-- **A ray class L-series in terms of the partial zeta functions.** On `Re s > 1` the L-series
of a ray class character `χ` of `𝔪` is `∑_c χ(c) ζ(s, c)`, the partial zeta functions `ζ(s, c)`
of the ray classes of `𝔪` weighted by the character values. -/
theorem sum_mul_LSeries_rayClassCoeff [Fintype (RayClassGroup 𝔪)] (χ : RayClassCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    ∑ c : RayClassGroup 𝔪, ((χ c : ℂˣ) : ℂ) * LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s =
      LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s := by
  simp_rw [← LSeries_smul]
  rw [← LSeries_sum fun c _ ↦ (LSeriesSummable_rayClassCoeff 𝔪 c hs).smul _]
  congr 1
  -- regroup the class expansion of the weight by norm, fibre by fibre
  funext n
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, normCoeff_eq_sum_normFiber,
    Finset.mul_sum, ← sum_smul_rayClassCoeff χ]
  exact Finset.sum_comm

/-- **Orthogonality: a partial zeta function in terms of the ray class L-series.** On
`Re s > 1`, `#Cl_𝔪 · ζ(s, c) = ∑_χ χ(c)⁻¹ L(s, χ)`, the sum running over all ray class
characters `χ` of `𝔪`. Both sides run over the ideals prime to the finite part of `𝔪`, so no
Euler correction appears; it appears only when the term of the trivial character is rewritten as
the Dedekind zeta function. -/
theorem sum_inv_mul_LSeries_toUnitaryIdealWeight (c : RayClassGroup 𝔪) {s : ℂ}
    (hs : 1 < s.re) :
    ∑ χ : RayClassCharacter 𝔪, (((χ c)⁻¹ : ℂˣ) : ℂ) *
        LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s =
      Nat.card (RayClassGroup 𝔪) * LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s := by
  have := Fintype.ofFinite (RayClassGroup 𝔪)
  have : NeZero (Monoid.exponent (RayClassGroup 𝔪) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  simp_rw [← sum_mul_LSeries_rayClassCoeff _ hs, ← smul_eq_mul]
  exact CommGroup.sum_inv_smul_sum_smul _ c

/-! ### Change of modulus -/

/-- **An imprimitive L-series in terms of the partial zeta functions of a larger modulus.** For
`𝔪 ∣ 𝔫` and a ray class character `χ` of `𝔪`, on `Re s > 1` the L-series of `χ` times the Euler
factors `RayClassCharacter.eulerCorrection χ 𝔫 s` at the primes dividing `𝔫₀` but not `𝔪₀` is
`∑_d χ(d) Z(s, d)`, where `Z(s, d)` is the sum of the partial zeta functions of the ray classes of
`𝔫` lying over the class `d` of `𝔪`. -/
theorem sum_mul_sum_LSeries_rayClassCoeff_classMap (h : 𝔪 ∣ 𝔫) [Fintype (RayClassGroup 𝔪)]
    [Fintype (RayClassGroup 𝔫)] [DecidableEq (RayClassGroup 𝔪)] (χ : RayClassCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    ∑ d : RayClassGroup 𝔪, ((χ d : ℂˣ) : ℂ) *
        ∑ c' with classMap h c' = d, LSeries (normCoeff K (rayClassCoeff 𝔫 c')) s =
      LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s *
        χ.eulerCorrection 𝔫 s := by
  -- the induced character is `χ ∘ classMap`, so its expansion over the classes of `𝔫` regroups
  -- along the fibres of `classMap`
  rw [← RayClassCharacter.LSeries_induced h χ hs, ← sum_mul_LSeries_rayClassCoeff _ hs,
    ← Finset.sum_fiberwise _ (classMap h)]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c' hc' ↦ ?_
  rw [RayClassCharacter.induced_apply, (Finset.mem_filter.mp hc').2]

/-- **Orthogonality across a change of modulus.** For `𝔪 ∣ 𝔫` and a ray class `c` of `𝔪`, on
`Re s > 1` the partial zeta functions of the ray classes of `𝔫` lying over `c` sum, after
multiplication by `#Cl_𝔪`, to `∑_χ χ(c)⁻¹ L(s, χ) E_χ(s)` over the ray class characters `χ` of
`𝔪`, where `E_χ(s) = RayClassCharacter.eulerCorrection χ 𝔫 s` is the product of the Euler factors
of `χ` at the primes dividing `𝔫₀` but not `𝔪₀`. -/
theorem sum_inv_mul_LSeries_toUnitaryIdealWeight_mul_eulerCorrection (h : 𝔪 ∣ 𝔫)
    [Fintype (RayClassGroup 𝔫)] [DecidableEq (RayClassGroup 𝔪)] (c : RayClassGroup 𝔪) {s : ℂ}
    (hs : 1 < s.re) :
    ∑ χ : RayClassCharacter 𝔪, (((χ c)⁻¹ : ℂˣ) : ℂ) *
        (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s *
          χ.eulerCorrection 𝔫 s) =
      Nat.card (RayClassGroup 𝔪) *
        ∑ c' with classMap h c' = c, LSeries (normCoeff K (rayClassCoeff 𝔫 c')) s := by
  have := Fintype.ofFinite (RayClassGroup 𝔪)
  have : NeZero (Monoid.exponent (RayClassGroup 𝔪) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  simp_rw [← sum_mul_sum_LSeries_rayClassCoeff_classMap h _ hs, ← smul_eq_mul]
  exact CommGroup.sum_inv_smul_sum_smul _ c

end TauCeti.LFunctions
