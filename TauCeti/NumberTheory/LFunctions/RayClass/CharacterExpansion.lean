/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff
public import TauCeti.NumberTheory.LFunctions.Hecke.Primitive
public import TauCeti.NumberTheory.LFunctions.RayClass.VonMangoldt

import TauCeti.NumberTheory.ArithmeticDirichletSeries.Transfer
import TauCeti.NumberTheory.LFunctions.Hecke.Orthogonality

/-!
# Character expansion of `rayClassPsi` and effective transfer to `rayClassPrimeCount`

For a modulus `𝔪` of a number field `K` and a ray class `c : RayClassGroup 𝔪`, finite Fourier
inversion on `RayClassGroup 𝔪` decomposes the ray-class Chebyshev function `rayClassPsi 𝔪 c` into
the character-twisted Chebyshev functions `rayClassCharacterPsi χ` of the ray class characters
`χ : RayClassCharacter 𝔪`:

`#Cl_𝔪 · ψ(x; 𝔪, c) = ∑_χ conj(χ(c)) · ψ(x, χ)`.

At the level of Dirichlet series on `Re s > 1`, the same orthogonality identity expands the
ray-class von Mangoldt series as a linear combination of the logarithmic derivatives
`-L'(s, χ) / L(s, χ)` of the ray-class L-series. Passing between an imprimitive character `χ` of `𝔪`
and the primitive character `χ.primitiveCharacter` of conductor `χ.conductor ∣ 𝔪` alters `ψ(x, χ)`
only at prime powers dividing `𝔪` outside `χ.conductor`, contributing `O(log x)` with an explicit
bound `((𝔪.support : Set _) \ χ.conductor.support).ncard * log x` for `x ≥ 1`. Finally, combining
higher-prime-power removal from `VonMangoldt.lean` with the effective Abel-summation identities of
`Transfer.lean` converts an expansion of `rayClassPsi 𝔪 c` on the `x exp (-c₀ √log x)` scale —
optionally carrying sublinear power secondary terms such as a Siegel-zero term `x ^ β₁ / β₁` — into
the corresponding asymptotic for `rayClassPrimeCount 𝔪 c` with no loss in `c₀`.

## Main definitions

* `TauCeti.LFunctions.rayClassCharacterPsi`: the character-twisted Chebyshev function `ψ(x, χ)` of a
  ray class character `χ : RayClassCharacter 𝔪`.

## Main results

* `TauCeti.LFunctions.sum_mul_rayClassPsi`, `TauCeti.LFunctions.sum_inv_mul_rayClassCharacterPsi`,
  `TauCeti.LFunctions.sum_conj_mul_rayClassCharacterPsi`, and
  `TauCeti.LFunctions.rayClassPsi_eq_inv_card_mul_sum_re`: Fourier expansion and inversion between
  `rayClassPsi` and `rayClassCharacterPsi`.
* `TauCeti.LFunctions.rayClassCharacterPsi_one`: at the principal character `1`, `ψ(x, 1)` is
  `ψ_K(x)` minus the contribution of `𝔪.support`.
* `TauCeti.LFunctions.norm_rayClassCharacterPsi_sub_induced_le` and
  `TauCeti.LFunctions.norm_rayClassCharacterPsi_sub_primitiveCharacter_le`: explicit `O(log x)`
  bounds comparing an induced presentation with its underlying character and conductor.
* `TauCeti.LFunctions.LSeriesHasSum_rayClassVonMangoldtCoeff`: on `Re s > 1`, the Dirichlet series
  of `rayClassVonMangoldtCoeff 𝔪 c` converges absolutely to
  `(#Cl_𝔪)⁻¹ ∑_χ χ(c)⁻¹ (-L'(s, χ) / L(s, χ))`.
* `TauCeti.LFunctions.rayClassPrimeCount_sub_mul_logIntegral_sub_sum_isLittleO` and
  `TauCeti.LFunctions.rayClassPrimeCount_sub_div_card_isLittleO_of_rayClassPsi_sub_sum_isBigO`:
  effective transfer from `rayClassPsi` to `rayClassPrimeCount`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§8 and 13.
* H. Davenport, *Multiplicative Number Theory*, Chapters 19 and 20.
-/

public section

namespace TauCeti.LFunctions

open Asymptotics Filter NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-! ### Pointwise von Mangoldt orthogonality -/

/-- **Class expansion of the von Mangoldt transform of a ray class character.** -/
theorem sum_mul_vonMangoldtTransform_rayClassCoeff [Fintype (RayClassGroup 𝔪)]
    (χ : RayClassCharacter 𝔪) (I : (Ideal (𝓞 K))⁰) :
    ∑ c : RayClassGroup 𝔪, ((χ c : ℂˣ) : ℂ) * (rayClassCoeff 𝔪 c).vonMangoldtTransform I =
      χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform I := by
  have h := congrFun (sum_smul_rayClassCoeff χ) I
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [IdealArithmeticFunction.vonMangoldtTransform_apply, ← mul_assoc, ← Finset.sum_mul, h]

/-- **Character orthogonality for the von Mangoldt transforms.** Summing `χ(c)⁻¹` against the von
Mangoldt transforms of all ray class characters of `𝔪` isolates `#Cl_𝔪` times the von Mangoldt
transform of `rayClassCoeff 𝔪 c`. -/
theorem sum_inv_mul_vonMangoldtTransform_toUnitaryIdealWeight (c : RayClassGroup 𝔪)
    (I : (Ideal (𝓞 K))⁰) :
    ∑ χ : RayClassCharacter 𝔪, (((χ c)⁻¹ : ℂˣ) : ℂ) *
        χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform I =
      (Nat.card (RayClassGroup 𝔪) : ℂ) * (rayClassCoeff 𝔪 c).vonMangoldtTransform I := by
  have h := congrFun (sum_inv_smul_toUnitaryIdealWeight c) I
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [IdealArithmeticFunction.vonMangoldtTransform_apply, ← mul_assoc, ← Finset.sum_mul, h]

/-! ### The character-twisted Chebyshev function `rayClassCharacterPsi` -/

/-- **Character-twisted Chebyshev function of a ray class character**: the ideal summatory function
of `χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform`, summing
`χ(𝔭) ^ m log N(𝔭)` over prime-power ideals `𝔭 ^ m` prime to `𝔪` of absolute norm at most `x`. -/
noncomputable def rayClassCharacterPsi (χ : RayClassCharacter 𝔪) (x : ℝ) : ℂ :=
  idealSummatory K χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform x

/-- Defining equation of `TauCeti.LFunctions.rayClassCharacterPsi`. -/
theorem rayClassCharacterPsi_def (χ : RayClassCharacter 𝔪) (x : ℝ) :
    rayClassCharacterPsi χ x =
      idealSummatory K χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform x :=
  (rfl)

/-- Prime-power summatory presentation of `rayClassCharacterPsi`. -/
theorem rayClassCharacterPsi_eq_primePowerSummatory (χ : RayClassCharacter 𝔪) (x : ℝ) :
    rayClassCharacterPsi χ x = primePowerSummatory K
      (fun A ↦ χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform
        (A : (Ideal (𝓞 K))⁰)) x :=
  idealSummatory_eq_primePowerSummatory K
    χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform _ (fun _ ↦ rfl)
    (fun _ hI ↦ IdealArithmeticFunction.vonMangoldtTransform_eq_zero_of_not_isPrimePow _ hI) x

/-- **Class expansion of `rayClassCharacterPsi`.** For every ray class character `χ` of `𝔪`,
`ψ(x, χ) = ∑_c χ(c) ψ(x; 𝔪, c)`. -/
theorem sum_mul_rayClassPsi [Fintype (RayClassGroup 𝔪)] (χ : RayClassCharacter 𝔪) (x : ℝ) :
    ∑ c : RayClassGroup 𝔪, ((χ c : ℂˣ) : ℂ) * (rayClassPsi 𝔪 c x : ℂ) =
      rayClassCharacterPsi χ x := by
  simp_rw [← idealSummatory_vonMangoldtTransform_rayClassCoeff, rayClassCharacterPsi_def,
    idealSummatory_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun I _ ↦ sum_mul_vonMangoldtTransform_rayClassCoeff χ I

/-- Below `2`, `rayClassCharacterPsi` vanishes. -/
theorem rayClassCharacterPsi_eq_zero_of_lt_two (χ : RayClassCharacter 𝔪) {x : ℝ} (hx : x < 2) :
    rayClassCharacterPsi χ x = 0 := by
  have := Fintype.ofFinite (RayClassGroup 𝔪)
  rw [← sum_mul_rayClassPsi]
  simp [rayClassPsi_eq_zero_of_lt_two _ _ hx]

/-- **Character orthogonality for `rayClassPsi` (`χ(c)⁻¹` form).** Summing `χ(c)⁻¹ · ψ(x, χ)` over
all ray class characters of `𝔪` gives `#Cl_𝔪 · ψ(x; 𝔪, c)`. -/
theorem sum_inv_mul_rayClassCharacterPsi (c : RayClassGroup 𝔪) (x : ℝ) :
    ∑ χ : RayClassCharacter 𝔪, (((χ c)⁻¹ : ℂˣ) : ℂ) * rayClassCharacterPsi χ x =
      (Nat.card (RayClassGroup 𝔪) : ℂ) * (rayClassPsi 𝔪 c x : ℂ) := by
  simp_rw [← idealSummatory_vonMangoldtTransform_rayClassCoeff, rayClassCharacterPsi_def,
    idealSummatory_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun I _ ↦ sum_inv_mul_vonMangoldtTransform_toUnitaryIdealWeight c I

/-- **Character orthogonality for `rayClassPsi` (conjugate form).** Summing `conj(χ(c)) · ψ(x, χ)`
over all ray class characters of `𝔪` gives `#Cl_𝔪 · ψ(x; 𝔪, c)`. -/
theorem sum_conj_mul_rayClassCharacterPsi (c : RayClassGroup 𝔪) (x : ℝ) :
    ∑ χ : RayClassCharacter 𝔪, starRingEnd ℂ ((χ c : ℂˣ) : ℂ) * rayClassCharacterPsi χ x =
      (Nat.card (RayClassGroup 𝔪) : ℂ) * (rayClassPsi 𝔪 c x : ℂ) := by
  simp_rw [RayClassCharacter.conj_apply_eq_inv]
  exact sum_inv_mul_rayClassCharacterPsi c x

/-- **Real-part character decomposition of `rayClassPsi`.** -/
theorem rayClassPsi_eq_inv_card_mul_sum_re (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassPsi 𝔪 c x = (Nat.card (RayClassGroup 𝔪) : ℝ)⁻¹ *
      ∑ χ : RayClassCharacter 𝔪,
        (starRingEnd ℂ ((χ c : ℂˣ) : ℂ) * rayClassCharacterPsi χ x).re := by
  have hre := congrArg Complex.re (sum_conj_mul_rayClassCharacterPsi c x)
  rw [Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re] at hre
  have hcard : (Nat.card (RayClassGroup 𝔪) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hre, inv_mul_cancel_left₀ hcard]

/-- **Principal ray class character.** At `1 : RayClassCharacter 𝔪`, `ψ(x, 1)` is `ψ_K(x)` minus the
contribution of the prime divisors of `𝔪`. -/
theorem rayClassCharacterPsi_one (𝔪 : Modulus K) (x : ℝ) :
    rayClassCharacterPsi (1 : RayClassCharacter 𝔪) x =
      ((primePsi K Set.univ x -
        primePsi K (𝔪.support : Set (HeightOneSpectrum (𝓞 K))) x : ℝ) : ℂ) := by
  have := Fintype.ofFinite (RayClassGroup 𝔪)
  rw [← sum_mul_rayClassPsi]
  simp only [MonoidHom.one_apply, Units.val_one, one_mul, ← Complex.ofReal_sum,
    ← sum_rayClassPsi_add_primePsi_support 𝔪 x, add_sub_cancel_right]

/-- At the trivial character of `Modulus.one K`, `rayClassCharacterPsi` is `ψ_K`. -/
@[simp]
theorem rayClassCharacterPsi_one_modulus_one (x : ℝ) :
    rayClassCharacterPsi (1 : RayClassCharacter (Modulus.one K)) x =
      (primePsi K Set.univ x : ℂ) := by
  simp [rayClassCharacterPsi_one, Modulus.support_one]

/-! ### Change of modulus and comparison with the primitive character -/

/-- On a prime-power ideal `A`, inducing `χ` along `h : 𝔪 ∣ 𝔫` changes its von Mangoldt transform
by `0` outside `𝔫.support \ 𝔪.support` and by a quantity of norm at most `primePowerWeight A`
inside `𝔫.support \ 𝔪.support`. -/
private theorem norm_vonMangoldtTransform_sub_induced_idealPrimePower (h : 𝔪 ∣ 𝔫)
    (χ : RayClassCharacter 𝔪) (A : IdealPrimePower K) :
    ‖χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform (A : (Ideal (𝓞 K))⁰) -
      (χ.induced h).toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform
        (A : (Ideal (𝓞 K))⁰)‖ ≤
      {B : IdealPrimePower K |
        primePowerBase B ∈ (𝔫.support : Set (HeightOneSpectrum (𝓞 K))) \ 𝔪.support}.indicator
        primePowerWeight A := by
  classical
  rw [IdealArithmeticFunction.vonMangoldtTransform_apply,
    IdealArithmeticFunction.vonMangoldtTransform_apply, vonMangoldt_eq_primePowerWeight, ← sub_mul,
    UnitaryIdealWeight.toIdealArithmeticFunction_apply,
    UnitaryIdealWeight.toIdealArithmeticFunction_apply,
    RayClassCharacter.toUnitaryIdealWeight_induced, UnitaryIdealWeight.val_restrictAway,
    RayClassCharacter.val_toUnitaryIdealWeight, MultiplicativeIdealWeight.restrictAway_apply]
  by_cases hAn : primePowerBase A ∈ 𝔫.support
  · rw [ite_eq_right (mt isPrimeTo_idealPrimePower_iff.mp (not_not.mpr hAn)), sub_zero]
    by_cases hAm : primePowerBase A ∈ 𝔪.support
    · have hnot : ¬ Ideal.IsPrimeTo (A : Ideal (𝓞 K)) 𝔪.support :=
        mt isPrimeTo_idealPrimePower_iff.mp (not_not.mpr hAm)
      have hmem : A ∉ {B : IdealPrimePower K |
          primePowerBase B ∈ (𝔫.support : Set (HeightOneSpectrum (𝓞 K))) \ 𝔪.support} :=
        fun h ↦ h.2 hAm
      rw [RayClassCharacter.toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hnot, zero_mul,
        norm_zero, Set.indicator_of_notMem hmem]
    · have hmem : A ∈ {B : IdealPrimePower K |
          primePowerBase B ∈ (𝔫.support : Set (HeightOneSpectrum (𝓞 K))) \ 𝔪.support} :=
        ⟨hAn, hAm⟩
      rw [Set.indicator_of_mem hmem, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (primePowerWeight_nonneg A),
        ← RayClassCharacter.val_toUnitaryIdealWeight]
      exact mul_le_of_le_one_left (primePowerWeight_nonneg A)
        (χ.toUnitaryIdealWeight.norm_le_one (A : Ideal (𝓞 K)))
  · have hmem : A ∉ {B : IdealPrimePower K |
        primePowerBase B ∈ (𝔫.support : Set (HeightOneSpectrum (𝓞 K))) \ 𝔪.support} :=
      fun h ↦ hAn h.1
    rw [ite_eq_left (isPrimeTo_idealPrimePower_iff.mpr hAn), sub_self, zero_mul, norm_zero,
      Set.indicator_of_notMem hmem]

/-- **Bad-prime domination under induction.** For `h : 𝔪 ∣ 𝔫`, the difference between
`rayClassCharacterPsi χ` and `rayClassCharacterPsi (χ.induced h)` is bounded in norm by `primePsi`
of the newly excluded prime set `(𝔫.support : Set _) \ 𝔪.support`. -/
theorem norm_rayClassCharacterPsi_sub_induced_le_primePsi (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪)
    (x : ℝ) :
    ‖rayClassCharacterPsi χ x - rayClassCharacterPsi (χ.induced h) x‖ ≤
      primePsi K ((𝔫.support : Set (HeightOneSpectrum (𝓞 K))) \ 𝔪.support) x := by
  rw [rayClassCharacterPsi_eq_primePowerSummatory, rayClassCharacterPsi_eq_primePowerSummatory,
    primePsi_apply, primePowerSummatory_apply, primePowerSummatory_apply, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun A _ ↦ norm_vonMangoldtTransform_sub_induced_idealPrimePower h χ A)

/-- When `𝔫` introduces no new finite prime divisors beyond `𝔪`, inducing leaves
`rayClassCharacterPsi` unchanged. -/
theorem rayClassCharacterPsi_induced_of_support_subset (h : 𝔪 ∣ 𝔫) (h' : 𝔫.support ⊆ 𝔪.support)
    (χ : RayClassCharacter 𝔪) (x : ℝ) :
    rayClassCharacterPsi (χ.induced h) x = rayClassCharacterPsi χ x := by
  have hle := norm_rayClassCharacterPsi_sub_induced_le_primePsi h χ x
  rw [Set.sdiff_eq_empty.mpr (Finset.coe_subset.mpr h'), primePsi_empty] at hle
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp hle)).symm

/-- **Explicit bad-prime bound under induction.** For `x ≥ 1` and `h : 𝔪 ∣ 𝔫`,
`‖ψ(x, χ) - ψ(x, χ.induced h)‖ ≤ ((𝔫.support : Set _) \ 𝔪.support).ncard * log x`. -/
theorem norm_rayClassCharacterPsi_sub_induced_le (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) {x : ℝ}
    (hx : 1 ≤ x) :
    ‖rayClassCharacterPsi χ x - rayClassCharacterPsi (χ.induced h) x‖ ≤
      ((𝔫.support : Set (HeightOneSpectrum (𝓞 K))) \ 𝔪.support).ncard * Real.log x :=
  (norm_rayClassCharacterPsi_sub_induced_le_primePsi h χ x).trans
    (primePsi_le_ncard_mul_log 𝔫.support.finite_toSet.sdiff hx)

/-- Inducing a ray class character along `h : 𝔪 ∣ 𝔫` changes `rayClassCharacterPsi` by
`O(log x)`. -/
theorem rayClassCharacterPsi_sub_induced_isBigO_log (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) :
    (fun x ↦ rayClassCharacterPsi χ x - rayClassCharacterPsi (χ.induced h) x)
      =O[atTop] Real.log := by
  set S : Set (HeightOneSpectrum (𝓞 K)) :=
    (𝔫.support : Set (HeightOneSpectrum (𝓞 K))) \ 𝔪.support
  have hS : S.Finite := 𝔫.support.finite_toSet.sdiff
  refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun x ↦ ?_))
    (primePsi_isBigO_log_of_finite hS)
  rw [one_mul, Real.norm_of_nonneg (primePsi_nonneg S x)]
  exact norm_rayClassCharacterPsi_sub_induced_le_primePsi h χ x

/-- **Explicit bad-prime bound against the primitive character.** For `x ≥ 1`, passing from `χ` to
`χ.primitiveCharacter` changes `rayClassCharacterPsi` by at most
`((𝔪.support : Set _) \ χ.conductor.support).ncard * log x`. -/
theorem norm_rayClassCharacterPsi_sub_primitiveCharacter_le (χ : RayClassCharacter 𝔪) {x : ℝ}
    (hx : 1 ≤ x) :
    ‖rayClassCharacterPsi χ x - rayClassCharacterPsi χ.primitiveCharacter x‖ ≤
      ((𝔪.support : Set (HeightOneSpectrum (𝓞 K))) \ χ.conductor.support).ncard * Real.log x := by
  have h := norm_rayClassCharacterPsi_sub_induced_le χ.conductor_dvd χ.primitiveCharacter hx
  rwa [χ.induced_primitiveCharacter, norm_sub_rev] at h

/-- Passing between a ray class character and its primitive character changes
`rayClassCharacterPsi` by `O(log x)`. -/
theorem rayClassCharacterPsi_sub_primitiveCharacter_isBigO_log (χ : RayClassCharacter 𝔪) :
    (fun x ↦ rayClassCharacterPsi χ x - rayClassCharacterPsi χ.primitiveCharacter x)
      =O[atTop] Real.log := by
  have h :=
    (rayClassCharacterPsi_sub_induced_isBigO_log χ.conductor_dvd χ.primitiveCharacter).neg_left
  refine h.congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
  dsimp only
  rw [neg_sub, χ.induced_primitiveCharacter]

/-! ### Logarithmic-derivative character expansion on `Re s > 1` -/

/-- On `Re s > 1`, the ideal-indexed von Mangoldt series of a ray class character converges
absolutely to `-logDeriv L(s, χ)`. -/
theorem hasSum_idealTerm_vonMangoldtTransform_toUnitaryIdealWeight (χ : RayClassCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (idealTerm K χ.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform s)
      (-logDeriv (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) s) := by
  have habs : idealAbscissaOfAbsConv K χ.toUnitaryIdealWeight.toIdealArithmeticFunction < s.re :=
    idealAbscissaOfAbsConv_lt_re_of_bounded (C := 1)
      (fun I ↦ by simpa using χ.toUnitaryIdealWeight.norm_le_one I) hs
  have hsum := IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform habs
  have hlog := MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform
    χ.toMultiplicativeIdealWeight
    (by simpa [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using habs)
  simp only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    RayClassCharacter.val_toUnitaryIdealWeight] at hsum ⊢
  rw [hlog, neg_neg]
  exact hsum.hasSum

/-- On `Re s > 1`, the ideal-indexed von Mangoldt series of `rayClassCoeff 𝔪 c` converges
absolutely to `(#Cl_𝔪)⁻¹ ∑_χ χ(c)⁻¹ (-logDeriv L(s, χ))`. -/
theorem hasSum_idealTerm_vonMangoldtTransform_rayClassCoeff (c : RayClassGroup 𝔪) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (idealTerm K (rayClassCoeff 𝔪 c).vonMangoldtTransform s)
      ((Nat.card (RayClassGroup 𝔪) : ℂ)⁻¹ * ∑ χ : RayClassCharacter 𝔪,
        (((χ c)⁻¹ : ℂˣ) : ℂ) * -logDeriv
          (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) s) := by
  have hcard : (Nat.card (RayClassGroup 𝔪) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum := (hasSum_sum fun χ (_ : χ ∈ (Finset.univ : Finset (RayClassCharacter 𝔪))) ↦
    (hasSum_idealTerm_vonMangoldtTransform_toUnitaryIdealWeight χ hs).mul_left
      (((χ c)⁻¹ : ℂˣ) : ℂ)).mul_left ((Nat.card (RayClassGroup 𝔪) : ℂ)⁻¹)
  refine hsum.congr_fun fun I ↦ ?_
  simp only [idealTerm_def, ← mul_div_assoc, ← Finset.sum_div,
    sum_inv_mul_vonMangoldtTransform_toUnitaryIdealWeight, inv_mul_cancel_left₀ hcard]

/-- **Character expansion of the ray-class von Mangoldt Dirichlet series (`LSeriesHasSum` form).**
On `Re s > 1`, the L-series of `rayClassVonMangoldtCoeff 𝔪 c` converges absolutely to
`(#Cl_𝔪)⁻¹ ∑_χ χ(c)⁻¹ (-logDeriv L(s, χ))`. -/
theorem LSeriesHasSum_rayClassVonMangoldtCoeff (c : RayClassGroup 𝔪) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (rayClassVonMangoldtCoeff 𝔪 c n : ℂ)) s
      ((Nat.card (RayClassGroup 𝔪) : ℂ)⁻¹ * ∑ χ : RayClassCharacter 𝔪,
        (((χ c)⁻¹ : ℂˣ) : ℂ) * -logDeriv
          (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) s) := by
  have h := regroupByNorm K (hasSum_idealTerm_vonMangoldtTransform_rayClassCoeff c hs)
  rwa [← funext (ofReal_rayClassVonMangoldtCoeff 𝔪 c)] at h

/-- The ray-class von Mangoldt Dirichlet series is absolutely summable on `Re s > 1`. -/
theorem LSeriesSummable_rayClassVonMangoldtCoeff (c : RayClassGroup 𝔪) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (rayClassVonMangoldtCoeff 𝔪 c n : ℂ)) s :=
  (LSeriesHasSum_rayClassVonMangoldtCoeff c hs).LSeriesSummable

/-- **Character expansion of the ray-class von Mangoldt `LSeries` on `Re s > 1`.** -/
theorem LSeries_rayClassVonMangoldtCoeff_eq_sum_logDeriv (c : RayClassGroup 𝔪) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n ↦ (rayClassVonMangoldtCoeff 𝔪 c n : ℂ)) s =
      (Nat.card (RayClassGroup 𝔪) : ℂ)⁻¹ * ∑ χ : RayClassCharacter 𝔪,
        (((χ c)⁻¹ : ℂˣ) : ℂ) * -logDeriv
          (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) s :=
  (LSeriesHasSum_rayClassVonMangoldtCoeff c hs).LSeries_eq

/-! ### Effective transfer from `rayClassPsi` to `rayClassPrimeCount` -/

/-- **Effective transfer from `rayClassPsi` to `rayClassPrimeCount` with power secondary terms.**
Combining higher-prime-power removal (`O(√x log² x) = o(x exp (-c₀ √log x))`) with Abel summation
converts `ψ(x; 𝔪, c) = δ x + ∑ i ∈ s, a i * (x ^ β i / β i) + O(x exp (-c₀ √log x))` into
`π(x; 𝔪, c) = δ Li(x) + ∑ i ∈ s, a i * Li(x ^ β i) + o(x exp (-c₀ √log x))` with no loss in `c₀`
and no sign restriction on `β` or `c₀`. -/
theorem rayClassPrimeCount_sub_mul_logIntegral_sub_sum_isLittleO {ι : Type*} (𝔪 : Modulus K)
    (c : RayClassGroup 𝔪) (δ : ℝ) (s : Finset ι) (a β : ι → ℝ) {c₀ : ℝ}
    (h : (fun x ↦ rayClassPsi 𝔪 c x - δ * x - ∑ i ∈ s, a i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x))) :
    (fun x ↦ (rayClassPrimeCount 𝔪 c x : ℝ) - δ * Real.logIntegral x -
      ∑ i ∈ s, a i * Real.logIntegral (x ^ β i)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x)) := by
  have hθ : (fun x ↦ primeTheta K (rayClassPrimeSet 𝔪 c) x - δ * x -
      ∑ i ∈ s, a i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x)) := by
    refine (h.sub (rayClassPsi_sub_rayClassTheta_isLittleO_mul_exp_neg_mul_sqrt_log
      𝔪 c c₀).isBigO).congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
    dsimp only
    rw [rayClassTheta_def]
    ring
  simpa only [← natCast_rayClassPrimeCount] using
    primeCount_sub_mul_logIntegral_sub_sum_isLittleO s a β hθ

/-- **Effective transfer from `rayClassPsi` to `rayClassPrimeCount` absorbing sublinear power
terms.** When every secondary exponent satisfies `β i < 1` (for instance a real Siegel zero of a
fixed modulus `𝔪`), each `Li(x ^ β i)` is absorbed into `o(x exp (-c₀ √log x))`, yielding
`π(x; 𝔪, c) - Li(x) / #Cl_𝔪 = o(x exp (-c₀ √log x))`. -/
theorem rayClassPrimeCount_sub_div_card_isLittleO_of_rayClassPsi_sub_sum_isBigO {ι : Type*}
    (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (s : Finset ι) (a β : ι → ℝ) {c₀ : ℝ}
    (hβ : ∀ i ∈ s, β i < 1)
    (h : (fun x ↦ rayClassPsi 𝔪 c x - x / Nat.card (RayClassGroup 𝔪) -
      ∑ i ∈ s, a i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x))) :
    (fun x ↦ (rayClassPrimeCount 𝔪 c x : ℝ) -
      Real.logIntegral x / Nat.card (RayClassGroup 𝔪)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x)) := by
  have hθ : (fun x ↦ primeTheta K (rayClassPrimeSet 𝔪 c) x -
      (Nat.card (RayClassGroup 𝔪) : ℝ)⁻¹ * x -
      ∑ i ∈ s, a i * (x ^ β i / β i)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x)) := by
    refine (h.sub (rayClassPsi_sub_rayClassTheta_isLittleO_mul_exp_neg_mul_sqrt_log
      𝔪 c c₀).isBigO).congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
    dsimp only
    rw [rayClassTheta_def, div_eq_inv_mul]
    ring
  refine (primeCount_sub_mul_logIntegral_isLittleO_of_sub_sum_isBigO s a β hβ hθ).congr'
    (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
  dsimp only
  rw [← natCast_rayClassPrimeCount, div_eq_inv_mul]

/-- **Direct effective transfer from `rayClassPsi` to `rayClassPrimeCount`.** -/
theorem rayClassPrimeCount_sub_div_card_isLittleO_of_rayClassPsi_isBigO (𝔪 : Modulus K)
    (c : RayClassGroup 𝔪) {c₀ : ℝ}
    (h : (fun x ↦ rayClassPsi 𝔪 c x - x / Nat.card (RayClassGroup 𝔪)) =O[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x))) :
    (fun x ↦ (rayClassPrimeCount 𝔪 c x : ℝ) -
      Real.logIntegral x / Nat.card (RayClassGroup 𝔪)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c₀ * √(Real.log x)) := by
  refine rayClassPrimeCount_sub_div_card_isLittleO_of_rayClassPsi_sub_sum_isBigO 𝔪 c
    (∅ : Finset Unit) 0 0 (by simp) ?_
  simpa only [Finset.sum_empty, sub_zero] using h

end TauCeti.LFunctions
