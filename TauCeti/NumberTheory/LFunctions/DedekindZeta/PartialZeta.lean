/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.MainTerm
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.LSeries.SumCoeff
import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Asymptotic

/-!
# The Dirichlet series of a ray class

For a modulus `𝔪` of a number field `K` and a ray class `c` of `𝔪`, the partial zeta function of
`c` is `ζ(s, c) = ∑_{𝔞 ∈ c} N(𝔞) ^ (-s)`, the sum over the nonzero integral ideals prime to the
finite part `𝔪₀` of `𝔪` whose ray class is `c`. This file develops its Dirichlet series on and
across the line `Re s = 1`.

The coefficient is the class indicator `rayClassCoeff 𝔪 c`, an ideal arithmetic function equal
to `1` exactly at the ideals prime to `𝔪₀` of class `c`. The class is read off the prime-to
carrier `integralIdealsPrimeTo 𝔪`, so no ray class is attached to an ideal sharing a prime with
`𝔪₀`. The indicator of a nontrivial class is not multiplicative, so it is not an ideal weight.

Summing the indicators over the classes gives the indicator of the ideals prime to `𝔪₀`, so

`∑_c ζ(s, c) = ζ_K(s) * ∏_{𝔭 ∣ 𝔪₀} (1 - N(𝔭) ^ (-s))`  for `Re s > 1`.

The product is `finiteEulerCorrection 𝔪 s`; at a real `s > 0` it is `1` exactly when the finite
part of `𝔪` is trivial (`finiteEulerCorrection_eq_one_iff`).

The number of ideals of class `c` of norm at most `x` is `κ_𝔪 x + O(x ^ (1 - 1 / [K : ℚ]))`, with
`κ_𝔪 = rayClassIdealMainTerm 𝔪` the same for every class. By partial summation,
`ζ(s, c) - κ_𝔪 / (s - 1)` continues holomorphically to `Re s > 1 - 1 / [K : ℚ]`, so every
partial zeta function has a simple pole at `s = 1` with the common residue
`κ_𝔪 = ρ_K * finiteEulerCorrection 𝔪 1 / #Cl_𝔪`, where `ρ_K = dedekindZeta_residue K`.

## Main definitions

* `TauCeti.LFunctions.rayClassCoeff 𝔪 c`: the indicator of the ray class `c` on nonzero ideals.
* `TauCeti.LFunctions.finiteEulerCorrection 𝔪 s`: the Euler factors
  `∏_{𝔭 ∣ 𝔪₀} (1 - N(𝔭) ^ (-s))` deleted by coprimality to `𝔪`.

## Main results

* `TauCeti.LFunctions.sum_rayClassCoeff`: the class indicators sum to the indicator of the ideals
  prime to `𝔪₀`.
* `TauCeti.LFunctions.idealSummatory_rayClassCoeff`: the partial sums of a class indicator are the
  ray class ideal counts.
* `TauCeti.LFunctions.LSeriesSummable_rayClassCoeff`: the Dirichlet series of a ray class
  converges absolutely on `Re s > 1`.
* `TauCeti.LFunctions.sum_LSeries_rayClassCoeff`: the sum over the ray classes is
  `ζ_K(s) * finiteEulerCorrection 𝔪 s`, and `sum_LSeries_rayClassCoeff_one` is the class-group
  case, in which it is `ζ_K(s)`.
* `TauCeti.LFunctions.finiteEulerCorrection_eq_one_iff`: at a real `s > 0` the correction is `1`
  exactly when the finite part of `𝔪` is trivial.
* `TauCeti.LFunctions.sum_LSeries_rayClassCoeff_eq_dedekindZeta_iff`: at a real `s > 1` the sum
  over the ray classes is `ζ_K(s)` exactly when the finite part of `𝔪` is trivial.
* `TauCeti.LFunctions.exists_differentiableOn_eq_LSeries_rayClassCoeff_sub`:
  `ζ(s, c) - κ_𝔪 / (s - 1)` extends holomorphically from `Re s > 1` to
  `Re s > 1 - 1 / [K : ℚ]`.
* `TauCeti.LFunctions.tendsto_sub_one_mul_LSeries_rayClassCoeff`: the residue of
  `ζ(s, c)` at `s = 1` is `κ_𝔪`, and `ofReal_rayClassIdealMainTerm` writes it as
  `ρ_K * finiteEulerCorrection 𝔪 1 / #Cl_𝔪`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5 and §6.
* S. Lang, *Algebraic Number Theory*, Chapter VIII, §2 and §3.
-/

public section

namespace TauCeti.LFunctions

open Asymptotics Filter NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors Topology
open IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K]

/-! ### The class indicator -/

open scoped Classical in
/-- **The indicator of a ray class** on nonzero integral ideals: `1` at an ideal prime to the
finite part of `𝔪` whose ray class is `c`, and `0` elsewhere. The class is read off the prime-to
carrier `integralIdealsPrimeTo 𝔪`, so an ideal sharing a prime with the finite part of `𝔪` has
coefficient `0` in every class. This is a general ideal arithmetic function, not an ideal
weight: the indicator of a nontrivial class is not multiplicative. -/
noncomputable def rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    IdealArithmeticFunction K := fun I ↦
  if ∃ hI : 𝔪.IsCoprimeTo (I : Ideal (𝓞 K)),
      idealClass 𝔪 ⟨I, Modulus.mem_integralIdealsPrimeTo.mpr hI⟩ = c then 1 else 0

open scoped Classical in
/-- Defining equation of `TauCeti.LFunctions.rayClassCoeff`. -/
theorem rayClassCoeff_apply (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (I : (Ideal (𝓞 K))⁰) :
    rayClassCoeff 𝔪 c I =
      if ∃ hI : 𝔪.IsCoprimeTo (I : Ideal (𝓞 K)),
        idealClass 𝔪 ⟨I, Modulus.mem_integralIdealsPrimeTo.mpr hI⟩ = c then 1 else 0 :=
  (rfl)

open scoped Classical in
/-- At an ideal prime to the modulus, the class indicator tests the ray class of the ideal. -/
theorem rayClassCoeff_apply_of_isCoprimeTo {𝔪 : Modulus K} (c : RayClassGroup 𝔪)
    {I : (Ideal (𝓞 K))⁰} (hI : 𝔪.IsCoprimeTo (I : Ideal (𝓞 K))) :
    rayClassCoeff 𝔪 c I =
      if idealClass 𝔪 ⟨I, Modulus.mem_integralIdealsPrimeTo.mpr hI⟩ = c then 1 else 0 := by
  rw [rayClassCoeff_apply]
  exact if_congr ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hI, h⟩⟩ rfl rfl

/-- At an ideal sharing a prime with the finite part of the modulus, every class indicator
vanishes. -/
@[simp]
theorem rayClassCoeff_apply_of_not_isCoprimeTo {𝔪 : Modulus K} (c : RayClassGroup 𝔪)
    {I : (Ideal (𝓞 K))⁰} (hI : ¬ 𝔪.IsCoprimeTo (I : Ideal (𝓞 K))) :
    rayClassCoeff 𝔪 c I = 0 := by
  rw [rayClassCoeff_apply, ite_eq_right fun ⟨h, _⟩ ↦ hI h]

/-- The class indicator takes the value `1` at an ideal of its own class. -/
@[simp]
theorem rayClassCoeff_idealClass {𝔪 : Modulus K} (J : integralIdealsPrimeTo 𝔪)
    (hJ : (J : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) :
    rayClassCoeff 𝔪 (idealClass 𝔪 J) ⟨J, hJ⟩ = 1 := by
  rw [rayClassCoeff_apply_of_isCoprimeTo _ (Modulus.mem_integralIdealsPrimeTo.mp J.2),
    ite_eq_left rfl]

/-- The class indicator vanishes at an ideal prime to the modulus lying in another class. -/
@[simp]
theorem rayClassCoeff_apply_of_idealClass_ne {𝔪 : Modulus K} {c : RayClassGroup 𝔪}
    {I : (Ideal (𝓞 K))⁰} (hI : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪)
    (hc : idealClass 𝔪 ⟨I, hI⟩ ≠ c) : rayClassCoeff 𝔪 c I = 0 := by
  rw [rayClassCoeff_apply_of_isCoprimeTo c (Modulus.mem_integralIdealsPrimeTo.mp hI),
    ite_eq_right hc]

/-- The class indicator takes values in `{0, 1}`, so it is bounded by `1`. -/
theorem norm_rayClassCoeff_le_one (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (I : (Ideal (𝓞 K))⁰) :
    ‖rayClassCoeff 𝔪 c I‖ ≤ 1 := by
  rw [rayClassCoeff_apply]
  split_ifs <;> simp

/-- **The class indicators sum to the indicator of the ideals prime to the modulus.** Every ideal
prime to the finite part of `𝔪` lies in exactly one ray class, and every other ideal in none. -/
theorem sum_rayClassCoeff (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)] :
    ∑ c : RayClassGroup 𝔪, rayClassCoeff 𝔪 c =
      (MultiplicativeIdealWeight.ofBadPrimes (𝔪.support : Set (HeightOneSpectrum (𝓞 K)))
        𝔪.support.finite_toSet).toIdealArithmeticFunction := by
  classical
  funext I
  rw [Finset.sum_apply, MultiplicativeIdealWeight.toIdealArithmeticFunction_apply,
    MultiplicativeIdealWeight.ofBadPrimes_apply]
  by_cases hI : 𝔪.IsCoprimeTo (I : Ideal (𝓞 K))
  · simp_rw [rayClassCoeff_apply_of_isCoprimeTo _ hI]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _),
      ite_eq_left (Ideal.isPrimeTo_iff.mpr (Modulus.isCoprimeTo_iff.mp hI))]
  · simp_rw [rayClassCoeff_apply_of_not_isCoprimeTo _ hI]
    rw [Finset.sum_const_zero,
      ite_eq_right fun h ↦ hI (Modulus.isCoprimeTo_iff.mpr (Ideal.isPrimeTo_iff.mp h))]

/-- **The partial sums of a class indicator are the ray class ideal counts**: summing
`rayClassCoeff 𝔪 c` over the nonzero ideals of norm at most `x` counts the ideals of class `c`
of norm at most `x`. -/
theorem idealSummatory_rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    idealSummatory K (rayClassCoeff 𝔪 c) x = rayClassIdealCountingFunction 𝔪 c x := by
  classical
  have hle (I : (Ideal (𝓞 K))⁰) : I ∈ idealsLE K x ↔ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x :=
    mem_normLE _
  simp_rw [idealSummatory_apply, rayClassCoeff_apply]
  rw [Finset.sum_boole, ← Nat.card_eq_finsetCard, rayClassIdealCountingFunction_def]
  congr 1
  -- An ideal of norm at most `x` in the class `c` is the same as an ideal of the prime-to carrier
  -- in the class `c` of norm at most `x`; the two carriers differ only in their nonvanishing proof.
  refine Nat.card_congr
    { toFun := fun I ↦ ⟨⟨I.1, Modulus.mem_integralIdealsPrimeTo.mpr
          (Finset.mem_filter.mp I.2).2.1⟩,
        (Finset.mem_filter.mp I.2).2.2, (hle _).mp (Finset.mem_filter.mp I.2).1⟩
      invFun := fun J ↦ ⟨⟨J.1, mem_nonZeroDivisors_of_ne_zero
          (Modulus.isCoprimeTo_iff.mp (Modulus.mem_integralIdealsPrimeTo.mp J.1.2)).1⟩,
        Finset.mem_filter.mpr ⟨(hle _).mpr J.2.2,
          Modulus.mem_integralIdealsPrimeTo.mp J.1.2, J.2.1⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-! ### The finite Euler correction -/

/-- **The finite Euler correction** `∏_{𝔭 ∣ 𝔪₀} (1 - N(𝔭) ^ (-s))`: the Euler factors of `ζ_K`
deleted by coprimality to the finite part `𝔪₀` of `𝔪`. The product runs over `𝔪.support`, the
primes dividing `𝔪₀` (`Modulus.mem_support_iff`). At a real `s > 0` it is `1` only when the finite
part of `𝔪` is trivial (`finiteEulerCorrection_eq_one_iff`). -/
noncomputable def finiteEulerCorrection (𝔪 : Modulus K) (s : ℂ) : ℂ :=
  ∏ 𝔭 ∈ 𝔪.support, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))

/-- Defining equation of `TauCeti.LFunctions.finiteEulerCorrection`. -/
theorem finiteEulerCorrection_def (𝔪 : Modulus K) (s : ℂ) :
    finiteEulerCorrection 𝔪 s = ∏ 𝔭 ∈ 𝔪.support, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) :=
  (rfl)

/-- The trivial modulus deletes no Euler factor. -/
@[simp]
theorem finiteEulerCorrection_one (s : ℂ) : finiteEulerCorrection (Modulus.one K) s = 1 := by
  rw [finiteEulerCorrection_def, Modulus.support_one, Finset.prod_empty]

/-- The finite Euler correction does not vanish on `Re s > 0`. -/
theorem finiteEulerCorrection_ne_zero (𝔪 : Modulus K) {s : ℂ} (hs : 0 < s.re) :
    finiteEulerCorrection 𝔪 s ≠ 0 :=
  prod_one_sub_absNorm_cpow_neg_ne_zero 𝔪.support hs

/-- **The finite Euler correction detects the finite part.** At a real `s > 0` every deleted
factor `1 - N(𝔭) ^ (-s)` lies strictly between `0` and `1`, so the correction is `1` exactly when
no prime divides the finite part of `𝔪`. -/
theorem finiteEulerCorrection_eq_one_iff (𝔪 : Modulus K) {s : ℝ} (hs : 0 < s) :
    finiteEulerCorrection 𝔪 s = 1 ↔ 𝔪.support = ∅ := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [finiteEulerCorrection_def, h, Finset.prod_empty]⟩
  by_contra hne
  obtain ⟨𝔮, h𝔮⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  -- each factor is the real number `1 - N(𝔭) ^ (-s)`, which lies in `(0, 1)`
  have hfac (𝔭 : HeightOneSpectrum (𝓞 K)) :
      1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-(s : ℂ)) =
        ((1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_natCast, Complex.ofReal_neg]
  have hpos (𝔭 : HeightOneSpectrum (𝓞 K)) : 0 < (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
    Real.rpow_pos_of_pos (zero_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) _
  have hlt (𝔭 : HeightOneSpectrum (𝓞 K)) : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭))
      (neg_neg_of_pos hs)
  rw [finiteEulerCorrection_def, Finset.prod_congr rfl fun 𝔭 _ ↦ hfac 𝔭, ← Complex.ofReal_prod,
    Complex.ofReal_eq_one, ← Finset.mul_prod_erase _ _ h𝔮] at h
  have hrest : ∏ 𝔭 ∈ 𝔪.support.erase 𝔮, (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ≤ 1 :=
    Finset.prod_le_one₀ (fun 𝔭 _ ↦ (sub_pos.mpr (hlt 𝔭)).le)
      fun 𝔭 _ ↦ sub_le_self _ (hpos 𝔭).le
  have hq : 1 - (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) < 1 := sub_lt_self _ (hpos 𝔮)
  nlinarith [sub_pos.mpr (hlt 𝔮)]

/-- **The main term of the ray class count, as a residue.** The common main term of the ray class
ideal counts is the Dedekind-zeta residue times the finite Euler correction at `s = 1`, divided by
the order of the ray class group. -/
theorem ofReal_rayClassIdealMainTerm (𝔪 : Modulus K) :
    (rayClassIdealMainTerm 𝔪 : ℂ) =
      dedekindZeta_residue K * finiteEulerCorrection 𝔪 1 / Nat.card (RayClassGroup 𝔪) := by
  rw [rayClassIdealMainTerm_eq, finiteEulerCorrection_def]
  push_cast
  simp_rw [Complex.cpow_neg_one]
  ring

/-! ### The Dirichlet series of a ray class -/

/-- The norm-regrouped Dirichlet series of a ray class converges absolutely on `Re s > 1`. -/
theorem LSeriesSummable_rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (normCoeff K (rayClassCoeff 𝔪 c)) s :=
  LSeriesSummable_normCoeff K
    (summable_idealTerm_of_bounded_of_one_lt_re (norm_rayClassCoeff_le_one 𝔪 c) hs)

/-- **The sum over the ray classes.** On `Re s > 1` the Dirichlet series of the ray classes of `𝔪`
sum to `ζ_K(s) * finiteEulerCorrection 𝔪 s`: the Dedekind zeta function with the Euler factors at
the primes dividing the finite part of `𝔪` deleted. At a real `s > 1` the correction factor is `1`
exactly when `𝔪.support` is empty (`finiteEulerCorrection_eq_one_iff`). -/
theorem sum_LSeries_rayClassCoeff (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)] {s : ℂ}
    (hs : 1 < s.re) :
    ∑ c : RayClassGroup 𝔪, LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s =
      dedekindZeta K s * finiteEulerCorrection 𝔪 s := by
  rw [← LSeries_sum fun c _ ↦ LSeriesSummable_rayClassCoeff 𝔪 c hs]
  have hcoe : ∑ c : RayClassGroup 𝔪, ⇑(normCoeff K (rayClassCoeff 𝔪 c)) =
      ⇑(normCoeff K (∑ c : RayClassGroup 𝔪, rayClassCoeff 𝔪 c)) := by
    funext n
    simp only [Finset.sum_apply, normCoeff_eq_sum_normFiber]
    exact Finset.sum_comm
  rw [hcoe, sum_rayClassCoeff, LSeries_ofBadPrimes _ hs, finiteEulerCorrection_def]

/-- **The class-group case.** For the trivial modulus no Euler factor is deleted, and the
Dirichlet series of the ideal classes sum to `ζ_K(s)` on `Re s > 1`. -/
theorem sum_LSeries_rayClassCoeff_one [Fintype (RayClassGroup (Modulus.one K))] {s : ℂ}
    (hs : 1 < s.re) :
    ∑ c : RayClassGroup (Modulus.one K), LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      dedekindZeta K s := by
  rw [sum_LSeries_rayClassCoeff _ hs, finiteEulerCorrection_one, mul_one]

/-- **The sum over the ray classes is `ζ_K` only for a trivial finite part.** At a real `s > 1`
the Dirichlet series of the ray classes of `𝔪` sum to `ζ_K(s)` exactly when `𝔪.support` is
empty; one prime dividing the finite part of `𝔪` already breaks the equality. -/
theorem sum_LSeries_rayClassCoeff_eq_dedekindZeta_iff (𝔪 : Modulus K)
    [Fintype (RayClassGroup 𝔪)] {s : ℝ} (hs : 1 < s) :
    ∑ c : RayClassGroup 𝔪, LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s = dedekindZeta K s ↔
      𝔪.support = ∅ := by
  have hs' : 1 < (s : ℂ).re := by rwa [Complex.ofReal_re]
  rw [sum_LSeries_rayClassCoeff 𝔪 hs', mul_eq_left₀ (dedekindZeta_ne_zero_of_one_lt_re hs'),
    finiteEulerCorrection_eq_one_iff 𝔪 (zero_lt_one.trans hs)]

/-- **The partial sums of the coefficients of a ray class are the ray class ideal counts**: the
norm coefficients of `rayClassCoeff 𝔪 c` up to `n` add up to the number of ideals of class `c`
of norm at most `n`. -/
theorem sum_Icc_normCoeff_rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, normCoeff K (rayClassCoeff 𝔪 c) k =
      rayClassIdealCountingFunction 𝔪 c n := by
  rw [← Nat.floor_natCast (R := ℝ) n, ← idealSummatory_eq_sum_Icc_normCoeff,
    idealSummatory_rayClassCoeff, Nat.floor_natCast]

/-- **The Dirichlet series of a ray class across `Re s = 1`.** There is a function holomorphic on
the half-plane `Re s > 1 - 1 / [K : ℚ]` that agrees with `ζ(s, c) - κ_𝔪 / (s - 1)` on `Re s > 1`,
where `ζ(s, c)` is the Dirichlet series of the ray class `c` and
`κ_𝔪 = rayClassIdealMainTerm 𝔪`. So `ζ(s, c)` continues meromorphically to
`Re s > 1 - 1 / [K : ℚ]`, with a single pole, simple with residue `κ_𝔪`, at `s = 1`. -/
theorem exists_differentiableOn_eq_LSeries_rayClassCoeff_sub (𝔪 : Modulus K)
    (c : RayClassGroup 𝔪) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s - rayClassIdealMainTerm 𝔪 / (s - 1) := by
  refine TauCeti.LSeries.exists_differentiableOn_eq_LSeries_sub_div_of_isBigO _ _
    (sub_nonneg.mpr (div_le_one_of_le₀ (Nat.one_le_cast.mpr Module.finrank_pos)
      (Nat.cast_nonneg _)))
    (sub_le_self _ (by positivity)) ?_ fun s hs ↦ LSeriesSummable_rayClassCoeff 𝔪 c hs
  -- the partial sums are the class counts, which are `κ_𝔪 n + O(n ^ (1 - 1 / [K : ℚ]))`
  have hsum (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, normCoeff K (rayClassCoeff 𝔪 c) k -
      (rayClassIdealMainTerm 𝔪 : ℂ) * n =
      ((rayClassIdealCountingFunction 𝔪 c n : ℝ) - rayClassIdealMainTerm 𝔪 * n : ℝ) := by
    push_cast
    rw [sum_Icc_normCoeff_rayClassCoeff]
  simp_rw [hsum, one_div]
  exact Complex.isBigO_ofReal_left.mpr
    ((isBigO_rayClassIdealCountingFunction_sub 𝔪 c).comp_tendsto tendsto_natCast_atTop_atTop)

/-- **The common residue.** As `s → 1⁺`, `(s - 1) ζ(s, c)` tends to `κ_𝔪 = rayClassIdealMainTerm 𝔪`
for every ray class `c` of `𝔪`. By `ofReal_rayClassIdealMainTerm` this residue is
`ρ_K * finiteEulerCorrection 𝔪 1 / #Cl_𝔪`; the correction is the one deleted from the sum over
the classes in `sum_LSeries_rayClassCoeff`. -/
theorem tendsto_sub_one_mul_LSeries_rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s) (𝓝[>] 1)
      (𝓝 (rayClassIdealMainTerm 𝔪 : ℂ)) := by
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div ?_ fun s hs ↦
    LSeriesSummable_rayClassCoeff 𝔪 c (by simpa using hs)
  refine ((tendsto_rayClassIdealCountingFunction_div 𝔪 c).comp
    tendsto_natCast_atTop_atTop).ofReal.congr fun n ↦ ?_
  simp [sum_Icc_normCoeff_rayClassCoeff]

end TauCeti.LFunctions
