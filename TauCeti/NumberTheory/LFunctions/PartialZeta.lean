/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.MainTerm
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Asymptotic

/-!
# The Dirichlet series of the partial zeta functions of ray classes

Let `𝔪` be a modulus of a number field `K` and `c` a ray class of `𝔪`. The partial zeta function
of `c` is `ζ(s, c) = ∑ N𝔞 ^ (-s)`, the sum over the nonzero integral ideals `𝔞` prime to `𝔪` whose
ray class is `c`. This file defines its coefficient, the indicator `rayClassCoeff 𝔪 c` of those
ideals, and proves the basic analytic facts about the norm-regrouped Dirichlet series on the
half-plane `Re s > 1` and at its boundary point `s = 1`.

The class is read off the carrier `integralIdealsPrimeTo 𝔪`, on which `idealClass` is
defined, so the coprimality proof travels with the ideal: there is no ray class of an ideal that is
not prime to `𝔪`, and the indicator is `0` there. The indicator of a nontrivial class is not
multiplicative, so it is a general `IdealArithmeticFunction` rather than an ideal weight.

Because every coefficient carries coprimality to the finite part `𝔪₀` of the modulus, summing over
the ray classes does **not** give the Dedekind zeta function: it gives the series over the ideals
prime to `𝔪₀`, which is `ζ_K` with the Euler factors at the primes dividing `𝔪₀` deleted,

`∑_c ζ(s, c) = ζ_K(s) ∏_{𝔭 ∣ 𝔪₀} (1 - N𝔭 ^ (-s))`.

The product is named once, `finiteEulerCorrection 𝔪 s`, as a product over `𝔪.support`. At a real
`s > 0` it is `1` exactly when the support is empty (`finiteEulerCorrection_eq_one_iff`), so at a
real `s > 1` the sum of the partial zeta series is `ζ_K(s)` exactly for a modulus with trivial
finite part (`sum_LSeries_rayClassCoeff_eq_dedekindZeta_iff`).

For every class `c`, `(s - 1) ζ(s, c)` has the same limit as `s → 1⁺` along the reals: the main
term `rayClassIdealMainTerm 𝔪` of the ray class ideal count, from which it is derived. Written
out (`rayClassIdealMainTerm_eq_finiteEulerCorrection`) it is the Dedekind-zeta residue times
`finiteEulerCorrection 𝔪 1`, divided by the ray class number; dropping the correction factor gives
the wrong residue as soon as `𝔪₀ ≠ 1`.

## Main definitions

* `TauCeti.LFunctions.rayClassCoeff`: the indicator of the ideals prime to `𝔪` in a ray class.
* `TauCeti.LFunctions.finiteEulerCorrection`: the deleted Euler factors
  `∏_{𝔭 ∣ 𝔪₀} (1 - N𝔭 ^ (-s))`.

## Main results

* `TauCeti.LFunctions.LSeriesSummable_normCoeff_rayClassCoeff`: absolute convergence on `Re s > 1`.
* `TauCeti.LFunctions.sum_LSeries_rayClassCoeff`: the partial zeta series of the ray classes sum to
  `ζ_K(s) · finiteEulerCorrection 𝔪 s` on `Re s > 1`, and
  `TauCeti.LFunctions.sum_LSeries_rayClassCoeff_one` to `ζ_K(s)` at the trivial modulus.
* `TauCeti.LFunctions.sum_LSeries_rayClassCoeff_eq_dedekindZeta_iff`: at a real `s > 1`, the sum is
  `ζ_K(s)` exactly when the support of the modulus is empty.
* `TauCeti.LFunctions.idealSummatory_rayClassCoeff`: the summatory function of the indicator is the
  ray class ideal counting function.
* `TauCeti.LFunctions.tendsto_sub_one_mul_LSeries_rayClassCoeff`: the common right-hand limit
  `rayClassIdealMainTerm 𝔪` of `(s - 1) ζ(s, c)` at `s = 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5 (partial zeta functions) and §8.
* S. Lang, *Algebraic Number Theory*, Chapter VIII, §2.
-/

public section

open Filter IsDedekindDomain NumberField
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The class indicator -/

open Classical in
/-- **The indicator of a ray class** on the nonzero integral ideals: `1` at an ideal prime to `𝔪`
whose ray class is `c`, and `0` at every other ideal, in particular at every ideal sharing a prime
with the finite part of `𝔪`. Its norm-regrouped Dirichlet series is the partial zeta function
`ζ(s, c)` of the class. -/
noncomputable def rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    IdealArithmeticFunction K := fun I ↦
  if h : 𝔪.IsCoprimeTo (I : Ideal (𝓞 K)) then
    if idealClass 𝔪 ⟨I, Modulus.mem_integralIdealsPrimeTo.mpr h⟩ = c then 1 else 0
  else 0

open Classical in
/-- At an ideal prime to `𝔪`, the indicator of `c` tests whether the ray class of the ideal is
`c`. -/
theorem rayClassCoeff_apply_of_isCoprimeTo {𝔪 : Modulus K} (c : RayClassGroup 𝔪)
    {I : (Ideal (𝓞 K))⁰} (hI : 𝔪.IsCoprimeTo (I : Ideal (𝓞 K))) :
    rayClassCoeff 𝔪 c I =
      if idealClass 𝔪 ⟨I, Modulus.mem_integralIdealsPrimeTo.mpr hI⟩ = c then 1 else 0 := by
  rw [rayClassCoeff, dite_eq_left hI]

/-- At an ideal not prime to `𝔪` every class indicator vanishes. -/
@[simp]
theorem rayClassCoeff_apply_of_not_isCoprimeTo {𝔪 : Modulus K} (c : RayClassGroup 𝔪)
    {I : (Ideal (𝓞 K))⁰} (hI : ¬ 𝔪.IsCoprimeTo (I : Ideal (𝓞 K))) :
    rayClassCoeff 𝔪 c I = 0 := by
  rw [rayClassCoeff, dite_eq_right hI]

/-- The indicator of `c` at an ideal of the carrier `integralIdealsPrimeTo 𝔪` lying in `c`. -/
theorem rayClassCoeff_apply_of_idealClass_eq {𝔪 : Modulus K} {c : RayClassGroup 𝔪}
    {I : (Ideal (𝓞 K))⁰} (hI : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪)
    (hc : idealClass 𝔪 ⟨I, hI⟩ = c) : rayClassCoeff 𝔪 c I = 1 := by
  rw [rayClassCoeff_apply_of_isCoprimeTo c (Modulus.mem_integralIdealsPrimeTo.mp hI),
    ite_eq_left hc]

/-- The indicator of `c` vanishes at an ideal of the carrier lying in another class. -/
theorem rayClassCoeff_apply_of_idealClass_ne {𝔪 : Modulus K} {c : RayClassGroup 𝔪}
    {I : (Ideal (𝓞 K))⁰} (hI : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪)
    (hc : idealClass 𝔪 ⟨I, hI⟩ ≠ c) : rayClassCoeff 𝔪 c I = 0 := by
  rw [rayClassCoeff_apply_of_isCoprimeTo c (Modulus.mem_integralIdealsPrimeTo.mp hI),
    ite_eq_right hc]

open Classical in
/-- The indicator as a single test: the ideal lies in the carrier and its class there is `c`. -/
private theorem rayClassCoeff_eq_ite (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (I : (Ideal (𝓞 K))⁰) :
    rayClassCoeff 𝔪 c I =
      if ∃ h : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪, idealClass 𝔪 ⟨I, h⟩ = c then 1
      else 0 := by
  by_cases hI : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪
  · by_cases hc : idealClass 𝔪 ⟨I, hI⟩ = c
    · rw [rayClassCoeff_apply_of_idealClass_eq hI hc, ite_eq_left ⟨hI, hc⟩]
    · rw [rayClassCoeff_apply_of_idealClass_ne hI hc, ite_eq_right fun ⟨_, h⟩ ↦ hc h]
  · rw [rayClassCoeff_apply_of_not_isCoprimeTo c (mt Modulus.mem_integralIdealsPrimeTo.mpr hI),
      ite_eq_right fun ⟨h, _⟩ ↦ hI h]

/-- The class indicator is bounded by `1`. -/
theorem norm_rayClassCoeff_le_one (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (I : (Ideal (𝓞 K))⁰) :
    ‖rayClassCoeff 𝔪 c I‖ ≤ 1 := by
  rw [rayClassCoeff_eq_ite]
  split_ifs <;> simp

/-- **The class indicators sum to the indicator of the ideals prime to `𝔪`**, which is the
indicator weight `ofBadPrimes` of the support of `𝔪`: every ideal prime to `𝔪` lies in exactly one
ray class, and an ideal sharing a prime with the finite part lies in none. -/
theorem sum_rayClassCoeff (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)] :
    ∑ c, rayClassCoeff 𝔪 c =
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
      ite_eq_right (mt (Modulus.isCoprimeTo_iff.mpr ∘ Ideal.isPrimeTo_iff.mp) hI)]

/-! ### The deleted Euler factors -/

/-- **The finite Euler correction** `∏_{𝔭 ∣ 𝔪₀} (1 - N𝔭 ^ (-s))`, the product over the support of
`𝔪`, that is over the primes dividing its finite part `𝔪₀` (`Modulus.mem_support_iff`). These are
exactly the Euler factors of `ζ_K` that coprimality to `𝔪` deletes. It is `1` for a modulus with
trivial finite part and, on the real half-line `s > 0`, only then
(`finiteEulerCorrection_eq_one_iff`). -/
noncomputable def finiteEulerCorrection (𝔪 : Modulus K) (s : ℂ) : ℂ :=
  ∏ 𝔭 ∈ 𝔪.support, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))

/-- The finite Euler correction, written out. -/
theorem finiteEulerCorrection_eq (𝔪 : Modulus K) (s : ℂ) :
    finiteEulerCorrection 𝔪 s = ∏ 𝔭 ∈ 𝔪.support, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) :=
  (rfl)

/-- The trivial modulus deletes no Euler factor. -/
@[simp]
theorem finiteEulerCorrection_one (s : ℂ) : finiteEulerCorrection (Modulus.one K) s = 1 := by
  rw [finiteEulerCorrection_eq, Modulus.support_one, Finset.prod_empty]

/-- **The finite Euler correction detects the finite part.** At a real `s > 0` each deleted factor
lies strictly between `0` and `1`, so the correction is `1` exactly when nothing is deleted, that
is, when the support of `𝔪` is empty. -/
theorem finiteEulerCorrection_eq_one_iff (𝔪 : Modulus K) {s : ℝ} (hs : 0 < s) :
    finiteEulerCorrection 𝔪 s = 1 ↔ 𝔪.support = ∅ := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [finiteEulerCorrection_eq, h, Finset.prod_empty]⟩
  by_contra hne
  obtain ⟨𝔭, h𝔭⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  -- the real factor `1 - N𝔭 ^ (-s)` of each prime lies in `(0, 1)`
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun v ↦ 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)
  have hpow (v : HeightOneSpectrum (𝓞 K)) : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (mod_cast HeightOneSpectrum.one_lt_absNorm v)
      (neg_lt_zero.mpr hs)
  have hpos (v : HeightOneSpectrum (𝓞 K)) : 0 < (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) :=
    Real.rpow_pos_of_pos (mod_cast (HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one) _
  have hreal : finiteEulerCorrection 𝔪 s = ((∏ v ∈ 𝔪.support, f v : ℝ) : ℂ) := by
    rw [finiteEulerCorrection_eq, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_neg, Complex.ofReal_natCast]
  have hlt : ∏ v ∈ 𝔪.support, f v < 1 := by
    rw [← Finset.mul_prod_erase _ f h𝔭]
    refine (mul_le_of_le_one_right (sub_pos.mpr (hpow 𝔭)).le (Finset.prod_le_one₀
      (fun v _ ↦ (sub_pos.mpr (hpow v)).le) fun v _ ↦ ?_)).trans_lt (sub_lt_self 1 (hpos 𝔭))
    exact sub_le_self 1 (hpos v).le
  rw [hreal] at h
  exact hlt.ne (Complex.ofReal_eq_one.mp h)

/-! ### The partial zeta series on `Re s > 1` -/

/-- **The partial zeta series converges absolutely on `Re s > 1`**, since its coefficients are
bounded by those of `ζ_K`. -/
theorem LSeriesSummable_normCoeff_rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (normCoeff K (rayClassCoeff 𝔪 c)) s :=
  LSeriesSummable_normCoeff K
    (summable_idealTerm_of_bounded_of_one_lt_re (norm_rayClassCoeff_le_one 𝔪 c) hs)

/-- **The sum over the ray classes is not `ζ_K`.** On `Re s > 1` the partial zeta series of the
ray classes of `𝔪` sum to the series over all ideals prime to `𝔪`, which is `ζ_K(s)` with the
Euler factors at the primes dividing the finite part of `𝔪` deleted. -/
theorem sum_LSeries_rayClassCoeff (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)] {s : ℂ}
    (hs : 1 < s.re) :
    ∑ c, LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s =
      dedekindZeta K s * finiteEulerCorrection 𝔪 s := by
  rw [← LSeries_sum fun c _ ↦ LSeriesSummable_normCoeff_rayClassCoeff 𝔪 c hs,
    finiteEulerCorrection_eq, ← LSeries_ofBadPrimes 𝔪.support hs, ← sum_rayClassCoeff]
  congr 1
  ext n
  simp only [Finset.sum_apply, normCoeff_eq_sum_normFiber]
  exact Finset.sum_comm

/-- **The class-group specialization.** For the trivial modulus nothing is deleted, and the
partial zeta series of the ideal classes sum to `ζ_K(s)` on `Re s > 1`. -/
theorem sum_LSeries_rayClassCoeff_one [Fintype (RayClassGroup (Modulus.one K))] {s : ℂ}
    (hs : 1 < s.re) :
    ∑ c, LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s = dedekindZeta K s := by
  rw [sum_LSeries_rayClassCoeff _ hs, finiteEulerCorrection_one, mul_one]

/-- **The sum over the ray classes is `ζ_K` only for a trivial finite part.** At a real `s > 1`
the partial zeta series of the ray classes of `𝔪` sum to `ζ_K(s)` exactly when the support of `𝔪`
is empty; one prime dividing the finite part already breaks the equality. -/
theorem sum_LSeries_rayClassCoeff_eq_dedekindZeta_iff (𝔪 : Modulus K)
    [Fintype (RayClassGroup 𝔪)] {s : ℝ} (hs : 1 < s) :
    ∑ c, LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s = dedekindZeta K s ↔ 𝔪.support = ∅ := by
  have hs' : 1 < (s : ℂ).re := by rwa [Complex.ofReal_re]
  rw [sum_LSeries_rayClassCoeff 𝔪 hs', mul_eq_left₀ (dedekindZeta_ne_zero_of_one_lt_re hs'),
    finiteEulerCorrection_eq_one_iff 𝔪 (zero_lt_one.trans hs)]

/-! ### The common residue at `s = 1` -/

/-- **The summatory function of a class indicator is the ray class ideal count**: summing the
indicator of `c` over the nonzero integral ideals of norm at most `x` counts the ideals prime to
`𝔪` in the class `c` of norm at most `x`. -/
theorem idealSummatory_rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    idealSummatory K (rayClassCoeff 𝔪 c) x = rayClassIdealCountingFunction 𝔪 c x := by
  classical
  rw [idealSummatory_apply]
  simp_rw [rayClassCoeff_eq_ite]
  rw [Finset.sum_boole, rayClassIdealCountingFunction_def, ← Nat.card_eq_finsetCard]
  congr 1
  set N : (Ideal (𝓞 K))⁰ → ℕ := fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K))
  -- an ideal of the carrier in the class `c` is a nonzero ideal of norm at most `x` passing the
  -- indicator's test, and conversely
  refine Nat.card_congr
    { toFun I := ⟨⟨I.1, (Finset.mem_filter.mp I.2).2.fst⟩, (Finset.mem_filter.mp I.2).2.snd,
        (mem_normLE N).mp (Finset.mem_filter.mp I.2).1⟩
      invFun J := ⟨⟨J.1, mem_nonZeroDivisors_of_ne_zero
          (Modulus.isCoprimeTo_iff.mp (Modulus.mem_integralIdealsPrimeTo.mp J.1.2)).1⟩,
        Finset.mem_filter.mpr ⟨(mem_normLE N).mpr J.2.2, J.1.2, J.2.1⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- **The common residue of the partial zeta functions.** As `s → 1⁺` along the reals,
`(s - 1) ζ(s, c)` tends to the main term `rayClassIdealMainTerm 𝔪` of the ray class ideal count,
the same for every class `c`. Its closed form is
`rayClassIdealMainTerm_eq_finiteEulerCorrection`. -/
theorem tendsto_sub_one_mul_LSeries_rayClassCoeff (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (normCoeff K (rayClassCoeff 𝔪 c)) s) (𝓝[>] 1)
      (𝓝 (rayClassIdealMainTerm 𝔪 : ℂ)) := by
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div ?_ fun s hs ↦
    LSeriesSummable_normCoeff_rayClassCoeff 𝔪 c (by rwa [Complex.ofReal_re])
  -- the partial sums of the coefficients are the ray class ideal counts
  refine ((Complex.continuous_ofReal.tendsto _).comp
    ((tendsto_rayClassIdealCountingFunction_div 𝔪 c).comp tendsto_natCast_atTop_atTop)).congr
    fun n ↦ ?_
  have h := idealSummatory_eq_sum_Icc_normCoeff K (rayClassCoeff 𝔪 c) n
  rw [Nat.floor_natCast, idealSummatory_rayClassCoeff] at h
  simp [← h]

/-- **The common residue, written out**: the Dedekind-zeta residue times the finite Euler
correction at `s = 1`, divided by the ray class number. -/
theorem rayClassIdealMainTerm_eq_finiteEulerCorrection (𝔪 : Modulus K) :
    (rayClassIdealMainTerm 𝔪 : ℂ) =
      dedekindZeta_residue K * finiteEulerCorrection 𝔪 1 / Nat.card (RayClassGroup 𝔪) := by
  rw [rayClassIdealMainTerm_eq, finiteEulerCorrection_eq]
  push_cast
  simp_rw [Complex.cpow_neg_one]
  ring

end TauCeti.LFunctions
