/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ThreeFourOne
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
import TauCeti.NumberTheory.LSeries.SumCoeff
import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Asymptotic

/-!
# The Dedekind zeta function across the line `Re s = 1`

Let `K` be a number field of degree `d = [K : ℚ]`. The number of nonzero integral ideals of `𝓞 K`
of absolute norm at most `x` is `ρ x + O(x ^ (1 - 1 / d))`, where `ρ = dedekindZeta_residue K`:
summing the ray class ideal counts over the classes of the trivial modulus recovers the total
count, and every class has the same main term.

By partial summation this power saving continues the Dedekind zeta function across the line
`Re s = 1`, with a single simple pole there. Comparing the Dirichlet coefficients of `ζ_K` with
`ρ` times those of the Riemann zeta function, the difference has partial sums `O(n ^ (1 - 1 / d))`,
so its `L`-series continues holomorphically to `Re s > 1 - 1 / d`; and `ζ(s) - 1 / (s - 1)` is
entire (Mathlib's `riemannZeta₀`). Hence `ζ_K(s) - ρ / (s - 1)` agrees on `Re s > 1` with a
function holomorphic on `Re s > 1 - 1 / d`.

Deleting finitely many Euler factors multiplies `ζ_K` by the entire function
`∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`, so the Dedekind zeta function with the Euler factors at a finite set
`S` of primes deleted has the same kind of continuation, with residue
`ρ * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))` at its simple pole `s = 1`. This is the `L`-series of the trivial
member of a family of ideal weights with bad primes `S`, such as the trivial Galois character of a
Galois extension, whose bad primes are the ramified ones.

The continuation has no zeros on the line `Re s = 1`. Off the pole this is the classical `3-4-1`
argument: the Euler product gives `1 ≤ ‖ζ_K(σ) ^ 3 ζ_K(σ + it) ^ 4 ζ_K(σ + 2it)‖` for `σ > 1`,
which a zero at `1 + it` would contradict as `σ → 1⁺`. It is the case of the trivial weight of the
criterion `TauCeti.UnitaryIdealWeight.ne_zero_of_eqOn_LSeries` for unitary ideal weights, whose
pointwise square is again the trivial weight, so `ζ_K` itself supplies the continuation of the
square's `L`-series. Consequently `(s - 1) ζ_K(s)` continues
holomorphically to `Re s > 1 - 1 / d` without zeros on `Re s ≥ 1`, and
`-ζ_K'(s) / ζ_K(s) - 1 / (s - 1)`, the negative logarithmic derivative of `ζ_K(s)` with its pole
removed, extends continuously from `Re s > 1` to `Re s ≥ 1`. This is the boundary behaviour a
Tauberian theorem needs to count prime ideals.

## Main results

* `TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re`: the closed half-plane
  `Re s ≥ 1` lies in the half-plane of continuation.
* `TauCeti.isBigO_card_idealsLE_sub`: the number of nonzero integral ideals of norm at most `x` is
  `ρ x + O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.exists_differentiableOn_eq_dedekindZeta_sub`: `ζ_K(s) - ρ / (s - 1)` extends
  holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]`.
* `TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub`: the same for the Dedekind zeta
  function with the Euler factors at a finite set of primes deleted, with the correspondingly
  corrected residue.
* `TauCeti.ne_zero_of_eqOn_dedekindZeta`: a continuation of `ζ_K` differentiable at a point
  `s ≠ 1` of the line `Re s = 1` does not vanish there.
* `TauCeti.exists_differentiableOn_eq_sub_one_mul_dedekindZeta`: `(s - 1) ζ_K(s)` extends
  holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]`, taking value
  `dedekindZeta_residue K` at `1` and nonvanishing on `Re s ≥ 1`.
* `TauCeti.exists_continuousOn_eq_neg_deriv_dedekindZeta_div_sub`: `-ζ_K'(s) / ζ_K(s) - 1 / (s - 1)`
  extends continuously from `Re s > 1` to `Re s ≥ 1`.
* `TauCeti.tendsto_re_dedekindZeta_nhdsGT_one`: `(ζ_K σ).re → +∞` as real `σ → 1⁺`.
* `TauCeti.tendsto_sub_one_mul_of_eqOn_dedekindZeta`: `(s - 1) * f s → dedekindZeta_residue K` as
  `s → 1` along `𝓝[≠] 1` for any local continuation `f` of `ζ_K` differentiable near `1`.
* `TauCeti.UnitaryIdealWeight.ne_zero_of_eqOn_LSeries_of_isNormTwistOnGood_sq`: `3-4-1`
  nonvanishing on `Re s = 1` away from `1 + (u / 2) * I` when `(χ ^ 2).1.IsNormTwistOnGood u`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI and Chapter VIII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4, for the `3-4-1` argument.
* The regularization by `(s - 1) ζ_K(s)` follows Mathlib's
  `DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁`
  (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`).
-/

public section

open Asymptotics Filter IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors Topology

namespace TauCeti

/-- The closed half-plane `Re s ≥ 1` lies in the half-plane of the Dedekind zeta continuation. -/
theorem setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re
    (K : Type*) [Field K] [NumberField K] :
    {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
  fun _ hs ↦
    (sub_lt_self (1 : ℝ) (one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))).trans_le hs

variable (K : Type*) [Field K] [NumberField K]

-- The nonzero integral ideals of norm at most `x` are those prime to the trivial modulus.
private theorem card_idealsLE_eq_sum_rayClassIdealCountingFunction
    [Fintype (RayClassGroup (Modulus.one K))] (x : ℝ) :
    (idealsLE K x).card =
      ∑ c : RayClassGroup (Modulus.one K), rayClassIdealCountingFunction (Modulus.one K) c x := by
  rw [sum_rayClassIdealCountingFunction, ← Nat.card_eq_finsetCard]
  -- An ideal is prime to the trivial modulus exactly when it is nonzero.
  have hmem (I : Ideal (𝓞 K)) :
      I ∈ (Ideal (𝓞 K))⁰ ↔ I ∈ integralIdealsPrimeTo (Modulus.one K) := by
    simp [mem_nonZeroDivisors_iff_ne_zero, NumberFieldArithmetic.mem_integralIdealsAway_iff]
  exact Nat.card_congr <| Equiv.subtypeEquiv (Equiv.subtypeEquivRight hmem) fun _ ↦ mem_normLE _

/-- **The ideal count with a power saving.** The number of nonzero integral ideals of `𝓞 K` of
absolute norm at most `x` is `dedekindZeta_residue K * x + O(x ^ (1 - 1 / [K : ℚ]))`. -/
theorem isBigO_card_idealsLE_sub :
    (fun x : ℝ ↦ ((idealsLE K x).card : ℝ) - dedekindZeta_residue K * x) =O[atTop]
      fun x : ℝ ↦ x ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  have : Fintype (RayClassGroup (Modulus.one K)) := Fintype.ofFinite _
  -- Each of the `#Cl(K)` classes of the trivial modulus has main term `ρ / #Cl(K)`.
  have hmain : ∑ _c : RayClassGroup (Modulus.one K), rayClassIdealMainTerm (Modulus.one K) =
      dedekindZeta_residue K := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
      rayClassIdealMainTerm_eq, Modulus.support_one, Finset.prod_empty, mul_one,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]
  have heq (x : ℝ) : ((idealsLE K x).card : ℝ) - dedekindZeta_residue K * x =
      ∑ c : RayClassGroup (Modulus.one K),
        ((rayClassIdealCountingFunction (Modulus.one K) c x : ℝ) -
          rayClassIdealMainTerm (Modulus.one K) * x) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmain,
      card_idealsLE_eq_sum_rayClassIdealCountingFunction, Nat.cast_sum]
  simp_rw [heq]
  exact IsBigO.fun_sum fun c _ ↦ isBigO_rayClassIdealCountingFunction_sub (Modulus.one K) c

-- The partial sums of the Dirichlet coefficients of `ζ_K` are `ρ n + O(n ^ (1 - 1 / [K : ℚ]))`.
private theorem isBigO_sum_Icc_dedekindZetaCoeff_sub :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (dedekindZetaCoeff K k : ℂ) -
        (dedekindZeta_residue K : ℂ) * n) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  -- The partial sums of the coefficients of `ζ_K` count the ideals of norm at most `n`.
  have hcount (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, (dedekindZetaCoeff K k : ℂ) =
      ((idealsLE K n).card : ℂ) := by
    have h := idealSummatory_eq_sum_Icc_normCoeff K 1 n
    rw [idealSummatory_apply, Nat.floor_natCast] at h
    simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [h]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [normCoeff_one_apply, ite_eq_right (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1)]
  have hsum (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, (dedekindZetaCoeff K k : ℂ) -
      (dedekindZeta_residue K : ℂ) * n =
      (((idealsLE K n).card : ℝ) - dedekindZeta_residue K * n : ℝ) := by
    simp [hcount]
  simp_rw [hsum, one_div]
  exact Complex.isBigO_ofReal_left.mpr
    ((isBigO_card_idealsLE_sub K).comp_tendsto tendsto_natCast_atTop_atTop)

/-- **The Dedekind zeta function across `Re s = 1`.** There is a function holomorphic on the
half-plane `Re s > 1 - 1 / [K : ℚ]` that agrees with `ζ_K(s) - ρ / (s - 1)` on `Re s > 1`, where
`ρ = dedekindZeta_residue K`. So `ζ_K` continues meromorphically to `Re s > 1 - 1 / [K : ℚ]`, with a
single pole, simple with residue `ρ`, at `s = 1`. -/
theorem exists_differentiableOn_eq_dedekindZeta_sub : ∃ G : ℂ → ℂ,
    DifferentiableOn ℂ G {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = dedekindZeta K s - dedekindZeta_residue K / (s - 1) := by
  obtain ⟨G, hG, hGζ⟩ := TauCeti.LSeries.exists_differentiableOn_eq_LSeries_sub_div_of_isBigO _ _
    (isBigO_sum_Icc_dedekindZetaCoeff_sub K)
    fun s hs ↦ (LSeriesSummable_dedekindZetaCoeff_iff K).mpr hs
  exact ⟨G, hG, fun s hs ↦ by rw [hGζ s hs, dedekindZeta_eq_LSeries_dedekindZetaCoeff]⟩

/-- **The Dedekind zeta function with finitely many Euler factors deleted, across `Re s = 1`.**
For a finite set `S` of primes of `𝓞 K`, there is a function holomorphic on the half-plane
`Re s > 1 - 1 / [K : ℚ]` that agrees on `Re s > 1` with `L_S(s) - ρ_S / (s - 1)`. Here `L_S` is
the `L`-series of the indicator of the ideals prime to `S`, that is
`ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`, and
`ρ_S = dedekindZeta_residue K * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))` is its residue at `s = 1`. -/
theorem exists_differentiableOn_eq_LSeries_ofBadPrimes_sub (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = LSeries (normCoeff K
          (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
            S.finite_toSet).toIdealArithmeticFunction) s -
        dedekindZeta_residue K * (∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ))) /
          (s - 1) := by
  obtain ⟨G, hG, hGζ⟩ := exists_differentiableOn_eq_dedekindZeta_sub K
  set E : ℂ → ℂ := fun s ↦ ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))
  have hE : Differentiable ℂ E := Differentiable.fun_finsetProd fun P _ ↦
    (differentiable_id.neg.const_cpow (Or.inl P.natCast_absNorm_ne_zero)).const_sub 1
  -- `L_S = ζ_K E = G E + ρ E / (s - 1)`, and `E(s) / (s - 1) = E(1) / (s - 1) + dslope E 1 s`.
  refine ⟨fun s ↦ G s * E s + dedekindZeta_residue K * dslope E 1 s,
    (hG.mul hE.differentiableOn).add ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
      hE.differentiableOn |>.const_mul _ |>.mono (Set.subset_univ _)), fun s hs ↦ ?_⟩
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [h] at hs
  dsimp only
  rw [hGζ s hs, LSeries_ofBadPrimes S hs, dslope_of_ne _ (sub_ne_zero.mp hs0), slope_def_field]
  simp only [E]
  ring

variable {K} in
/-- **The Dedekind zeta function has no zeros on the line `Re s = 1` away from its pole.** If `f`
agrees with `ζ_K` on `Re s > 1` and is complex differentiable at a point `s ≠ 1` with `Re s = 1`,
then `f s ≠ 0`. By `exists_differentiableOn_eq_dedekindZeta_sub`, such an `f` exists: the
meromorphic continuation of `ζ_K`. -/
theorem ne_zero_of_eqOn_dedekindZeta {f : ℂ → ℂ} {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1)
    (hf : DifferentiableAt ℂ f s) (hfζ : Set.EqOn f (dedekindZeta K) {z | 1 < z.re}) :
    f s ≠ 0 := by
  obtain ⟨G, hG, hGζ⟩ := exists_differentiableOn_eq_dedekindZeta_sub K
  -- `ζ_K` continues to `T = G + ρ / (s - 1)`, which is continuous at `2s - 1 ≠ 1`.
  set T : ℂ → ℂ := fun z ↦ G z + dedekindZeta_residue K / (z - 1)
  have hs₂1 : 2 * s - 1 ≠ 1 := fun h ↦ hs1 (by linear_combination h / 2)
  have hT : ContinuousAt T (2 * s - 1) := by
    have hmem : {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} ∈ 𝓝 (2 * s - 1) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K
          (show 1 ≤ (2 * s - 1).re by norm_num [hs]))
    exact (hG.differentiableAt hmem).continuousAt.add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs₂1))
  have hTζ : Set.EqOn T (dedekindZeta K) {z | 1 < z.re} := fun z hz ↦ by
    simp only [T, hGζ z hz, sub_add_cancel]
  -- `ζ_K` is the `L`-series of the trivial unitary weight, whose pointwise square is itself; so
  -- the `3-4-1` criterion for unitary weights applies, with `T` continuing the square's series.
  have hζ : LSeries (normCoeff K (1 : UnitaryIdealWeight K).toIdealArithmeticFunction) =
      dedekindZeta K := by
    funext z
    rw [UnitaryIdealWeight.toIdealArithmeticFunction_one, dedekindZeta_eq_LSeries_normCoeff_one]
  exact (1 : UnitaryIdealWeight K).ne_zero_of_eqOn_LSeries hs hf (by rwa [hζ]) hT
    (by rwa [one_pow, hζ])

/-- **The regularized Dedekind zeta function across `Re s = 1`.** There is a function `H`
holomorphic on `Re s > 1 - 1 / [K : ℚ]` agreeing with `(s - 1) * ζ_K(s)` on `Re s > 1`, taking
value `dedekindZeta_residue K` at `s = 1`, and nonvanishing throughout `Re s ≥ 1`. -/
theorem exists_differentiableOn_eq_sub_one_mul_dedekindZeta : ∃ H : ℂ → ℂ,
    DifferentiableOn ℂ H {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
      (∀ s : ℂ, 1 < s.re → H s = (s - 1) * dedekindZeta K s) ∧
      H 1 = (dedekindZeta_residue K : ℂ) ∧
      ∀ s : ℂ, 1 ≤ s.re → H s ≠ 0 := by
  obtain ⟨G, hG, hGζ⟩ := exists_differentiableOn_eq_dedekindZeta_sub K
  set U := {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUs {s : ℂ} (hs : 1 ≤ s.re) : U ∈ 𝓝 s :=
    hU.mem_nhds (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs)
  set ρ : ℂ := (dedekindZeta_residue K : ℂ)
  set H : ℂ → ℂ := fun s ↦ (s - 1) * G s + ρ
  have hH : DifferentiableOn ℂ H U := ((differentiableOn_id.sub_const 1).mul hG).add_const ρ
  have hsub {s : ℂ} (hs : 1 < s.re) : s - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ by simp [h] at hs
  have hHζ : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * dedekindZeta K s := fun s hs ↦ by
    simp only [H, hGζ s hs]
    field_simp [hsub hs]
    ring
  have hH1 : H 1 = ρ := by simp [H]
  refine ⟨H, hH, hHζ, hH1, fun s hs ↦ ?_⟩
  rcases hs.lt_or_eq with hs | hs
  · rw [hHζ s hs]
    exact mul_ne_zero (hsub hs) (dedekindZeta_ne_zero_of_one_lt_re hs)
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [hH1]
    simpa [ρ] using dedekindZeta_residue_ne_zero K
  have hne := ne_zero_of_eqOn_dedekindZeta (K := K) (f := fun z ↦ H z / (z - 1)) hs.symm hs1
    ((hH.differentiableAt (hUs hs.le)).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1))
    fun z (hz : 1 < z.re) ↦ by simp only [hHζ z hz, mul_div_cancel_left₀ _ (hsub hz)]
  exact fun h ↦ hne (by simp [h])

/-- **The regularized logarithmic derivative of the Dedekind zeta function.** The function
`-ζ_K'(s) / ζ_K(s) - 1 / (s - 1)` extends from `Re s > 1` to a function continuous on
`Re s ≥ 1`: the pole of `ζ_K` at `s = 1` is simple, and `ζ_K` has no zeros on `Re s ≥ 1`. -/
theorem exists_continuousOn_eq_neg_deriv_dedekindZeta_div_sub : ∃ G : ℂ → ℂ,
    ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      G s = -deriv (dedekindZeta K) s / dedekindZeta K s - 1 / (s - 1) := by
  obtain ⟨H, hH, hHζ, _, hH0⟩ := exists_differentiableOn_eq_sub_one_mul_dedekindZeta K
  set U := {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUs {s : ℂ} (hs : 1 ≤ s.re) : U ∈ 𝓝 s :=
    hU.mem_nhds (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs)
  have hsub {s : ℂ} (hs : 1 < s.re) : s - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ by simp [h] at hs
  refine ⟨fun s ↦ -logDeriv H s, ?_, fun s hs ↦ ?_⟩
  · simp only [logDeriv_apply]
    exact (((hH.deriv hU).continuousOn.mono
      (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K)).div
      (hH.continuousOn.mono (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K))
      fun _ hs ↦ hH0 _ hs).neg
  have hL : logDeriv (dedekindZeta K) s = logDeriv (H / fun z ↦ z - 1) s :=
    (logDeriv_congr_nhds <| eventually_of_mem
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) fun z (hz : 1 < z.re) ↦ by
        simp only [Pi.div_apply, hHζ z hz, mul_div_cancel_left₀ _ (hsub hz)]).eq_of_nhds
  dsimp only
  rw [neg_div, ← logDeriv_apply, hL, logDeriv_div (g := fun z ↦ z - 1) s (hH0 s hs.le) (hsub hs)
    (hH.differentiableAt (hUs hs.le)) (differentiableAt_id.sub_const 1), logDeriv_apply (· - 1),
    deriv_sub_const, deriv_id'']
  ring

/-- **Real blowup of the Dedekind zeta function at `1⁺`.** As real `σ → 1⁺`, the real part of
`ζ_K(σ)` tends to `+∞`, since `(σ - 1) ζ_K(σ)` tends to the positive residue
`NumberField.dedekindZeta_residue K`. -/
theorem tendsto_re_dedekindZeta_nhdsGT_one :
    Tendsto (fun σ : ℝ ↦ (dedekindZeta K σ).re) (𝓝[>] 1) atTop := by
  have hre : Tendsto (fun σ : ℝ ↦ (σ - 1) * (dedekindZeta K σ).re) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K)) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    refine (Complex.ofReal_re (dedekindZeta_residue K) ▸ h).congr fun σ ↦ ?_
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.re_ofReal_mul]
  have hsub0 : Tendsto (fun σ : ℝ ↦ σ - 1) (𝓝 1) (𝓝 0) := by
    simpa using (continuous_sub_right (1 : ℝ)).tendsto 1
  have hsub : Tendsto (fun σ : ℝ ↦ σ - 1) (𝓝[>] 1) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsub0.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) ↦ sub_pos.mpr hσ)
  refine (Filter.Tendsto.atTop_mul_pos (dedekindZeta_residue_pos K)
    (tendsto_inv_nhdsGT_zero.comp hsub) hre).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  simp [inv_mul_cancel_left₀ (sub_ne_zero.mpr (ne_of_gt hσ))]

/-- On a small punctured disc around `1`, `(s - 1) * f s` agrees with the regularized Dedekind
zeta continuation `H s` whenever `f` is differentiable near `1` and agrees with `ζ_K` on the right
side of a neighbourhood of `1`. -/
private theorem eventuallyEq_sub_one_mul_of_eqOn_dedekindZeta {K : Type*} [Field K] [NumberField K]
    {f H : ℂ → ℂ} (hH : DifferentiableOn ℂ H {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re})
    (hHζ : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * dedekindZeta K s)
    (hf : ∀ᶠ s in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ f s)
    (hfζ : f =ᶠ[𝓝[{s : ℂ | 1 < s.re}] 1] dedekindZeta K) :
    (fun s : ℂ ↦ (s - 1) * f s) =ᶠ[𝓝[≠] 1] H := by
  obtain ⟨r₁, hr₁, hfr₁⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hf)
  obtain ⟨r₂, hr₂, hfr₂⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hfζ)
  set r : ℝ := min r₁ (min r₂ (1 / (Module.finrank ℚ K : ℝ)))
  have hr : 0 < r :=
    lt_min hr₁ (lt_min hr₂ (one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)))
  set V : Set ℂ := Metric.ball (1 : ℂ) r \ {1}
  have hVopen : IsOpen V := Metric.isOpen_ball.sdiff isClosed_singleton
  have hVsub : V ⊆ {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := fun s hs ↦ by
    have hdist : dist s 1 < 1 / (Module.finrank ℚ K : ℝ) :=
      (Metric.mem_ball.mp hs.1).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hre : 1 - s.re ≤ dist s 1 := by
      rw [Complex.dist_eq]
      calc 1 - s.re = -(s - 1).re := by simp
        _ ≤ |(s - 1).re| := neg_le_abs _
        _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    have hre' : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re := by linarith
    simpa only [Set.mem_ofPred_eq] using hre'
  have hFdiff : DifferentiableOn ℂ (fun s : ℂ ↦ (s - 1) * f s) V := fun s hs ↦
    ((differentiableAt_id.sub_const 1).mul
      (hfr₁ ((Metric.mem_ball.mp hs.1).trans_le (min_le_left _ _)) hs.2)).differentiableWithinAt
  have hFV : AnalyticOnNhd ℂ (fun s : ℂ ↦ (s - 1) * f s) V := hFdiff.analyticOnNhd hVopen
  have hHV : AnalyticOnNhd ℂ H V := (hH.mono hVsub).analyticOnNhd hVopen
  have hVconn : IsPreconnected V :=
    (isConnected_ball_sdiff_singleton (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ) hr).isPreconnected
  set z₀ : ℂ := 1 + ((r / 2 : ℝ) : ℂ)
  have hz₀_ball : dist z₀ 1 < r := by
    rw [Complex.dist_eq]
    simpa [z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using half_lt_self hr
  have hz₀V : z₀ ∈ V :=
    ⟨Metric.mem_ball.mpr hz₀_ball,
      fun h ↦ by have := congrArg Complex.re h; simp [z₀] at this; linarith⟩
  have hnhds : Metric.ball (1 : ℂ) r₂ ∩ {s : ℂ | 1 < s.re} ∈ 𝓝 z₀ :=
    (Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds
      ⟨Metric.mem_ball.mpr (hz₀_ball.trans_le ((min_le_right _ _).trans (min_le_left _ _))),
        by simp [z₀, half_pos hr]⟩
  have hfeq : (fun s : ℂ ↦ (s - 1) * f s) =ᶠ[𝓝 z₀] H :=
    Filter.eventuallyEq_of_mem hnhds fun s hs ↦ by
      rw [hfr₂ (Metric.mem_ball.mp hs.1) hs.2, hHζ s hs.2]
  have hEqV : Set.EqOn (fun s : ℂ ↦ (s - 1) * f s) H V :=
    hFV.eqOn_of_preconnected_of_eventuallyEq hHV hVconn hz₀V hfeq
  filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds (1 : ℂ) hr)] with s hs
  exact hEqV ⟨hs.2, hs.1⟩

variable {K} in
/-- **Any punctured-neighbourhood continuation of `ζ_K` has residue `dedekindZeta_residue K` at
`1`.** If `f` is complex differentiable on a punctured neighbourhood of `1` and agrees with `ζ_K`
on the `Re s > 1` side of a neighbourhood of `1`, then `(s - 1) * f s → dedekindZeta_residue K`
along `𝓝[≠] 1`. -/
theorem tendsto_sub_one_mul_of_eqOn_dedekindZeta {f : ℂ → ℂ}
    (hf : ∀ᶠ s in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ f s)
    (hfζ : f =ᶠ[𝓝[{s : ℂ | 1 < s.re}] 1] dedekindZeta K) :
    Tendsto (fun s : ℂ ↦ (s - 1) * f s) (𝓝[≠] 1) (𝓝 (dedekindZeta_residue K : ℂ)) := by
  obtain ⟨H, hH, hHζ, hH1, _⟩ := exists_differentiableOn_eq_sub_one_mul_dedekindZeta K
  have hHcont : ContinuousAt H 1 :=
    (hH.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K (by simp)))).continuousAt
  have hlim : Tendsto H (𝓝[≠] 1) (𝓝 (dedekindZeta_residue K : ℂ)) := by
    rw [← hH1]
    exact hHcont.tendsto.mono_left nhdsWithin_le_nhds
  exact hlim.congr' (eventuallyEq_sub_one_mul_of_eqOn_dedekindZeta hH hHζ hf hfζ).symm

variable {K} in
/-- **The `3-4-1` nonvanishing criterion on `Re s = 1` away from `1 + (u / 2) * I`** for a
unitary weight `χ` whose square is a purely imaginary norm twist `I ↦ N(I) ^ (u * I)` on its good
ideals. -/
theorem UnitaryIdealWeight.ne_zero_of_eqOn_LSeries_of_isNormTwistOnGood_sq
    (χ : UnitaryIdealWeight K) {u : ℝ} (hχ₂ : (χ ^ 2).1.IsNormTwistOnGood u) {L : ℂ → ℂ}
    {s : ℂ} (hs : s.re = 1) (hsu : s ≠ 1 + (u : ℂ) / 2 * Complex.I)
    (hLs : DifferentiableAt ℂ L s)
    (hLL : Set.EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re}) :
    L s ≠ 0 := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (χ ^ 2).1.badPrimes = (S : Set (HeightOneSpectrum (𝓞 K))) :=
    ⟨(χ ^ 2).1.finite_badPrimes.toFinset, (χ ^ 2).1.finite_badPrimes.coe_toFinset.symm⟩
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K S
  set ρ : ℂ := dedekindZeta_residue K * ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ))
  set w₀ : ℂ := 2 * s - 1 - (u : ℂ) * Complex.I
  have hw₀ : w₀ - 1 ≠ 0 := fun h ↦ hsu (by linear_combination h / 2)
  have hcont : ContinuousAt
      (fun z : ℂ ↦ G (z - (u : ℂ) * Complex.I) + ρ / (z - (u : ℂ) * Complex.I - 1))
      (2 * s - 1) := by
    have hG₀ : ContinuousAt G w₀ :=
      (hG.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K
          (show 1 ≤ w₀.re by norm_num [w₀, hs])))).continuousAt
    have hsub : ContinuousAt (fun z : ℂ ↦ z - (u : ℂ) * Complex.I) (2 * s - 1) :=
      continuousAt_id.sub continuousAt_const
    exact (hG₀.comp_of_eq hsub rfl).add
      (continuousAt_const.div (hsub.sub continuousAt_const) hw₀)
  refine χ.ne_zero_of_eqOn_LSeries hs hLs hLL hcont fun z hz ↦ ?_
  have hz' : 1 < (z - (u : ℂ) * Complex.I).re := by simpa using hz
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, hχ₂.LSeries_normCoeff hS, hGL _ hz',
    sub_add_cancel]

end TauCeti
