/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import TauCeti.NumberTheory.NumberField.HalfPlane
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.HalfPlaneIdentity
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

* `TauCeti.isBigO_card_idealsLE_sub`: the number of nonzero integral ideals of norm at most `x` is
  `ρ x + O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.exists_differentiableOn_eq_dedekindZeta_sub`: `ζ_K(s) - ρ / (s - 1)` extends
  holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]`.
* `TauCeti.exists_differentiableOn_eq_dedekindZeta`: `ζ_K` extends holomorphically from
  `Re s > 1` to `{s | 1 - 1 / [K : ℚ] < s.re} \ {1}`.
* `TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub` and
  `TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes`: the same for the Dedekind zeta
  function with the Euler factors at a finite set of primes deleted, with the correspondingly
  corrected residue.
* `TauCeti.ne_zero_of_eqOn_dedekindZeta`: a continuation of `ζ_K` differentiable at a point
  `s ≠ 1` of the line `Re s = 1` does not vanish there.
* `TauCeti.exists_differentiableOn_eq_sub_one_mul_dedekindZeta`: `(s - 1) ζ_K(s)` extends
  holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]`, taking value
  `dedekindZeta_residue K` at `1` and nonvanishing on `Re s ≥ 1`.
* `TauCeti.exists_continuousOn_eq_neg_deriv_dedekindZeta_div_sub`: `-ζ_K'(s) / ζ_K(s) - 1 / (s - 1)`
  extends continuously from `Re s > 1` to `Re s ≥ 1`.
* `TauCeti.tendsto_sub_one_mul_of_eventuallyEq_dedekindZeta`:
  `(s - 1) * f s → dedekindZeta_residue K` as `s → 1` along `𝓝[≠] 1` for any local continuation
  `f` of `ζ_K` differentiable on a punctured neighbourhood of `1`.

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

-- Adding `ρ / (s - 1)` back to a regularized continuation gives punctured-domain differentiability
-- and agreement with `F` on `Re s > 1`.
private theorem exists_differentiableOn_add_div_sub_one {F G : ℂ → ℂ} {ρ : ℂ}
    (hG : DifferentiableOn ℂ G {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - ρ / (s - 1)) :
    ∃ T : ℂ → ℂ, DifferentiableOn ℂ T ({s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} \ {1}) ∧
      Set.EqOn T F {s | 1 < s.re} := by
  refine ⟨fun s ↦ G s + ρ / (s - 1), (hG.mono Set.sdiff_subset).add
    ((differentiableOn_const ρ).div (differentiableOn_id.sub_const 1) fun _ hs ↦
      sub_ne_zero.mpr hs.2), fun s hs ↦ ?_⟩
  simp only [hGF s hs, sub_add_cancel]

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

/-- **Meromorphic continuation of the Dedekind zeta function across `Re s = 1`.** There is a
function holomorphic on `{s | 1 - 1 / [K : ℚ] < s.re} \ {1}` agreeing with `ζ_K` on `Re s > 1`. -/
theorem exists_differentiableOn_eq_dedekindZeta :
    ∃ T : ℂ → ℂ, DifferentiableOn ℂ T ({s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} \ {1}) ∧
      Set.EqOn T (dedekindZeta K) {s | 1 < s.re} := by
  obtain ⟨G, hG, hGζ⟩ := exists_differentiableOn_eq_dedekindZeta_sub K
  exact exists_differentiableOn_add_div_sub_one K hG hGζ

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

/-- **Meromorphic continuation across `Re s = 1` of the Dedekind zeta function with finitely many
Euler factors deleted.** There is a function holomorphic on `{s | 1 - 1 / [K : ℚ] < s.re} \ {1}`
agreeing with the `L`-series of the indicator of ideals prime to `S` on `Re s > 1`. -/
theorem exists_differentiableOn_eq_LSeries_ofBadPrimes (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ T : ℂ → ℂ, DifferentiableOn ℂ T ({s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} \ {1}) ∧
      Set.EqOn T (LSeries (normCoeff K
        (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
          S.finite_toSet).toIdealArithmeticFunction)) {s | 1 < s.re} := by
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K S
  exact exists_differentiableOn_add_div_sub_one K hG hGL

variable {K} in
/-- **The Dedekind zeta function has no zeros on the line `Re s = 1` away from its pole.** If `f`
agrees with `ζ_K` on `Re s > 1` and is complex differentiable at a point `s ≠ 1` with `Re s = 1`,
then `f s ≠ 0`. By `exists_differentiableOn_eq_dedekindZeta`, such an `f` exists: the
meromorphic continuation of `ζ_K`. -/
theorem ne_zero_of_eqOn_dedekindZeta {f : ℂ → ℂ} {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1)
    (hf : DifferentiableAt ℂ f s) (hfζ : Set.EqOn f (dedekindZeta K) {z | 1 < z.re}) :
    f s ≠ 0 := by
  obtain ⟨T, hT, hTζ⟩ := exists_differentiableOn_eq_dedekindZeta K
  have hs₂1 : 2 * s - 1 ≠ 1 := fun h ↦ hs1 (by linear_combination h / 2)
  have hs₂re : 1 ≤ (2 * s - 1).re := by norm_num [hs]
  have hTcont : ContinuousAt T (2 * s - 1) := by
    have hopen : IsOpen ({z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} \ {1}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    exact (hT.differentiableAt (hopen.mem_nhds
      ⟨setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs₂re, hs₂1⟩)).continuousAt
  -- `ζ_K` is the `L`-series of the trivial unitary weight, whose pointwise square is itself; so
  -- the `3-4-1` criterion for unitary weights applies, with `T` continuing the square's series.
  have hζ : LSeries (normCoeff K (1 : UnitaryIdealWeight K).toIdealArithmeticFunction) =
      dedekindZeta K := by
    funext z
    rw [UnitaryIdealWeight.toIdealArithmeticFunction_one, dedekindZeta_eq_LSeries_normCoeff_one]
  exact (1 : UnitaryIdealWeight K).ne_zero_of_eqOn_LSeries hs hf (by rwa [hζ]) hTcont
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

/-- On a small punctured disc around `1`, `(s - 1) * f s` agrees with the regularized Dedekind
zeta continuation `H s` whenever `f` is differentiable on a punctured neighbourhood of `1` and
agrees with `ζ_K` on the right side of a neighbourhood of `1`. -/
private theorem eventuallyEq_sub_one_mul_of_eventuallyEq_dedekindZeta {K : Type*} [Field K]
    [NumberField K] {f H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re})
    (hHζ : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * dedekindZeta K s)
    (hf : ∀ᶠ s in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ f s)
    (hfζ : f =ᶠ[𝓝[{s : ℂ | 1 < s.re}] 1] dedekindZeta K) :
    (fun s : ℂ ↦ (s - 1) * f s) =ᶠ[𝓝[≠] 1] H := by
  have hFdiff : ∀ᶠ s in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ (fun z : ℂ ↦ (z - 1) * f z) s := by
    filter_upwards [hf] with s hs
    exact (differentiableAt_id.sub_const 1).mul hs
  have hHdiff : ∀ᶠ s in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ H s := by
    have hmem : {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K (by simp))
    filter_upwards [nhdsWithin_le_nhds hmem] with s hs
    exact hH.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have hFH : (fun s : ℂ ↦ (s - 1) * f s) =ᶠ[𝓝[{s : ℂ | 1 < s.re}] 1] H := by
    filter_upwards [hfζ, self_mem_nhdsWithin] with s hfs hs
    rw [hfs, hHζ s hs]
  exact TauCeti.eventuallyEq_nhdsNE_of_differentiableAt_of_eventuallyEq_re_gt hFdiff hHdiff
    (by simpa using hFH)

variable {K} in
/-- **Any punctured-neighbourhood continuation of `ζ_K` has residue `dedekindZeta_residue K` at
`1`.** If `f` is complex differentiable on a punctured neighbourhood of `1` and agrees with `ζ_K`
on the `Re s > 1` side of a neighbourhood of `1`, then `(s - 1) * f s → dedekindZeta_residue K`
along `𝓝[≠] 1`. -/
theorem tendsto_sub_one_mul_of_eventuallyEq_dedekindZeta {f : ℂ → ℂ}
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
  exact hlim.congr' (eventuallyEq_sub_one_mul_of_eventuallyEq_dedekindZeta hH hHζ hf hfζ).symm

end TauCeti
