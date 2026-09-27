/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
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

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI and Chapter VIII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
-/

public section

open Asymptotics Filter IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

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

-- The Dirichlet coefficients of `ζ_K` minus `ρ` times those of the Riemann zeta function have
-- partial sums `O(n ^ (1 - 1 / [K : ℚ]))`.
private theorem isBigO_sum_Icc_dedekindZetaCoeff_sub :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ((fun k ↦ (dedekindZetaCoeff K k : ℂ)) -
        (dedekindZeta_residue K : ℂ) • (1 : ℕ → ℂ)) k) =O[atTop]
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
  have hsum (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, ((fun k ↦ (dedekindZetaCoeff K k : ℂ)) -
      (dedekindZeta_residue K : ℂ) • (1 : ℕ → ℂ)) k =
      (((idealsLE K n).card : ℝ) - dedekindZeta_residue K * n : ℝ) := by
    simp [Finset.sum_sub_distrib, hcount, mul_comm]
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
  have hO := isBigO_sum_Icc_dedekindZetaCoeff_sub K
  generalize hf : (fun k ↦ (dedekindZetaCoeff K k : ℂ)) -
    (dedekindZeta_residue K : ℂ) • (1 : ℕ → ℂ) = f at hO
  -- The partial-summation integral of `f` continues `LSeries f`; add `ρ (ζ(s) - 1 / (s - 1))`.
  refine ⟨fun s ↦ s * (∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) *
      (t : ℂ) ^ (-(s + 1))) + dedekindZeta_residue K * riemannZeta₀ s,
    (TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO f hO).fun_add
      (differentiable_riemannZeta₀.const_mul _).differentiableOn, fun s hs ↦ ?_⟩
  have hr : 0 ≤ 1 - 1 / (Module.finrank ℚ K : ℝ) :=
    sub_nonneg.mpr (div_le_one_of_le₀ (Nat.one_le_cast.mpr Module.finrank_pos) (Nat.cast_nonneg _))
  have hsζ : LSeriesSummable (fun k ↦ (dedekindZetaCoeff K k : ℂ)) s :=
    (LSeriesSummable_dedekindZetaCoeff_iff K).mpr hs
  have hs1 : LSeriesSummable ((dedekindZeta_residue K : ℂ) • (1 : ℕ → ℂ)) s :=
    LSeriesSummable.smul _ (LSeriesSummable_one_iff.mpr hs)
  have hs0 : s ≠ 1 := fun h ↦ by simp [h] at hs
  have hrs : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re :=
    setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.le
  dsimp only
  rw [← LSeries_eq_mul_integral f hr hrs (hf ▸ hsζ.sub hs1) hO, ← hf, LSeries_sub hsζ hs1,
    LSeries_smul, LSeries_one_eq_riemannZeta hs, riemannZeta_eq_inv_sub_add hs0,
    dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  ring

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

end TauCeti
