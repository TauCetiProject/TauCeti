/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.DedekindDomain.Ideal.Away
import TauCeti.RingTheory.Valuation.Approximation

/-!
# Moving fractional ideals while preserving finite congruences

Let `R` be a Dedekind domain with fraction field `K`. A fractional ideal whose multiplicities
vanish on a finite set `S` can be moved to one whose multiplicities vanish on any other finite
set `T`, by multiplying by a principal ideal with generator congruent to one to prescribed
orders at the primes in `S`.

This is the moving argument for surjectivity of transitions between finite ray class groups:
the multiplier preserves the smaller ray class and removes the additional prime divisors.
The multiplier lies in `Kˣ`; neither it nor the resulting fractional ideal is required to be
integral. This differs from choosing an integral representative of one fixed ray class.

The proof uses `Valuation.exists_forall_sub_lt` and the principal-ideal multiplicity formula
`FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation`. At the original primes the target
is one; at each additional prime its valuation cancels the multiplicity of the given ideal.
No finiteness of residue fields or of the class group is needed.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors WithZero

namespace TauCeti.NumberFieldArithmetic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A fractional ideal away from `S` has a principal multiple away from `T` whose generator
is congruent to one to any prescribed orders at `S`. The generator is a field unit, and the
congruence is expressed by the normalized adic valuations. No inclusion between `S` and `T`
is required. -/
theorem exists_mul_toPrincipalIdeal_mem_idealsAway {S : Finset (HeightOneSpectrum R)}
    (I : idealsAway K S) (T : Finset (HeightOneSpectrum R)) (n : HeightOneSpectrum R → ℕ) :
    ∃ x : Kˣ,
      (∀ v ∈ S, v.valuation K ((x : K) - 1) ≤ WithZero.exp (-(n v : ℤ))) ∧
      (I : (FractionalIdeal R⁰ K)ˣ) * toPrincipalIdeal R K x ∈ idealsAway K T := by
  classical
  by_cases hST : S ∪ T = ∅
  · have hS : S = ∅ := Finset.union_eq_empty.mp hST |>.1
    have hT : T = ∅ := Finset.union_eq_empty.mp hST |>.2
    exact ⟨1, by simp [hS], by simp [hT]⟩
  -- Approximate one at the original primes and targets of the cancelling valuation elsewhere.
  choose p hp using fun v : HeightOneSpectrum R ↦
    v.valuation_surjective K (WithZero.exp (FractionalIdeal.count K v I.1.1))
  let a : HeightOneSpectrum R → K := fun v ↦ if v ∈ S then 1 else p v
  let ε : HeightOneSpectrum R → ℤᵐ⁰ := fun v ↦
    if v ∈ S then WithZero.exp (-(n v : ℤ))
    else WithZero.exp (FractionalIdeal.count K v I.1.1)
  obtain ⟨x, hx⟩ := Valuation.exists_forall_sub_lt
    (fun v : {v : HeightOneSpectrum R // v ∈ S ∪ T} ↦ v.1.valuation K)
    (fun _ ↦ inferInstance)
    (fun v w hvw heq ↦ hvw (Subtype.ext (eq_of_valuation_isEquiv_valuation heq)))
    (fun v ↦ a v.1) (fun v ↦ ε v.1) (fun v ↦ by
      dsimp [ε]
      split <;> exact WithZero.exp_ne_zero)
  have hval (v : HeightOneSpectrum R) (hv : v ∈ S ∪ T) :
      v.valuation K x = if v ∈ S then 1 else
        WithZero.exp (FractionalIdeal.count K v I.1.1) := by
    by_cases hvS : v ∈ S
    · have hε : ε v ≤ 1 := by simp [ε, hvS]
      have hlt : v.valuation K (x - 1) < 1 := by
        simpa [a, hvS] using (hx ⟨v, hv⟩).trans_le hε
      simpa [hvS] using Valuation.map_eq_of_sub_lt (v.valuation K) (x := 1) (y := x)
        (by simpa only [map_one] using hlt)
    · have hlt : v.valuation K (x - p v) < v.valuation K (p v) := by
        simpa [a, ε, hvS, hp] using hx ⟨v, hv⟩
      simp [hvS, Valuation.map_eq_of_sub_lt (v.valuation K) hlt, hp]
  -- A nonzero prescribed valuation at any prime in the union rules out a zero multiplier.
  have hx0 : x ≠ 0 := by
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hST
    have hne : v.valuation K x ≠ 0 := by
      rw [hval v hv]
      split
      · exact one_ne_zero
      · exact WithZero.exp_ne_zero
    exact (Valuation.ne_zero_iff _).mp hne
  -- Read the approximation as congruence, and the exact valuations as ideal multiplicities.
  refine ⟨Units.mk0 x hx0, fun v hv ↦ ?_, mem_idealsAway_iff.mpr fun v hv ↦ ?_⟩
  · simpa [a, ε, hv] using (hx ⟨v, Finset.mem_union_left T hv⟩).le
  · rw [Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero I.1)
      (Units.ne_zero (toPrincipalIdeal R K (Units.mk0 x hx0))),
      FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation, Units.val_mk0,
      hval v (Finset.mem_union_right S hv)]
    by_cases hvS : v ∈ S
    · simp [hvS, mem_idealsAway_iff.mp I.2 v hvS]
    · simp [hvS]

end TauCeti.NumberFieldArithmetic
