/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates

/-!
# Convergence of the ideal- and prime-indexed Dirichlet series

The nonzero integral ideals of `𝓞 K` carry the Dirichlet series `∑ N(I) ^ (-s)`, whose abscissa
of absolute convergence is exactly `1`: that is `TauCeti.summable_idealTerm_one_iff`, read off
from the two-sided linear ideal counts.  Distinct height-one primes are distinct nonzero
integral ideals, so the prime-indexed series `∑ N(𝔭) ^ (-s)` is a subfamily of that one, and
converges for every `s > 1`.  Only convergence transfers this way, not the abscissa: divergence
of the all-prime sum at `s = 1` is a separate statement, and is not proved here.

`NumberField.Set.primeIdealZetaSum S s` is that sum restricted to a set `S` of primes.  It is a
`tsum`, and a `tsum` takes the junk value `0` on a family that is not summable, so summability
is what separates a statement about the prime Dirichlet sum from a statement about that junk
value.  The results below supply it for every `s > 1` and every set of primes.

## Main results

* `TauCeti.summable_absNorm_rpow_ideal_iff`: over the nonzero integral ideals of `𝓞 K`, the
  series `∑ N(I) ^ (-s)` converges exactly for `1 < s`.  This is the real-variable form of
  `TauCeti.summable_idealTerm_one_iff`.
* `TauCeti.summable_absNorm_rpow_primes_of_one_lt`: over the height-one primes of `𝓞 K`, the
  series `∑ N(𝔭) ^ (-s)` converges for every `1 < s`.
* `TauCeti.summable_absNorm_rpow_subtype_of_one_lt`: the same over an arbitrary set of
  height-one primes.  This is the family `NumberField.Set.primeIdealZetaSum` sums, so it is the
  form its consumers need.
* `NumberField.Set.primeIdealZetaSum_mono_set`: the prime ideal zeta sum is monotone under
  inclusion of sets of primes, given summability over the larger set;
  `NumberField.Set.primeIdealZetaSum_mono_set_of_one_lt` is its `1 < s` specialization.
* `NumberField.Set.primeIdealZetaSum_pos`: a summable sum over a nonempty set of primes is
  positive; `NumberField.Set.primeIdealZetaSum_univ_pos` applies this to all primes. The
  corresponding `_of_one_lt` lemmas supply summability from `1 < s`.

## Implementation notes

The prime-indexed statement is obtained by restricting the ideal-indexed one along
`𝔭 ↦ 𝔭.asIdeal`, which is injective into `(Ideal (𝓞 K))⁰`, rather than by comparing each
`N(𝔭) = p ^ f` with the rational prime `p` below it and summing over the rational primes.  The
restriction is the shorter route on the full set of primes, and reuses the exact abscissa already
established for the trivial ideal weight.  The comparison route is not redundant: on the primes
of residue degree above one it yields the strictly wider half-line `s > 1/2`, and
`TauCeti.summable_absNorm_rpow_higherDegreePrimes` takes it for exactly that reason.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* Adapted from the Birkbeck–Brasca Chebotarev density project,
  <https://github.com/CBirkbeck/chebotarev-density> (Apache-2.0), commit
  `8575c9df1ae0a61120ab5c964c7911414254bec7`, file `CebotarevDensity/Density.lean`:
  `summable_absNorm_rpow_ideal_iff` from `summable_nonzeroIdeal_absNorm_rpow`,
  `summable_absNorm_rpow_subtype_of_one_lt` from `summable_prime_absNorm_rpow`, and
  `NumberField.Set.primeIdealZetaSum_mono_set` from `primeIdealZetaSum_le_of_subset`.
-/

public section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti

-- Source: Layer 7.1 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, which builds the
-- Dirichlet-density calculus directly on `NumberField.Set.primeIdealZetaSum`, and whose
-- Chebotarev consumer is Layer 3 of `TauCetiRoadmap/Chebotarev/README.md`.

/-! ### The ideal-indexed series, as a real Dirichlet series -/

/-- **The ideal-indexed Dirichlet series converges exactly on `s > 1`.** The real-variable form
of `TauCeti.summable_idealTerm_one_iff`, stated for the real power `N(I) ^ (-s)` rather than for
the complex term `TauCeti.idealTerm`, which is the shape the prime-indexed results below meet. -/
@[simp]
theorem summable_absNorm_rpow_ideal_iff {s : ℝ} :
    (Summable fun I : (Ideal (𝓞 K))⁰ ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)) ↔ 1 < s := by
  -- Each real term is the norm of the complex term at `s`, and norms decide summability.
  have key : (fun I : (Ideal (𝓞 K))⁰ ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s))
      = fun I ↦ ‖idealTerm K (1 : IdealArithmeticFunction K) (s : ℂ) I‖ :=
    funext fun I ↦ by simp [Real.rpow_neg]
  rw [key, summable_norm_iff, summable_idealTerm_one_iff, Complex.ofReal_re]

/-! ### The prime-indexed series -/

/-- **The prime-indexed Dirichlet series converges for `s > 1`.** The height-one-prime analogue of
`TauCeti.summable_absNorm_rpow_ideal_iff`. -/
theorem summable_absNorm_rpow_primes_of_one_lt {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  -- Every height-one prime is a nonzero integral ideal and is determined by that ideal, so the
  -- prime-indexed family is an injective reindexing of a subfamily of the ideal-indexed one.
  -- The injectivity is Mathlib's `HeightOneSpectrum.asIdeal_injective` factored through the
  -- `nonZeroDivisors` coercion; nothing about it is proved here.
  have hinj : Function.Injective fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ : (Ideal (𝓞 K))⁰) :=
    Function.Injective.of_comp (f := Subtype.val) HeightOneSpectrum.asIdeal_injective
  exact ((summable_absNorm_rpow_ideal_iff.mpr hs).comp_injective hinj).congr fun _ ↦ rfl

/-- **Restricted to any set of height-one primes**, the prime-indexed Dirichlet series still
converges for `s > 1`: a subfamily of a summable family is summable.

This is the family `NumberField.Set.primeIdealZetaSum` sums, so it is the summability its
consumers need in order to denote a genuine sum rather than the `tsum` junk value. -/
theorem summable_absNorm_rpow_subtype_of_one_lt (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ}
    (hs : 1 < s) : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) :=
  (summable_absNorm_rpow_primes_of_one_lt hs).subtype S

end TauCeti

namespace NumberField.Set

open TauCeti

/-- **The prime ideal zeta sum is monotone under inclusion of sets of primes.** The hypothesis is
summability over the larger set, which is what the proof actually consumes: a sparse set of primes
can be summable well outside the half-line on which the all-prime series converges.
`primeIdealZetaSum_mono_set_of_one_lt` is the specialization to `1 < s`.

Summability is not decoration: `tsum` returns `0` on a family that is not summable, so an
inequality between two such sums can fail with a positive left-hand side and a vanishing right. -/
theorem primeIdealZetaSum_mono_set {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T) {s : ℝ}
    (hT : Summable fun 𝔭 : T ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  -- Enlarging the set of primes adds nonnegative terms to a convergent sum: `Set.inclusion hST`
  -- is injective, and matches the terms of the two sums exactly; summability over `S` is the
  -- restriction of `hT` along that inclusion.
  exact (hT.comp_injective (Set.inclusion_injective hST)).tsum_le_tsum_of_inj (Set.inclusion hST)
    (Set.inclusion_injective hST) (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl) hT

/-- The `1 < s` specialization of `primeIdealZetaSum_mono_set`, where summability over the larger
set is automatic. -/
theorem primeIdealZetaSum_mono_set_of_one_lt {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    {s : ℝ} (hs : 1 < s) : S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s :=
  primeIdealZetaSum_mono_set hST (summable_absNorm_rpow_subtype_of_one_lt T hs)

/-- **A summable prime ideal zeta sum over a nonempty set of primes is positive.** Every term is
positive; summability ensures that the sum is genuine rather than the `tsum` junk value `0`. -/
theorem primeIdealZetaSum_pos {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Nonempty) {s : ℝ}
    (h : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    0 < S.primeIdealZetaSum s := by
  obtain ⟨𝔭, h𝔭⟩ := hS
  rw [primeIdealZetaSum_def]
  exact h.tsum_pos (fun _ ↦ by positivity) ⟨𝔭, h𝔭⟩
    (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨_, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩)) _)

/-- The `1 < s` specialization of `primeIdealZetaSum_pos`, where summability is automatic. -/
theorem primeIdealZetaSum_pos_of_one_lt {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Nonempty)
    {s : ℝ} (hs : 1 < s) : 0 < S.primeIdealZetaSum s :=
  primeIdealZetaSum_pos hS (summable_absNorm_rpow_subtype_of_one_lt S hs)

/-- **A summable sum over all primes is positive.** This is the denominator of the ratio defining
`NumberField.Set.HasDirichletDensity`; the ring of integers is not a field, so it has a height-one
prime. -/
theorem primeIdealZetaSum_univ_pos {s : ℝ}
    (h : Summable fun 𝔭 : (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ↦
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    0 < (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
  obtain ⟨𝔭, -⟩ := (HeightOneSpectrum.ideal_ne_top_iff_exists
    (RingOfIntegers.not_isField K) (⊥ : Ideal (𝓞 K))).1 bot_ne_top
  exact primeIdealZetaSum_pos ⟨𝔭, Set.mem_univ 𝔭⟩ h

/-- The `1 < s` specialization of `primeIdealZetaSum_univ_pos`, where summability is automatic. -/
theorem primeIdealZetaSum_univ_pos_of_one_lt {s : ℝ} (hs : 1 < s) :
    0 < (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s :=
  primeIdealZetaSum_univ_pos (summable_absNorm_rpow_subtype_of_one_lt Set.univ hs)

end NumberField.Set
