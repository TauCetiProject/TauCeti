/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Basic
import Mathlib.RingTheory.Flat.Localization
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.Localization.Module
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Localizing a Cohen–Macaulay module

Let `M` be a finite Cohen–Macaulay module over a Noetherian local ring `R`. Then for every prime
`p` of `R`, the localization `M_p` is a Cohen–Macaulay module over `R_p` (Stacks, Lemma 10.103.11
(0AAG)). This is what makes the two usual definitions of a Cohen–Macaulay ring agree: asking
that `R_m` be Cohen–Macaulay at every maximal ideal `m`, or that `R_p` be Cohen–Macaulay at every
prime `p`. Over a Noetherian local ring it also shows that a finite Cohen–Macaulay module satisfies
every Serre condition `(S_n)` (`Module.IsCohenMacaulay.satisfiesSerreS`).

## Proof

We follow Matsumura's argument, by induction on `n = depth M_p`. If `n = 0`, then `p` is an
associated prime of `M`. A Cohen–Macaulay module has no embedded primes, so `p` is minimal in the
support of `M`, and the support of `M_p` is the closed point alone; a module with
zero-dimensional support is Cohen–Macaulay. If `n > 0`, then `p` is not an associated prime of
`M`. No associated prime of `M` contains `p` either: being minimal in the support, it would equal
`p`. Prime avoidance gives an `M`-regular `x ∈ p`. Then `M ⧸ x M` is Cohen–Macaulay over `R`, and
its localization `M_p ⧸ x M_p` has depth `n - 1`, so it is Cohen–Macaulay over `R_p` by induction.
Since `x` stays regular on `M_p`, the module `M_p` is Cohen–Macaulay.

## Main results

* `Module.IsCohenMacaulay.localizedModule`: the localization of a finite Cohen–Macaulay module
  over a Noetherian local ring at a prime is Cohen–Macaulay.

## References

* [Stacks Project, Lemma 10.103.11](https://stacks.math.columbia.edu/tag/0AAG)
* H. Matsumura, *Commutative Ring Theory*, Theorem 17.3 (iii).
-/

public section

universe u v

open IsLocalRing

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]

/-- The induction behind `Module.IsCohenMacaulay.localizedModule`, on the depth `n` of `M_p`. -/
private theorem IsCohenMacaulay.localizedModule_of_depth_eq {p : Ideal R} [p.IsPrime] (n : ℕ)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] (h : IsCohenMacaulay R M)
    (hn : depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) = n) :
    IsCohenMacaulay (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  induction n generalizing M with
  | zero =>
    rcases subsingleton_or_nontrivial (LocalizedModule p.primeCompl M) with _ | _
    · exact isCohenMacaulay_of_subsingleton
    -- `p` is associated to `M`, hence minimal in its support, so `dim Supp M_p = 0`.
    have hp := TauCeti.depth_localizedModule_eq_zero_iff.1 hn
    rw [h.associatedPrimes_eq_minimalPrimes] at hp
    rw [isCohenMacaulay_iff_supportDim_le_depth, hn]
    exact_mod_cast (supportDim_localizedModule_nonpos_iff hp.1.2).2 hp
  | succ n ih =>
    -- `M_p ≠ 0`, since its depth is finite, so `p` lies in the support of `M`.
    have : Nontrivial (LocalizedModule p.primeCompl M) := not_subsingleton_iff_nontrivial.1 fun _ ↦
      ENat.natCast_ne_top _ (hn ▸ depth_eq_top_of_subsingleton _)
    have hann : annihilator R M ≤ p :=
      annihilator_le_of_mem_support (p := ⟨p, ‹_›⟩) (mem_support_iff.2 ‹_›)
    -- No associated prime `q ⊇ p` of `M` exists: `q` would be minimal in the support, hence `p`,
    -- while `depth M_p ≠ 0` says that `p` is not associated.
    have hp : p ∉ associatedPrimes R M := TauCeti.one_le_depth_localizedModule_iff.1 <| by
      rw [hn]
      exact_mod_cast Nat.succ_pos n
    obtain ⟨x, hxp, reg⟩ := (p.exists_mem_isSMulRegular_iff (M := M)).2 fun q hq hpq ↦ by
      rw [h.associatedPrimes_eq_minimalPrimes] at hp hq
      exact hp (le_antisymm (hq.2 ⟨‹_›, hann⟩ hpq) hpq ▸ hq)
    have hx : algebraMap R (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p x).2 hxp
    have regₚ := IsSMulRegular.of_isLocalizedModule (S := Localization.AtPrime p) p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) reg
    let e : LocalizedModule p.primeCompl (QuotSMulTop x M) ≃ₗ[Localization.AtPrime p]
        QuotSMulTop (algebraMap R (Localization.AtPrime p) x) (LocalizedModule p.primeCompl M) :=
      TauCeti.localizedQuotSMulTopEquiv M x p.primeCompl
    -- `(M ⧸ x M)_p = M_p ⧸ x M_p` has depth `n`, so it is Cohen–Macaulay by induction.
    have hquot := ih ((isCohenMacaulay_quotSMulTop_iff reg (le_maximalIdeal_of_isPrime p hxp)).2 h)
      (by
        have hsucc := TauCeti.depth_localizedModule_quotSMulTop_add_one reg p hxp
        rw [hn, Nat.cast_add_one] at hsucc
        exact WithTop.add_right_cancel ENat.one_ne_top hsucc)
    exact (isCohenMacaulay_quotSMulTop_iff regₚ hx).1 ((LinearEquiv.isCohenMacaulay_iff e).1 hquot)

/-- The localization of a finite Cohen–Macaulay module over a Noetherian local ring at a prime `p`
is a Cohen–Macaulay module over `R_p`. Stacks, Lemma 10.103.11 (0AAG). -/
@[stacks 0AAG]
theorem IsCohenMacaulay.localizedModule {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (h : IsCohenMacaulay R M) (p : Ideal R) [p.IsPrime] :
    IsCohenMacaulay (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  rcases subsingleton_or_nontrivial (LocalizedModule p.primeCompl M) with _ | _
  · exact isCohenMacaulay_of_subsingleton
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 <| mt (depth_eq_top_iff
    (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M))).1 (not_subsingleton _)
  exact h.localizedModule_of_depth_eq n hn.symm

end Module
