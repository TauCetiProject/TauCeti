/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Height and coheight of primes in a Cohen–Macaulay local ring

In a Noetherian local ring `R` that is Cohen–Macaulay over itself, every prime `p` satisfies
`ht p + dim (R ⧸ p) = dim R` (Stacks, Lemma 10.103.10 (0AAF)). The inequality `≤` holds in every
ring (`Ideal.height_add_ringKrullDim_quotient_le`); the Cohen–Macaulay hypothesis gives the
reverse one. Without it the equation fails: in a local ring whose spectrum is a plane meeting a
line at a point, a minimal prime `p` cutting out the line has `ht p + dim (R ⧸ p) = 1 < 2`.

The proof chooses an `R`-regular sequence `r₁, …, rₖ` in `p` of maximal length. Its length is at
most `ht p`, and by maximality every element of `p` is a zero divisor on `N = R ⧸ (r₁, …, rₖ)`.
By prime avoidance `p` lies in an associated prime of `N`. Now `N` is again Cohen–Macaulay, of
dimension `dim R - k`, so it has no embedded primes, and `p` is itself associated to `N`. By
unmixedness `dim (R ⧸ p) = dim N = dim R - k ≥ dim R - ht p`.

This is the dimension formula that makes Cohen–Macaulay rings catenary: applied in the
localizations of a Cohen–Macaulay ring, it says that heights add along chains of primes.

## Main results

* `Module.IsCohenMacaulay.height_add_ringKrullDim_quotient`: for a Noetherian local ring `R`
  that is Cohen–Macaulay over itself and a prime `p`, `ht p + dim (R ⧸ p) = dim R`
  (Stacks, Lemma 10.103.10 (0AAF)).

## References

* [Stacks Project, Lemma 10.103.10](https://stacks.math.columbia.edu/tag/0AAF).
* H. Matsumura, *Commutative Ring Theory*, Theorem 17.4 (i).
-/

public section

universe u

open IsLocalRing RingTheory.Sequence Ideal

namespace Module.IsCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **The dimension formula in a Cohen–Macaulay local ring.** For a Noetherian local ring `R`
that is Cohen–Macaulay over itself and a prime `p` of `R`, `ht p + dim (R ⧸ p) = dim R`.
Stacks, Lemma 10.103.10 (0AAF); H. Matsumura, *Commutative Ring Theory*, Theorem 17.4 (i). -/
@[stacks 0AAF]
theorem height_add_ringKrullDim_quotient (h : IsCohenMacaulay R R) (p : Ideal R) [p.IsPrime] :
    p.height + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  refine le_antisymm p.height_add_ringKrullDim_quotient_le ?_
  -- The lengths of weakly `R`-regular sequences in `p` are bounded by `ht p`, so the longest one
  -- exists.
  let lengths : Set ℕ∞ := {(List.length rs : ℕ∞) | (rs : List R)
    (_ : IsWeaklyRegular R rs) (_ : ∀ r ∈ rs, r ∈ p)}
  have : Nonempty lengths := ⟨⟨0, [], IsWeaklyRegular.nil R R, by simp, rfl⟩⟩
  have hbound : sSup lengths ≤ p.height := by
    rw [← p.depth_eq_sSup_length_isWeaklyRegular (ModuleCat.of R R)]
    refine p.depth_le_height _ p le_rfl ?_
    exact (annihilator_eq_bot.2 inferInstance).trans_le bot_le
  obtain ⟨rs, reg, mem, hlen⟩ := ENat.sSup_mem_of_nonempty_of_lt_top <|
    hbound.trans_lt (height_lt_top IsPrime.ne_top')
  have regR : IsRegular R rs :=
    (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal fun r hr ↦
      le_maximalIdeal IsPrime.ne_top' (mem r hr)).2 reg
  -- The quotient `N = R ⧸ (r₁, …, rₖ)` is Cohen–Macaulay, of dimension `dim R - k`.
  let N := R ⧸ ofList rs • (⊤ : Submodule R R)
  have hN : IsCohenMacaulay R N := (isCohenMacaulay_quotient_ofList_smul_iff rs regR).2 h
  have hann : annihilator R N ≤ p := by
    simp only [N, smul_eq_mul, mul_top, Ideal.annihilator_quotient]
    exact span_le.2 mem
  -- By maximality of `r₁, …, rₖ`, no element of `p` is regular on `N`.
  have hnreg : ¬ ∃ a ∈ p, IsSMulRegular N a := fun ⟨a, ha, hreg⟩ ↦ by
    have hmem : ((rs ++ [a]).length : ℕ∞) ∈ lengths := ⟨rs ++ [a],
      (isWeaklyRegular_append_iff R rs [a]).2 ⟨reg, (isWeaklyRegular_singleton_iff N a).2 hreg⟩,
      by simpa [or_imp, forall_and] using ⟨mem, ha⟩, rfl⟩
    exact absurd (le_sSup hmem) (by simp [← hlen, ENat.lt_add_one_iff])
  -- So `p` lies in an associated prime of `N`, which is minimal over the annihilator of `N`, so
  -- `p` is itself associated to `N`.
  obtain ⟨q, hq, hpq⟩ : ∃ q ∈ associatedPrimes R N, p ≤ q := by
    simpa using mt (p.exists_mem_isSMulRegular_iff (M := N)).2 hnreg
  have hqp : q = p :=
    le_antisymm ((hN.associatedPrimes_eq_minimalPrimes ▸ hq).2 ⟨inferInstance, hann⟩ hpq) hpq
  have hpN : IsAssociatedPrime p N := AssociatedPrimes.mem_iff.1 (hqp ▸ hq)
  -- By unmixedness `dim (R ⧸ p) = dim N = dim R - k`, and `k ≤ ht p`.
  rw [hN.ringKrullDim_quotient_eq_supportDim hpN, ← supportDim_self_eq_ringKrullDim,
    ← supportDim_add_length_eq_supportDim_of_isRegular rs regR, add_comm]
  gcongr
  exact_mod_cast hlen ▸ hbound

end Module.IsCohenMacaulay
