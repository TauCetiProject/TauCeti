/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.PowerBounded

import TauCeti.RingTheory.Affinoid.ValueGroup

/-!
# When the supremum seminorm is a multiplicative norm

Let `A` be a nonzero affinoid algebra over a complete nonarchimedean field `K`, with a complete
ultrametric algebra norm, and let `A° ⊇ A°°` be its power-bounded subring and its ideal of
topologically nilpotent elements. This file shows that the supremum seminorm `|·|sup` is
multiplicative exactly when the canonical reduction `Ã = A° ⧸ A°°` is an integral domain, that is,
when `A°°` is a prime ideal of `A°` (`Ideal.Quotient.isDomain_iff_prime`). Since the kernel of
`|·|sup` is the nilradical, `|·|sup` is a multiplicative norm, an `AbsoluteValue A ℝ`, exactly when
moreover `A` is reduced.

Both conditions are needed. In `K⟨T⟩ ⧸ (T²)` the nonzero nilpotent `T` has supremum seminorm
zero, while `|a + bT|sup = |a|` shows that `Ã` is the residue field of `K`. Conversely, for
`0 < |c| < 1` the annulus algebra `K⟨X, Y⟩ ⧸ (XY - c)` is a domain with `|X|sup = |Y|sup = 1` but
`|XY|sup = |c|`, so a reduced domain need not have a multiplicative supremum seminorm.

The criterion only uses `A° = {f | |f|sup ≤ 1}`, `A°° = {f | |f|sup < 1}` and the value-group
normalisation: a single exponent `m ≥ 1` and scalars `c, d` give `|c f ^ m|sup = |d g ^ m|sup = 1`
whenever `|f|sup` and `|g|sup` are positive, so primality of `A°°` forces `|c d (f g) ^ m|sup = 1`.

## Main results

* `TauCeti.IsAffinoidAlgebra.supSeminorm_mul`: if `A°°` is prime, then `|f g|sup = |f|sup |g|sup`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_mul_iff_isPrime`: for nonzero `A`, `|·|sup` is
  multiplicative if and only if `A°°` is a prime ideal of `A°`.
* `TauCeti.IsAffinoidAlgebra.supAbsoluteValue`: `|·|sup` as an absolute value on a reduced `A`
  with prime `A°°`.
* `TauCeti.IsAffinoidAlgebra.exists_absoluteValue_coe_eq_supSeminorm_iff`: for nonzero `A`,
  `|·|sup` is an absolute value if and only if `A` is reduced and `A°°` is prime.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§6.2.1
  and 6.2.3.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- If the ideal `A°°` of topologically nilpotent elements is prime in `A°`, that is, if the
canonical reduction `A° ⧸ A°°` is a domain, then the supremum seminorm is multiplicative. -/
theorem supSeminorm_mul (hA : IsAffinoidAlgebra K A)
    (hP : (Huber.topologicallyNilpotentIdeal A).IsPrime) (f g : A) :
    supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g := by
  refine (hA.supSeminorm_mul_le f g).antisymm ?_
  rcases (supSeminorm_nonneg (K := K) f).eq_or_lt with hf | hf
  · rw [← hf, zero_mul]
    exact supSeminorm_nonneg _
  rcases (supSeminorm_nonneg (K := K) g).eq_or_lt with hg | hg
  · rw [← hg, mul_zero]
    exact supSeminorm_nonneg _
  -- Normalise `f ^ m` and `g ^ m` to supremum seminorm one.
  obtain ⟨m, hm, hnorm⟩ := hA.exists_supSeminorm_smul_pow_eq_one
  obtain ⟨c, hc⟩ := hnorm f hf
  obtain ⟨d, hd⟩ := hnorm g hg
  have hm0 : m ≠ 0 := by omega
  have hpb {u : A} (hu : supSeminorm K u = 1) : u ∈ Huber.powerBoundedSubring A :=
    Huber.mem_powerBoundedSubring.mpr (hA.isPowerBounded_iff_supSeminorm_le_one.mpr hu.le)
  have hnil {u : A} (hu : supSeminorm K u = 1) (hu' : u ∈ Huber.powerBoundedSubring A) :
      ⟨u, hu'⟩ ∉ Huber.topologicallyNilpotentIdeal A := by
    rw [Huber.mem_topologicallyNilpotentIdeal, hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one,
      hu]
    exact lt_irrefl 1
  -- In the domain `A° ⧸ A°°` the product of the two normalised elements is nonzero.
  have hprod : ¬supSeminorm K ((c : K) • f ^ m * ((d : K) • g ^ m)) < 1 := by
    have := mt (hP.mem_or_mem (x := ⟨_, hpb hc⟩) (y := ⟨_, hpb hd⟩))
      (not_or.mpr ⟨hnil hc (hpb hc), hnil hd (hpb hd)⟩)
    rwa [Huber.mem_topologicallyNilpotentIdeal, Subring.coe_mul,
      hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one] at this
  have hcd : ((c : K) • f ^ m * ((d : K) • g ^ m)) = ((c : K) * d) • (f * g) ^ m := by
    rw [smul_mul_smul_comm, mul_pow]
  rw [hcd, hA.supSeminorm_smul, hA.supSeminorm_pow _ hm0, not_lt] at hprod
  rw [hA.supSeminorm_smul, hA.supSeminorm_pow _ hm0] at hc hd
  -- Hence `(|f|sup |g|sup) ^ m ≤ |f g|sup ^ m`.
  refine le_of_pow_le_pow_left₀ hm0 (supSeminorm_nonneg _) ?_
  have hcd0 : 0 < ‖(c : K) * d‖ := norm_pos_iff.mpr (mul_ne_zero c.ne_zero d.ne_zero)
  refine le_of_mul_le_mul_left ?_ hcd0
  calc ‖(c : K) * d‖ * (supSeminorm K f * supSeminorm K g) ^ m
      = (‖(c : K)‖ * supSeminorm K f ^ m) * (‖(d : K)‖ * supSeminorm K g ^ m) := by
        rw [norm_mul]; ring
    _ = 1 := by rw [hc, hd, one_mul]
    _ ≤ ‖(c : K) * d‖ * supSeminorm K (f * g) ^ m := hprod

/-- On a nonzero affinoid algebra, a multiplicative supremum seminorm makes the ideal `A°°` of
topologically nilpotent elements prime in `A°`. -/
theorem isPrime_topologicallyNilpotentIdeal_of_supSeminorm_mul [Nontrivial A]
    (hA : IsAffinoidAlgebra K A)
    (h : ∀ f g : A, supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g) :
    (Huber.topologicallyNilpotentIdeal A).IsPrime := by
  have hmem {u : Huber.powerBoundedSubring A} :
      u ∈ Huber.topologicallyNilpotentIdeal A ↔ supSeminorm K (u : A) < 1 := by
    rw [Huber.mem_topologicallyNilpotentIdeal, hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one]
  have hle (u : Huber.powerBoundedSubring A) : supSeminorm K (u : A) ≤ 1 :=
    hA.isPowerBounded_iff_supSeminorm_le_one.mp (Huber.mem_powerBoundedSubring.mp u.2)
  refine Ideal.isPrime_iff.mpr ⟨fun htop ↦ ?_, fun {u v} huv ↦ ?_⟩
  · have := hmem.mp ((Ideal.eq_top_iff_one _).mp htop)
    rw [OneMemClass.coe_one, supSeminorm_one] at this
    exact lt_irrefl 1 this
  · rw [hmem, Subring.coe_mul, h] at huv
    rw [hmem, hmem]
    by_contra! huv'
    have h1 : 1 ≤ supSeminorm K (u : A) * supSeminorm K (v : A) := by
      simpa using mul_le_mul huv'.1 huv'.2 zero_le_one (supSeminorm_nonneg _)
    exact huv.not_ge h1

/-- **Multiplicativity of the supremum seminorm.** On a nonzero affinoid algebra,
`|f g|sup = |f|sup |g|sup` for all `f, g` if and only if the ideal `A°°` of topologically nilpotent
elements is prime in the power-bounded subring `A°`, that is, if and only if the canonical reduction
`A° ⧸ A°°` is an integral domain. -/
theorem supSeminorm_mul_iff_isPrime [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    (∀ f g : A, supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g) ↔
      (Huber.topologicallyNilpotentIdeal A).IsPrime :=
  ⟨hA.isPrime_topologicallyNilpotentIdeal_of_supSeminorm_mul, hA.supSeminorm_mul⟩

/-- The supremum seminorm of a reduced affinoid algebra whose ideal `A°°` of topologically
nilpotent elements is prime in `A°`, as an absolute value. -/
noncomputable def supAbsoluteValue (hA : IsAffinoidAlgebra K A) [IsReduced A]
    (hP : (Huber.topologicallyNilpotentIdeal A).IsPrime) : AbsoluteValue A ℝ where
  toFun := supSeminorm K
  map_mul' := hA.supSeminorm_mul hP
  nonneg' := supSeminorm_nonneg
  eq_zero' f := ⟨(hA.isReduced_iff_supSeminorm_eq_zero.mp ‹_›) f, fun hf ↦ hf ▸ supSeminorm_zero⟩
  add_le' f g := (hA.supSeminorm_add_le f g).trans
    (max_le_add_of_nonneg (supSeminorm_nonneg f) (supSeminorm_nonneg g))

@[simp]
theorem coe_supAbsoluteValue (hA : IsAffinoidAlgebra K A) [IsReduced A]
    (hP : (Huber.topologicallyNilpotentIdeal A).IsPrime) :
    ⇑(hA.supAbsoluteValue hP) = supSeminorm K :=
  (rfl)

/-- **The supremum seminorm is a multiplicative norm exactly when `A` is reduced and its
canonical reduction is a domain.** On a nonzero affinoid algebra, `|·|sup` is an absolute value if
and only if `A` is reduced and the ideal `A°°` of topologically nilpotent elements is prime in the
power-bounded subring `A°`. -/
theorem exists_absoluteValue_coe_eq_supSeminorm_iff [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    (∃ v : AbsoluteValue A ℝ, ⇑v = supSeminorm K) ↔
      IsReduced A ∧ (Huber.topologicallyNilpotentIdeal A).IsPrime := by
  refine ⟨fun ⟨v, hv⟩ ↦ ⟨hA.isReduced_iff_supSeminorm_eq_zero.mpr fun f hf ↦ ?_,
    hA.isPrime_topologicallyNilpotentIdeal_of_supSeminorm_mul fun f g ↦ ?_⟩,
    fun ⟨_, hP⟩ ↦ ⟨hA.supAbsoluteValue hP, coe_supAbsoluteValue hA hP⟩⟩
  · rwa [← hv, AbsoluteValue.eq_zero] at hf
  · simp only [← hv, map_mul]

end TauCeti.IsAffinoidAlgebra
