/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.MainLemma

/-!
# Prime degeneracy decomposition in the Atkin--Lehner Main Lemma

The Atkin--Lehner Main Lemma says that a cusp form whose Fourier coefficients vanish at every
index coprime to its level is old.  For a form of fixed nebentypus, the stronger conclusion used
in newform theory is an explicit decomposition

`f = ∑ p ∣ N, V_p f_p`,

where `f_p` has level `N / p`.  This file derives that sharp form from the prime-supported
decomposition of `Newforms/MainLemma.lean` and the level-lowering dichotomy: each summand supported
on multiples of `p` is the level-raise of a genuine cusp form at level `N / p` (or is zero).

## Main result

* `TauCeti.exists_eq_sum_levelRaise_prime_of_forall_coprime_qExpansion_coeff_eq_zero`: the
  prime-degeneracy form of the Main Lemma in a fixed nebentypus space.

## Provenance

The mathematical decomposition is Miyake's Lemma 4.6.8 and the sharp form of the Atkin--Lehner
Main Lemma in Diamond--Shurman, Theorem 5.7.1.  The proof follows the route in the AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> at commit
`eb9621e7bcb0ce220ad53983ec45d987cb5b9002`), combining
`StrongMultiplicityOne/InductiveStep.lean` with the level-lowering dichotomy in
`Eigenforms/ConductorTheorem.lean`.  Tau Ceti's existing sieve already supplies the
prime-supported summands; only the explicit lower-level witnesses are assembled here.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.8.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.7.1.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **Prime-degeneracy form of the Atkin--Lehner Main Lemma, at fixed nebentypus.**
If `f ∈ S_k(N, χ)` has vanishing Fourier coefficient at every index coprime to `N`, then
`f` is a sum of prime degeneracy images `V_p f_p`, with `f_p` a cusp form of level `N / p` for
each prime `p ∣ N`.  In particular, this records the lower-level witnesses hidden by the
oldspace-membership conclusion of the Main Lemma. -/
theorem exists_eq_sum_levelRaise_prime_of_forall_coprime_qExpansion_coeff_eq_zero
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n N → (qExpansion 1 f).coeff n = 0) :
    ∃ F : ∀ p : {p // p ∈ N.primeFactors},
        CuspForm ((Gamma1 (N / p.1)).map (mapGL ℝ)) k,
      f = ∑ p : {p // p ∈ N.primeFactors},
        haveI : NeZero p.1 := ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
        CuspForm.levelRaise p.1
          (Gamma1_map_le_conjAct_scaleGL_of_dvd
            (Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors p.2)).dvd) (F p) := by
  obtain ⟨g, hsum, hsupp, hchar⟩ :=
    exists_eq_sum_of_forall_coprime_prod_qExpansion_coeff_eq_zero (Finset.Subset.refl _) hf
      fun n hn ↦ hvan n (Nat.coprime_of_dvd fun q hq hqn hqN ↦ hq.one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqn hn)
          (Finset.dvd_prod_of_mem id (Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩))))
  have hex : ∀ p : {p // p ∈ N.primeFactors},
      ∃ G : CuspForm ((Gamma1 (N / p.1)).map (mapGL ℝ)) k,
        haveI : NeZero p.1 := ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
        g p.1 = CuspForm.levelRaise p.1
          (Gamma1_map_le_conjAct_scaleGL_of_dvd
            (Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors p.2)).dvd) G := by
    intro p
    have hp := Nat.prime_of_mem_primeFactors p.2
    have hpN := Nat.dvd_of_mem_primeFactors p.2
    let _ : NeZero p.1 := ⟨hp.ne_zero⟩
    exact exists_eq_levelRaise_of_mem_qSupportedOnDvdSubmodule hpN χ
      (hchar p.1 p.2) (hsupp p.1 p.2)
  choose F hF using hex
  refine ⟨F, ?_⟩
  rw [hsum, ← Finset.sum_attach]
  exact Finset.sum_congr rfl fun p _ ↦ hF p

end TauCeti
