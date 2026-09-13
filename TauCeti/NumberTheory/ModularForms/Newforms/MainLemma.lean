/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.PrimeFactorsProd
public import TauCeti.NumberTheory.ModularForms.Newforms.AtkinLehner
public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Dichotomy
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Coefficient
public import TauCeti.NumberTheory.ModularForms.Newforms.QSupport

/-!
# The Main Lemma, per character

Miyake's Lemma 4.6.8: a cusp form `f ∈ S_k(Γ₁(N), χ)` whose Fourier coefficients vanish at every
index coprime to `N` is a sum, over the primes `p ∣ N`, of forms in `S_k(Γ₁(N), χ)` supported on
the multiples of `p`; each such summand is old. This file assembles the descent witness
(`Newforms/Descent/Coefficient.lean`) and the factor dichotomy
(`Newforms/CoprimeFilter/Dichotomy.lean`) into the inductive step and the induction over the
primes.

## Main results

* `TauCeti.mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero`: the per-character Main
  Lemma — a cusp form in `S_k(Γ₁(N), χ)` whose coefficients vanish at every index coprime to `N`
  lies in the old subspace.
* `TauCeti.exists_eq_sum_of_forall_coprime_prod_qExpansion_coeff_eq_zero`: the induction over a
  set of primes that proves it.
* `TauCeti.exists_mem_qSupportedOnDvdSubmodule_and_qExpansion_coeff_sub_eq_zero`: its inductive
  step, one prime peeled.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/InductiveStep.lean` and
`MainLemma.lean` — declarations `miyake_4_6_8_inductive_step`, `miyake_4_6_8_induction` and
`mainLemma_charSpace`. The source inducts on the cardinality of the set of remaining primes with
the decomposition carried as a list; here the induction is on `Finset.card` with the pieces
produced as a function `ℕ → CuspForm`, and the dichotomy's second branch is consumed through
`DirichletCharacter.FactorsThrough`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.8.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.7.1.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N p : ℕ} [NeZero N] {k : ℤ}

/-- **The inductive step of the Main Lemma** (Miyake, Lemma 4.6.8). For `f ∈ S_k(Γ₁(N), χ)` with
`χ` pulled back from `χ₀` modulo `N / p`, vanishing at every index coprime to `p L` for a
squarefree `L` coprime to `p` whose primes divide `N`, there is `f_p ∈ S_k(Γ₁(N), χ)` supported
on the multiples of `p` with `f − f_p` vanishing at every index coprime to `L`: the level-raise
`V_p` of the descent witness of level `N / p`. -/
theorem exists_mem_qSupportedOnDvdSubmodule_and_qExpansion_coeff_sub_eq_zero (hp : p.Prime)
    (hpN : p ∣ N) {L : ℕ} (hL : Squarefree L) (hLN : L.primeFactors ⊆ N.primeFactors)
    (hpL : Nat.Coprime p L) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ∃ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k, g ∈ qSupportedOnDvdSubmodule N k p ∧
      g ∈ cuspFormCharSpace k χ ∧
      ∀ n, Nat.Coprime n L → (qExpansion 1 ⇑(f - g)).coeff n = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F, hF, hFcoeff⟩ := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_coprime
    hp hpN hL hLN hpL hcomp hf hvan
  have hdvd : p * (N / p) ∣ N := dvd_of_eq (Nat.mul_div_cancel' hpN)
  refine ⟨CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) F, ?_, ?_,
    fun n hn ↦ ?_⟩
  · exact mem_qSupportedOnDvdSubmodule.mpr (qExpansionSupportedOnDvd_iff.mpr
      (CuspForm.isSupportedOnDvd_qExpansion_levelRaise (one_mem_strictPeriods_Gamma1_map _)
        (one_mem_strictPeriods_Gamma1_map _) _ F))
  · rw [hcomp]
    exact CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdvd χ₀ hF
  · rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _),
      map_sub, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
        (one_mem_strictPeriods_Gamma1_map _)]
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [ite_eq_left (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos,
        hFcoeff m (Nat.coprime_mul_iff_left.mp hn).2, sub_self]
    · rw [ite_eq_right hpn, sub_zero]
      exact hvan n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hpn).symm hn)

/-! ### The induction over the primes -/

omit [NeZero N] in
omit [NeZero N] in
/-- Extending a decomposition over `S.erase p` by a piece at `p`. -/
private theorem exists_eq_sum_of_sub_eq_sum_erase {χ : (ZMod N)ˣ →* ℂˣ} {S : Finset ℕ} {p : ℕ}
    (hpS : p ∈ S) {f gp : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hgp_supp : gp ∈ qSupportedOnDvdSubmodule N k p) (hgp_char : gp ∈ cuspFormCharSpace k χ)
    {g : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hsum : f - gp = ∑ q ∈ S.erase p, g q)
    (hsupp : ∀ q ∈ S.erase p, g q ∈ qSupportedOnDvdSubmodule N k q)
    (hchar : ∀ q ∈ S.erase p, g q ∈ cuspFormCharSpace k χ) :
    ∃ g : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k, f = ∑ p ∈ S, g p ∧
      (∀ p ∈ S, g p ∈ qSupportedOnDvdSubmodule N k p) ∧ ∀ p ∈ S, g p ∈ cuspFormCharSpace k χ := by
  refine ⟨Function.update g p gp, ?_, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · rw [Finset.sum_update_of_mem hpS, Finset.sdiff_singleton_eq_erase, ← hsum, add_sub_cancel]
  · by_cases hqp : q = p
    · simp only [hqp, Function.update_self]; exact hgp_supp
    · simp only [Function.update_of_ne hqp]
      exact hsupp q (Finset.mem_erase.mpr ⟨hqp, hq⟩)
  · by_cases hqp : q = p
    · simp only [hqp, Function.update_self]; exact hgp_char
    · simp only [Function.update_of_ne hqp]
      exact hchar q (Finset.mem_erase.mpr ⟨hqp, hq⟩)

/-- **The coprime sieve decomposes along the primes** (Miyake, Lemma 4.6.8, the induction). For
`S ⊆ N.primeFactors` and `f ∈ S_k(Γ₁(N), χ)` vanishing at every index coprime to the product of
`S`, `f = ∑_{p ∈ S} f_p` with each `f_p ∈ S_k(Γ₁(N), χ)` supported on the multiples of `p`. -/
theorem exists_eq_sum_of_forall_coprime_prod_qExpansion_coeff_eq_zero {χ : (ZMod N)ˣ →* ℂˣ}
    {S : Finset ℕ} (hS : S ⊆ N.primeFactors) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (S.prod id) → (qExpansion 1 f).coeff n = 0) :
    ∃ g : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k, f = ∑ p ∈ S, g p ∧
      (∀ p ∈ S, g p ∈ qSupportedOnDvdSubmodule N k p) ∧ ∀ p ∈ S, g p ∈ cuspFormCharSpace k χ := by
  induction hcard : S.card generalizing S f with
  | zero =>
    obtain rfl : S = ∅ := Finset.card_eq_zero.mp hcard
    refine ⟨fun _ ↦ 0, ?_, fun p hp ↦ absurd hp (Finset.notMem_empty p),
      fun p hp ↦ absurd hp (Finset.notMem_empty p)⟩
    rw [Finset.sum_empty]
    have hq : qExpansion 1 (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 :=
      PowerSeries.ext fun n ↦ by
        simpa using hvan n (by rw [Finset.prod_empty]; exact Nat.coprime_one_right n)
    refine CuspForm.toModularFormₗ_injective ?_
    rw [CuspForm.toModularFormₗ_eq_coe, map_zero]
    exact (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_Gamma1_map _) _).mp hq
  | succ m ih =>
    obtain ⟨p, hpS⟩ : S.Nonempty := Finset.card_pos.mp (hcard ▸ Nat.succ_pos m)
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (hS hpS)
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors (hS hpS)
    have hS' : S.erase p ⊆ N.primeFactors := fun q hq ↦ hS (Finset.mem_of_mem_erase hq)
    have hcard' : (S.erase p).card = m := by rw [Finset.card_erase_of_mem hpS, hcard]; rfl
    obtain ⟨hsq, hpL, hLN⟩ := squarefree_prod_and_coprime_of_subset_primeFactors
      ((Finset.erase_subset _ _).trans hS) hp (Finset.notMem_erase p S)
    have hprod : S.prod id = p * (S.erase p).prod id := by
      rw [← Finset.mul_prod_erase S id hpS]; rfl
    have hvan' : ∀ n, Nat.Coprime n (p * (S.erase p).prod id) → (qExpansion 1 f).coeff n = 0 :=
      fun n hn ↦ hvan n (hprod ▸ hn)
    rcases qExpansion_coeff_eq_zero_of_coprime_or_factorsThrough χ hf hp hpN hLN hpL
      hvan' with hvan'' | hfac
    · -- `p` needs no descent: `f` already vanishes off the remaining primes
      obtain ⟨g, hsum, hsupp, hchar⟩ := ih hS' hf hvan'' hcard'
      exact exists_eq_sum_of_sub_eq_sum_erase hpS (Submodule.zero_mem _) (Submodule.zero_mem _)
        (by rw [sub_zero, hsum]) hsupp hchar
    · -- descend along `p`, then recurse on the remainder
      -- the lowered unit homomorphism, and the factorisation the descent lemmas take
      obtain ⟨χ₀, hcomp⟩ :=
        DirichletCharacter.exists_eq_comp_unitsMap_of_factorsThrough (Nat.div_dvd_of_dvd hpN) hfac
      obtain ⟨gp, hgp_supp, hgp_char, hdiff⟩ :=
        exists_mem_qSupportedOnDvdSubmodule_and_qExpansion_coeff_sub_eq_zero hp hpN hsq hLN hpL
          hcomp hf hvan'
      obtain ⟨g, hsum, hsupp, hchar⟩ := ih hS' (Submodule.sub_mem _ hf hgp_char) hdiff hcard'
      exact exists_eq_sum_of_sub_eq_sum_erase hpS hgp_supp hgp_char hsum hsupp hchar


/-! ### The Main Lemma -/

/-- **The Main Lemma, per character** (Miyake, Lemma 4.6.8; Diamond–Shurman, Theorem 5.7.1): a
cusp form in `S_k(Γ₁(N), χ)` whose Fourier coefficients vanish at every index coprime to `N`
lies in the old subspace. It is a sum, over the primes `p ∣ N`, of forms of the same nebentypus
supported on the multiples of `p`, and each of those is old. -/
theorem mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n N → (qExpansion 1 f).coeff n = 0) : f ∈ cuspFormsOld N k := by
  obtain ⟨g, hsum, hsupp, hchar⟩ :=
    exists_eq_sum_of_forall_coprime_prod_qExpansion_coeff_eq_zero (Finset.Subset.refl _) hf
      fun n hn ↦ hvan n (Nat.coprime_of_dvd fun q hq hqn hqN ↦ hq.one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqn hn)
          (Finset.dvd_prod_of_mem id (Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩))))
  have hunit : (MulChar.ofUnitHom χ).toUnitHom = χ := MulChar.equivToUnitHom.apply_symm_apply χ
  rw [hsum]
  refine Submodule.sum_mem _ fun p hp ↦
    mem_cuspFormsOld_of_qExpansionSupportedOnDvd (Nat.prime_of_mem_primeFactors hp).ne_one
      (Nat.dvd_of_mem_primeFactors hp) (MulChar.ofUnitHom χ) (by rw [hunit]; exact hchar p hp)
      (mem_qSupportedOnDvdSubmodule.mp (hsupp p hp))


end TauCeti
