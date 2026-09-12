/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic
import TauCeti.NumberTheory.ModularForms.ConductorDichotomy
import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Basic

/-!
# The factor dichotomy of the coprime sieve

Let `f ∈ S_k(Γ₁(N), χ)` vanish at every index coprime to `p L`, for a prime `p ∣ N` and an
`L` coprime to `p` (so `L ≠ 0`) whose primes divide `N`. Either `f` already vanishes at every index
coprime to `L`, or the nebentypus `χ` factors through `N / p`. This is
the case split of Miyake's proof of Lemma 4.6.8 (the Main Lemma of Diamond–Shurman §5.7, per
character): the second case is what a later descent along `p` needs, and in the first the prime
`p` needs no descent at all.

The coprime filter of `f` (`Newforms/CoprimeFilter/Basic.lean`) is a form `G` of level `L' N`,
`L'` the product of the primes of `L`, carrying the coefficients of `f` at the indices coprime
to `L` and supported on the multiples of `p`; the level-lowering dichotomy
(`ConductorDichotomy.lean`) either finds `G` to be a level-raise from `L' N / p`, so that the
pulled-back character factors through `L' N / p` and, by the conductor
(`DirichletCharacter.factorsThrough_div_of_changeLevel_factorsThrough`), `χ` factors through
`N / p`, or forces `G = 0`, which is the required vanishing of the coefficients of `f` at the
indices coprime to `L`.

## Main results

* `TauCeti.qExpansion_coeff_eq_zero_of_coprime_or_factorsThrough`: the dichotomy.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/InductiveStep.lean`,
`miyake_4_6_8_factor_dichotomy`. The source's private conductor lemmas
(`conductor_dvd_of_factorsThrough`, `factorsThrough_of_conductor_dvd`, `conductor_changeLevel`)
are Mathlib's `DirichletCharacter.conductor_dvd_of_mem_conductorSet`,
`mem_conductorSet_iff_conductor_dvd` and `conductor_changeLevel`; the source assumes `L`
squarefree, which the filter at the radical of `L` makes unnecessary.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.8.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The factor dichotomy.** For `f ∈ S_k(Γ₁(N), χ)` vanishing at every index coprime to `p L`,
with `p ∣ N` prime and `L` coprime to `p` with primes dividing `N`: either `f` vanishes at
every index coprime to `L`, or the nebentypus factors through `N / p`.

The second branch is stated with Mathlib's `DirichletCharacter.FactorsThrough`: its `χ₀`, `dvd`
and `eq_changeLevel` give a consumer the lowered character modulo `N / p` and the factorisation
of `χ` through it, which is what the descent lemmas take.
-/
theorem qExpansion_coeff_eq_zero_of_coprime_or_factorsThrough (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {p L : ℕ}
    (hp : p.Prime) (hpN : p ∣ N) (hLN : L.primeFactors ⊆ N.primeFactors)
    (hpL : Nat.Coprime p L) (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    (∀ n, Nat.Coprime n L → (qExpansion 1 f).coeff n = 0) ∨
      DirichletCharacter.FactorsThrough (MulChar.ofUnitHom χ) (N / p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  -- `L ≠ 0`: a prime is not coprime to `0`
  have : NeZero L := ⟨by rintro rfl; exact hp.ne_one ((Nat.coprime_zero_right p).mp hpL)⟩
  -- the filter lives at the level `L' N`, `L'` the radical of `L`
  obtain ⟨G, hGχ, hGsupp, hGcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd χ hf hp hLN hvan
  have hL'L : L.primeFactors.prod id ∣ L := Nat.prod_primeFactors_dvd L
  have : NeZero (L.primeFactors.prod id) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne L) hL'L⟩
  have hpL' : Nat.Coprime p (L.primeFactors.prod id) := hpL.coprime_dvd_right hL'L
  have hpLN : p ∣ L.primeFactors.prod id * N := dvd_mul_of_dvd_right hpN _
  have hNLN : N ∣ L.primeFactors.prod id * N := Nat.dvd_mul_left N _
  obtain ⟨φ, hGφ, hφT⟩ :=
    CuspForm.exists_eq_smul_slash_scaleGL_and_slash_T_eq_of_qExpansionSupportedOnDvd G hGsupp
  -- the nebentypus of `G` is the level-`L N` lift of `χ`, as a Dirichlet character
  have hψχ : (MulChar.ofUnitHom χ).toUnitHom = χ := MulChar.equivToUnitHom.apply_symm_apply χ
  have hGψ : G ∈ cuspFormCharSpace k
      (DirichletCharacter.changeLevel hNLN (MulChar.ofUnitHom χ)).toUnitHom := by
    rwa [DirichletCharacter.changeLevel_toUnitHom, hψχ]
  rcases exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero hpLN k _ φ G hGψ hGφ hφT with
    ⟨hfac, -, -, -⟩ | hφ0
  · -- `χ` lifted to level `L N` factors through `L N / p`, so `χ` factors through `N / p`
    exact Or.inr
      (DirichletCharacter.factorsThrough_div_of_changeLevel_factorsThrough hpN hpL' hfac)
  · -- `G = 0`: the coefficients of `f` at the indices coprime to `L` are those of `G`
    refine Or.inl fun n hn ↦ ?_
    have hG0 : (⇑G : ℍ → ℂ) = 0 := by rw [hGφ, hφ0, SlashAction.zero_slash, smul_zero]
    have h := hGcoeff n
    rw [hG0, qExpansion_zero, map_zero, ite_eq_left hn] at h
    exact h.symm

end TauCeti
