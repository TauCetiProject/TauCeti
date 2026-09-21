/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CharacterSpace

/-!
# The coprime filter descends one prime

Let `f ∈ S_k(Γ₁(N), χ)` vanish at every index coprime to `p * L`, for a prime `p ∣ N` with `χ`
the pull-back of a character `χ₀` modulo `N / p`, and a squarefree
`L` coprime to `p` whose primes divide `N`. The coprime filter of `f`
(`Newforms/CoprimeFilter/Basic.lean`) is a form of level `L * N` supported on the multiples of
`p`, so peeling `p` off it (`Newforms/Descent/CharacterSpace.lean`) gives a form
`g ∈ S_k(Γ₁(L * N / p), χ₀ ∘ π)` with
`a_m(g) = a_{pm}(f)` at the indices `m` coprime to `L`, and `0` elsewhere: the coefficients of
`f` along the multiples of `p` are those of a form of lower level, with the lowered nebentypus.
This is Miyake's "`V_p`-descent identity" in the proof of Lemma 4.6.7, and the strong
multiplicity one argument descends along it one prime at a time.

## Main results

* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul`: the
  descended form `g ∈ S_k(Γ₁(L * N / p), χ₀ ∘ π)` with `a_m(g) = a_{pm}(f)` for `m` coprime to
  `L` and `a_m(g) = 0` otherwise.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/SquarefreeDecomp.lean`,
theorem `miyake_V_p_descend_identity_with_char` and its degenerate case
`miyake_V_p_descend_with_char_of_vanishing`. The source states the level as `l' * (N / p)` and
transports the descended form across `(l' * N) / p = l' * (N / p)`; here the level is
`L * N / p` as the dichotomy produces it, so nothing is transported, and the source's first
conclusion (`a_n(f) = a_{n/p}(g)` for `p ∣ n` coprime to `l'`) is the second one read at
`n = p * m`, so it is not restated. The dichotomy step is the peeling theorem of
`Newforms/Descent/CharacterSpace.lean`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.7.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The coprime filter descends one prime.** For `f ∈ S_k(Γ₁(N), χ)` vanishing at every index
coprime to `p * L`, with `p ∣ N` prime, `χ` the pull-back of `χ₀` modulo `N / p`, and `L`
squarefree, coprime to `p`, with primes dividing `N`, there is `g ∈ S_k(Γ₁(L * N / p), χ₀ ∘ π)`
whose coefficients are those of `f` along the multiples of `p`:
`a_m(g) = a_{pm}(f)` for `m` coprime to `L`, and `a_m(g) = 0` otherwise. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {p L : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    {χ₀ : (ZMod (N / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (hL : Squarefree L) (hLN : L.primeFactors ⊆ N.primeFactors) (hpL : Nat.Coprime p L)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    ∃ g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k
        (χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L))) ∧
        ∀ m, (qExpansion 1 g).coeff m =
          if Nat.Coprime m L then (qExpansion 1 f).coeff (p * m) else 0 := by
  have : NeZero (L * N) := ⟨Nat.mul_ne_zero hL.ne_zero (NeZero.ne N)⟩
  have hpLN : p ∣ L * N := dvd_mul_of_dvd_right hpN L
  obtain ⟨G, hGχ, hGsupp, hGcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd_of_squarefree χ hf hp hL hLN hvan
  -- the nebentypus of the filter, factored through `L * N / p`
  have hGχ' : G ∈ cuspFormCharSpace k
      ((χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L))).comp
        (ZMod.unitsMap (Nat.div_dvd_of_dvd hpLN))) := by
    rw [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp] at hGχ
    rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  obtain ⟨g, hgχ, hgcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd hpLN _
      hGχ' hGsupp
  refine ⟨g, hgχ, fun m ↦ ?_⟩
  have h := hgcoeff (p * m)
  rw [hGcoeff] at h
  simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left m hp.pos,
    Nat.coprime_mul_iff_left, and_iff_right hpL] at h
  exact h.symm

end TauCeti
