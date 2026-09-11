/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ConductorDichotomy
public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Basic

/-!
# The coprime filter descends one prime

Let `f ∈ S_k(Γ₁(N), χ)` vanish at every index coprime to `p * L`, for a prime `p ∣ N` and a
squarefree `L` coprime to `p` whose primes divide `N`. The coprime filter of `f`
(`Newforms/CoprimeFilter/Basic.lean`) is a form `G` of level `L * N` supported on the multiples
of `p`, so it is a level-raise `V_p` of a period-one function (`Newforms/Descent/Basic.lean`),
and the level-lowering dichotomy (`ConductorDichotomy.lean`) either finds that function as a
cusp form of level `L * N / p` with a lowered nebentypus, or forces `G = 0`. Either way the
descended form `g` has `q`-expansion coefficients `a_m(g) = a_{pm}(f)` at the indices `m`
coprime to `L`, and `0` elsewhere: the coefficients of `f` along the multiples of `p` are those
of a form of lower level. This is Miyake's "`V_p`-descent identity" in the proof of Lemma 4.6.7,
and the strong multiplicity one argument descends along it one prime at a time.

## Main results

* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul`: the
  descended form `g ∈ S_k(Γ₁(L * N / p), χ')` with `a_m(g) = a_{pm}(f)` for `m` coprime to `L`
  and `a_m(g) = 0` otherwise.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/SquarefreeDecomp.lean`,
theorem `miyake_V_p_descend_identity_with_char` and its degenerate case
`miyake_V_p_descend_with_char_of_vanishing`. The source states the level as `l' * (N / p)` and
transports the descended form across `(l' * N) / p = l' * (N / p)`; here the level is
`L * N / p` as the dichotomy produces it, so nothing is transported, and the source's first
conclusion (`a_n(f) = a_{n/p}(g)` for `p ∣ n` coprime to `l'`) is the second one read at
`n = p * m`, so it is not restated.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.7.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

omit [NeZero N] in
/-- The degenerate case of the descent: when `f` already vanishes along the multiples of `p`
at the indices coprime to `L`, the zero form of level `L * N / p` witnesses the identity. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul_of_eq_zero
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {p L : ℕ}
    (hf : ∀ m, Nat.Coprime m L → (qExpansion 1 f).coeff (p * m) = 0) :
    ∃ (χ' : (ZMod (L * N / p))ˣ →* ℂˣ) (g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k),
      g ∈ cuspFormCharSpace k χ' ∧
        ∀ m, (qExpansion 1 g).coeff m =
          if Nat.Coprime m L then (qExpansion 1 f).coeff (p * m) else 0 :=
  ⟨1, 0, Submodule.zero_mem _, fun m ↦ by
    rw [FunLike.coe_zero, qExpansion_zero, map_zero]
    split_ifs with h
    · exact (hf m h).symm
    · rfl⟩

/-- **The coprime filter descends one prime.** For `f ∈ S_k(Γ₁(N), χ)` vanishing at every index
coprime to `p * L`, with `p ∣ N` prime and `L` squarefree, coprime to `p`, with primes dividing
`N`, there is a form `g ∈ S_k(Γ₁(L * N / p), χ')` whose `q`-expansion is that of `f` along the
multiples of `p`: `a_m(g) = a_{pm}(f)` for `m` coprime to `L`, and `a_m(g) = 0` otherwise. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {p L : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hL : Squarefree L)
    (hLN : L.primeFactors ⊆ N.primeFactors) (hpL : Nat.Coprime p L)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    ∃ (χ' : (ZMod (L * N / p))ˣ →* ℂˣ) (g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k),
      g ∈ cuspFormCharSpace k χ' ∧
        ∀ m, (qExpansion 1 g).coeff m =
          if Nat.Coprime m L then (qExpansion 1 f).coeff (p * m) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (L * N) := ⟨Nat.mul_ne_zero hL.ne_zero (NeZero.ne N)⟩
  have hpLN : p ∣ L * N := dvd_mul_of_dvd_right hpN L
  have hcop (m : ℕ) : Nat.Coprime (p * m) L ↔ Nat.Coprime m L :=
    ⟨fun h ↦ (Nat.coprime_mul_iff_left.mp h).2, fun h ↦ Nat.coprime_mul_iff_left.mpr ⟨hpL, h⟩⟩
  -- the filter `G`, supported on the multiples of `p`, and its `V_p`-preimage `φ`
  obtain ⟨G, hGχ, hGsupp, hGcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd_of_squarefree χ hf hp hL hLN hvan
  obtain ⟨φ, hGφ, hφT⟩ :=
    CuspForm.exists_eq_smul_slash_scaleGL_and_slash_T_eq_of_qExpansionSupportedOnDvd G hGsupp
  -- the nebentypus of `G`, as a Dirichlet character
  have hGχ' : G ∈ cuspFormCharSpace k
      (MulChar.ofUnitHom (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L)))).toUnitHom := by
    rwa [show (MulChar.ofUnitHom (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L)))).toUnitHom =
      χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L)) from MulChar.equivToUnitHom.apply_symm_apply _]
  rcases exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero hpLN k _ φ G hGχ' hGφ hφT with
    ⟨hfac, g, hgχ, hgφ⟩ | hφ0
  · -- the dichotomy found `g` with `V_p g = G`
    refine ⟨hfac.χ₀.toUnitHom, g, hgχ, fun m ↦ ?_⟩
    rw [CuspForm.qExpansion_coeff_eq_qExpansion_coeff_mul_of_coe_eq_smul_slash_scaleGL hpLN
      (hgφ ▸ hGφ), hGcoeff]
    simp only [hcop]
  · -- `φ = 0` forces `G = 0`, so `f` already vanishes along the multiples of `p`
    have hG0 : (⇑G : ℍ → ℂ) = 0 := by rw [hGφ, hφ0, SlashAction.zero_slash, smul_zero]
    refine exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul_of_eq_zero
      fun m hm ↦ ?_
    have h := hGcoeff (p * m)
    rw [hG0, qExpansion_zero, map_zero] at h
    simp only [hcop] at h
    split_ifs at h
    exact h.symm

end TauCeti
