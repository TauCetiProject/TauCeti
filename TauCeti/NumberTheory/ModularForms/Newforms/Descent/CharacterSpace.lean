/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ConductorDichotomy
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Basic

/-!
# Descent of a supported form within a character space

A cusp form `G ∈ S_k(Γ₁(M), χ₀ ∘ π)` whose `q`-expansion is supported on the multiples of a
divisor `p ∣ M`, with `χ₀` a character modulo `M / p`, is the level-raise `V_p` of a period-one
function (`Newforms/Descent/Basic.lean`), and the level-lowering dichotomy
(`ConductorDichotomy.lean`) either finds that function as a cusp form `F ∈ S_k(Γ₁(M / p), χ₀)`,
or forces `G = 0`, when `F = 0` will do. Either way `a_n(G) = a_{n/p}(F)` for `p ∣ n` and
`a_n(G) = 0` otherwise: `G` is `V_p F` on coefficients. This is the step that lowers the level of
one prime at a time in Miyake's proofs of Lemmas 4.6.7 and 4.6.8.

## Main results

* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd`:
  peeling a divisor off a form supported on its multiples.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/SquarefreeDecomp.lean`: the
dichotomy step inside `miyake_V_p_descend_identity_with_char`, separated out with the lowered
character explicit.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.4 and Lemma 4.6.7.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {k : ℤ}

/-- **Peeling a divisor off a form supported on its multiples.** If `G ∈ S_k(Γ₁(M), χ₀ ∘ π)` is
supported on the multiples of `p ∣ M`, where `χ₀` is a character modulo `M / p`, then there is
`F ∈ S_k(Γ₁(M / p), χ₀)` with `a_n(G) = a_{n/p}(F)` for `p ∣ n` and `a_n(G) = 0` otherwise:
`G` is `V_p F` on coefficients. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd
    {M p : ℕ} [NeZero M] (hpM : p ∣ M) (χ₀ : (ZMod (M / p))ˣ →* ℂˣ)
    {G : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hG : G ∈ cuspFormCharSpace k (χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))))
    (hsupp : QExpansionSupportedOnDvd p G) :
    ∃ F : CuspForm ((Gamma1 (M / p)).map (mapGL ℝ)) k, F ∈ cuspFormCharSpace k χ₀ ∧
      ∀ n, (qExpansion 1 G).coeff n = if p ∣ n then (qExpansion 1 F).coeff (n / p) else 0 := by
  have : NeZero p := NeZero.of_dvd hpM
  obtain ⟨φ, hGφ, hφT⟩ :=
    CuspForm.exists_eq_smul_slash_scaleGL_and_slash_T_eq_of_qExpansionSupportedOnDvd G hsupp
  -- the nebentypus of `G`, as a Dirichlet character
  have hunit : (MulChar.ofUnitHom (χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))).toUnitHom =
      χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)) := MulChar.equivToUnitHom.apply_symm_apply _
  have hGχ : G ∈ cuspFormCharSpace k
      (MulChar.ofUnitHom (χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))).toUnitHom := by
    rwa [hunit]
  rcases exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero hpM k _ φ G hGχ hGφ hφT with
    ⟨hfac, F, hFχ, hFφ⟩ | hφ0
  · -- the lowered character of the dichotomy is `χ₀`: both pull back to the nebentypus of `G`
    have hχ₀ : hfac.χ₀.toUnitHom = χ₀ := by
      have h := congrArg MulChar.toUnitHom hfac.eq_changeLevel
      rw [hunit, DirichletCharacter.changeLevel_toUnitHom] at h
      refine MonoidHom.ext fun u ↦ ?_
      obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) u
      exact (congrArg (fun ψ ↦ ψ v) h).symm
    refine ⟨F, hχ₀ ▸ hFχ, fun n ↦ ?_⟩
    by_cases hn : p ∣ n
    · obtain ⟨m, rfl⟩ := hn
      simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left m (NeZero.pos p)]
      exact (CuspForm.qExpansion_coeff_eq_qExpansion_coeff_mul_of_coe_eq_smul_slash_scaleGL hpM
        (hFφ ▸ hGφ) m).symm
    · simp only [hn, ↓reduceIte]
      exact PowerSeries.isSupportedOnDvd_iff.mp (qExpansionSupportedOnDvd_iff.mp hsupp) n hn
  · have hG0 : (⇑G : ℍ → ℂ) = 0 := by rw [hGφ, hφ0, SlashAction.zero_slash, smul_zero]
    refine ⟨0, Submodule.zero_mem _, fun n ↦ ?_⟩
    rw [hG0, qExpansion_zero, map_zero, FunLike.coe_zero, qExpansion_zero]
    simp only [map_zero, ite_self]

end TauCeti
