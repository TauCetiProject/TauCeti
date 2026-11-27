/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
public import TauCeti.LinearAlgebra.RootSystem.Finite.DoubleChain
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

/-!
# Local coordinates in an embedded G₂

The roots in the integral span of a distinguished G₂ pair are exactly the twelve tabulated
roots, even when the ambient root pairing has other components. This gives root exclusions
and root-string lengths without an irreducibility or spanning assumption.

The inputs are Mathlib's `EmbeddedG2.allRoots_eq_map_allCoeffs` and
`EmbeddedG2.isOrthogonal_short_and_long`. The short-pair extension uses the native
`RootPairing.chainCoeff_cases_of_root_add_mem` classification.

## References

* Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate IX.
-/

public section

namespace RootPairing.EmbeddedG2

variable {ι R X Y : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Finite ι]
  (P : RootPairing ι R X Y) [P.EmbeddedG2]

/-- An integral linear combination of the distinguished short and long roots is a root
precisely when its coefficients occur in the G₂ table. Other components are allowed. -/
theorem smul_add_smul_mem_range_root_iff (a b : ℤ) :
    a • shortRoot P + b • longRoot P ∈ Set.range P.root ↔ ![a, b] ∈ allCoeffs := by
  classical
  have hli := (linearIndependent_short_long P).restrict_scalars' ℤ
  have hcomb (v : Fin 2 → ℤ) :
      Fintype.linearCombination ℤ ![shortRoot P, longRoot P] v =
        v 0 • shortRoot P + v 1 • longRoot P := by
    simp [Fintype.linearCombination_apply, Fin.sum_univ_two]
  have hinj := hli.fintypeLinearCombination_injective
  constructor
  · rintro ⟨k, hk⟩
    have hm : P.root k ∈ allRoots P := by
      by_contra hn
      obtain ⟨hs, hl⟩ := isOrthogonal_short_and_long P hn
      have hs' : P.pairingIn ℤ k (short P) = 0 := by
        apply FaithfulSMul.algebraMap_injective ℤ R
        simpa only [P.algebraMap_pairingIn, map_zero] using hs.1
      have hl' : P.pairingIn ℤ k (long P) = 0 := by
        apply FaithfulSMul.algebraMap_injective ℤ R
        simpa only [P.algebraMap_pairingIn, map_zero] using hl.1
      have h₁ := P.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := short P) hk
      have h₂ := P.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := long P) hk
      simp only [hs', hl', P.pairingIn_same, pairingIn_long_short, pairingIn_short_long,
        smul_eq_mul] at h₁ h₂
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      exact P.ne_zero k (by simpa [ha, hb] using hk)
    rw [allRoots_eq_map_allCoeffs] at hm
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hm
    have : v = ![a, b] := hinj (by simpa only [hcomb, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] using he.trans hk)
    simpa only [this] using hv
  · intro h
    have hm : a • shortRoot P + b • longRoot P ∈ allRoots P := by
      rw [allRoots_eq_map_allCoeffs]
      exact List.mem_map.mpr ⟨![a, b], h, by simp only [hcomb,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]⟩
    exact (allRoots_subset_range_root P) (List.mem_toFinset.mpr hm)

end RootPairing.EmbeddedG2

namespace RootPairing

variable {ι R X Y : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Finite ι]
  (P : RootPairing ι R X Y) [P.IsCrystallographic] [P.IsReduced]

/-- Three consecutive positive steps in a root string force the G₂ Cartan integer `-3`.
This does not require irreducibility of the ambient root pairing. -/
theorem pairingIn_eq_neg_three_of_triple_chain {α β γ δ ε : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ) : P.pairingIn ℤ β α = -3 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have htop : 3 ≤ P.chainTopCoeff α β :=
    (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli).mp
      ⟨ε, by rw [hε, hδ, hγ]; module⟩
  have hlen := P.chainBotCoeff_add_chainTopCoeff_le_three (i := α) (j := β)
  have hp := P.chainBotCoeff_sub_chainTopCoeff hli
  omega

/-- A short-pair configuration with both double roots extends backwards to a triple string.
The additional long root is the difference of the original short roots. -/
theorem exists_root_eq_sub_of_g2_short_pair {α β γ δ ε : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root γ + P.root β) :
    ∃ η, P.root η = P.root β - P.root α := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have ht := P.two_le_chainTopCoeff_of_root_eq_add_of_root_eq_add hγ hδ
  have ht' := P.two_le_chainTopCoeff_of_root_eq_add_of_root_eq_add
    (hγ.trans (add_comm _ _)) (hε.trans (add_comm _ _))
  have hb : 1 ≤ P.chainBotCoeff α β := by
    rcases P.chainCoeff_cases_of_root_add_mem ⟨γ, hγ⟩ with h | h | h | h | h <;> omega
  obtain ⟨η, hη⟩ := (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli (n := 1)).mpr hb
  exact ⟨η, by simpa only [one_smul] using hη⟩

end RootPairing

