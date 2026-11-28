/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Obstructions
import Mathlib.Algebra.Field.ZMod
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.ZMod
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Card

/-!
# Explicit fixed-level checks for principal modular quotients and obstructions

These examples evaluate the general order, signed-quotient, projective-index, and obstruction
theorems at specific finite levels `N ∈ {6, 8, 10, 11, 12}`:

* **Orders of `SL₂(ℤ/Nℤ)`, `Q_N = SL₂(ℤ/Nℤ) ⧸ {±I}`, and `PSL₂(ℤ/Nℤ)` at `N = 8, 12`**:
  `Q_8` has order `192` while `PSL₂(ℤ/8ℤ)` has order `96`, and `Q_12` has order `576` while
  `PSL₂(ℤ/12ℤ)` has order `288`, because `±3I` (mod `8`) and `±5I` (mod `12`) are extra central
  elements outside `{±I}`.
* **Projective indices `(GammaProjective N).index`** at `N ∈ {6, 8, 10, 11, 12}` (`72`, `192`,
  `360`, `660`, `576`), ruling out `7 ∣ (GammaProjective N).index` at `N ∈ {6, 10, 12}`.
* **Separation of the composition-factor obstruction from the order obstruction (`N = 11`,
  `ℓ = 5`)**: `|PSL₂(𝔽₅)| = 60 ∣ 660 = (GammaProjective 11).index`, yet `PSL₂(𝔽₅)` cannot occur
  as a subnormal section of `PSL₂(ℤ) ⧸ Γ.normalCore` whenever `Γ(11) ≤ Γ.liftSL`, since `5 ∤ 11`.
-/

public section

open Matrix Matrix.SpecialLinearGroup TauCeti.CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti.Examples.NumberTheory.ModularForms.CongruenceSubgroups

/-! ### Finite-level orders of `SL₂(ℤ/Nℤ)`, `Q_N`, and `PSL₂(ℤ/Nℤ)` -/

private theorem card_fin_two_zmod_of_index {N k : ℕ} [NeZero N] (hN : 3 ≤ N)
    (hidx : (GammaProjective N).index = k)
    (hroots : Fintype.card { u : (ZMod N)ˣ // u ^ 2 = 1 } = 4) :
    Nat.card SL(2, ZMod N) = 2 * k ∧
      Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)) = k ∧
      Nat.card PSL(2, ZMod N) = k / 2 := by
  have hq : Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)) = k :=
    (GammaProjective_index_eq_card N).symm.trans hidx
  have hsl : Nat.card SL(2, ZMod N) = 2 * k := by
    have h := two_mul_GammaProjective_index hN
    rw [hidx] at h
    exact h.symm
  refine ⟨hsl, hq, ?_⟩
  have h := Matrix.ProjectiveSpecialLinearGroup.card_mul_card_rootsOfUnity 2 two_pos (ZMod N)
  have h4 : Nat.card (rootsOfUnity 2 (ZMod N)) = 4 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun u : (ZMod N)ˣ ↦ mem_rootsOfUnity 2 u),
      Nat.card_eq_fintype_card]
    exact hroots
  rw [hsl, h4] at h
  omega

/-- At modulus `8`, `|SL₂(ℤ/8ℤ)| = 384`, `|Q_8| = 192`, and `|PSL₂(ℤ/8ℤ)| = 96`. -/
theorem card_fin_two_zmod_eight :
    Nat.card SL(2, ZMod 8) = 384 ∧
      Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod 8)) = 192 ∧
      Nat.card PSL(2, ZMod 8) = 96 :=
  card_fin_two_zmod_of_index (by omega) GammaProjective_index_eight (by decide)

/-- At modulus `12`, `|SL₂(ℤ/12ℤ)| = 1152`, `|Q_12| = 576`, and `|PSL₂(ℤ/12ℤ)| = 288`. -/
theorem card_fin_two_zmod_twelve :
    Nat.card SL(2, ZMod 12) = 1152 ∧
      Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod 12)) = 576 ∧
      Nat.card PSL(2, ZMod 12) = 288 :=
  card_fin_two_zmod_of_index (by omega) GammaProjective_index_twelve (by decide)

/-! ### Projective indices and explicit obstruction checks -/

private theorem gammaProjective_index_eleven : (GammaProjective 11).index = 660 := by
  have h := two_mul_GammaProjective_index (N := 11) (by omega)
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [TauCeti.natCard_SL_fin_two_zmod] at h
  omega

/-- Projective indices `(GammaProjective N).index` at `N ∈ {6, 8, 10, 11, 12}` and
non-divisibility by `7` at `N ∈ {6, 10, 12}`. -/
theorem gammaProjective_index_checks :
    ((GammaProjective 6).index = 72 ∧ ¬ 7 ∣ (GammaProjective 6).index) ∧
      (GammaProjective 8).index = 192 ∧
      ((GammaProjective 10).index = 360 ∧ ¬ 7 ∣ (GammaProjective 10).index) ∧
      (GammaProjective 11).index = 660 ∧
      ((GammaProjective 12).index = 576 ∧ ¬ 7 ∣ (GammaProjective 12).index) := by
  rw [GammaProjective_index_six, GammaProjective_index_eight, GammaProjective_index_ten,
    gammaProjective_index_eleven, GammaProjective_index_twelve]
  decide

/-- Separation of the composition-factor obstruction from the order obstruction (`N = 11`,
`ℓ = 5`): `|PSL₂(𝔽₅)| = 60 ∣ 660 = (GammaProjective 11).index`, yet `PSL₂(𝔽₅)` cannot occur as a
subnormal section of `PSL₂(ℤ) ⧸ Γ.normalCore` whenever `Γ(11) ≤ Γ.liftSL`. -/
theorem psl_zmod_five_dvd_index_and_not_hasSubnormalSection_eleven
    {Γ : Subgroup PSL(2, ℤ)} (h : CongruenceSubgroup.Gamma 11 ≤ Γ.liftSL) :
    Nat.card PSL(2, ZMod 5) ∣ (GammaProjective 11).index ∧
      ¬ TauCeti.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) PSL(2, ZMod 5) := by
  refine ⟨?_, fun hsec ↦ ?_⟩
  · have h5 := Matrix.ProjectiveSpecialLinearGroup.two_mul_card_fin_two_zmod_prime
      Nat.prime_five (by decide)
    have hcard5 : Nat.card PSL(2, ZMod 5) = 60 := by omega
    rw [gammaProjective_index_eleven, hcard5]
    decide
  · have := dvd_of_hasSubnormalSection_psl_zmod_of_Gamma_le_liftSL (N := 11) (ℓ := 5)
      (by decide) Nat.prime_five le_rfl h hsec
    omega

end TauCeti.Examples.NumberTheory.ModularForms.CongruenceSubgroups
