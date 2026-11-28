/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Truncation
public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration

/-!
# Truncated Lie-to-enveloping homomorphisms

For a positively graded Lie algebra `L`, the canonical map `ι : L → U(L)` sends the degree ideal
`d.degreeIdeal ℒ k` into the `(k + 1)`-st degree-filtration ideal of `U(L)`, inducing compatible Lie
homomorphisms `truncatedLieToU : d.truncatedLie ℒ k →ₗ⁅R⁆ U(L) ⧸ (𝓕 ...).ideal (k + 1)`.
When `ι : L → U(L)` is injective, each `truncatedLieToU` is injective.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝓕" => degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)

/-- The canonical Lie map sends `d.degreeIdeal ℒ k` into filtration order `k + 1`. -/
theorem ι_mem_degreeFiltration_succ_of_mem_degreeIdeal {k : ℕ} {x : L}
    (hx : x ∈ d.degreeIdeal ℒ k) : ι R x ∈ (𝓕).ideal (k + 1) := by
  rw [mem_degreeFiltration_ideal_iff]; intro n hn
  rw [ι_apply, coe_decompose_mkAlgHom_ι, (d.mem_degreeIdeal_iff ℒ).mp hx n (by omega), map_zero]

/-- When `ι : L → U(L)` is injective, the preimage of filtration order `k + 1` is
`d.degreeIdeal ℒ k`. -/
theorem comap_degreeFiltration_succ_ι (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    (((𝓕).ideal (k + 1)).restrictScalars R).comap (ι R : L →ₗ⁅R⁆ U).toLinearMap =
      (d.degreeIdeal ℒ k).toSubmodule := by
  rw [comap_degreeFiltration_ι ℒ d.degree (d.eq_bot_of_degree_neg ℒ) hι (k + 1)]; ext x
  simp only [DirectSum.mem_degreeTail_iff, LieSubmodule.mem_toSubmodule, d.mem_degreeIdeal_iff ℒ]
  exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩

/-- The Lie homomorphism from the order-`k` Lie truncation to the order-`k` enveloping quotient. -/
noncomputable def truncatedLieToU (k : ℕ) : d.truncatedLie ℒ k →ₗ⁅R⁆ U ⧸ (𝓕).ideal (k + 1) :=
  (d.degreeIdeal ℒ k).liftQ ((Ideal.Quotient.mkₐ R ((𝓕).ideal (k + 1))).toLieHom.comp (ι R))
    fun _ hx => by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using
        ι_mem_degreeFiltration_succ_of_mem_degreeIdeal d ℒ hx

@[simp]
theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    truncatedLieToU d ℒ k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk ((𝓕).ideal (k + 1)) (ι R x) := by simp [truncatedLieToU]

/-- When `ι : L → U(L)` is injective, every truncated Lie-to-enveloping map is injective. -/
theorem truncatedLieToU_injective (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    Function.Injective (truncatedLieToU d ℒ k) := by
  rw [truncatedLieToU, LieIdeal.liftQ_injective_iff]
  exact fun _ hx => (comap_degreeFiltration_succ_ι d ℒ hι k).le
    (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hx)

/-- `truncatedLieToU` commutes with transitions between degree cutoffs. -/
theorem factor_truncatedLieToU {k l : ℕ} (h : k ≤ l) (z : d.truncatedLie ℒ l) :
    Ideal.Quotient.factor ((𝓕).antitone (Nat.add_le_add_right h 1)) (truncatedLieToU d ℒ l z) =
      truncatedLieToU d ℒ k (LieIdeal.factor (d.degreeIdeal_antitone ℒ h) z) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ z; simp [LieIdeal.mkQ_apply]

end TauCeti.UniversalEnvelopingAlgebra
