/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NearIsometry.SecondMoment
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Spanning.Basic

/-!
# Ramified translates from the second moment

A second-moment bound on the scaled Poincaré map supplies enough translates of the
ramified source to span almost all of the good target. The moment estimates are taken in
the coordinates of the scaled map, while the span can be taken in the original source
coordinates and with any nonzero scalar normalization of the translates.

The constants are those of `New.Data.isSpread_goodPoincare` and `New.Data.enough_forms`
in lsernau/grh-lean at `72fead1` (`New/Spanning/SecondMoment/SpanningTheorem.lean` and
`New/Reduction/ShortAndEnough.lean`, respectively).
-/

public section

open Module Finset
open scoped InnerProductSpace

namespace TauCeti.OneSidedBound

/-- From a near-isometry error of `5/b⁴` and a relative second-moment error of `9/b⁴`,
select translates whose images of a subspace of relative codimension at most `b⁻⁸` span
at least `1 - 4/b²` of the good target. The cost of a translate is the dimension of the
restricted source. `e` identifies the original source with the coordinates of the
second-moment computation; `c` allows a nonzero change of normalization. -/
theorem exists_card_mul_finrank_le_and_le_finrank_biSup_map_of_second_moment
    {𝕜 V S T Γ : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [NormedAddCommGroup S] [InnerProductSpace 𝕜 S] [FiniteDimensional 𝕜 S] [Nontrivial S]
    [NormedAddCommGroup T] [InnerProductSpace 𝕜 T] [FiniteDimensional 𝕜 T]
    [Group Γ] [Fintype Γ] {ρ : Representation 𝕜 Γ T} {T₀ : Submodule 𝕜 T}
    (hρ : ∀ s x, ‖ρ s x‖ = ‖x‖)
    (h_comm : ∀ s x, T₀.starProjection (ρ s x) = ρ s (T₀.starProjection x))
    {B : S →ₗ[𝕜] T} {b : ℝ} (hb : 72 ≤ b ^ 2)
    (hnear : ((T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ B).IsNearIsometry (5 / b ^ 4))
    (hmoment : finrank 𝕜 T₀ * ∑ s : Γ,
      UnitarilyInvariantSeminorm.frobenius 𝕜 S S (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2 ≤
        Fintype.card Γ * ((1 + 9 / b ^ 4) * finrank 𝕜 S ^ 2))
    (e : V ≃ₗ[𝕜] S) (c : 𝕜ˣ) (U : Submodule 𝕜 V)
    (hU : (finrank 𝕜 V : ℝ) - finrank 𝕜 U ≤ (b ^ 8)⁻¹ * finrank 𝕜 V) :
    0 < finrank 𝕜 T₀ ∧ ∃ t : Finset Γ,
      #t * finrank 𝕜 U ≤ 5 * Real.log (1 + 2 * b ^ 2) * finrank 𝕜 T₀ ∧
      (1 - 4 / b ^ 2) * finrank 𝕜 T₀ ≤ finrank 𝕜 ↥(⨆ s ∈ t,
        U.map ((c : 𝕜) • ((T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ ρ s ∘ₗ B ∘ₗ e))) := by
  let A (s : Γ) : S →ₗ[𝕜] T₀ := (T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ ρ s ∘ₗ B
  have hb₂ : 0 < b ^ 2 := by linarith
  have hb₄ : b ^ 4 = b ^ 2 * b ^ 2 := by ring
  have hbudget : 9 / b ^ 4 ≤ 1 / (8 * b ^ 2) := by
    rw [hb₄, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hb hb₂.le]
  -- Use one error parameter for both moment estimates before applying greedy selection.
  have hnear' := hnear.mono ((div_le_div_of_nonneg_right (by norm_num : (5 : ℝ) ≤ 9)
    (by positivity)).trans hbudget)
  have hspread : IsSpread A (3 / 2 * (1 / (8 * b ^ 2))) :=
    isSpread_of_sum_sq_frobenius_le hρ h_comm (by positivity) hnear'
      (hmoment.trans (by gcongr))
  have hη : (3 : ℝ) / 2 * (1 / (8 * b ^ 2)) = 3 / (16 * b ^ 2) := by ring
  rw [hη] at hspread
  have hdim : finrank 𝕜 V = finrank 𝕜 S := e.finrank_eq
  have hU' : (finrank 𝕜 S : ℝ) - finrank 𝕜 (U.map e.toLinearMap) ≤ (b ^ 8)⁻¹ * finrank 𝕜 S := by
    simpa only [e.finrank_map_eq, ← hdim] using hU
  obtain ⟨t, ht, hspan⟩ := hspread.exists_card_mul_finrank_le_and_le_finrank_biSup_map
    (by rintro rfl; norm_num at hb) finrank_pos (U.map e.toLinearMap) hU'
  have hε : 5 / b ^ 4 < 1 := by
    rw [hb₄, div_lt_iff₀ (by positivity), one_mul]
    nlinarith [mul_le_mul_of_nonneg_right hb hb₂.le]
  have htarget : 0 < finrank 𝕜 T₀ := by
    rcases subsingleton_or_nontrivial T₀ with h | h
    · exact (hnear.ne_zero hε (Subsingleton.elim _ _)).elim
    · exact finrank_pos
  refine ⟨htarget, t, by simpa only [e.finrank_map_eq] using ht, ?_⟩
  -- Return to the original source coordinates without changing the selected image subspaces.
  have himage (s : Γ) :
      U.map ((c : 𝕜) • ((T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ ρ s ∘ₗ B ∘ₗ e)) =
        (U.map e.toLinearMap).map (A s) := by
    rw [Submodule.map_smul _ _ _ c.ne_zero, ← Submodule.map_comp]
    simp only [A, LinearMap.comp_assoc]
  have hsup : (⨆ s ∈ t,
      U.map ((c : 𝕜) • ((T₀.orthogonalProjectionOnto : T →ₗ[𝕜] T₀) ∘ₗ ρ s ∘ₗ B ∘ₗ e))) =
      ⨆ s ∈ t, (U.map e.toLinearMap).map (A s) :=
    iSup_congr fun s ↦ iSup_congr fun _ ↦ himage s
  rw [hsup]
  exact hspan

end TauCeti.OneSidedBound
