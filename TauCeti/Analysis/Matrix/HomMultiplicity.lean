/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.LinearAlgebra.Matrix.HomMultiplicity
import TauCeti.Analysis.Matrix.MurrayVonNeumann
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# Unitary classification of `⋆`-homomorphisms between full matrix algebras

Over `𝕜 = ℝ` or `ℂ`, two `⋆`-homomorphisms `φ ψ : Mₙ(𝕜) → Mₘ(𝕜)` are conjugate by a unitary of
`Mₘ(𝕜)` exactly when they have the same multiplicity
(`NonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq_iff`). In particular any two unital
`⋆`-homomorphisms `Mₙ(𝕜) → Mₘ(𝕜)` are unitarily conjugate
(`StarAlgHom.exists_mem_unitary_mul_map_mul_star_eq`). Together with the realisation of
multiplicities (`Matrix.exists_nonUnitalStarAlgHom_homMultiplicity_eq_iff`), this classifies, for
`n ≠ 0`, the `⋆`-homomorphisms `Mₙ(𝕜) → Mₘ(𝕜)` up to unitary conjugacy by the natural numbers `μ`
with `n * μ ≤ m` (for `n = 0` the only multiplicity is `0`), the single-block case of the
classification of `⋆`-homomorphisms between finite-dimensional C⋆-algebras by multiplicity
matrices.

Equal multiplicities make the images `φ(Eᵢᵢ)` and `ψ(Eᵢᵢ)` of a diagonal matrix unit projections of
equal rank, and likewise the complements `1 - φ 1` and `1 - ψ 1`; such projections are
Murray–von Neumann equivalent (`Matrix.isMurrayVonNeumannEquivalent_iff_rank_eq`), and the
implementing partial isometries assemble into the unitary
(`NonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq`).

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Chapter 7.
* K. R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6 (1996), Chapter III.
-/

public section

open TauCeti Matrix

variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **Classification of `⋆`-homomorphisms between full matrix algebras.** Two `⋆`-homomorphisms
`Mₙ(𝕜) → Mₘ(𝕜)` over `𝕜 = ℝ` or `ℂ` are conjugate by a unitary of `Mₘ(𝕜)` exactly when they have
the same multiplicity. -/
theorem NonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq_iff
    (φ ψ : Matrix n n 𝕜 →⋆ₙₐ[𝕜] Matrix m m 𝕜) :
    (∃ u ∈ unitary (Matrix m m 𝕜), ∀ x, u * φ x * star u = ψ x) ↔
      homMultiplicity φ = homMultiplicity ψ := by
  have h1φ : IsStarProjection (φ 1) := (IsStarProjection.one _).map φ
  have h1ψ : IsStarProjection (ψ 1) := (IsStarProjection.one _).map ψ
  obtain hn | ⟨⟨i⟩⟩ := isEmpty_or_nonempty n
  · exact ⟨fun _ => by simp, fun _ => ⟨1, one_mem _, fun x => by simp [Subsingleton.elim x 0]⟩⟩
  refine ⟨fun ⟨u, hu, h⟩ => ?_, fun h => ?_⟩
  · -- conjugate projections have equal rank
    have hrank := (h1φ.isMurrayVonNeumannEquivalent_mul_mul_star hu).rank_eq
    rw [h] at hrank
    exact Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.mpr ⟨i⟩) (by
      rw [card_mul_homMultiplicity, card_mul_homMultiplicity, hrank])
  · have hE : IsStarProjection (single i i (1 : 𝕜)) :=
      ⟨by simp [IsIdempotentElem], by simp [IsSelfAdjoint, star_eq_conjTranspose]⟩
    -- `φ(Eᵢᵢ) ∼ ψ(Eᵢᵢ)`, both of rank the common multiplicity
    obtain ⟨v, hvφ, hvψ, hv⟩ := ((isMurrayVonNeumannEquivalent_iff_rank_eq (hE.map φ)
      (hE.map ψ)).mpr (by rw [← homMultiplicity_eq_rank_map_single,
        ← homMultiplicity_eq_rank_map_single, h])).exists_mul_conjTranspose_mul_self_eq
    -- `1 - φ 1 ∼ 1 - ψ 1`, both of rank `m - n μ`
    have hrank : (φ 1).rank = (ψ 1).rank := by
      rw [← card_mul_homMultiplicity, ← card_mul_homMultiplicity, h]
    obtain ⟨w, hwφ, hwψ, hw⟩ := ((isMurrayVonNeumannEquivalent_iff_rank_eq h1φ.one_sub
      h1ψ.one_sub).mpr (by
        have hφ := h1φ.isIdempotentElem.rank_one_sub_add_rank
        have hψ := h1ψ.isIdempotentElem.rank_one_sub_add_rank
        omega)).exists_mul_conjTranspose_mul_self_eq
    rw [← star_eq_conjTranspose] at hvφ hvψ hv hwφ hwψ hw
    exact φ.exists_mem_unitary_mul_map_mul_star_eq ψ i (isPartialIsometry_iff.mpr hv) hvφ hvψ
      (isPartialIsometry_iff.mpr hw) hwφ hwψ

/-- Any two unital `⋆`-homomorphisms `Mₙ(𝕜) → Mₘ(𝕜)` over `𝕜 = ℝ` or `ℂ` are conjugate by a
unitary of `Mₘ(𝕜)`. -/
theorem StarAlgHom.exists_mem_unitary_mul_map_mul_star_eq
    (φ ψ : Matrix n n 𝕜 →⋆ₐ[𝕜] Matrix m m 𝕜) :
    ∃ u ∈ unitary (Matrix m m 𝕜), ∀ x, u * φ x * star u = ψ x := by
  refine (φ.toNonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq_iff
    ψ.toNonUnitalStarAlgHom).mpr ?_
  cases isEmpty_or_nonempty n with
  | inl _ => simp
  | inr _ =>
    refine Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := n)) ?_
    rw [(card_mul_homMultiplicity_eq_card_iff _).mpr (by simp),
      (card_mul_homMultiplicity_eq_card_iff _).mpr (by simp)]
