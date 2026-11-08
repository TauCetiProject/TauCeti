/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.AlmostInvariant
public import TauCeti.RepresentationTheory.Continuous.InvariantComplement

/-!
# Spectral gap of a representation

Spectral gap is a finite sum-of-squares displacement bound on the orthogonal complement of
invariant vectors, not on the whole representation space. For a unitary group representation it
is equivalent to the absence of almost invariant vectors in that complement. This is the
representation-theoretic criterion used for spectral gap of actions and commutator representations.

Every representation of a finite group has spectral gap, without a unitarity assumption, and the
trivial representation has spectral gap even on a nonzero space. None of these results requires
completeness or finite dimensionality.

The mathematical reference is Anantharaman–Popa, *An Introduction to II₁ Factors*,
Definition 15.1.1 and Corollary 15.1.4.
-/

public section

namespace ContRepresentation

section Monoid

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

/-- A representation has spectral gap if finitely many squared displacements control the squared
norm of every vector orthogonal to its invariant vectors. -/
def HasSpectralGap (ρ : ContRepresentation 𝕜 G V) : Prop :=
  ∃ (F : Finset G) (C : ℝ), 0 < C ∧
    ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2

/-- The finite sum-of-squares criterion for spectral gap. -/
theorem hasSpectralGap_def (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap ↔ ∃ (F : Finset G) (C : ℝ), 0 < C ∧
      ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
  Iff.rfl

/-- The trivial representation has spectral gap: its invariant complement is zero, even when the
ambient space is nonzero. -/
@[simp]
theorem hasSpectralGap_trivial :
    (ContRepresentation.trivial 𝕜 G V).HasSpectralGap := by
  refine ⟨∅, 1, zero_lt_one, fun v hv ↦ ?_⟩
  have hinv : (ContRepresentation.trivial 𝕜 G V).invariants = ⊤ := by
    ext v
    simp
  have hvzero : v = 0 := by simpa [hinv] using hv
  simp [hvzero]

end Monoid

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

/-- A unitary representation has spectral gap exactly when the representation on the orthogonal
complement of its fixed vectors has no almost invariant vectors. -/
theorem hasSpectralGap_iff_not_invariantsOrthogonal_hasAlmostInvariantVectors
    (ρ : ContRepresentation 𝕜 G V) (hρ : ρ.IsUnitary) :
    ρ.HasSpectralGap ↔ ¬ hρ.invariantsOrthogonal.HasAlmostInvariantVectors := by
  rw [not_hasAlmostInvariantVectors_iff_exists_norm_sq_le]
  constructor
  · rintro ⟨F, C, hC, hbound⟩
    refine ⟨F, C, hC, fun v ↦ ?_⟩
    simpa only [← Submodule.norm_coe, Submodule.coe_sub,
      IsUnitary.coe_invariantsOrthogonal_apply] using hbound v v.property
  · rintro ⟨F, C, hC, hbound⟩
    refine ⟨F, C, hC, fun v hv ↦ ?_⟩
    simpa only [← Submodule.norm_coe, Submodule.coe_sub,
      IsUnitary.coe_invariantsOrthogonal_apply] using hbound ⟨v, hv⟩

/-- Every representation of a finite group has spectral gap, without unitarity or completeness. -/
theorem hasSpectralGap_of_finite [Finite G] (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap := by
  classical
  let := Fintype.ofFinite G
  refine ⟨Finset.univ, 1, zero_lt_one, fun v hv ↦ ?_⟩
  simp only [one_mul]
  by_contra! hbound
  have hmove : ∀ g, ‖ρ g v - v‖ < ‖v‖ := by
    intro g
    have hsingle := Finset.single_le_sum
      (fun g (_ : g ∈ Finset.univ) ↦ sq_nonneg ‖ρ g v - v‖) (Finset.mem_univ g)
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsingle.trans_lt hbound)
  obtain ⟨w, hw, hclose⟩ := ρ.exists_invariant_norm_sub_lt hmove
  have horth : inner (𝕜 := 𝕜) w v = 0 := hv w hw
  have hnorm := norm_sub_sq (𝕜 := 𝕜) w v
  rw [horth, map_zero] at hnorm
  have hsq := (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hclose
  nlinarith [sq_nonneg ‖w‖]

end ContRepresentation
