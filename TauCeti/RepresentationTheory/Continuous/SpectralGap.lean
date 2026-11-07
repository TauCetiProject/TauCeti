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

Every representation of a finite group has spectral gap when it is unitary, and the trivial
representation has spectral gap even on a nonzero space. None of these results requires
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

namespace IsUnitary

variable {ρ : ContRepresentation 𝕜 G V}

/-- The restriction of a unitary representation to the orthogonal complement of its fixed vectors.
This is the representation on which absence of almost invariant vectors detects spectral gap. -/
def invariantComplement (hρ : ρ.IsUnitary) : ContRepresentation 𝕜 G ρ.invariantsᗮ :=
  ρ.subrepresentation _ (hρ.apply_mem_orthogonal (fun g v hv ↦ by simpa [hv g] using hv))

/-- The action on the invariant complement agrees with the ambient action. -/
@[simp]
theorem coe_invariantComplement_apply (hρ : ρ.IsUnitary) (g : G) (v : ρ.invariantsᗮ) :
    (hρ.invariantComplement g v : V) = ρ g (v : V) :=
  coe_subrepresentation_apply g v

/-- The invariant complement remains unitary. -/
theorem isUnitary_invariantComplement (hρ : ρ.IsUnitary) : hρ.invariantComplement.IsUnitary :=
  hρ.subrepresentation _

/-- The invariant complement has no nonzero fixed vectors. -/
@[simp]
theorem invariants_invariantComplement (hρ : ρ.IsUnitary) :
    hρ.invariantComplement.invariants = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hfixed : (v : V) ∈ ρ.invariants :=
    mem_invariants_subrepresentation.mp hv
  apply Subtype.ext
  exact (Submodule.disjoint_def.mp ρ.invariants.orthogonal_disjoint) v hfixed v.property

end IsUnitary

/-- A unitary representation has spectral gap exactly when the representation on the orthogonal
complement of its fixed vectors has no almost invariant vectors. -/
theorem hasSpectralGap_iff_not_hasAlmostInvariantVectors
    (ρ : ContRepresentation 𝕜 G V) (hρ : ρ.IsUnitary) :
    ρ.HasSpectralGap ↔ ¬ hρ.invariantComplement.HasAlmostInvariantVectors := by
  rw [not_hasAlmostInvariantVectors_iff_exists_norm_sq_le]
  constructor
  · rintro ⟨F, C, hC, hbound⟩
    refine ⟨F, C, hC, fun v ↦ ?_⟩
    simpa only [← Submodule.norm_coe, Submodule.coe_sub,
      IsUnitary.coe_invariantComplement_apply] using hbound v v.property
  · rintro ⟨F, C, hC, hbound⟩
    refine ⟨F, C, hC, fun v hv ↦ ?_⟩
    simpa only [← Submodule.norm_coe, Submodule.coe_sub,
      IsUnitary.coe_invariantComplement_apply] using hbound ⟨v, hv⟩

/-- Every unitary representation of a finite group has spectral gap. -/
theorem IsUnitary.hasSpectralGap_of_finite [Finite G] {ρ : ContRepresentation 𝕜 G V}
    (hρ : ρ.IsUnitary) : ρ.HasSpectralGap := by
  rw [hasSpectralGap_iff_not_hasAlmostInvariantVectors ρ hρ]
  intro h
  obtain ⟨v, hv, hfixed⟩ := h.exists_invariant_ne_zero
  exact hv (by simpa only [hρ.invariants_invariantComplement, Submodule.mem_bot] using hfixed)

end ContRepresentation
