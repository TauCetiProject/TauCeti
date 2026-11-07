/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.AlmostInvariant
public import TauCeti.RepresentationTheory.Continuous.InvariantComplement

/-!
# Spectral gap of a unitary representation

A representation has spectral gap when a finite sum of squared orbit displacements controls
squared norms on the orthogonal complement of its invariant vectors. The fixed subspace is
removed: in particular a trivial representation has spectral gap.

For a unitary group representation the orthogonal complement carries a unitary representation,
`IsUnitary.invariantsOrthogonal`. Spectral gap is equivalent to the absence of almost invariant
vectors in this representation. Every unitary representation of a finite group has spectral gap.
These criteria are the representation-theoretic starting point for spectral gap of actions.
Neither completeness nor a topology on the acting group is needed here.

The reference is Anantharaman–Popa, *An Introduction to II₁ Factors*, Definition 15.1.1 and
Corollary 15.1.4. Almost invariant vectors express weak containment of the trivial representation;
no general weak-containment relation is defined here.
-/

public section

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

/-- A representation has spectral gap if finitely many squared orbit displacements control the
squared norm of every vector orthogonal to the invariant subspace. -/
def HasSpectralGap (ρ : ContRepresentation 𝕜 G V) : Prop :=
  ∃ (F : Finset G) (C : ℝ), 0 < C ∧
    ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2

/-- The finite quadratic inequality characterizing spectral gap. -/
theorem hasSpectralGap_def (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap ↔ ∃ (F : Finset G) (C : ℝ), 0 < C ∧
      ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
  Iff.rfl

namespace IsUnitary

variable {ρ : ContRepresentation 𝕜 G V}

/-- The restriction of a unitary representation to the orthogonal complement of its invariant
vectors. -/
def invariantsOrthogonal (hρ : ρ.IsUnitary) : ContRepresentation 𝕜 G ρ.invariantsᗮ :=
  ρ.subrepresentation ρ.invariantsᗮ
    (fun g _ hv ↦ hρ.apply_mem_orthogonal (fun h _ hw ↦ by simpa only [hw h] using hw) g hv)

/-- The action on the orthogonal complement is the original action on underlying vectors. -/
@[simp]
theorem coe_invariantsOrthogonal_apply (hρ : ρ.IsUnitary) (g : G) (v : ρ.invariantsᗮ) :
    (hρ.invariantsOrthogonal g v : V) = ρ g v :=
  coe_subrepresentation_apply _ _

/-- The orthogonal-complement representation is unitary. -/
theorem isUnitary_invariantsOrthogonal (hρ : ρ.IsUnitary) :
    hρ.invariantsOrthogonal.IsUnitary :=
  hρ.subrepresentation _

/-- Removing the invariant subspace leaves no nonzero invariant vectors. -/
@[simp]
theorem invariants_invariantsOrthogonal (hρ : ρ.IsUnitary) :
    hρ.invariantsOrthogonal.invariants = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have hfixed : (v : V) ∈ ρ.invariants := by
    intro g
    simpa only [coe_invariantsOrthogonal_apply] using congrArg Subtype.val (hv g)
  have hzero : (v : V) = 0 :=
    (Submodule.disjoint_def.mp ρ.invariants.orthogonal_disjoint) v hfixed v.property
  exact Subtype.ext hzero

end IsUnitary

/-- Spectral gap means that the representation on the orthogonal complement of the invariant
vectors has no almost invariant vectors. Equivalently, the trivial representation is not weakly
contained in that complement. -/
theorem hasSpectralGap_iff_not_hasAlmostInvariantVectors
    (ρ : ContRepresentation 𝕜 G V) (hρ : ρ.IsUnitary) :
    ρ.HasSpectralGap ↔ ¬hρ.invariantsOrthogonal.HasAlmostInvariantVectors := by
  rw [not_hasAlmostInvariantVectors_iff]
  constructor
  · rintro ⟨F, C, hC, hF⟩
    refine ⟨F, C⁻¹, inv_pos.mpr hC, fun v ↦ ?_⟩
    have hv := hF v v.property
    calc
      C⁻¹ * ‖v‖ ^ 2 ≤ C⁻¹ * (C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hC.le)
      _ = ∑ g ∈ F, ‖hρ.invariantsOrthogonal g v - v‖ ^ 2 := by
        simp [← Submodule.norm_coe, hC.ne']
  · rintro ⟨F, c, hc, hF⟩
    refine ⟨F, c⁻¹, inv_pos.mpr hc, fun v hv ↦ ?_⟩
    have hbound := hF ⟨v, hv⟩
    have hsum : (∑ g ∈ F, ‖hρ.invariantsOrthogonal g ⟨v, hv⟩ - ⟨v, hv⟩‖ ^ 2) =
        ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := by
      simp [← Submodule.norm_coe]
    rw [hsum] at hbound
    calc
      ‖v‖ ^ 2 = c⁻¹ * (c * ‖v‖ ^ 2) := by simp [hc.ne']
      _ ≤ c⁻¹ * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hc.le)

/-- Every unitary representation of a finite group has spectral gap. -/
theorem hasSpectralGap_of_finite (ρ : ContRepresentation 𝕜 G V) (hρ : ρ.IsUnitary)
    [Finite G] : ρ.HasSpectralGap := by
  rw [hasSpectralGap_iff_not_hasAlmostInvariantVectors ρ hρ]
  intro h
  obtain ⟨v, hv, hfixed⟩ := h.exists_invariant_ne_zero
  rw [hρ.invariants_invariantsOrthogonal, Submodule.mem_bot] at hfixed
  exact hv hfixed

/-- The trivial representation has spectral gap, since its invariant complement is zero. -/
@[simp]
theorem hasSpectralGap_trivial :
    (trivial 𝕜 G V).HasSpectralGap := by
  refine ⟨∅, 1, zero_lt_one, fun v hv ↦ ?_⟩
  have hfixed : v ∈ (trivial 𝕜 G V).invariants := by simp
  have hzero : v = 0 :=
    (Submodule.disjoint_def.mp (trivial 𝕜 G V).invariants.orthogonal_disjoint) v hfixed hv
  simp [hzero]

end ContRepresentation
