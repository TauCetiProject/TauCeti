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

A representation has spectral gap when a finite sum of squared orbit displacements controls
squared norms on the orthogonal complement of its invariant vectors. The fixed subspace is
removed: in particular a trivial representation has spectral gap.

For a unitary monoid representation the orthogonal complement carries a unitary representation,
`IsUnitary.invariantsOrthogonal`. Spectral gap is equivalent to the absence of almost invariant
vectors in this representation. Every representation of a finite group has spectral gap.
These criteria are the representation-theoretic starting point for spectral gap of actions.
Neither completeness nor a topology on the acting group is needed here.

The reference is Anantharaman–Popa, *An Introduction to II₁ Factors*, Definition 15.1.1 and
Corollary 15.1.4. Almost invariant vectors express weak containment of the trivial representation;
no general weak-containment relation is defined here.
-/

public section

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

section Monoid

variable [Monoid G]

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

end Monoid

section Group

variable [Group G]

/-- Every representation of a finite group has spectral gap, without unitarity or
completeness assumptions. -/
theorem hasSpectralGap_of_finite [Finite G] (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap := by
  classical
  let := Fintype.ofFinite G
  refine ⟨Finset.univ, 1, zero_lt_one, fun v hv ↦ ?_⟩
  rw [one_mul]
  by_contra! hbound
  have hmove (g : G) : ‖ρ g v - v‖ < ‖v‖ := by
    have hsingle := Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset G)) ↦ sq_nonneg ‖ρ i v - v‖)
      (Finset.mem_univ g)
    nlinarith [norm_nonneg (ρ g v - v), norm_nonneg v]
  obtain ⟨w, hw, hclose⟩ := ρ.exists_invariant_norm_sub_lt hmove
  have horth := (ρ.invariants.mem_orthogonal v).mp hv w hw
  have hpyth := norm_sub_sq (𝕜 := 𝕜) w v
  rw [horth, map_zero, mul_zero, sub_zero] at hpyth
  nlinarith [sq_nonneg ‖w‖, norm_nonneg (w - v), norm_nonneg v]

end Group

section Monoid

variable [Monoid G]

/-- The trivial representation has spectral gap, since its invariant complement is zero. -/
@[simp]
theorem hasSpectralGap_trivial :
    (trivial 𝕜 G V).HasSpectralGap := by
  refine ⟨∅, 1, zero_lt_one, fun v hv ↦ ?_⟩
  have hfixed : v ∈ (trivial 𝕜 G V).invariants := by simp
  have hzero : v = 0 :=
    (Submodule.disjoint_def.mp (trivial 𝕜 G V).invariants.orthogonal_disjoint) v hfixed hv
  simp [hzero]

end Monoid

end ContRepresentation
