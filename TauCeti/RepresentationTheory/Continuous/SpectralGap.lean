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

A representation has spectral gap when finitely many displacement operators control the norm
on the orthogonal complement of its invariant vectors. For a unitary group representation,
this is equivalent to the absence of almost invariant vectors in that complement. In particular,
fixed vectors do not obstruct spectral gap: the trivial representation has spectral gap.

The proof uses the general squared-displacement criterion `not_hasAlmostInvariantVectors_iff`
from `AlmostInvariant`, which needs neither unitarity nor completeness.
Every representation of a finite group has spectral gap.

Reference: Anantharaman–Popa, *An Introduction to II₁ Factors*, Definition 15.1.1 and
Corollary 15.1.4.
-/

public section

namespace ContRepresentation

section InnerProduct

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

/-- Finitely many displacement operators control the squared norm on the orthogonal complement
of the invariant vectors. The inequality is not imposed on the fixed subspace itself. -/
def HasSpectralGap (ρ : ContRepresentation 𝕜 G V) : Prop :=
  ∃ (F : Finset G) (C : ℝ), 0 < C ∧
    ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2

/-- The finite-set inequality defining spectral gap. -/
theorem hasSpectralGap_def (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap ↔ ∃ (F : Finset G) (C : ℝ), 0 < C ∧
      ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
  Iff.rfl

/-- If every vector is fixed, the representation has spectral gap, including when its space
is nonzero. -/
theorem hasSpectralGap_of_invariants_eq_top (ρ : ContRepresentation 𝕜 G V)
    (hρ : ρ.invariants = ⊤) : ρ.HasSpectralGap := by
  refine ⟨∅, 1, zero_lt_one, fun v hv ↦ ?_⟩
  simpa [hρ] using hv

/-- The trivial representation has spectral gap: its orthogonal complement of fixed vectors
is zero, even on a nonzero representation space. -/
@[simp]
theorem hasSpectralGap_trivial : (trivial 𝕜 G V).HasSpectralGap := by
  apply hasSpectralGap_of_invariants_eq_top
  ext v
  simp [mem_invariants]

end InnerProduct

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] {ρ : ContRepresentation 𝕜 G V}

/-- A unitary group representation has spectral gap exactly when its restriction to the
orthogonal complement of the fixed vectors has no almost invariant vectors. -/
theorem hasSpectralGap_iff_not_hasAlmostInvariantVectors_invariantsOrthogonal
    (hρ : ρ.IsUnitary) :
    ρ.HasSpectralGap ↔ ¬hρ.invariantsOrthogonal.HasAlmostInvariantVectors := by
  rw [not_hasAlmostInvariantVectors_iff]
  constructor
  · rintro ⟨F, C, hC, hbound⟩
    refine ⟨F, C, hC, fun v ↦ ?_⟩
    simpa only [← Submodule.norm_coe, Submodule.coe_sub, IsUnitary.coe_invariantsOrthogonal_apply]
      using hbound v v.property
  · rintro ⟨F, C, hC, hbound⟩
    refine ⟨F, C, hC, fun v hv ↦ ?_⟩
    simpa only [← Submodule.norm_coe, Submodule.coe_sub, IsUnitary.coe_invariantsOrthogonal_apply]
      using hbound ⟨v, hv⟩

/-- Every representation of a finite group has spectral gap. No unitarity, completeness or
finite-dimensionality hypothesis on the representation space is needed. -/
theorem hasSpectralGap_of_finite [Finite G] (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap := by
  classical
  let := Fintype.ofFinite G
  refine ⟨Finset.univ, 1, zero_lt_one, fun v hv ↦ ?_⟩
  rw [one_mul]
  by_contra! hbound
  have hdis (g : G) : ‖ρ g v - v‖ < ‖v‖ := by
    have hle : ‖ρ g v - v‖ ^ 2 ≤ ∑ g : G, ‖ρ g v - v‖ ^ 2 :=
      Finset.single_le_sum (fun g _ ↦ sq_nonneg ‖ρ g v - v‖) (Finset.mem_univ g)
    nlinarith [norm_nonneg (ρ g v - v), norm_nonneg v]
  obtain ⟨w, hw, hclose⟩ := ρ.exists_invariant_norm_sub_lt hdis
  have hpyth : ‖w - v‖ ^ 2 = ‖w‖ ^ 2 + ‖v‖ ^ 2 := by
    simpa only [hv w hw, map_zero, mul_zero, sub_zero] using (norm_sub_sq (𝕜 := 𝕜) w v)
  nlinarith [sq_nonneg ‖w‖, norm_nonneg (w - v), norm_nonneg v]

end Unitary

end ContRepresentation
