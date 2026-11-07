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

The norm estimate characterizing absence of almost invariant vectors is proved first for
arbitrary normed representations over `ℝ` or `ℂ`; neither unitarity nor completeness is needed
for that estimate. Every unitary representation of a finite group has spectral gap.

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
theorem hasSpectralGap_iff_not_hasAlmostInvariantVectors (hρ : ρ.IsUnitary) :
    ρ.HasSpectralGap ↔
      ¬(ρ.subrepresentation ρ.invariantsᗮ
        (fun g _ hv ↦ hρ.apply_mem_orthogonal
          (fun g w hw ↦ by simpa [hw g] using hw) g hv)).HasAlmostInvariantVectors := by
  rw [not_hasAlmostInvariantVectors_iff]
  constructor
  · rintro ⟨F, C, hC, hbound⟩
    refine ⟨F, C, hC, fun v ↦ ?_⟩
    simpa only [← Submodule.norm_coe, Submodule.coe_sub, coe_subrepresentation_apply]
      using hbound v v.property
  · rintro ⟨F, C, hC, hbound⟩
    refine ⟨F, C, hC, fun v hv ↦ ?_⟩
    simpa only [← Submodule.norm_coe, Submodule.coe_sub, coe_subrepresentation_apply]
      using hbound ⟨v, hv⟩

/-- Every unitary representation of a finite group has spectral gap. No completeness or
finite-dimensionality hypothesis on the representation space is needed. -/
theorem IsUnitary.hasSpectralGap_of_finite [Finite G] (hρ : ρ.IsUnitary) :
    ρ.HasSpectralGap := by
  rw [hasSpectralGap_iff_not_hasAlmostInvariantVectors hρ]
  intro h
  obtain ⟨v, hv, hfixed⟩ := h.exists_invariant_ne_zero
  have hmem : (v : V) ∈ ρ.invariants := mem_invariants_subrepresentation.mp hfixed
  have hzero : (v : V) = 0 :=
    (Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint ρ.invariants)) _ hmem v.property
  exact hv (Subtype.ext hzero)

end Unitary

end ContRepresentation
