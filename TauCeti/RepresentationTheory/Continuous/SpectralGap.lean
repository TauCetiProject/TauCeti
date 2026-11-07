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

A representation has spectral gap when a finite sum of squared displacements controls the
squared norm on the orthogonal complement of its invariant vectors. For a unitary group
representation this is equivalent to absence of almost invariant vectors in that complement.
It is not absence of almost invariant vectors in the whole representation: in particular,
trivial representations have spectral gap.

We first prove the normed-space coercivity criterion for absence of almost invariant vectors.
The spectral-gap inequality also has a version controlling the distance to the invariant
subspace, whenever that subspace admits an orthogonal projection. None of these inequalities
requires completeness; unitarity is used only to make the orthogonal complement invariant.

Reference: Anantharaman–Popa, *An Introduction to II₁ Factors*, Definition 15.1.1 and
Corollary 15.1.4, for the spectral-gap convention.
-/

public section

namespace ContRepresentation

section NormedSpace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]

/-- Absence of almost invariant vectors is equivalent to a finite sum of squared displacements
controlling the squared norm on the whole space. This criterion does not require unitarity. -/
theorem not_hasAlmostInvariantVectors_iff_exists_norm_sq_le_sum
    (ρ : ContRepresentation 𝕜 G V) :
    ¬ρ.HasAlmostInvariantVectors ↔ ∃ (F : Finset G) (C : ℝ), 0 < C ∧
      ∀ v : V, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := by
  classical
  constructor
  · intro hρ
    simp only [hasAlmostInvariantVectors_def, not_forall, not_exists, not_and,
      not_lt] at hρ
    obtain ⟨F, ε, hε, hF⟩ := hρ
    refine ⟨F, (ε ^ 2)⁻¹, by positivity, fun v ↦ ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    obtain ⟨g, hg, hmove⟩ := hF ((‖v‖⁻¹ : 𝕜) • v) (norm_smul_inv_norm hv)
    rw [map_smul, ← smul_sub, norm_smul] at hmove
    simp only [norm_inv, RCLike.norm_ofReal, abs_norm] at hmove
    have hlower : ε * ‖v‖ ≤ ‖ρ g v - v‖ := by
      simpa [mul_comm] using (le_inv_mul_iff₀ hvnorm).mp hmove
    have hsum : ‖ρ g v - v‖ ^ 2 ≤ ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
      Finset.single_le_sum (f := fun g ↦ ‖ρ g v - v‖ ^ 2) (fun _ _ ↦ sq_nonneg _) hg
    have hsq : ε ^ 2 * ‖v‖ ^ 2 ≤ ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := by
      nlinarith [sq_le_sq₀ (by positivity : 0 ≤ ε * ‖v‖) (norm_nonneg _) |>.mpr hlower]
    exact (le_inv_mul_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith)
  · rintro ⟨F, C, hC, hF⟩ hρ
    let δ : ℝ := Real.sqrt (2 * C * ((F.card : ℝ) + 1))⁻¹
    have hden : 0 < 2 * C * ((F.card : ℝ) + 1) := by positivity
    have hδ : 0 < δ := Real.sqrt_pos.2 (inv_pos.2 hden)
    have hδsq : (2 * C * ((F.card : ℝ) + 1)) * δ ^ 2 = 1 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ (2 * C * ((F.card : ℝ) + 1))⁻¹)]
      exact mul_inv_cancel₀ hden.ne'
    obtain ⟨v, hv, hmove⟩ := (hasAlmostInvariantVectors_def ρ).mp hρ F δ hδ
    have hsum : (∑ g ∈ F, ‖ρ g v - v‖ ^ 2) ≤ (F.card : ℝ) * δ ^ 2 := by
      calc
        _ ≤ ∑ _g ∈ F, δ ^ 2 := Finset.sum_le_sum fun g hg ↦
          (sq_le_sq₀ (norm_nonneg _) hδ.le).mpr (hmove g hg).le
        _ = _ := by simp
    have hbound := hF v
    rw [hv, one_pow] at hbound
    have := mul_le_mul_of_nonneg_left hsum hC.le
    nlinarith [mul_nonneg hC.le (sq_nonneg δ)]

end NormedSpace

section InnerProductSpace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

/-- A representation has spectral gap if finitely many squared displacements control the squared
norm on the orthogonal complement of its invariant vectors. In applications the representation
is unitary; the inequality itself makes sense without that assumption. -/
def HasSpectralGap (ρ : ContRepresentation 𝕜 G V) : Prop :=
  ∃ (F : Finset G) (C : ℝ), 0 < C ∧
    ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2

/-- The finite-set inequality defining spectral gap. -/
theorem hasSpectralGap_def (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap ↔ ∃ (F : Finset G) (C : ℝ), 0 < C ∧
      ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
  Iff.rfl

/-- If there are no invariant vectors, spectral gap is exactly absence of almost invariant
vectors in the whole representation. -/
theorem hasSpectralGap_iff_not_hasAlmostInvariantVectors_of_invariants_eq_bot
    (ρ : ContRepresentation 𝕜 G V) (hρ : ρ.invariants = ⊥) :
    ρ.HasSpectralGap ↔ ¬ρ.HasAlmostInvariantVectors := by
  rw [not_hasAlmostInvariantVectors_iff_exists_norm_sq_le_sum, hasSpectralGap_def, hρ]
  simp

/-- Spectral gap controls the distance to the invariant subspace by finitely many displacements.
Only existence of the orthogonal projection is needed, not completeness of the ambient space. -/
theorem hasSpectralGap_iff_exists_norm_sub_starProjection_sq_le
    (ρ : ContRepresentation 𝕜 G V) [ρ.invariants.HasOrthogonalProjection] :
    ρ.HasSpectralGap ↔ ∃ (F : Finset G) (C : ℝ), 0 < C ∧
      ∀ v : V, ‖v - ρ.invariants.starProjection v‖ ^ 2 ≤
        C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := by
  classical
  constructor
  · rintro ⟨F, C, hC, hF⟩
    refine ⟨F, C, hC, fun v ↦ ?_⟩
    have hfixed := ρ.invariants.starProjection_apply_mem v
    have hmove (g : G) :
        ρ g (v - ρ.invariants.starProjection v) - (v - ρ.invariants.starProjection v) =
          ρ g v - v := by
      rw [map_sub, (mem_invariants _).mp hfixed g]
      abel
    simpa only [hmove] using
      hF _ (ρ.invariants.sub_starProjection_mem_orthogonal v)
  · rintro ⟨F, C, hC, hF⟩
    refine ⟨F, C, hC, fun v hv ↦ ?_⟩
    simpa [ρ.invariants.starProjection_apply_eq_zero_iff.mpr hv] using hF v

/-- A representation on which every vector is invariant has spectral gap, since the inequality
is imposed only on the zero orthogonal complement. -/
theorem hasSpectralGap_of_invariants_eq_top (ρ : ContRepresentation 𝕜 G V)
    (hρ : ρ.invariants = ⊤) : ρ.HasSpectralGap := by
  refine ⟨∅, 1, zero_lt_one, ?_⟩
  intro v hv
  simpa [hρ] using hv

/-- In particular, a trivial representation has spectral gap, even when its space is nonzero. -/
@[simp]
theorem hasSpectralGap_trivial : (trivial 𝕜 G V).HasSpectralGap := by
  apply hasSpectralGap_of_invariants_eq_top
  ext v
  simp

end InnerProductSpace

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] {ρ : ContRepresentation 𝕜 G V}

/-- A unitary group representation has spectral gap exactly when its restriction to the
orthogonal complement of invariant vectors has no almost invariant vectors. -/
theorem IsUnitary.hasSpectralGap_iff_not_hasAlmostInvariantVectors (hρ : ρ.IsUnitary) :
    ρ.HasSpectralGap ↔ ¬(ρ.subrepresentation ρ.invariantsᗮ
      (fun g _ hv ↦ hρ.apply_mem_orthogonal
        (fun g v hv ↦ by simpa [(mem_invariants v).mp hv g] using hv) g hv)
      ).HasAlmostInvariantVectors := by
  rw [not_hasAlmostInvariantVectors_iff_exists_norm_sq_le_sum, hasSpectralGap_def]
  simp only [← Submodule.norm_coe, Submodule.coe_sub, coe_subrepresentation_apply]
  exact ⟨fun ⟨F, C, hC, hF⟩ ↦ ⟨F, C, hC, fun v ↦ hF v v.property⟩,
    fun ⟨F, C, hC, hF⟩ ↦ ⟨F, C, hC, fun v hv ↦ hF ⟨v, hv⟩⟩⟩

end Unitary

end ContRepresentation
