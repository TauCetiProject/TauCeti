/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
import TauCeti.RepresentationTheory.Invariants
import TauCeti.Algebra.BigOperators.Finset.Average

/-!
# Almost invariant vectors

A representation has almost invariant vectors if every finite set of group elements moves some
unit vector by arbitrarily little. Restriction along a homomorphism preserves this condition.
For finite groups it is equivalent to the existence of a nonzero invariant vector, without
unitarity or completeness assumptions. The quantitative averaging lemma also produces an
invariant vector close to a vector whose entire orbit is close to it. Almost invariant vectors
also have arbitrarily small total squared displacement on a finite set. Their absence is
equivalent to a finite sum-of-squares bound on the whole space, the normed-space criterion
underlying spectral gap.

These results provide the finite-group averaging step in the theory of property (T).
The definition follows Anantharaman–Popa, *An Introduction to II₁ Factors*, Definition 14.1.1.
The finite average is Mathlib's `Representation.averageMap`.
-/

public section

namespace ContRepresentation

section Definition

variable {R G V : Type*} [Ring R] [Monoid G] [NormedAddCommGroup V] [Module R V]

/-- Every finite set of group elements admits an arbitrarily nearly fixed unit vector.
No topology on the acting monoid is required; in particular this is the discrete-group notion. -/
def HasAlmostInvariantVectors (ρ : ContRepresentation R G V) : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ v : V, ‖v‖ = 1 ∧ ∀ g ∈ F, ‖ρ g v - v‖ < ε

/-- The finite-set criterion for almost invariant vectors. -/
theorem hasAlmostInvariantVectors_def (ρ : ContRepresentation R G V) :
    ρ.HasAlmostInvariantVectors ↔ ∀ (F : Finset G) (ε : ℝ), 0 < ε →
      ∃ v : V, ‖v‖ = 1 ∧ ∀ g ∈ F, ‖ρ g v - v‖ < ε :=
  Iff.rfl

variable {ρ : ContRepresentation R G V}

/-- A representation with almost invariant vectors has a nonzero vector. -/
theorem HasAlmostInvariantVectors.exists_ne_zero (hρ : ρ.HasAlmostInvariantVectors) :
    ∃ v : V, v ≠ 0 := by
  obtain ⟨v, hv, _⟩ := hρ ∅ 1 zero_lt_one
  exact ⟨v, fun h ↦ by simp [h] at hv⟩

/-- A fixed unit vector witnesses almost invariant vectors. -/
theorem hasAlmostInvariantVectors_of_invariant_unit {v : V} (hv : ‖v‖ = 1)
    (hfixed : v ∈ ρ.invariants) : ρ.HasAlmostInvariantVectors := by
  intro F ε hε
  exact ⟨v, hv, fun g _ ↦ by simpa [hfixed g] using hε⟩

/-- Pulling back a representation along any monoid homomorphism preserves almost invariant
vectors. -/
theorem HasAlmostInvariantVectors.restrict {K : Type*} [Monoid K]
    (hρ : ρ.HasAlmostInvariantVectors) (f : K →* G) :
    (ρ.restrict f).HasAlmostInvariantVectors := by
  classical
  intro F ε hε
  obtain ⟨v, hv, hF⟩ := hρ (F.image f) ε hε
  refine ⟨v, hv, fun g hg ↦ ?_⟩
  simpa only [restrict_apply_apply] using hF (f g) (Finset.mem_image_of_mem f hg)

end Definition

section NormedSpace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] {ρ : ContRepresentation 𝕜 G V}

/-- A nonzero invariant vector can be normalized to witness almost invariant vectors. -/
theorem hasAlmostInvariantVectors_of_invariant {v : V} (hv : v ≠ 0)
    (hfixed : v ∈ ρ.invariants) : ρ.HasAlmostInvariantVectors :=
  hasAlmostInvariantVectors_of_invariant_unit (norm_smul_inv_norm hv)
    (ρ.invariants.smul_mem (‖v‖⁻¹ : 𝕜) hfixed)

/-- Almost invariant vectors have arbitrarily small total squared displacement on any finite
set. The vector is still required to have norm one. -/
theorem HasAlmostInvariantVectors.exists_sum_norm_sq_lt
    (hρ : ρ.HasAlmostInvariantVectors) (F : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : V, ‖v‖ = 1 ∧ ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 < ε := by
  have hd : 0 < (F.card : ℝ) + 1 := by positivity
  have hq : 0 < ε / (F.card + 1) := div_pos hε hd
  obtain ⟨v, hv, hF⟩ := hρ F (Real.sqrt (ε / (F.card + 1))) (Real.sqrt_pos.2 hq)
  refine ⟨v, hv, ?_⟩
  have hsum : ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 ≤ F.card * (ε / (F.card + 1)) := by
    calc
      _ ≤ ∑ _g ∈ F, ε / (F.card + 1) := by
        apply Finset.sum_le_sum
        intro g hg
        exact (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 (hF g hg) |>.le.trans
          (Real.sq_sqrt hq.le).le
      _ = _ := by simp
  have hmul := (div_mul_cancel₀ ε hd.ne').symm
  nlinarith

/-- Absence of almost invariant vectors is equivalent to a finite sum-of-squares bound on the
whole representation space. No unitarity, inner product, or completeness is needed. -/
theorem not_hasAlmostInvariantVectors_iff_exists_norm_sq_le (ρ : ContRepresentation 𝕜 G V) :
    ¬ ρ.HasAlmostInvariantVectors ↔
      ∃ (F : Finset G) (C : ℝ), 0 < C ∧
        ∀ v : V, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := by
  classical
  constructor
  · intro hρ
    obtain ⟨F, ε, hε, hF⟩ : ∃ (F : Finset G) (ε : ℝ), 0 < ε ∧
        ∀ v : V, ‖v‖ = 1 → ∃ g ∈ F, ε ≤ ‖ρ g v - v‖ := by
      simpa only [HasAlmostInvariantVectors, not_forall, not_exists, not_and,
        exists_prop, not_lt] using hρ
    refine ⟨F, (ε ^ 2)⁻¹, by positivity, fun v ↦ ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    obtain ⟨g, hg, hmove⟩ := hF ((‖v‖⁻¹ : 𝕜) • v) (norm_smul_inv_norm hv)
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hscaled : ε * ‖v‖ ≤ ‖ρ g v - v‖ := by
      have : ε ≤ ‖ρ g v - v‖ / ‖v‖ := by
        simpa [map_smul, ← smul_sub, norm_smul, div_eq_inv_mul] using hmove
      exact (le_div_iff₀ hnorm).mp this
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ ε * ‖v‖) (norm_nonneg _)).2 hscaled
    have hsingle := Finset.single_le_sum (fun g (_ : g ∈ F) ↦ sq_nonneg ‖ρ g v - v‖) hg
    apply (le_inv_mul_iff₀ (sq_pos_of_pos hε)).2
    nlinarith
  · rintro ⟨F, C, hC, hbound⟩ hρ
    obtain ⟨v, hv, hsmall⟩ := hρ.exists_sum_norm_sq_lt F (inv_pos.mpr hC)
    have h := hbound v
    rw [hv, one_pow] at h
    have := (mul_lt_mul_of_pos_left hsmall hC).trans_eq (mul_inv_cancel₀ hC.ne')
    linarith

end NormedSpace

section Finite

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [Finite G] [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]

/-- If every group element moves a vector by less than `ε`, averaging produces an invariant
vector within `ε` of it. This does not require the representation to be unitary. -/
theorem exists_invariant_norm_sub_lt (ρ : ContRepresentation 𝕜 G V) {v : V} {ε : ℝ}
    (hv : ∀ g, ‖ρ g v - v‖ < ε) :
    ∃ w : V, w ∈ ρ.invariants ∧ ‖w - v‖ < ε := by
  classical
  let := Fintype.ofFinite G
  let : Invertible (Fintype.card G : 𝕜) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hc : 0 < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨ρ.toRepresentation.averageMap v, ?_, ?_⟩
  · exact ρ.toRepresentation.averageMap_invariant v
  · have havg : ρ.toRepresentation.averageMap v - v =
        (Fintype.card G : 𝕜)⁻¹ • ∑ g : G, (ρ g v - v) := by
      rw [Representation.averageMap_apply, Finset.sum_sub_distrib, smul_sub,
        ← invOf_eq_inv, Fintype.invOf_card_smul_sum_const]
      -- Forgetting continuity via `toRepresentation` leaves each operator's action unchanged.
      rfl
    rw [havg, norm_smul]
    simp only [norm_inv, RCLike.norm_natCast]
    calc
      (Fintype.card G : ℝ)⁻¹ * ‖∑ g : G, (ρ g v - v)‖ ≤
          (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖ρ g v - v‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ < (Fintype.card G : ℝ)⁻¹ * ∑ _g : G, ε :=
        mul_lt_mul_of_pos_left
          (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun g _ ↦ hv g)
          (by positivity)
      _ = ε := by simp [hc.ne']

/-- For a finite group, almost invariant vectors give a nonzero invariant vector even in an
incomplete normed representation. -/
theorem HasAlmostInvariantVectors.exists_invariant_ne_zero
    {ρ : ContRepresentation 𝕜 G V} (hρ : ρ.HasAlmostInvariantVectors) :
    ∃ v : V, v ≠ 0 ∧ v ∈ ρ.invariants := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨v, hv, hF⟩ := hρ Finset.univ 1 zero_lt_one
  obtain ⟨w, hw, hclose⟩ := ρ.exists_invariant_norm_sub_lt (fun g ↦ hF g (Finset.mem_univ g))
  refine ⟨w, ?_, hw⟩
  intro hzero
  simp [hzero, hv] at hclose

/-- For finite groups, having almost invariant vectors is exactly having a nonzero invariant
vector. Neither unitarity nor completeness is needed. -/
theorem hasAlmostInvariantVectors_iff_exists_invariant_ne_zero
    (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasAlmostInvariantVectors ↔ ∃ v : V, v ≠ 0 ∧ v ∈ ρ.invariants :=
  ⟨fun h ↦ h.exists_invariant_ne_zero,
    fun ⟨_, hv, hfixed⟩ ↦ hasAlmostInvariantVectors_of_invariant hv hfixed⟩

end Finite

end ContRepresentation
