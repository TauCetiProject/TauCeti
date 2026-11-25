/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
import TauCeti.RepresentationTheory.Continuous.Basic
import TauCeti.RepresentationTheory.Invariants
import TauCeti.Topology.MetricSpace.SimultaneousApproximation
import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Almost invariant vectors

A representation has almost invariant vectors if every finite set of group elements moves some
unit vector by arbitrarily little. Restriction along a homomorphism preserves this condition, and
almost invariant vectors yield a directed net of unit vectors whose displacements tend to `0` at
every element of the monoid. Its failure is characterized by a finite quadratic lower bound on
orbit displacements. For finite groups it is equivalent to the existence of a nonzero invariant
vector, without unitarity or completeness assumptions. Almost invariant vectors also have
arbitrarily small total squared displacement on any finite set.

The quantitative averaging lemma works for a subgroup `S` of finite index: averaging the translates
of an `S`-invariant vector over the coset representatives of `S` gives a vector invariant under the
whole group, and it is close to the original vector when those representatives move it little. This
is the averaging step in the finite-index transfer of relative property (T); for a finite group,
taking `S = ⊥`, it produces an invariant vector close to a vector whose entire orbit is close to it.

The definition follows Anantharaman–Popa, *An Introduction to II₁ Factors*, Definition 14.1.1.
The average over coset representatives is `Representation.relNorm`, divided by the index.
-/

public section

open Filter Topology

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

/-- Extract a directed net of unit vectors whose displacements tend to `0` at every monoid element
from `ContRepresentation.HasAlmostInvariantVectors`. -/
theorem HasAlmostInvariantVectors.exists_unit_net_tendsto_sub_zero
    (hρ : ρ.HasAlmostInvariantVectors) :
    ∃ v : Finset G × ℕ → V, (∀ p, ‖v p‖ = 1) ∧
      ∀ g : G, Tendsto (fun p ↦ ‖ρ g (v p) - v p‖) atTop (𝓝 0) :=
  TauCeti.exists_net_tendsto_of_forall_finset_dist_lt
    (p := fun v : V ↦ ‖v‖ = 1) (F := fun g v ↦ ‖ρ g v - v‖) (x := fun _ ↦ 0)
    fun s ε hε ↦ by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using
        (hasAlmostInvariantVectors_def ρ).mp hρ s ε hε

end Definition

section NormedSpace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] {ρ : ContRepresentation 𝕜 G V}

/-- A nonzero invariant vector can be normalized to witness almost invariant vectors. -/
theorem hasAlmostInvariantVectors_of_invariant {v : V} (hv : v ≠ 0)
    (hfixed : v ∈ ρ.invariants) : ρ.HasAlmostInvariantVectors :=
  hasAlmostInvariantVectors_of_invariant_unit (norm_smul_inv_norm hv)
    (ρ.invariants.smul_mem (‖v‖⁻¹ : 𝕜) hfixed)

/-- Failure of almost invariant vectors is equivalent to a uniform finite quadratic lower
bound on orbit displacements. This applies to normed representations, without unitarity or
completeness assumptions. -/
theorem not_hasAlmostInvariantVectors_iff (ρ : ContRepresentation 𝕜 G V) :
    ¬ρ.HasAlmostInvariantVectors ↔
      ∃ (F : Finset G) (c : ℝ), 0 < c ∧
        ∀ v : V, c * ‖v‖ ^ 2 ≤ ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := by
  classical
  constructor
  · intro hρ
    simp only [HasAlmostInvariantVectors, not_forall, not_exists, not_and,
      not_lt, exists_prop] at hρ
    obtain ⟨F, ε, hε, hF⟩ := hρ
    refine ⟨F, ε ^ 2, sq_pos_of_pos hε, fun v ↦ ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    obtain ⟨g, hg, hgv⟩ := hF ((‖v‖⁻¹ : 𝕜) • v) (norm_smul_inv_norm hv)
    have hnorm : ε * ‖v‖ ≤ ‖ρ g v - v‖ := by
      simp only [map_smul, ← smul_sub, norm_smul, norm_inv,
        RCLike.norm_ofReal, abs_norm] at hgv
      exact (le_div_iff₀ (norm_pos_iff.mpr hv)).mp
        (by simpa [div_eq_inv_mul] using hgv)
    calc
      ε ^ 2 * ‖v‖ ^ 2 = (ε * ‖v‖) ^ 2 := (mul_pow _ _ _).symm
      _ ≤ ‖ρ g v - v‖ ^ 2 := pow_le_pow_left₀ (by positivity) hnorm 2
      _ ≤ ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
        Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖ρ i v - v‖) hg
  · rintro ⟨F, c, hc, hF⟩ hρ
    obtain ⟨v, hv, hsmall⟩ := hρ.exists_sum_norm_sq_lt F hc
    have hbound := hF v
    rw [hv, one_pow, mul_one] at hbound
    exact (not_lt_of_ge hbound) hsmall

end NormedSpace

section FiniteIndex

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Let `v` be fixed by a subgroup `S` of finite index. If each chosen representative of the
cosets of `S` moves `v` by less than `ε`, then averaging the translates of `v` over these
representatives produces a vector fixed by the whole group within `ε` of `v`. -/
theorem exists_invariant_norm_sub_lt_of_finiteIndex (ρ : ContRepresentation 𝕜 G V)
    {S : Subgroup G} [S.FiniteIndex] {v : V} (hv : v ∈ (ρ.restrict S.subtype).invariants)
    {ε : ℝ} (hε : ∀ q : G ⧸ S, ‖ρ q.out v - v‖ < ε) :
    ∃ w : V, w ∈ ρ.invariants ∧ ‖w - v‖ < ε := by
  classical
  let := S.fintypeQuotientOfFiniteIndex
  have hc : 0 < (Fintype.card (G ⧸ S) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hc' : (Fintype.card (G ⧸ S) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card (G ⧸ S) : 𝕜)⁻¹ • Representation.relNorm ρ.toRepresentation S v,
    fun g ↦ ?_, ?_⟩
  · rw [map_smul, ← toRepresentation_apply, Representation.relNorm_apply_eq_self
      ρ.toRepresentation (H := S) (fun s ↦ by simpa using hv s) g]
  · -- The difference is the average of the displacements `ρ q.out v - v`.
    have havg : (Fintype.card (G ⧸ S) : 𝕜)⁻¹ • Representation.relNorm ρ.toRepresentation S v - v =
        (Fintype.card (G ⧸ S) : 𝕜)⁻¹ • ∑ q : G ⧸ S, (ρ q.out v - v) := by
      rw [Representation.relNorm_apply]
      simp [Finset.sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul 𝕜, hc']
    rw [havg, norm_smul, norm_inv, RCLike.norm_natCast, inv_mul_lt_iff₀ hc]
    calc ‖∑ q : G ⧸ S, (ρ q.out v - v)‖ ≤ ∑ q : G ⧸ S, ‖ρ q.out v - v‖ := norm_sum_le _ _
      _ < ∑ _q : G ⧸ S, ε := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun q _ ↦ hε q
      _ = Fintype.card (G ⧸ S) * ε := by simp

end FiniteIndex

section Finite

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [Finite G] [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]

/-- If every group element moves a vector by less than `ε`, averaging produces an invariant
vector within `ε` of it. This does not require the representation to be unitary. -/
theorem exists_invariant_norm_sub_lt (ρ : ContRepresentation 𝕜 G V) {v : V} {ε : ℝ}
    (hv : ∀ g, ‖ρ g v - v‖ < ε) :
    ∃ w : V, w ∈ ρ.invariants ∧ ‖w - v‖ < ε :=
  -- Average over the cosets of the trivial subgroup, which has finite index and fixes `v`.
  ρ.exists_invariant_norm_sub_lt_of_finiteIndex (S := ⊥)
    (fun ⟨_, hs⟩ ↦ by simp [Subgroup.mem_bot.mp hs]) fun q ↦ hv q.out

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
