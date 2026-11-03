/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Setoid.Basic
public import TauCeti.Data.Setoid.Countable
public import TauCeti.ModelTheory.Counting.Stratification

/-!
# Back-and-forth scattered sets of configurations

A set `K` of relational configurations on `ℕ` is *back-and-forth scattered* when, at every
countable back-and-forth level `α`, it meets only countably many `α`-classes. These are classes of
the level restricted to `K`, not individual configurations: `K` itself may be uncountable. The
notion is monotone, and a set meeting countably many isomorphism classes is scattered, since
isomorphism refines every level. Scatteredness can be checked through observations: maps with
countably many values on `K` at each level, equal values forcing equivalence at that level.

Scatteredness is what makes an isolating rank count isomorphism classes exactly. On a scattered
set, each rank stratum of the isomorphism classes injects into a countable level quotient, so it is
countable. Hence a scattered set meets at most `ℵ₁` isomorphism classes (the stratification bound
`TauCeti.IsIsolatingRank.mk_isoClasses_le_aleph_one_of_countable_levels`, applied to
`TauCeti.BFScattered.countable_quotient`), exactly `ℵ₁` when it meets uncountably many, and
countably many exactly when the rank is bounded below `ω₁` on it. In particular, whether a rank is
bounded on a scattered set does not depend on which isolating rank is used.

No definability or invariance of `K`, and no countability of the language, is assumed.

## Main definitions

* `TauCeti.BFScattered K`: `K` meets countably many classes at every countable level.

## Main results

* `TauCeti.bfScattered_iff_countable_image`: the image form of scatteredness.
* `TauCeti.BFScattered.mono`: subsets of scattered sets are scattered.
* `TauCeti.BFScattered.of_countable_isoClasses`: countably many isomorphism classes give a
  scattered set.
* `TauCeti.bfScattered_of_observation`: scatteredness from observations at each level.
* `TauCeti.IsIsolatingRank.countable_rankOnIsoClasses_preimage`: on a scattered set, every rank
  stratum of the isomorphism classes is countable.
* `TauCeti.IsIsolatingRank.mk_isoClasses_eq_aleph_one`: a scattered set meeting uncountably many
  isomorphism classes meets exactly `ℵ₁` of them.
* `TauCeti.IsIsolatingRank.countable_isoClasses_iff_bounded`: a scattered set meets countably many
  isomorphism classes exactly when the rank is bounded below `ω₁` on it.
* `TauCeti.IsIsolatingRank.exists_rank_bound_iff`: on a scattered set, any two isolating ranks are
  bounded together.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the
  chapter on Vaught counterexamples (scattered sentences).
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.1 (scattered and unbounded sentences).
* Back-and-forth scatteredness and the counting of scattered classes are also formalized in
  Cameron Freer's `cameronfreer/infinitary-logic`, `InfinitaryLogic/Descriptive/BFScattered.lean`
  and `InfinitaryLogic/Descriptive/ScatteredCounting.lean` (checkpoint `518a366`, Apache-2.0).
  The statements here are for an arbitrary isolating rank.
-/

public section

universe u v

open FirstOrder Cardinal Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {K C : Set (RelationalConfiguration L ℕ)}

/-- A set `K` of configurations on `ℕ` is *back-and-forth scattered* when, at every countable
level `α`, the restriction of `bfEquivSetoid L ℕ α` to `K` has countably many classes. The set
`K` itself may be uncountable. -/
def BFScattered (K : Set (RelationalConfiguration L ℕ)) : Prop :=
  ∀ α : Ordinal.{0}, α < ω₁ →
    Countable (Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _)))

/-- Unfolding lemma for `TauCeti.BFScattered`. -/
theorem bfScattered_iff : BFScattered K ↔ ∀ α : Ordinal.{0}, α < ω₁ →
    Countable (Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _))) :=
  Iff.rfl

/-- A set is scattered exactly when it meets countably many classes of every countable level. -/
theorem bfScattered_iff_countable_image : BFScattered K ↔
    ∀ α : Ordinal.{0}, α < ω₁ → (Quotient.mk (bfEquivSetoid L ℕ α) '' K).Countable := by
  simp only [bfScattered_iff, Setoid.countable_quotient_comap_val_iff]

/-- A scattered set has countably many classes at each countable level. -/
theorem BFScattered.countable_quotient (hK : BFScattered K) {α : Ordinal.{0}} (hα : α < ω₁) :
    Countable (Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _))) :=
  hK α hα

/-- Subsets of scattered sets are scattered. -/
theorem BFScattered.mono (hKC : K ⊆ C) (hC : BFScattered C) : BFScattered K :=
  bfScattered_iff_countable_image.2 fun α hα =>
    (bfScattered_iff_countable_image.1 hC α hα).mono (image_mono hKC)

/-- A set meeting countably many isomorphism classes is scattered: isomorphism refines every
back-and-forth level. -/
theorem BFScattered.of_countable_isoClasses
    [Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)))] : BFScattered K := by
  intro α _
  have hle : (isoSetoid L ℕ).comap (Subtype.val : K → _) ≤
      (bfEquivSetoid L ℕ α).comap Subtype.val := fun x y h => isoSetoid_le_bfEquivSetoid α h
  exact (Setoid.map_of_le_surjective hle).countable

/-- **Scatteredness from observations.** Suppose that at each countable level `α` an observation
`obs α` on the members of `K` takes countably many values, and members with equal observations
are `α`-equivalent. Then `K` is scattered. -/
theorem bfScattered_of_observation {β : Ordinal.{0} → Type*} (obs : ∀ α, K → β α)
    (hcount : ∀ α < ω₁, (range (obs α)).Countable)
    (hobs : ∀ α < ω₁, ∀ c d : K, obs α c = obs α d → bfEquivSetoid L ℕ α c d) :
    BFScattered K := by
  intro α hα
  have := (hcount α hα).to_subtype
  -- Each class is the class of a chosen member with a given observed value.
  exact Function.Surjective.countable
    (f := fun y : range (obs α) => Quotient.mk _ y.2.choose) fun q =>
      Quotient.inductionOn q fun c =>
        ⟨⟨obs α c, c, rfl⟩,
          Quotient.sound (hobs α hα _ _ (⟨c, rfl⟩ : ∃ d, obs α d = obs α c).choose_spec)⟩

namespace IsIsolatingRank

variable {ρ σ : RelationalConfiguration L ℕ → Ordinal.{0}}

/-- On a scattered set, every rank stratum of the isomorphism classes is countable: it injects
into the level quotient at that rank. -/
theorem countable_rankOnIsoClasses_preimage (h : IsIsolatingRank ρ) (hK : BFScattered K)
    (α : Ordinal.{0}) : (rankOnIsoClasses h.iso_invariant K ⁻¹' {α}).Countable := by
  by_cases hα : α < ω₁
  · obtain ⟨f, hf⟩ := h.exists_injective_rank_fiber K α
    have := hK.countable_quotient hα
    exact countable_coe_iff.1 hf.countable
  · -- Above the countable ordinals the stratum is empty.
    refine (countable_empty : (∅ : Set _).Countable).mono fun q hq => hα ?_
    rw [← mem_singleton_iff.1 hq]
    exact rankOnIsoClasses_lt_omega_one h.iso_invariant h.lt_omega_one K q

/-- A scattered set meeting uncountably many isomorphism classes meets exactly `ℵ₁` of them. -/
theorem mk_isoClasses_eq_aleph_one (h : IsIsolatingRank ρ) (hK : BFScattered K)
    [Uncountable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)))] :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) = ℵ₁ :=
  mk_eq_aleph_one_of_countable_preimage
    (rankOnIsoClasses_lt_omega_one h.iso_invariant h.lt_omega_one K)
    fun α _ => h.countable_rankOnIsoClasses_preimage hK α

/-- A scattered set meets countably many isomorphism classes exactly when the isolating rank is
bounded on it by a countable ordinal. -/
theorem countable_isoClasses_iff_bounded (h : IsIsolatingRank ρ) (hK : BFScattered K) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ↔
      ∃ β < ω₁, ∀ c ∈ K, ρ c < β := by
  refine ⟨fun _ => exists_rank_bound_of_countable_isoClasses h.iso_invariant h.lt_omega_one K,
    fun ⟨β, hβ, hb⟩ => ?_⟩
  rw [h.comap_isoSetoid_eq_bfEquivSetoid fun c hc => (hb c hc).le]
  exact hK.countable_quotient hβ

/-- On a scattered set, two isolating ranks are bounded below `ω₁` together. -/
theorem exists_rank_bound_iff (hρ : IsIsolatingRank ρ) (hσ : IsIsolatingRank σ)
    (hK : BFScattered K) :
    (∃ β < ω₁, ∀ c ∈ K, ρ c < β) ↔ ∃ β < ω₁, ∀ c ∈ K, σ c < β :=
  (hρ.countable_isoClasses_iff_bounded hK).symm.trans (hσ.countable_isoClasses_iff_bounded hK)

end IsIsolatingRank

end TauCeti
