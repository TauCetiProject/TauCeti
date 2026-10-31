/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.SetTheory.Cardinal.AlephOne

/-!
# Isolating ranks and the stratification of isomorphism classes

An isolating rank assigns a countable ordinal to each relational configuration on `ℕ`,
is invariant under isomorphism, and isolates a configuration's isomorphism class at its rank.
Isolation is one-sided: equivalence at the rank of `c` decides isomorphism with `c`.
Any larger isomorphism-invariant countable rank is again isolating.

For an arbitrary set `K` of configurations, the rank descends to its isomorphism classes.
The classes of rank `α` inject into the back-and-forth classes of `K` at level `α`.
Consequently, if every countable level has at most `ℵ₁` classes, then `K` meets at most
`ℵ₁` isomorphism classes. In particular this holds when all these levels are countable.
No definability or invariance of `K`, and no countability of the language, is required.
Countably many isomorphism classes also give a countable bound on every isolating rank.

## References

The isolating-rank contract is adapted from Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/Descriptive/ScatteredCounting.lean` (checkpoint `518a366`, Apache-2.0).
The stratification bound is adapted from `mk_isoSetoid_subtype_le_aleph_one` in
`InfinitaryLogic/ModelTheory/MorleyCounting.lean` at the same checkpoint, replacing Scott height
with any isolating rank. For Morley's counting argument, see Antonio Montalbán,
*Computable Structure Theory: Beyond the Arithmetic*, Chapter XII.
-/

public section

universe u v

open FirstOrder Cardinal Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]

/-- A countable, isomorphism-invariant rank that isolates each configuration's isomorphism
class at its own back-and-forth level. It need not be the least such level. -/
structure IsIsolatingRank (ρ : RelationalConfiguration L ℕ → Ordinal.{0}) : Prop where
  /-- Isomorphic configurations have equal ranks. -/
  iso_invariant : ∀ ⦃c d⦄, isoSetoid L ℕ c d → ρ c = ρ d
  /-- Every rank is a countable ordinal. -/
  lt_omega_one : ∀ c, ρ c < ω₁
  /-- Back-and-forth equivalence at the rank of the first configuration decides isomorphism. -/
  isolates : ∀ ⦃c d⦄, bfEquivSetoid L ℕ (ρ c) c d → isoSetoid L ℕ c d

variable {ρ σ : RelationalConfiguration L ℕ → Ordinal.{0}}

/-- An isomorphism-invariant rank induced on the isomorphism classes represented in `K`. -/
def rankOnIsoClasses (hinv : ∀ ⦃c d⦄, isoSetoid L ℕ c d → ρ c = ρ d)
    (K : Set (RelationalConfiguration L ℕ)) :
    Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)) → Ordinal.{0} :=
  Quotient.lift (fun c : K => ρ c) (fun _ _ hcd => hinv hcd)

@[simp]
theorem rankOnIsoClasses_mk (hinv : ∀ ⦃c d⦄, isoSetoid L ℕ c d → ρ c = ρ d)
    (K : Set (RelationalConfiguration L ℕ)) (c : K) :
    rankOnIsoClasses hinv K (Quotient.mk _ c) = ρ c := (rfl)

/-- The induced rank still takes only countable values. -/
theorem rankOnIsoClasses_lt_omega_one
    (hinv : ∀ ⦃c d⦄, isoSetoid L ℕ c d → ρ c = ρ d) (hρ : ∀ c, ρ c < ω₁)
    (K : Set (RelationalConfiguration L ℕ))
    (q : Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) :
    rankOnIsoClasses hinv K q < ω₁ := by
  induction q using Quotient.inductionOn with
  | h c => exact hρ c

namespace IsIsolatingRank

/-- Isolation holds at every level at or above the rank of the first configuration. -/
theorem isolates_of_le (h : IsIsolatingRank ρ) {c d : RelationalConfiguration L ℕ}
    {α : Ordinal.{0}} (hc : ρ c ≤ α) (hcd : bfEquivSetoid L ℕ α c d) :
    isoSetoid L ℕ c d :=
  h.isolates (bfEquivSetoid_anti hc hcd)

/-- Raising an isolating rank to an invariant countable rank preserves isolation. -/
theorem of_le (h : IsIsolatingRank ρ) (hle : ρ ≤ σ)
    (hinv : ∀ ⦃c d⦄, isoSetoid L ℕ c d → σ c = σ d)
    (hσ : ∀ c, σ c < ω₁) : IsIsolatingRank σ :=
  ⟨hinv, hσ, fun {c _} hcd => h.isolates_of_le (hle c) hcd⟩

/-- On a set where the rank is bounded by `α`, isomorphism equals equivalence at level `α`.
No definability or invariance of the set is needed. -/
theorem comap_isoSetoid_eq_bfEquivSetoid (h : IsIsolatingRank ρ)
    {K : Set (RelationalConfiguration L ℕ)} {α : Ordinal.{0}}
    (hK : ∀ c ∈ K, ρ c ≤ α) :
    (isoSetoid L ℕ).comap (Subtype.val : K → _) =
      (bfEquivSetoid L ℕ α).comap (Subtype.val : K → _) := by
  ext c d
  exact ⟨fun hcd => isoSetoid_le_bfEquivSetoid α hcd,
    fun hcd => h.isolates_of_le (hK c c.2) hcd⟩

/-- A rank stratum of isomorphism classes injects into the quotient at that level.
This is the step that makes it possible to count classes stratum by stratum. -/
theorem exists_injective_rank_fiber (h : IsIsolatingRank ρ)
    (K : Set (RelationalConfiguration L ℕ)) (α : Ordinal.{0}) :
    ∃ f : (rankOnIsoClasses h.iso_invariant K ⁻¹' {α}) →
      Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _)), Function.Injective f := by
  let f : (rankOnIsoClasses h.iso_invariant K ⁻¹' {α}) →
      Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _)) :=
    fun q => Quotient.mk _ q.1.out
  refine ⟨f, fun q r heq => Subtype.ext ?_⟩
  have hq : ρ q.1.out.val = α := by
    rw [← rankOnIsoClasses_mk h.iso_invariant K q.1.out, Quotient.out_eq]
    exact q.2
  have hqr := Quotient.exact
    (s := (bfEquivSetoid L ℕ α).comap (Subtype.val : K → _)) heq
  have hiso := h.isolates_of_le hq.le hqr
  have he := Quotient.sound (s := (isoSetoid L ℕ).comap (Subtype.val : K → _)) hiso
  simpa only [Quotient.out_eq] using he

/-- If every countable level of `K` has at most `ℵ₁` classes, then `K` meets at most `ℵ₁`
isomorphism classes. The set `K` need not be Borel or isomorphism invariant. -/
theorem mk_isoClasses_le_aleph_one (h : IsIsolatingRank ρ)
    (K : Set (RelationalConfiguration L ℕ))
    (hlevels : ∀ α : Ordinal.{0}, α < ω₁ →
      #(Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _))) ≤ ℵ₁) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ≤ ℵ₁ := by
  have hfib (α : Ordinal.{0}) (hα : α < ω₁) :
      #(rankOnIsoClasses h.iso_invariant K ⁻¹' {α}) ≤ ℵ₁ := by
    obtain ⟨f, hf⟩ := h.exists_injective_rank_fiber K α
    exact (mk_le_of_injective hf).trans (hlevels α hα)
  have hb := mk_le_aleph_one_mul_of_mk_preimage_le
    (rankOnIsoClasses_lt_omega_one h.iso_invariant h.lt_omega_one K) hfib
  rwa [mul_eq_self (aleph0_le_aleph 1)] at hb

/-- Countably many classes at each countable back-and-forth level give at most `ℵ₁`
isomorphism classes, for any isolating rank. -/
theorem mk_isoClasses_le_aleph_one_of_countable_levels (h : IsIsolatingRank ρ)
    (K : Set (RelationalConfiguration L ℕ))
    (hlevels : ∀ α : Ordinal.{0}, α < ω₁ →
      Countable (Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _)))) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ≤ ℵ₁ :=
  h.mk_isoClasses_le_aleph_one K fun α hα =>
    (mk_le_aleph0_iff.mpr (hlevels α hα)).trans (aleph0_le_aleph 1)

end IsIsolatingRank

/-- Countably many isomorphism classes bound every invariant countable rank strictly below
one countable ordinal. Neither isolation nor smallness of the levels is required. -/
theorem exists_rank_bound_of_countable_isoClasses
    (hinv : ∀ ⦃c d⦄, isoSetoid L ℕ c d → ρ c = ρ d) (hρ : ∀ c, ρ c < ω₁)
    (K : Set (RelationalConfiguration L ℕ))
    [Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)))] :
    ∃ β < ω₁, ∀ c ∈ K, ρ c < β := by
  obtain ⟨β, hβ, hb⟩ := (Set.to_countable (Set.univ :
    Set (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))))).exists_lt_omega_one_forall_lt
      (r := rankOnIsoClasses hinv K) (fun q _ => rankOnIsoClasses_lt_omega_one hinv hρ K q)
  refine ⟨β, hβ, fun c hc => ?_⟩
  simpa only [rankOnIsoClasses_mk] using hb (Quotient.mk _ ⟨c, hc⟩) (mem_univ _)

end TauCeti
