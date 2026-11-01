/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.ExtensionSpectrum
public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.ModelTheory.Scott.Height
public import TauCeti.SetTheory.Cardinal.AlephOne

/-!
# Isolating ranks and the stratification of isomorphism classes

An isolating rank assigns a countable ordinal to each relational configuration on `ℕ`,
is invariant under isomorphism, and isolates a configuration's isomorphism class at its rank.
Isolation is one-sided: equivalence at the rank of `c` decides isomorphism with `c`.
Any larger isomorphism-invariant countable rank is again isolating, so the contract does not
determine the rank: on a set meeting uncountably many isomorphism classes, every isolating rank
lies below one that is unbounded below `ω₁` there.

The Scott height of the decoded structure is an isolating rank. Isolating ranks therefore exist
for every relational language, and the stratification bound below needs no rank as input.

For an arbitrary set `K` of configurations, the rank descends to its isomorphism classes.
The classes of rank `α` inject into the back-and-forth classes of `K` at level `α`.
Consequently, if every countable level has at most `ℵ₁` classes, then `K` meets at most
`ℵ₁` isomorphism classes. In particular this holds when all these levels are countable.
No definability or invariance of `K`, and no countability of the language, is required.
Countably many isomorphism classes also give a countable bound on every isolating rank.
Finally, if the structures decoded from `K` are small level by level (`TauCeti.BFSmall`), then
every countable level of `K` has countably many classes, so `K` meets at most `ℵ₁` isomorphism
classes.

## Main results

* `TauCeti.IsIsolatingRank.mk_isoClasses_le_aleph_one`: the stratification bound for a given
  isolating rank.
* `TauCeti.IsIsolatingRank.exists_unbounded_of_not_countable`: an isolating rank can always be
  raised to one that is unbounded on a set meeting uncountably many classes.
* `TauCeti.isIsolatingRank_scottHeight`: the Scott height is an isolating rank.
* `TauCeti.mk_isoClasses_le_aleph_one_of_countable_levels`: countable levels give at most `ℵ₁`
  isomorphism classes, with no rank in the statement.
* `TauCeti.BFSmall.mk_isoClasses_le_aleph_one`: level-by-level smallness of the decoded
  structures gives at most `ℵ₁` isomorphism classes.

## References

The isolating-rank contract is adapted from Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/Descriptive/ScatteredCounting.lean` (checkpoint `518a366`, Apache-2.0).
The stratification bound is adapted from `mk_isoSetoid_subtype_le_aleph_one` in
`InfinitaryLogic/ModelTheory/MorleyCounting.lean` at the same checkpoint, replacing Scott height
with any isolating rank. The raising of an isolating rank to an unbounded one follows
`IsIsolatingRank.exists_unbounded_of_not_countable` in `ScatteredCounting.lean`, and the bound
from level-by-level smallness follows `mk_representedIn_le_aleph_one_of_bfSmall` in
`InfinitaryLogic/ModelTheory/BFSmallCounting.lean`, both at the same checkpoint; there the rank
instance is a stabilization ordinal rather than the Scott height. For Morley's counting argument,
see Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Chapter XII.
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

/-- **The contract does not bound the rank.** On a set `K` meeting uncountably many isomorphism
classes, every isolating rank lies below an isolating rank that takes values at or above every
countable ordinal on `K`. -/
theorem exists_unbounded_of_not_countable (h : IsIsolatingRank ρ)
    {K : Set (RelationalConfiguration L ℕ)}
    (hK : ¬ Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)))) :
    ∃ σ, IsIsolatingRank σ ∧ ρ ≤ σ ∧ ∀ β < ω₁, ∃ c ∈ K, β ≤ σ c := by
  have := not_countable_iff.1 hK
  obtain ⟨f, hf⟩ := exists_surjective_Iio_omega_one.{v, 0}
    (X := Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)))
  -- The classes met by `K` embed among all isomorphism classes; read `f` through this embedding
  -- to get an isomorphism-invariant rank on all configurations.
  let g : Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)) → Quotient (isoSetoid L ℕ) :=
    Quotient.map' Subtype.val fun _ _ => id
  have hg : Function.Injective g := fun q r => Quotient.inductionOn₂ q r fun _ _ hcd =>
    Quotient.sound (Quotient.exact (s := isoSetoid L ℕ) hcd)
  let τ : RelationalConfiguration L ℕ → Ordinal.{0} :=
    fun c => f (Function.invFun g (Quotient.mk _ c))
  have hτ (c : K) : τ c = f (Quotient.mk _ c) :=
    congrArg (fun q => (f q : Ordinal.{0})) (Function.leftInverse_invFun hg (Quotient.mk _ c))
  refine ⟨ρ ⊔ τ, h.of_le le_sup_left (fun c d hcd => ?_)
    (fun c => max_lt (h.lt_omega_one c) (f _).2), le_sup_left, fun β hβ => ?_⟩
  · simp only [Pi.sup_apply, τ, h.iso_invariant hcd, Quotient.sound hcd]
  · obtain ⟨q, hq⟩ := hf ⟨β, hβ⟩
    induction q using Quotient.inductionOn with
    | h c =>
      refine ⟨c, c.2, le_sup_of_le_right ?_⟩
      rw [hτ, hq]

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

/-! ### The Scott height as an isolating rank -/

variable (L) in
/-- **The Scott height is an isolating rank.** The Scott height of the structure decoded from a
configuration on `ℕ` is invariant under isomorphism and countable, and back-and-forth
equivalence of the empty tuples at the Scott height of `c` decides isomorphism with `c`. -/
theorem isIsolatingRank_scottHeight :
    IsIsolatingRank fun c : RelationalConfiguration L ℕ => @scottHeight L _ ℕ c.toStructure where
  iso_invariant c d hcd := by
    obtain ⟨e⟩ := isoSetoid_apply.1 hcd
    exact @Language.Equiv.scottHeight_eq L _ ℕ c.toStructure ℕ d.toStructure e
  lt_omega_one c := @scottHeight_lt_omega_one L _ ℕ c.toStructure _
  isolates c d hcd := isoSetoid_apply.2
    (@nonempty_equiv_of_bfEquiv_of_scottHeight_le L _ ℕ c.toStructure _ ℕ d.toStructure _ _ le_rfl
      (bfEquivSetoid_apply.1 hcd))

variable (L) in
/-- Every relational language has an isolating rank on its configurations on `ℕ`. -/
theorem exists_isIsolatingRank :
    ∃ ρ : RelationalConfiguration L ℕ → Ordinal.{0}, IsIsolatingRank ρ :=
  ⟨_, isIsolatingRank_scottHeight L⟩

/-- **The stratification bound.** If every countable back-and-forth level of a set `K` of
configurations on `ℕ` has countably many classes, then `K` meets at most `ℵ₁` isomorphism
classes. The set `K` need not be Borel or isomorphism invariant, and the language need not be
countable. -/
theorem mk_isoClasses_le_aleph_one_of_countable_levels (K : Set (RelationalConfiguration L ℕ))
    (hlevels : ∀ α : Ordinal.{0}, α < ω₁ →
      Countable (Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _)))) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ≤ ℵ₁ :=
  (isIsolatingRank_scottHeight L).mk_isoClasses_le_aleph_one_of_countable_levels K hlevels

/-- **Level-by-level smallness bounds the isomorphism classes.** If the structures decoded from a
set `K` of configurations on `ℕ` are small level by level (`TauCeti.BFSmall`), then `K` meets at
most `ℵ₁` isomorphism classes. -/
theorem BFSmall.mk_isoClasses_le_aleph_one {K : Set (RelationalConfiguration L ℕ)}
    (h : @BFSmall L _ K (fun _ => ℕ) fun c => c.1.toStructure) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ≤ ℵ₁ := by
  refine mk_isoClasses_le_aleph_one_of_countable_levels K fun α hα => ?_
  have := @BFSmall.countable_quotient L _ K (fun _ => ℕ) (fun c => c.1.toStructure) h α hα 0
  -- At arity `0` both relations compare the empty tuples of the decoded structures, so the
  -- level-`α` relation on `K` is the pullback of the depth-`α` relation of the family.
  have hcomap : (bfEquivSetoid L ℕ α).comap (Subtype.val : K → _) =
      (@bfTupleSetoid L _ K (fun _ => ℕ) (fun c => c.1.toStructure) α 0).comap
        fun c => ⟨c, Fin.elim0⟩ :=
    Setoid.ext fun c d => by
      simp only [Setoid.comap_rel]
      exact bfEquivSetoid_apply.trans (@bfTupleSetoid_apply L _ K (fun _ => ℕ)
        (fun c => c.1.toStructure) α 0 ⟨c, Fin.elim0⟩ ⟨d, Fin.elim0⟩).symm
  rw [hcomap]
  exact Countable.of_equiv _ (Setoid.comapQuotientEquiv _ _).symm

end TauCeti
