/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Stratification

/-!
# Borel isomorphism on classes of bounded rank

On a set of relational configurations on `ℕ`, a countable bound on an isolating rank makes
isomorphism equal to one back-and-forth level. In a countable vocabulary that level is Borel,
so isomorphism has Borel graph on the set. This supplies the relation to which a descriptive
set-theoretic dichotomy can be applied when counting models of bounded rank.

The set need not be measurable or isomorphism invariant: the graph is measurable for the
induced measurable structure on its square. To apply a dichotomy requiring a standard Borel
domain, the caller must separately establish that the set is Borel.

The Scott height supplies the canonical isolating rank. A bound `β` on the internal Scott rank
also suffices, but gives a bound `β + ω` on the Scott height, not necessarily `β` itself.
Countably many isomorphism classes give Borel isomorphism as well, since they bound every
isolating rank.

## Main results

* `TauCeti.IsIsolatingRank.measurableSet_setOf_comap_isoSetoid`: a bounded isolating rank gives
  a Borel isomorphism relation.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_scottHeight_le` and
  `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_internalScottRank_le`:
  the external and internal Scott rank forms.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_countable_isoClasses`:
  countably many isomorphism classes give a Borel isomorphism relation.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016,
  the chapter on the space of countable models.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2,
  Chapter XII, §XII.1.

The isolating-rank and Scott-height arguments use the APIs in
`TauCeti.ModelTheory.Counting.Stratification` and `TauCeti.ModelTheory.Scott.Height`.
-/

public section

universe u v

open FirstOrder Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
  {K : Set (RelationalConfiguration L ℕ)} {β : Ordinal.{0}}

/-- A countable bound on an isolating rank makes isomorphism Borel on `K`, for the induced
measurable structure. No measurability or invariance of `K` is required. -/
theorem IsIsolatingRank.measurableSet_setOf_comap_isoSetoid
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (hβ : β < ω₁) (hK : ∀ c ∈ K, ρ c ≤ β) :
    MeasurableSet {p : K × K | (isoSetoid L ℕ).comap Subtype.val p.1 p.2} := by
  rw [hρ.comap_isoSetoid_eq_bfEquivSetoid hK]
  exact (measurableSet_setOf_bfEquivSetoid hβ).preimage
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd))

namespace RelationalConfiguration

/-- A countable uniform bound on the Scott heights of the decoded structures makes
isomorphism Borel on `K`. -/
theorem measurableSet_setOf_comap_isoSetoid_of_scottHeight_le (hβ : β < ω₁)
    (hK : ∀ c ∈ K, @scottHeight L _ ℕ c.toStructure ≤ β) :
    MeasurableSet {p : K × K | (isoSetoid L ℕ).comap Subtype.val p.1 p.2} :=
  (isIsolatingRank_scottHeight L).measurableSet_setOf_comap_isoSetoid hβ hK

/-- A countable bound on the internal Scott ranks of the decoded structures makes
isomorphism Borel on `K`. The associated bound on Scott height is `β + ω`. -/
theorem measurableSet_setOf_comap_isoSetoid_of_internalScottRank_le (hβ : β < ω₁)
    (hK : ∀ c ∈ K, @internalScottRank L _ ℕ c.toStructure ≤ β) :
    MeasurableSet {p : K × K | (isoSetoid L ℕ).comap Subtype.val p.1 p.2} := by
  apply measurableSet_setOf_comap_isoSetoid_of_scottHeight_le (β := β + ω)
    (Ordinal.isPrincipal_add_omega 1 hβ Ordinal.omega0_lt_omega_one)
  intro c hc
  exact (@scottHeight_le_internalScottRank_add_omega0 L _ ℕ c.toStructure).trans
    (add_le_add (hK c hc) le_rfl)

/-- On a set meeting countably many isomorphism classes, isomorphism has Borel graph for
its induced measurable structure, even if the set itself is not Borel. -/
theorem measurableSet_setOf_comap_isoSetoid_of_countable_isoClasses
    [Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)))] :
    MeasurableSet {p : K × K | (isoSetoid L ℕ).comap Subtype.val p.1 p.2} := by
  obtain ⟨β, hβ, hb⟩ := exists_rank_bound_of_countable_isoClasses
    (isIsolatingRank_scottHeight L).iso_invariant
    (isIsolatingRank_scottHeight L).lt_omega_one K
  exact measurableSet_setOf_comap_isoSetoid_of_scottHeight_le hβ fun c hc => (hb c hc).le

end RelationalConfiguration

end TauCeti
