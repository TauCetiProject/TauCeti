/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.BackAndForth.AllLevels

/-!
# Back-and-forth levels of relational configurations

For a relational language `L` and an ordinal `α`, two configurations on a carrier `V` are
`α`-equivalent when the empty tuples of their decoded structures are back-and-forth equivalent at
depth `α`. This is the setoid `TauCeti.RelationalConfiguration.bfEquivSetoid L V α`. The levels
decrease as `α` grows, each one is coarser than isomorphism, and on a countable carrier their
intersection over all ordinals is isomorphism, by Scott's back-and-forth argument.

On a countable carrier, in a vocabulary with countably many relation symbols of each arity, every
countable level is Borel: back-and-forth equivalence of any two tuples at a depth `α < ω₁` is a
Borel condition on the pair of configurations. Level zero is a countable conjunction of atomic
tests, a successor quantifies over the countably many one-point extensions, and a limit below
`ω₁` is a countable conjunction of earlier levels. These levels stratify isomorphism into Borel
equivalence relations, which is what descriptive dichotomies such as Silver's theorem consume when
counting the countable models of an infinitary sentence.

## Main definitions

* `TauCeti.RelationalConfiguration.bfEquivSetoid L V α` — back-and-forth equivalence at depth `α`
  of the decoded structures, as a setoid on the configurations on `V`.

## Main results

* `TauCeti.RelationalConfiguration.bfEquivSetoid_anti` — the levels decrease with `α`;
* `TauCeti.RelationalConfiguration.isoSetoid_le_bfEquivSetoid` — isomorphic configurations are
  equivalent at every level;
* `TauCeti.RelationalConfiguration.isoSetoid_iff_forall_bfEquivSetoid` — on a countable carrier,
  isomorphism is equivalence at every level;
* `TauCeti.RelationalConfiguration.measurableSet_setOf_bfEquiv` and
  `TauCeti.RelationalConfiguration.measurableSet_setOf_bfEquivSetoid` — below `ω₁`, back-and-forth
  equivalence of tuples, and hence each level, has Borel graph.

## References

* David Marker, *Lectures on Infinitary Model Theory*, the chapter on the space of countable
  models.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Chapter XII.
* The back-and-forth setoid on codes also appears in Cameron Freer's
  `cameronfreer/infinitary-logic`, `InfinitaryLogic/ModelTheory/MorleyCounting.lean`.
-/

public section

universe u v w o

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- Below `ω₁`, on a countable carrier and in a vocabulary with countably many relation symbols of
each arity, back-and-forth equivalence at depth `α` of two fixed tuples is a Borel condition on the
pair of decoded configurations. -/
theorem measurableSet_setOf_bfEquiv [Countable V] [∀ n, Countable (L.Relations n)]
    {α : Ordinal.{o}} (hα : α < Ordinal.omega 1) {n : ℕ} (a b : Fin n → V) :
    MeasurableSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      @BFEquiv L _ V V p.1.toStructure p.2.toStructure α n a b} := by
  rw [measurableSet_setOfPred]
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    -- Level zero: agreement on the countably many atomic tests.
    simp only [BFEquiv.zero, sameAtomicType_def]
    refine Measurable.forall fun i => ?_
    cases i with
    | eq i j =>
      simp only [AtomicIdx.holds_eq]
      exact measurable_const
    | rel r f =>
      simp only [AtomicIdx.holds_rel, toStructure_relMap]
      exact (((measurable_eval _).comp measurable_fst).eq_const true).iff
        (((measurable_eval _).comp measurable_snd).eq_const true)
  | add_one α ih =>
    -- Successor: the previous level and both extension clauses, over countably many points.
    have hα' : α < Ordinal.omega 1 := (Order.lt_add_one_iff.mpr le_rfl).trans hα
    simp only [BFEquiv.add_one]
    exact (ih hα' a b).and ((Measurable.forall fun x => Measurable.exists fun y =>
      ih hα' _ _).and (Measurable.forall fun y => Measurable.exists fun x => ih hα' _ _))
  | limit α hlim ih =>
    -- Limit below `ω₁`: a conjunction over the countably many smaller levels.
    have : Countable (Set.Iio α) := (Cardinal.countable_Iio_of_lt_omega_one hα).to_subtype
    simp only [BFEquiv.limit hlim]
    have h := Measurable.forall (ι := Set.Iio α) fun β => ih β.1 β.2 (β.2.trans hα) a b
    simpa only [Subtype.forall, Set.mem_Iio] using h

variable (L V) in
/-- Back-and-forth equivalence at depth `α`, as a setoid on the configurations on `V`: two
configurations are related when the empty tuples of their decoded structures are back-and-forth
equivalent at depth `α`. -/
def bfEquivSetoid (α : Ordinal.{o}) : Setoid (RelationalConfiguration L V) where
  r c d := @BFEquiv L _ V V c.toStructure d.toStructure α 0 Fin.elim0 Fin.elim0
  iseqv :=
    { refl c := @BFEquiv.refl L _ V c.toStructure 0 α Fin.elim0
      symm {c d} h := @BFEquiv.symm L _ V V c.toStructure d.toStructure 0 Fin.elim0 Fin.elim0 α h
      trans {c d e} h h' := @BFEquiv.trans L _ V V V c.toStructure d.toStructure e.toStructure
        0 Fin.elim0 Fin.elim0 Fin.elim0 α h h' }

/-- Two configurations are `α`-equivalent exactly when the empty tuples of their decoded
structures are back-and-forth equivalent at depth `α`. -/
theorem bfEquivSetoid_apply {α : Ordinal.{o}} {c d : RelationalConfiguration L V} :
    bfEquivSetoid L V α c d ↔
      @BFEquiv L _ V V c.toStructure d.toStructure α 0 Fin.elim0 Fin.elim0 :=
  Iff.rfl

/-- The back-and-forth levels decrease: equivalence at a level implies equivalence at every lower
level. -/
theorem bfEquivSetoid_anti : Antitone (bfEquivSetoid L V : Ordinal.{o} → _) :=
  fun α β hαβ c d h =>
    @BFEquiv.mono L _ V V c.toStructure d.toStructure 0 Fin.elim0 Fin.elim0 α β h hαβ

/-- Isomorphic configurations are equivalent at every back-and-forth level. -/
theorem isoSetoid_le_bfEquivSetoid (α : Ordinal.{o}) : isoSetoid L V ≤ bfEquivSetoid L V α :=
  fun c d hcd => by
    obtain ⟨e⟩ := isoSetoid_apply.mp hcd
    have h := @Language.Equiv.bfEquiv L _ V V c.toStructure d.toStructure e α 0 Fin.elim0
    rwa [Subsingleton.elim (e ∘ Fin.elim0) Fin.elim0] at h

/-- On a countable carrier, two configurations are isomorphic exactly when they are equivalent at
every back-and-forth level. This is Scott's back-and-forth argument for the decoded
structures. -/
theorem isoSetoid_iff_forall_bfEquivSetoid [Countable V] {c d : RelationalConfiguration L V} :
    isoSetoid L V c d ↔ ∀ α : Ordinal.{w}, bfEquivSetoid L V α c d := by
  rw [isoSetoid_apply]
  exact (@countable_potentialIso_iff_iso L V V c.toStructure d.toStructure _ _).symm.trans
    (@potentialIso_iff_bfEquiv_all L _ V V c.toStructure d.toStructure)

/-- Below `ω₁`, on a countable carrier and in a vocabulary with countably many relation symbols of
each arity, each back-and-forth level has Borel graph. -/
theorem measurableSet_setOf_bfEquivSetoid [Countable V] [∀ n, Countable (L.Relations n)]
    {α : Ordinal.{o}} (hα : α < Ordinal.omega 1) :
    MeasurableSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      bfEquivSetoid L V α p.1 p.2} :=
  measurableSet_setOf_bfEquiv hα Fin.elim0 Fin.elim0

end TauCeti.RelationalConfiguration
