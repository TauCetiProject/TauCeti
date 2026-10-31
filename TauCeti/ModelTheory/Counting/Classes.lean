/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.SetTheory.Descriptive.Antichain

/-!
# Classes of countable models

Let `L` be a relational language and `φ` an infinitary sentence. A countable structure is
isomorphic to one on `ℕ` or on some `Fin n`, so the isomorphism classes of the countable models of
`φ` are the classes of its model classes on these carriers, under isomorphism of the decoded
structures:

* `TauCeti.RelationalConfiguration.isoSetoidOn V φ`: isomorphism restricted to the configurations
  on `V` decoding to models of `φ`;
* `TauCeti.CountableModelClasses φ`: the disjoint union of the quotient on `ℕ` (the countably
  infinite models) and the quotients on each `Fin n` (the models with `n` elements);
* `TauCeti.countableModelCount φ`: its cardinality, the number of countable models of `φ` up to
  isomorphism.

Countable here means at most countable: the finite models, including the empty structure, are
counted. Leaving them out would be wrong, not just incomplete: with countably many unary
predicates, the sentence saying that there is exactly one element has no model on `ℕ` and
continuum many pairwise non-isomorphic models on `Fin 1`.

Models in arbitrary universes enter through `TauCeti.classOf`, which sends a countable model to
the class of its transport to `Fin n` if it has `n` elements and to `ℕ` otherwise. Two countable
models, in any two universes, have the same class exactly when they are isomorphic
(`TauCeti.classOf_eq_classOf_iff`), and every class is the class of a countable model in every
universe (`TauCeti.classOf_surjective`). So `CountableModelClasses φ` is the set of isomorphism
classes of countable models of `φ`, presented as a type in the universe of the relation symbols,
and no statement has to count a proper class of structures.

In a language with countably many relation symbols there are at most continuum many countable
models. A perfect set of pairwise non-isomorphic models, at the tier `ℕ` or at some finite tier,
gives exactly continuum many (`TauCeti.HasPerfectlyManyCountableModels.countableModelCount_eq`).
These are the two alternatives between which Morley's theorem and Vaught's conjecture place the
count.

## Main results

* `TauCeti.countableModelCount_eq_add_sum`: the count is the count on `ℕ` plus the sum of the
  counts on the finite carriers.
* `TauCeti.countableModelCount_le_add_aleph0_mul` and `TauCeti.countableModelCount_le_aleph0_iff`:
  bounds tier by tier; there are countably many countable models exactly when every tier has
  countably many classes.
* `TauCeti.countableModelCount_le_of_subset`: a sentence whose countable models are models of
  another has at most as many countable models.
* `TauCeti.classOf_eq_classOf_iff` and `TauCeti.classOf_surjective`: `classOf` is a bijection
  between isomorphism classes of countable models, in any universe, and `CountableModelClasses φ`.
* `TauCeti.exists_classOf_eq_inl_iff` and `TauCeti.exists_classOf_eq_inr_iff`: the infinite
  models land on the tier `ℕ`, the models with `n` elements on the tier `Fin n`.
* `TauCeti.countableModelCount_le_continuum`: at most continuum many countable models.
* `TauCeti.HasPerfectlyManyCountableModels.countableModelCount_eq`: a perfect set of pairwise
  non-isomorphic models gives continuum many.

## References

* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18.
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the chapter
  on the space of countable models.

The tiered presentation of the classes follows `AllCodedIsoClasses` and `isoSetoidOn` in Cameron
Freer's `cameronfreer/infinitary-logic` (`InfinitaryLogic/Descriptive/FiniteCarrier.lean`,
checkpoint `518a366`, Apache-2.0), whose bridges are for models in `Type`; here they work in every
universe.
-/

public section

universe u v w w' uι uι'

open FirstOrder FirstOrder.Language Cardinal Set

namespace TauCeti

namespace RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι}

variable (V : Type w) in
/-- Isomorphism of decoded structures, restricted to the configurations on `V` that decode to
models of `φ`. Its classes are the isomorphism classes of the models of `φ` with carrier `V`.
It is an abbreviation, so results stated for the restriction of `isoSetoid L V` to an arbitrary
set of configurations apply to it. -/
abbrev isoSetoidOn (φ : L.SentenceInf ι) : Setoid (modelsOf (V := V) φ) :=
  (isoSetoid L V).comap Subtype.val

/-- Two models of `φ` are related exactly when their decoded structures are isomorphic. -/
@[simp]
theorem isoSetoidOn_apply {V : Type w} {φ : L.SentenceInf ι} {c d : modelsOf (V := V) φ} :
    isoSetoidOn V φ c d ↔ isoSetoid L V c d :=
  Iff.rfl

/-- If every model of `φ` on `V` is a model of `ψ`, the models of `φ` on `V` have at most as many
isomorphism classes as those of `ψ`: the inclusion of model classes is injective on classes. -/
theorem mk_quotient_isoSetoidOn_le_of_subset {ι' : Type uι'} {V : Type w} {φ : L.SentenceInf ι}
    {ψ : L.SentenceInf ι'} (h : modelsOf (V := V) φ ⊆ modelsOf ψ) :
    #(Quotient (isoSetoidOn V φ)) ≤ #(Quotient (isoSetoidOn V ψ)) := by
  refine mk_le_of_injective (f := Quotient.map (inclusion h) fun _ _ hcd => hcd) ?_
  intro p q
  induction p, q using Quotient.inductionOn₂ with
  | h c d =>
    intro hcd
    exact Quotient.sound (Quotient.exact (s := isoSetoidOn V ψ) hcd)

/-- On a countable carrier, in a language with countably many relation symbols of each arity,
the models of a sentence have at most continuum many isomorphism classes. -/
theorem mk_quotient_isoSetoidOn_le_continuum [∀ n, Countable (L.Relations n)] (V : Type w)
    [Countable V] (φ : L.SentenceInf ι) : #(Quotient (isoSetoidOn V φ)) ≤ 𝔠 :=
  mk_quotient_le.trans (mk_subtype_le _ |>.trans (mk_le_continuum L V))

end RelationalConfiguration

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι} {ι' : Type uι'}

/-- The isomorphism classes of the countable models of `φ`, tier by tier: the classes of the
models with carrier `ℕ`, and, for each `n`, the classes of the models with carrier `Fin n`. Every
countable model of `φ`, in any universe, has exactly one class here (`classOf_eq_classOf_iff`,
`classOf_surjective`). -/
abbrev CountableModelClasses (φ : L.SentenceInf ι) : Type v :=
  Quotient (isoSetoidOn ℕ φ) ⊕ Σ n : ℕ, Quotient (isoSetoidOn (Fin n) φ)

/-- The number of countable models of `φ` up to isomorphism, finite models included. -/
noncomputable def countableModelCount (φ : L.SentenceInf ι) : Cardinal.{v} :=
  #(CountableModelClasses φ)

/-- The number of countable models is the number of models on `ℕ` up to isomorphism plus, summed
over `n`, the number of models on `Fin n` up to isomorphism. -/
theorem countableModelCount_eq_add_sum (φ : L.SentenceInf ι) :
    countableModelCount φ =
      #(Quotient (isoSetoidOn ℕ φ)) + sum fun n => #(Quotient (isoSetoidOn (Fin n) φ)) := by
  simp [countableModelCount, CountableModelClasses, mk_sigma]

/-- The models on `ℕ` contribute at most the number of countable models. -/
theorem mk_quotient_isoSetoidOn_nat_le_countableModelCount (φ : L.SentenceInf ι) :
    #(Quotient (isoSetoidOn ℕ φ)) ≤ countableModelCount φ :=
  mk_le_of_injective Sum.inl_injective

/-- The models on `Fin n` contribute at most the number of countable models. -/
theorem mk_quotient_isoSetoidOn_fin_le_countableModelCount (φ : L.SentenceInf ι) (n : ℕ) :
    #(Quotient (isoSetoidOn (Fin n) φ)) ≤ countableModelCount φ :=
  mk_le_of_injective (f := fun q => .inr ⟨n, q⟩) (Sum.inr_injective.comp sigma_mk_injective)

/-- If the models on `ℕ` have at most `a` isomorphism classes and those on each `Fin n` at most
`b`, there are at most `a + ℵ₀ * b` countable models. -/
theorem countableModelCount_le_add_aleph0_mul {φ : L.SentenceInf ι} {a b : Cardinal.{v}}
    (ha : #(Quotient (isoSetoidOn ℕ φ)) ≤ a) (hb : ∀ n, #(Quotient (isoSetoidOn (Fin n) φ)) ≤ b) :
    countableModelCount φ ≤ a + ℵ₀ * b := by
  rw [countableModelCount_eq_add_sum]
  refine add_le_add ha ((sum_le_sum _ _ hb).trans_eq ?_)
  simp

/-- There are countably many countable models of `φ` exactly when the models on `ℕ`, and those on
each `Fin n`, have countably many isomorphism classes. -/
theorem countableModelCount_le_aleph0_iff {φ : L.SentenceInf ι} :
    countableModelCount φ ≤ ℵ₀ ↔
      Countable (Quotient (isoSetoidOn ℕ φ)) ∧
        ∀ n, Countable (Quotient (isoSetoidOn (Fin n) φ)) := by
  simp only [← mk_le_aleph0_iff]
  refine ⟨fun h => ⟨(mk_quotient_isoSetoidOn_nat_le_countableModelCount φ).trans h,
    fun n => (mk_quotient_isoSetoidOn_fin_le_countableModelCount φ n).trans h⟩,
    fun ⟨hℕ, hfin⟩ => ?_⟩
  exact (countableModelCount_le_add_aleph0_mul hℕ hfin).trans_eq (by simp)

/-- If every countable model of `φ`, on `ℕ` and on each `Fin n`, is a model of `ψ`, then `φ` has at
most as many countable models as `ψ`. -/
theorem countableModelCount_le_of_subset {φ : L.SentenceInf ι} {ψ : L.SentenceInf ι'}
    (hℕ : modelsOf (V := ℕ) φ ⊆ modelsOf ψ) (hfin : ∀ n, modelsOf (V := Fin n) φ ⊆ modelsOf ψ) :
    countableModelCount φ ≤ countableModelCount ψ := by
  rw [countableModelCount_eq_add_sum, countableModelCount_eq_add_sum]
  exact add_le_add (mk_quotient_isoSetoidOn_le_of_subset hℕ)
    (sum_le_sum _ _ fun n => mk_quotient_isoSetoidOn_le_of_subset (hfin n))

/-- In a language with countably many relation symbols of each arity, there are at most continuum
many countable models. -/
theorem countableModelCount_le_continuum [∀ n, Countable (L.Relations n)] (φ : L.SentenceInf ι) :
    countableModelCount φ ≤ 𝔠 :=
  (countableModelCount_le_add_aleph0_mul (mk_quotient_isoSetoidOn_le_continuum ℕ φ)
    fun n => mk_quotient_isoSetoidOn_le_continuum (Fin n) φ).trans_eq
      (by rw [aleph0_mul_continuum, continuum_add_self])

/-! ### Countable models in arbitrary universes -/

section ClassOf

variable {φ : L.SentenceInf ι} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

variable (φ) in
/-- The class of a countable model of `φ`, in any universe: the class of its transport to `Fin n`
along a bijection if it has `n` elements, and to `ℕ` otherwise. It does not depend on the
bijection (`classOf_eq_inl`, `classOf_eq_inr`). -/
noncomputable def classOf [Countable M] (hM : φ.Realize M) : CountableModelClasses φ := by
  classical
  exact if h : Finite M then
    .inr ⟨Nat.card M,
      ⟦⟨(Finite.equivFin M).encodeVia, (Finite.equivFin M).encodeVia_mem_modelsOf_iff.2 hM⟩⟧⟩
  else
    have : Infinite M := not_finite_iff_infinite.1 h
    .inl ⟦⟨(nonempty_equiv_of_countable.some : M ≃ ℕ).encodeVia,
      Equiv.encodeVia_mem_modelsOf_iff _ |>.2 hM⟩⟧

/-- The class of an infinite countable model is that of its transport to `ℕ` along any
bijection. -/
theorem classOf_eq_inl [Countable M] [Infinite M] (hM : φ.Realize M) (e : M ≃ ℕ) :
    classOf φ hM = .inl ⟦⟨e.encodeVia, e.encodeVia_mem_modelsOf_iff.2 hM⟩⟧ := by
  unfold classOf
  split_ifs with h
  · exact (not_finite M).elim
  exact congrArg Sum.inl <| Quotient.sound <|
    (Equiv.isoSetoid_encodeVia_iff _ e).2 ⟨Language.Equiv.refl L M⟩

/-- The class of a model with `n` elements is that of its transport to `Fin n` along any
bijection. -/
theorem classOf_eq_inr [Countable M] {n : ℕ} (hM : φ.Realize M) (e : M ≃ Fin n) :
    classOf φ hM = .inr ⟨n, ⟦⟨e.encodeVia, e.encodeVia_mem_modelsOf_iff.2 hM⟩⟧⟩ := by
  have : Finite M := .of_equiv _ e.symm
  obtain rfl : Nat.card M = n := (Nat.card_congr e).trans (Nat.card_fin n)
  unfold classOf
  split_ifs
  exact congrArg Sum.inr <| congrArg (Sigma.mk _) <| Quotient.sound <|
    (Equiv.isoSetoid_encodeVia_iff _ e).2 ⟨Language.Equiv.refl L M⟩

/-- The class of the structure decoded from a model of `φ` on `ℕ` is the class of that model. -/
theorem classOf_toStructure_nat (c : modelsOf (V := ℕ) φ) :
    letI := c.1.toStructure
    classOf φ (mem_modelsOf.1 c.2) = .inl ⟦c⟧ := by
  let := c.1.toStructure
  rw [classOf_eq_inl _ (Equiv.refl ℕ)]
  congr
  simp

/-- The class of the structure decoded from a model of `φ` on `Fin n` is the class of that
model. -/
theorem classOf_toStructure_fin {n : ℕ} (c : modelsOf (V := Fin n) φ) :
    letI := c.1.toStructure
    classOf φ (mem_modelsOf.1 c.2) = .inr ⟨n, ⟦c⟧⟩ := by
  let := c.1.toStructure
  rw [classOf_eq_inr _ (Equiv.refl (Fin n))]
  congr
  simp

/-- Isomorphic countable models, in any two universes, have the same class. -/
theorem classOf_congr [Countable M] [Countable N] (g : M ≃[L] N) (hM : φ.Realize M)
    (hN : φ.Realize N) : classOf φ hM = classOf φ hN := by
  rcases finite_or_infinite M with hfin | hinf
  · let e := Finite.equivFin M
    rw [classOf_eq_inr hM e, classOf_eq_inr hN (g.symm.toEquiv.trans e)]
    exact congrArg Sum.inr <| congrArg (Sigma.mk _) <| Quotient.sound <|
      (Equiv.isoSetoid_encodeVia_iff _ _).2 ⟨g⟩
  · have : Infinite N := .of_injective (⇑g) g.injective
    let e : M ≃ ℕ := nonempty_equiv_of_countable.some
    rw [classOf_eq_inl hM e, classOf_eq_inl hN (g.symm.toEquiv.trans e)]
    exact congrArg Sum.inl <| Quotient.sound <| (Equiv.isoSetoid_encodeVia_iff _ _).2 ⟨g⟩

/-- The class of a countable model lies on the tier `ℕ` exactly when the model is infinite. -/
theorem exists_classOf_eq_inl_iff [Countable M] (hM : φ.Realize M) :
    (∃ q, classOf φ hM = .inl q) ↔ Infinite M := by
  rcases finite_or_infinite M with h | h
  · simp [classOf_eq_inr hM (Finite.equivFin M), not_infinite_iff_finite.2 h]
  · simp [classOf_eq_inl hM nonempty_equiv_of_countable.some, h]

/-- The class of a countable model lies on the tier `Fin n` exactly when the model has `n`
elements. -/
theorem exists_classOf_eq_inr_iff [Countable M] (hM : φ.Realize M) (n : ℕ) :
    (∃ q, classOf φ hM = .inr ⟨n, q⟩) ↔ Nonempty (M ≃ Fin n) := by
  refine ⟨fun ⟨q, hq⟩ => ?_, fun ⟨e⟩ => ⟨_, classOf_eq_inr hM e⟩⟩
  rcases finite_or_infinite M with h | h
  · rw [classOf_eq_inr hM (Finite.equivFin M), Sum.inr.injEq, Sigma.mk.inj_iff] at hq
    exact ⟨(Finite.equivFin M).trans (finCongr hq.1)⟩
  · rw [classOf_eq_inl hM nonempty_equiv_of_countable.some] at hq
    exact absurd hq Sum.inl_ne_inr

/-- Two countable models of `φ`, in any two universes, have the same class exactly when they are
isomorphic. -/
theorem classOf_eq_classOf_iff [Countable M] [Countable N] (hM : φ.Realize M) (hN : φ.Realize N) :
    classOf φ hM = classOf φ hN ↔ Nonempty (M ≃[L] N) := by
  refine ⟨fun h => ?_, fun ⟨g⟩ => classOf_congr g hM hN⟩
  -- The tier of the common class gives bijections of `M` and `N` with one carrier.
  rcases finite_or_infinite M with hM' | hM'
  · let e := Finite.equivFin M
    obtain ⟨f⟩ := (exists_classOf_eq_inr_iff hN _).1 ⟨_, h ▸ classOf_eq_inr hM e⟩
    rw [classOf_eq_inr hM e, classOf_eq_inr hN f, Sum.inr.injEq, Sigma.mk.inj_iff] at h
    exact (Equiv.isoSetoid_encodeVia_iff e f).1
      (Quotient.exact (s := isoSetoidOn _ φ) (eq_of_heq h.2))
  · let e : M ≃ ℕ := nonempty_equiv_of_countable.some
    have := (exists_classOf_eq_inl_iff hN).1 ⟨_, h ▸ classOf_eq_inl hM e⟩
    let f : N ≃ ℕ := nonempty_equiv_of_countable.some
    rw [classOf_eq_inl hM e, classOf_eq_inl hN f, Sum.inl.injEq] at h
    exact (Equiv.isoSetoid_encodeVia_iff e f).1 (Quotient.exact (s := isoSetoidOn ℕ φ) h)

/-- Every class of countable models of `φ` is the class of a countable model in every universe. -/
theorem classOf_surjective (q : CountableModelClasses φ) :
    ∃ (M : Type w) (_ : L.Structure M) (_ : Countable M) (hM : φ.Realize M), classOf φ hM = q := by
  -- Transport the decoded structure `V` of a representative to `ULift V`, in universe `w`.
  have key {V : Type} [Countable V] (c : modelsOf (V := V) φ) :
      ∃ (M : Type w) (_ : L.Structure M) (_ : Countable M) (hM : φ.Realize M),
        letI := c.1.toStructure
        classOf φ hM = classOf φ (mem_modelsOf.1 c.2) := by
    let := c.1.toStructure
    let e : V ≃ ULift.{w} V := Equiv.ulift.symm
    let := e.inducedStructure (L := L)
    have hM : φ.Realize (ULift.{w} V) :=
      (StrongHomClass.realize_sentenceInf e.inducedStructureEquiv φ).1 (mem_modelsOf.1 c.2)
    exact ⟨ULift.{w} V, _, inferInstance, hM, classOf_congr e.inducedStructureEquiv.symm hM _⟩
  rcases q with q | ⟨n, q⟩
  · induction q using Quotient.inductionOn with
    | h c =>
      obtain ⟨M, _, _, hM, h⟩ := key c
      exact ⟨M, _, _, hM, h.trans (classOf_toStructure_nat c)⟩
  · induction q using Quotient.inductionOn with
    | h c =>
      obtain ⟨M, _, _, hM, h⟩ := key c
      exact ⟨M, _, _, hM, h.trans (classOf_toStructure_fin c)⟩

end ClassOf

/-! ### Perfect sets of non-isomorphic models -/

/-- `φ` has *perfectly many* countable models: on `ℕ` or on some `Fin n`, its model class contains
a nonempty perfect set of configurations whose decoded structures are pairwise non-isomorphic.
The finite tiers are needed: with countably many unary predicates, the sentence saying that there
is exactly one element has such a set on `Fin 1` and no model on `ℕ`. -/
def HasPerfectlyManyCountableModels (φ : L.SentenceInf ι) : Prop :=
  (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf φ) ∨
    ∃ n, (isoSetoid L (Fin n)).HasPerfectAntichainOn (modelsOf φ)

/-- In a language with countably many relation symbols of each arity, a sentence with perfectly
many countable models has exactly continuum many. -/
theorem HasPerfectlyManyCountableModels.countableModelCount_eq [∀ n, Countable (L.Relations n)]
    {φ : L.SentenceInf ι} (h : HasPerfectlyManyCountableModels φ) : countableModelCount φ = 𝔠 := by
  refine (countableModelCount_le_continuum φ).antisymm ?_
  rcases h with h | ⟨n, h⟩
  · exact h.hasCantorAntichainOn.continuum_le_mk_quotient_comap.trans
      (mk_quotient_isoSetoidOn_nat_le_countableModelCount φ)
  · exact h.hasCantorAntichainOn.continuum_le_mk_quotient_comap.trans
      (mk_quotient_isoSetoidOn_fin_le_countableModelCount φ n)

end TauCeti
