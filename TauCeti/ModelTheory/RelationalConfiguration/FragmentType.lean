/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.FragmentType
public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.SetTheory.Descriptive.Antichain
import TauCeti.Data.Setoid.Countable
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Fragment types and type spectra of relational configurations

Let `F` be a fragment of `L_{ω₁ω}` and `c` a relational configuration on a carrier `V`. The
*coded type* `F.pointedType c a` of an `n`-tuple `a` of `V` is the truth assignment that the
decoded structure `c.toStructure` gives to the formulas of the arity slice `F.slice n` at `a`
(`FirstOrder.Language.Fragment.truthAssignment`). On a countable carrier it is Borel in the
configuration, and jointly measurable in the configuration and the tuple; isomorphisms of
configurations carry the types of tuples to the types of their images.

The *type spectrum* `F.typeSpectrum n C` of a set `C` of configurations collects the types
realized by `n`-tuples in members of `C`. Two configurations are *spectrum equivalent* at arity
`n` (`F.typeSpectrumSetoid n`) when they realize the same types. Isomorphism refines spectrum
equivalence, and for a countable fragment on a countable carrier, spectrum equivalence has Borel
graph: realizing the same types is a countable Boolean combination of Borel conditions.

These are the objects of Morley's notion of a scattered sentence, which asks that each countable
fragment have only countably many types realized in the countable models. Silver's theorem applied
to spectrum equivalence on a Borel set `C` of configurations gives a dichotomy: either `C` meets
countably many spectrum classes, and then realizes countably many types, since each configuration
realizes countably many; or `C` carries a Cantor antichain of pairwise non-isomorphic
configurations. So a thin Borel set, one carrying no nonempty perfect set of pairwise
non-isomorphic configurations, realizes only countably many types of each arity for every
countable fragment.

## Main definitions

* `FirstOrder.Language.Fragment.pointedType F c a`: the type of the tuple `a` in the decoded
  structure of `c`, as a truth assignment on the arity slice of `F`.
* `FirstOrder.Language.Fragment.typeSpectrum F n C`: the types of `n`-tuples realized in members
  of `C`.
* `FirstOrder.Language.Fragment.typeSpectrumSetoid F n`: equality of the realized types of
  arity `n`.

## Main results

* `FirstOrder.Language.Fragment.measurable_pointedType` and
  `FirstOrder.Language.Fragment.measurable_uncurry_pointedType`: measurability of coded types.
* `FirstOrder.Language.Fragment.pointedType_comp_equiv`: transport of coded types along an
  isomorphism of decoded structures.
* `FirstOrder.Language.Fragment.isoSetoid_le_typeSpectrumSetoid`: isomorphism refines spectrum
  equivalence.
* `FirstOrder.Language.Fragment.measurableSet_setOf_typeSpectrumSetoid`: for a countable fragment
  on a countable carrier, spectrum equivalence has Borel graph.
* `FirstOrder.Language.Fragment.countable_typeSpectrum_or_hasCantorAntichainOn`: a Borel set of
  configurations realizes countably many types or carries a Cantor antichain for isomorphism.
* `FirstOrder.Language.Fragment.countable_typeSpectrum_of_isThinOn`: a thin Borel set of
  configurations realizes countably many types of each arity for every countable fragment.

## References

* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18 (scattered
  sentences).
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the chapter
  on Vaught counterexamples (scattered sentences, Definition 3.3.1).
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* Coded fragment types, type spectra, spectrum equivalence and its Borelness, and the Silver
  dichotomy for spectra follow Cameron Freer's `cameronfreer/infinitary-logic` (checkpoint
  `518a366`, Apache-2.0): `InfinitaryLogic/Descriptive/FragmentSpectrum.lean`,
  `InfinitaryLogic/Descriptive/RealizedSpectrum.lean` and
  `fragmentSpectrum_countable_or_cantor` in `InfinitaryLogic/Conditional/FragmentSpectrumThin.lean`.
  There the carrier is `ℕ` and the language is in universe `0`; here the carrier is any countable
  type, the language is in any universe, and only the relevant slice of the fragment is assumed
  countable.
-/

public section

universe u v w w'

open Set TauCeti TauCeti.RelationalConfiguration

namespace FirstOrder.Language.Fragment

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'} (F : Fragment L)
  {n : ℕ}

/-! ### Coded types -/

/-- The *coded type* of an `n`-tuple `a` in a configuration `c`: the truth assignment on the arity
slice `F.slice n` realized by `a` in the decoded structure `c.toStructure`. -/
def pointedType (c : RelationalConfiguration L V) (a : Fin n → V) : F.slice n → Prop :=
  @truthAssignment L F V c.toStructure n a

/-- A coded type is the realized truth assignment of the decoded structure. -/
theorem pointedType_def (c : RelationalConfiguration L V) (a : Fin n → V) :
    F.pointedType c a = @truthAssignment L F V c.toStructure n a :=
  (rfl)

/-- Evaluating a coded type at a formula of the slice is realization of the formula at the tuple
in the decoded structure. -/
@[simp]
theorem pointedType_apply (c : RelationalConfiguration L V) (a : Fin n → V) (φ : F.slice n) :
    F.pointedType c a φ ↔ @BoundedFormulaInf.Realize L ℕ Empty V c.toStructure n φ.1 Empty.elim a :=
  letI := c.toStructure
  truthAssignment_apply F a φ

/-- Two tuples, in possibly different configurations, have the same coded type exactly when they
satisfy the same formulas of the slice. -/
theorem pointedType_eq_iff {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    {a : Fin n → V} {b : Fin n → W} :
    F.pointedType c a = F.pointedType d b ↔ ∀ φ : F.slice n,
      (F.pointedType c a φ ↔ F.pointedType d b φ) := by
  simp only [funext_iff, propext_iff]

/-- An isomorphism of decoded structures carries the coded type of a tuple to the coded type of
its image. -/
@[simp]
theorem pointedType_comp_equiv {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    (e : @Language.Equiv L V W c.toStructure d.toStructure) (a : Fin n → V) :
    F.pointedType d (e ∘ a) = F.pointedType c a :=
  letI := c.toStructure
  letI := d.toStructure
  Equiv.truthAssignment_comp e F a

/-- On a countable carrier, each formula of the slice holds of a fixed tuple on a Borel set of
configurations. -/
theorem measurable_pointedType_apply [Countable V] (a : Fin n → V) (φ : F.slice n) :
    Measurable fun c : RelationalConfiguration L V => F.pointedType c a φ :=
  measurableSet_setOfPred.1 <| by
    simpa only [pointedType_apply] using measurableSet_setOf_realize φ.1 Empty.elim a

/-- On a countable carrier, the coded type of a fixed tuple is a Borel function of the
configuration. -/
@[fun_prop]
theorem measurable_pointedType [Countable V] (a : Fin n → V) :
    Measurable fun c : RelationalConfiguration L V => F.pointedType c a :=
  measurable_pi_iff.2 (F.measurable_pointedType_apply a)

/-- On a countable carrier whose singletons are measurable, the coded type is jointly measurable in
the configuration and the tuple. -/
theorem measurable_uncurry_pointedType [Countable V] [MeasurableSpace V]
    [MeasurableSingletonClass V] :
    Measurable (Function.uncurry (F.pointedType (V := V) (n := n))) :=
  measurable_from_prod_countable_left F.measurable_pointedType

/-! ### Type spectra -/

/-- The *type spectrum* of a set `C` of configurations at arity `n`: the coded types of the
`n`-tuples in members of `C`. -/
def typeSpectrum (n : ℕ) (C : Set (RelationalConfiguration L V)) : Set (F.slice n → Prop) :=
  ⋃ c ∈ C, range (F.pointedType (n := n) c)

/-- A truth assignment lies in the type spectrum of `C` exactly when it is the coded type of a
tuple in a member of `C`. -/
@[simp]
theorem mem_typeSpectrum {C : Set (RelationalConfiguration L V)} {τ : F.slice n → Prop} :
    τ ∈ F.typeSpectrum n C ↔ ∃ c ∈ C, ∃ a : Fin n → V, F.pointedType c a = τ := by
  simp [typeSpectrum]

/-- The type spectrum of the empty set is empty. -/
@[simp]
theorem typeSpectrum_empty (n : ℕ) :
    F.typeSpectrum n (∅ : Set (RelationalConfiguration L V)) = ∅ := by
  simp [typeSpectrum]

/-- The type spectrum of a union is the union of the type spectra. -/
theorem typeSpectrum_union (n : ℕ) (C D : Set (RelationalConfiguration L V)) :
    F.typeSpectrum n (C ∪ D) = F.typeSpectrum n C ∪ F.typeSpectrum n D :=
  biUnion_union C D _

/-- The coded type of a tuple in a member of `C` lies in the type spectrum of `C`. -/
theorem pointedType_mem_typeSpectrum {C : Set (RelationalConfiguration L V)}
    {c : RelationalConfiguration L V} (hc : c ∈ C) (a : Fin n → V) :
    F.pointedType c a ∈ F.typeSpectrum n C :=
  (F.mem_typeSpectrum).2 ⟨c, hc, a, rfl⟩

/-- The type spectrum of a single configuration is the range of its coded types. -/
@[simp]
theorem typeSpectrum_singleton (n : ℕ) (c : RelationalConfiguration L V) :
    F.typeSpectrum n {c} = range (F.pointedType (n := n) c) := by
  simp [typeSpectrum]

/-- The type spectrum is monotone in the set of configurations. -/
theorem typeSpectrum_mono (n : ℕ) {C D : Set (RelationalConfiguration L V)} (h : C ⊆ D) :
    F.typeSpectrum n C ⊆ F.typeSpectrum n D :=
  biUnion_mono h fun _ _ => Subset.rfl

/-- The type spectrum of a set is the union of the type spectra of its members. -/
theorem typeSpectrum_eq_biUnion (n : ℕ) (C : Set (RelationalConfiguration L V)) :
    F.typeSpectrum n C = ⋃ c ∈ C, F.typeSpectrum n {c} := by
  simp_rw [typeSpectrum_singleton]
  rfl

/-- On a countable carrier, a single configuration realizes countably many types of each arity. -/
theorem countable_typeSpectrum_singleton [Countable V] (n : ℕ) (c : RelationalConfiguration L V) :
    (F.typeSpectrum n {c}).Countable := by
  rw [typeSpectrum_singleton]
  exact countable_range _

/-- Isomorphic configurations realize the same types. -/
theorem typeSpectrum_singleton_eq_of_isoSetoid (n : ℕ) {c d : RelationalConfiguration L V}
    (h : isoSetoid L V c d) : F.typeSpectrum n {c} = F.typeSpectrum n {d} := by
  -- Each inclusion transports tuples along an isomorphism, in one direction or the other.
  have key : ∀ {c d : RelationalConfiguration L V}, isoSetoid L V c d →
      F.typeSpectrum n {c} ⊆ F.typeSpectrum n {d} := fun {c d} h => by
    obtain ⟨e⟩ := isoSetoid_apply.1 h
    rw [typeSpectrum_singleton]
    rintro _ ⟨a, rfl⟩
    rw [← F.pointedType_comp_equiv e a]
    exact F.pointedType_mem_typeSpectrum rfl _
  exact (key h).antisymm (key ((isoSetoid L V).symm h))

/-! ### Spectrum equivalence -/

/-- *Spectrum equivalence* at arity `n`: two configurations are related when they realize the same
coded types of `n`-tuples. -/
def typeSpectrumSetoid (n : ℕ) : Setoid (RelationalConfiguration L V) :=
  Setoid.ker fun c => F.typeSpectrum n {c}

/-- Two configurations are spectrum equivalent exactly when their type spectra agree. -/
@[simp]
theorem typeSpectrumSetoid_apply {c d : RelationalConfiguration L V} :
    F.typeSpectrumSetoid n c d ↔ F.typeSpectrum n {c} = F.typeSpectrum n {d} :=
  Iff.rfl

/-- Isomorphism refines spectrum equivalence. -/
theorem isoSetoid_le_typeSpectrumSetoid (n : ℕ) :
    isoSetoid L V ≤ F.typeSpectrumSetoid n :=
  fun _ _ h => F.typeSpectrum_singleton_eq_of_isoSetoid n h

section Measurable

variable [Countable V] {X : Type*} [MeasurableSpace X] {f g : X → RelationalConfiguration L V}

/-- For a countable slice, agreement of the coded types of two tuples, in configurations depending
measurably on a parameter, is a Borel condition on the parameter. -/
private theorem measurable_pointedType_eq [Countable (F.slice n)] (hf : Measurable f)
    (hg : Measurable g) (a b : Fin n → V) :
    Measurable fun x => F.pointedType (f x) a = F.pointedType (g x) b := by
  simp_rw [pointedType_eq_iff]
  exact .forall fun φ =>
    ((F.measurable_pointedType_apply a φ).comp hf).iff
      ((F.measurable_pointedType_apply b φ).comp hg)

/-- For a countable slice, inclusion of the type spectra of two configurations depending
measurably on a parameter is a Borel condition on the parameter. -/
private theorem measurable_typeSpectrum_singleton_subset [Countable (F.slice n)]
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => F.typeSpectrum n {f x} ⊆ F.typeSpectrum n {g x} := by
  simp_rw [typeSpectrum_singleton, range_subset_iff, mem_range]
  exact .forall fun a => .exists fun b => F.measurable_pointedType_eq hg hf b a

/-- **Spectrum equivalence is Borel.** On a countable carrier, when the arity slice of the fragment
is countable, in particular for a countable fragment
(`FirstOrder.Language.Fragment.slice_countable`), spectrum equivalence has Borel graph: realizing
the same types is a countable Boolean combination of the Borel conditions that a formula of the
slice holds of a tuple. -/
theorem measurableSet_setOf_typeSpectrumSetoid (hF : (F.slice n).Countable) :
    MeasurableSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      F.typeSpectrumSetoid n p.1 p.2} := by
  have := hF.to_subtype
  simpa only [typeSpectrumSetoid_apply, Subset.antisymm_iff] using
    ((F.measurable_typeSpectrum_singleton_subset measurable_fst measurable_snd).and
      (F.measurable_typeSpectrum_singleton_subset measurable_snd measurable_fst)).setOf

end Measurable

/-! ### Countable spectra -/

/-- On a countable carrier, a set of configurations meeting countably many spectrum classes of
arity `n` realizes countably many types of arity `n`. -/
theorem countable_typeSpectrum_of_countable_quotient [Countable V]
    {C : Set (RelationalConfiguration L V)}
    [Countable (Quotient ((F.typeSpectrumSetoid n).comap (Subtype.val : C → _)))] :
    (F.typeSpectrum n C).Countable := by
  -- The spectra of the members of `C` form the image of its countably many classes.
  have hC := (Setoid.countable_quotient_comap_val_iff.1 ‹_›).image
    (Quotient.lift (s := F.typeSpectrumSetoid n) (fun c => F.typeSpectrum n {c}) fun _ _ => id)
  rw [← image_comp] at hC
  rw [typeSpectrum_eq_biUnion, ← sUnion_image]
  exact hC.sUnion (forall_mem_image.2 fun c _ => F.countable_typeSpectrum_singleton n c)

/-- **Silver's dichotomy for type spectra.** In a language with countably many relation symbols of
each arity, on a countable carrier, a Borel set `C` of configurations either realizes countably
many types of arity `n` for the fragment `F`, whose slice of arity `n` is assumed countable, or
carries a Cantor antichain of pairwise non-isomorphic configurations. No isomorphism invariance of
`C` is required. -/
theorem countable_typeSpectrum_or_hasCantorAntichainOn [∀ n, Countable (L.Relations n)]
    [Countable V] (hF : (F.slice n).Countable) {C : Set (RelationalConfiguration L V)}
    (hC : MeasurableSet C) :
    (F.typeSpectrum n C).Countable ∨ (isoSetoid L V).HasCantorAntichainOn C := by
  -- Silver's theorem for spectrum equivalence on `C`, which isomorphism refines.
  obtain hq | hA := Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V)
    ((F.typeSpectrumSetoid n).comap Subtype.val)
    (fun _ _ hxy => F.isoSetoid_le_typeSpectrumSetoid n hxy)
    ((F.measurableSet_setOf_typeSpectrumSetoid hF).preimage
      (measurable_subtype_coe.prodMap measurable_subtype_coe))
  · exact .inl F.countable_typeSpectrum_of_countable_quotient
  · exact .inr hA

/-- **Thin sets realize countably many types.** In a language with countably many relation symbols
of each arity, on a countable carrier, a Borel set `C` of configurations carrying no nonempty
perfect set of pairwise non-isomorphic configurations realizes only countably many types of
arity `n` for every fragment with countable slice of arity `n`, in particular for every countable
fragment. No isomorphism invariance of `C` is required. -/
theorem countable_typeSpectrum_of_isThinOn [∀ n, Countable (L.Relations n)] [Countable V]
    (hF : (F.slice n).Countable) {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (h : (isoSetoid L V).IsThinOn C) : (F.typeSpectrum n C).Countable :=
  (F.countable_typeSpectrum_or_hasCantorAntichainOn hF hC).resolve_right
    fun hA => Setoid.isThinOn_iff.1 h hA.hasPerfectAntichainOn

end FirstOrder.Language.Fragment
