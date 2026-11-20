/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.FragmentType
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf

/-!
# Fragment type spectra of sets of configurations

For a relational language `L`, a fragment `A` of `L_{ω₁ω}` and an arity `n`, the **type
spectrum** `TauCeti.RelationalConfiguration.fragmentSpectrum A n C` of a set `C` of configurations
on a carrier `V` collects the `A`-types (`FirstOrder.Language.fragmentType`) realized by `n`-tuples
of the decoded structures of members of `C`. Two configurations are **spectrum equivalent**
(`TauCeti.RelationalConfiguration.fragmentSpectrumSetoid A n`) when their decoded structures
realize the same `A`-types at arity `n`.

Isomorphism refines spectrum equivalence. On a countable carrier and for a countable fragment, the
pairs of configurations whose tuples have equal `A`-types form a Borel set, and so does the graph of
spectrum equivalence: each type equality is a countable conjunction over the arity slice of `A`,
and realizing the same types quantifies over the countably many tuples. These are the inputs for
Silver's dichotomy that characterize thinness of Borel classes by countability of their fragment
spectra.

## Main definitions

* `TauCeti.RelationalConfiguration.fragmentSpectrum`: the `A`-types realized at arity `n` across a
  set of configurations.
* `TauCeti.RelationalConfiguration.fragmentSpectrumSetoid`: spectrum equivalence, realizing the
  same `A`-types at arity `n`.

## Main results

* `TauCeti.RelationalConfiguration.isoSetoid_le_fragmentSpectrumSetoid`: isomorphic configurations
  are spectrum equivalent.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_fragmentType_eq`: equality of coded
  fragment types is Borel in the pair of configurations.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_fragmentSpectrumSetoid`: spectrum
  equivalence has Borel graph.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapters 1 and 4 (fragments, types relative to a fragment, scattered sentences).
-/

public section

universe u v w

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {A B : Fragment L} {n : ℕ}
  {C D : Set (RelationalConfiguration L V)}

/-! ### Type spectra -/

/-- The **type spectrum** of a set `C` of configurations relative to a fragment `A` at arity `n`:
the `A`-types realized by `n`-tuples of the decoded structures of members of `C`. -/
def fragmentSpectrum (A : Fragment L) (n : ℕ) (C : Set (RelationalConfiguration L V)) :
    Set (Set (L.BoundedFormulaω Empty n)) :=
  ⋃ c ∈ C, @realizedFragmentTypes L A V c.toStructure n

/-- A set of formulas lies in the type spectrum of `C` exactly when it is the `A`-type of a tuple
of a member of `C`. -/
@[simp]
theorem mem_fragmentSpectrum {p : Set (L.BoundedFormulaω Empty n)} :
    p ∈ fragmentSpectrum A n C ↔
      ∃ c ∈ C, ∃ a : Fin n → V, @fragmentType L A V c.toStructure n a = p := by
  simp only [fragmentSpectrum, Set.mem_iUnion, mem_realizedFragmentTypes, exists_prop]

/-- The type spectrum of a single configuration is the set of fragment types realized in its
decoded structure. -/
@[simp]
theorem fragmentSpectrum_singleton (A : Fragment L) (n : ℕ) (c : RelationalConfiguration L V) :
    fragmentSpectrum A n {c} = @realizedFragmentTypes L A V c.toStructure n := by
  simp only [fragmentSpectrum, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]

/-- The type spectrum is monotone in the set of configurations. -/
theorem fragmentSpectrum_mono (hCD : C ⊆ D) : fragmentSpectrum A n C ⊆ fragmentSpectrum A n D :=
  Set.biUnion_subset_biUnion_left hCD

/-- Restricting to a smaller fragment intersects every type of the spectrum with its arity slice. -/
theorem fragmentSpectrum_eq_image_of_le (hAB : A ≤ B) (n : ℕ)
    (C : Set (RelationalConfiguration L V)) :
    fragmentSpectrum A n C = (A.slice n ∩ ·) '' fragmentSpectrum B n C := by
  ext p
  simp only [mem_fragmentSpectrum, Set.mem_image]
  constructor
  · rintro ⟨c, hc, a, rfl⟩
    exact ⟨_, ⟨c, hc, a, rfl⟩, (@fragmentType_eq_inter_of_le L V c.toStructure A B n hAB a).symm⟩
  · rintro ⟨_, ⟨c, hc, a, rfl⟩, rfl⟩
    exact ⟨c, hc, a, @fragmentType_eq_inter_of_le L V c.toStructure A B n hAB a⟩

/-! ### Spectrum equivalence -/

/-- **Spectrum equivalence** relative to a fragment `A` at arity `n`: the decoded structures realize
the same `A`-types at arity `n`. -/
def fragmentSpectrumSetoid (A : Fragment L) (n : ℕ) : Setoid (RelationalConfiguration L V) :=
  Setoid.ker fun c => @realizedFragmentTypes L A V c.toStructure n

/-- Two configurations are spectrum equivalent exactly when their decoded structures realize the
same fragment types. -/
@[simp]
theorem fragmentSpectrumSetoid_apply {c d : RelationalConfiguration L V} :
    fragmentSpectrumSetoid A n c d ↔
      @realizedFragmentTypes L A V c.toStructure n = @realizedFragmentTypes L A V d.toStructure n :=
  Iff.rfl

/-- Two configurations are spectrum equivalent exactly when they have the same type spectrum. -/
theorem fragmentSpectrumSetoid_iff_fragmentSpectrum_eq {c d : RelationalConfiguration L V} :
    fragmentSpectrumSetoid A n c d ↔ fragmentSpectrum A n {c} = fragmentSpectrum A n {d} := by
  rw [fragmentSpectrumSetoid_apply, fragmentSpectrum_singleton, fragmentSpectrum_singleton]

/-- Isomorphic configurations are spectrum equivalent. -/
theorem isoSetoid_le_fragmentSpectrumSetoid (A : Fragment L) (n : ℕ) :
    isoSetoid L V ≤ fragmentSpectrumSetoid A n := fun c d h =>
  let ⟨e⟩ := isoSetoid_apply.1 h
  @Equiv.realizedFragmentTypes_eq L V V c.toStructure d.toStructure e A n

/-! ### Borelness -/

/-- On a countable carrier and for a countable fragment, the pairs of configurations at which two
fixed tuples have the same fragment type form a measurable set. Neither the language nor its
relation symbols need be countable. -/
theorem measurableSet_setOf_fragmentType_eq [Countable V]
    (hA : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) (a b : Fin n → V) :
    MeasurableSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      @fragmentType L A V p.1.toStructure n a = @fragmentType L A V p.2.toStructure n b} := by
  have hset : {p : RelationalConfiguration L V × RelationalConfiguration L V |
      @fragmentType L A V p.1.toStructure n a = @fragmentType L A V p.2.toStructure n b} =
      ⋂ φ ∈ A.slice n,
        {p | @BoundedFormulaInf.Realize L ℕ Empty V p.1.toStructure n φ Empty.elim a ↔
          @BoundedFormulaInf.Realize L ℕ Empty V p.2.toStructure n φ Empty.elim b} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, fragmentType_eq_iff]
  rw [hset]
  exact .biInter (Fragment.slice_countable hA n) fun φ _ =>
    (measurable_fst (measurableSet_setOf_realize φ Empty.elim a)).iff
      (measurable_snd (measurableSet_setOf_realize φ Empty.elim b))

/-- On a countable carrier and for a countable fragment, spectrum equivalence has measurable graph.
Neither the language nor its relation symbols need be countable. -/
theorem measurableSet_setOf_fragmentSpectrumSetoid [Countable V]
    (hA : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) (n : ℕ) :
    MeasurableSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      fragmentSpectrumSetoid A n p.1 p.2} := by
  have hset : {p : RelationalConfiguration L V × RelationalConfiguration L V |
      fragmentSpectrumSetoid A n p.1 p.2} =
      (⋂ a : Fin n → V, ⋃ b : Fin n → V, {p | @fragmentType L A V p.1.toStructure n a =
        @fragmentType L A V p.2.toStructure n b}) ∩
      ⋂ b : Fin n → V, ⋃ a : Fin n → V, {p | @fragmentType L A V p.1.toStructure n a =
        @fragmentType L A V p.2.toStructure n b} := by
    ext p
    simp only [Set.mem_ofPred_eq, fragmentSpectrumSetoid_apply, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_iUnion]
    rw [Set.Subset.antisymm_iff]
    simp only [Set.subset_def, mem_realizedFragmentTypes, forall_exists_index,
      forall_apply_eq_imp_iff]
    exact and_congr_left' (forall_congr' fun a => exists_congr fun b => eq_comm)
  rw [hset]
  exact (MeasurableSet.iInter fun a => .iUnion fun b =>
    measurableSet_setOf_fragmentType_eq hA a b).inter
      (MeasurableSet.iInter fun b => .iUnion fun a => measurableSet_setOf_fragmentType_eq hA a b)

end TauCeti.RelationalConfiguration
