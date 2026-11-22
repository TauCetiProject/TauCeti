/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FirstOrderImage
public import TauCeti.ModelTheory.ModelExistence.FragmentType
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.ModelTheory.RelationalConfiguration.Separation
public import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Ordinal
import TauCeti.Data.Setoid.Basic
import TauCeti.ModelTheory.Scott.Formula
import TauCeti.SetTheory.Cardinal.AlephOne
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Fragment type spectra of relational configurations

Fix a relational language `L`, a fragment `F : FirstOrder.Language.Fragment L`, and an arity
`n : ℕ`. On any carrier `V`, a relational configuration `c : RelationalConfiguration L V` and a
tuple `a : Fin n → V` determine a coded fragment type `F.pointedType c a : F.slice n → Prop`, namely
the realized truth assignment `F.truthAssignment V a` in the decoded structure `c.toStructure`.
Varying the tuple gives the realized `n`-types `c.realizedTypes F n` of `c` (the structure-level
`F.realizedTypes V n` evaluated in `c.toStructure`), and varying both `c` across a class
`C : Set (RelationalConfiguration L V)` and `a` across `Fin n → V` gives the **fragment type
spectrum** `F.typeSpectrum n C`.

Two configurations are **spectrum-equivalent** at `(F, n)` (`F.typeSpectrumSetoid V n`) when they
realize the same `F`-types at arity `n`. Isomorphism of decoded structures transports pointed
fragment types (`FirstOrder.Language.Equiv.pointedType_comp`) and therefore refines spectrum
equivalence (`TauCeti.RelationalConfiguration.isoSetoid_le_typeSpectrumSetoid`). When `V` is
countable, `F.pointedType c a` is measurable in `c` for each tuple `a` and jointly measurable in
`(c, a)` whenever `V` has measurable singletons; if `F.slice n` is countable,
`F.typeSpectrumSetoid V n` has Borel graph, with no countability hypothesis on `L`. Moreover, a
countable slice has quantifier ranks bounded below `ω₁`, so some countable back-and-forth level
`bfEquivSetoid L V (α + n)` refines `F.typeSpectrumSetoid V n`.

Combining spectrum equivalence with Silver's dichotomy and canonical Scott formulas yields two
complementary characterizations on a countable carrier `V`:

* **Forward direction.** If `C` meets countably many classes at every countable back-and-forth
  level, then `F.typeSpectrum n C` is countable for every fragment with countable `n`-slice, with
  no Borelness assumption on `C` and no countability assumption on `L`
  (`TauCeti.RelationalConfiguration.countable_typeSpectrum_of_countable_bfEquivSetoid`). In a
  countable relational vocabulary, Silver's theorem applied directly to `F.typeSpectrumSetoid V n`
  on a Borel class `C` shows that either `F.typeSpectrum n C` is countable or `C` carries a Cantor
  (and hence perfect) antichain of pairwise non-isomorphic configurations
  (`TauCeti.RelationalConfiguration.countable_typeSpectrum_or_hasCantorAntichainOn`), so thinness
  of `C` forces `F.typeSpectrum n C` to be countable.
* **Converse direction.** In a countable relational vocabulary, if `F.typeSpectrum n C` is countable
  for every countable fragment `F` and every arity `n`, transfinite induction along countable levels
  using `Fragment.firstOrder L` at depth `0` and canonical Scott formulas (together with their
  one-variable existential closures at successors) shows that `bfTupleSetoid` on `C` has countably
  many classes at every countable depth `α < ω₁` and every arity `n`
  (`TauCeti.RelationalConfiguration.countable_quotient_bfTupleSetoid_of_countable_typeSpectrum`).
  Uniform back-and-forth separation then rules out Cantor antichains and makes `C` thin, with no
  Borelness or invariance assumption on `C`. Together with the forward direction, a Borel class `C`
  is thin for isomorphism if and only if every countable fragment has a countable type spectrum on
  `C` at every arity (`TauCeti.RelationalConfiguration.isThinOn_iff_countable_typeSpectrum`).

## Main definitions

* `FirstOrder.Language.Fragment.pointedType`: the coded fragment type `F.slice n → Prop` of a tuple
  in a relational configuration.
* `TauCeti.RelationalConfiguration.realizedTypes`: the fragment `n`-types realized in the structure
  decoded from a single configuration.
* `FirstOrder.Language.Fragment.typeSpectrum`: the fragment `n`-types realized across a set of
  configurations.
* `FirstOrder.Language.Fragment.typeSpectrumSetoid`: equivalence of configurations by having the
  same realized fragment `n`-types.

## Main results

* `FirstOrder.Language.Fragment.measurable_pointedType_left` and
  `FirstOrder.Language.Fragment.measurable_pointedType`: measurability in the configuration and
  joint measurability in the configuration and tuple.
* `FirstOrder.Language.Equiv.pointedType_comp` and
  `TauCeti.RelationalConfiguration.realizedTypes_perm_smul`: transport of coded fragment types along
  isomorphisms and invariance of realized-type sets under the logic action.
* `TauCeti.RelationalConfiguration.countable_image_mem_modelsOf_of_countable_typeSpectrum`: a
  countable arity-`0` spectrum for `Fragment.ofTheory (Set.range θ)` forces countably many realized
  sentence truth sequences for `θ`.
* `TauCeti.RelationalConfiguration.isoSetoid_le_typeSpectrumSetoid`,
  `TauCeti.RelationalConfiguration.bfEquivSetoid_le_typeSpectrumSetoid`, and
  `TauCeti.RelationalConfiguration.measurableSet_setOf_typeSpectrumSetoid`: refinement by
  isomorphism and by back-and-forth levels, and Borelness of spectrum equivalence.
* `TauCeti.RelationalConfiguration.countable_typeSpectrum_or_hasCantorAntichainOn`: Silver's
  dichotomy for fragment type spectra on Borel classes.
* `TauCeti.RelationalConfiguration.countable_quotient_bfTupleSetoid_of_countable_typeSpectrum` and
  `TauCeti.RelationalConfiguration.isThinOn_iff_countable_typeSpectrum`: countable fragment spectra
  at all arities bound all countable back-and-forth tuple quotients and characterize thin Borel
  classes.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1
  (countable fragments and fragment types) and the chapters on the space of countable models and
  Vaught counterexamples (scattered classes).
* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* Related formalizations appear in Cameron Freer's `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Descriptive/FragmentSpectrum.lean`,
  `InfinitaryLogic/Descriptive/RealizedSpectrum.lean`, and
  `InfinitaryLogic/Conditional/FragmentSpectrumThin.lean` (Apache-2.0).
* Divergences from that source: `pointedType` is the computable `Prop`-valued truth assignment on
  `F.slice n` over an arbitrary carrier `V`; Borelness of spectrum equivalence and the forward
  bound from countable back-and-forth levels impose no countability hypothesis on `L`; Silver's
  theorem is discharged unconditionally on arbitrary countable carriers; and the converse from
  countable fragment spectra to countable level quotients and thinness is proved unconditionally on
  the class `C` via canonical Scott formulas and uniform back-and-forth separation, without
  Borelness of `C` or López–Escobar separation.
-/

public section

universe u v w w' o uι

open Cardinal MeasureTheory Ordinal Set TauCeti TauCeti.RelationalConfiguration
open scoped Pointwise

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'} {n : ℕ}

namespace Fragment

/-! ### Coded pointed fragment types -/

/-- The **coded fragment type** of a tuple `a : Fin n → V` in a configuration
`c : RelationalConfiguration L V`: the realized truth assignment of `a` on `F.slice n` in the
decoded structure `c.toStructure`. -/
def pointedType (F : Fragment L) (c : RelationalConfiguration L V) {n : ℕ} (a : Fin n → V) :
    F.slice n → Prop :=
  @Fragment.truthAssignment L F V c.toStructure n a

/-- Evaluating `F.pointedType c a` at a slice member tests realization in `c.toStructure`. -/
@[simp]
theorem pointedType_apply (F : Fragment L) (c : RelationalConfiguration L V) (a : Fin n → V)
    (φ : F.slice n) :
    F.pointedType c a φ ↔
      @BoundedFormulaInf.Realize L ℕ Empty V c.toStructure n φ.val Empty.elim a :=
  @truthAssignment_apply L V c.toStructure n F a φ

/-- `F.pointedType c a` is `F.truthAssignment` in the decoded structure `c.toStructure`. -/
theorem pointedType_eq_truthAssignment (F : Fragment L) (c : RelationalConfiguration L V)
    (a : Fin n → V) :
    F.pointedType c a = @Fragment.truthAssignment L F V c.toStructure n a :=
  (rfl)

/-- On the slice, `F.pointedType c a` records membership in
`@fragmentType L F V c.toStructure n a`. -/
theorem pointedType_iff_mem_fragmentType (F : Fragment L) (c : RelationalConfiguration L V)
    (a : Fin n → V) (φ : F.slice n) :
    F.pointedType c a φ ↔ φ.val ∈ @fragmentType L F V c.toStructure n a :=
  @truthAssignment_iff_mem_fragmentType L V c.toStructure n F a φ

/-- Restricting to a smaller fragment precomposes `pointedType` with the slice inclusion. -/
theorem pointedType_restrict {A B : Fragment L} (hAB : A ≤ B) (c : RelationalConfiguration L V)
    (a : Fin n → V) :
    A.pointedType c a = B.pointedType c a ∘ Set.inclusion (slice_mono hAB n) :=
  @truthAssignment_restrict L V c.toStructure A B n hAB a

/-- Equality of coded pointed types is equality of fragment types in the decoded structures. -/
theorem pointedType_eq_iff_fragmentType_eq {F : Fragment L}
    {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    {a : Fin n → V} {b : Fin n → W} :
    F.pointedType c a = F.pointedType d b ↔
      @fragmentType L F V c.toStructure n a = @fragmentType L F W d.toStructure n b :=
  @truthAssignment_eq_iff L V W c.toStructure d.toStructure F n a b

/-- Equality of coded pointed types means agreement on every formula in the slice. -/
theorem pointedType_eq_iff {F : Fragment L}
    {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    {a : Fin n → V} {b : Fin n → W} :
    F.pointedType c a = F.pointedType d b ↔
      ∀ φ ∈ F.slice n,
        @BoundedFormulaInf.Realize L ℕ Empty V c.toStructure n φ Empty.elim a ↔
          @BoundedFormulaInf.Realize L ℕ Empty W d.toStructure n φ Empty.elim b :=
  pointedType_eq_iff_fragmentType_eq.trans
    (@fragmentType_eq_iff L V W c.toStructure d.toStructure F n a b)

/-- Encoding a relational structure along a bijection transports `truthAssignment` to
`pointedType`. -/
@[simp]
theorem pointedType_encodeVia {M : Type w'} [L.Structure M]
    (F : Fragment L) (f : M ≃ V) (a : Fin n → M) :
    F.pointedType (f.encodeVia (L := L)) (f ∘ a) = F.truthAssignment M a := by
  rw [pointedType_eq_truthAssignment, Equiv.toStructure_encodeVia]
  exact @Equiv.truthAssignment_comp L V M f.inducedStructure _ n f.inducedStructureEquiv F a

/-- Encoding a relational structure on its own carrier transports `truthAssignment` to
`pointedType`. -/
@[simp]
theorem pointedType_ofStructure {M : Type w} [L.Structure M]
    (F : Fragment L) (a : Fin n → M) :
    F.pointedType (ofStructure L M) a = F.truthAssignment M a := by
  simpa using F.pointedType_encodeVia (_root_.Equiv.refl M) a

/-- Relabelling a configuration by a permutation of the carrier transports pointed fragment types
along the same permutation. -/
@[simp]
theorem pointedType_perm_smul (F : Fragment L) (σ : Equiv.Perm V)
    (c : RelationalConfiguration L V) (a : Fin n → V) :
    F.pointedType (σ • c) (σ ∘ a) = F.pointedType c a := by
  rw [perm_smul_eq_encodeVia, @pointedType_encodeVia L _ V n V c.toStructure F σ a,
    ← F.pointedType_eq_truthAssignment]

/-- On a countable carrier in a relational language, `F.pointedType c a` is measurable in the
configuration `c` for each fixed tuple `a`, with no countability hypothesis on `L` or `F` and no
measurable-space structure on `V`. -/
@[fun_prop]
theorem measurable_pointedType_left [Countable V] (F : Fragment L)
    (a : Fin n → V) :
    Measurable fun c : RelationalConfiguration L V => F.pointedType c a := by
  refine Measurable.of_eval fun φ => measurableSet_setOfPred.1 ?_
  simpa only [pointedType_apply] using measurableSet_setOf_realize φ.val Empty.elim a

/-- On a countable carrier with measurable singletons (such as `ℕ` or `Fin m`) in a relational
language, `F.pointedType` is jointly measurable in the configuration and the tuple. -/
@[fun_prop]
theorem measurable_pointedType [Countable V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (F : Fragment L) :
    Measurable fun p : RelationalConfiguration L V × (Fin n → V) => F.pointedType p.1 p.2 :=
  measurable_from_prod_countable_left fun a => F.measurable_pointedType_left a

end Fragment

namespace Equiv

/-- An isomorphism between decoded structures preserves coded pointed fragment types. -/
@[simp]
theorem pointedType_comp {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    (e : @Language.Equiv L V W c.toStructure d.toStructure) (F : Fragment L) (a : Fin n → V) :
    F.pointedType d (e ∘ a) = F.pointedType c a :=
  @Equiv.truthAssignment_comp L W V d.toStructure c.toStructure n e F a

end Equiv

end FirstOrder.Language

namespace TauCeti.RelationalConfiguration

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'} {n : ℕ}

/-! ### Realized fragment types of one configuration -/

/-- The fragment `n`-types realized by `n`-tuples in the structure decoded from `c`. -/
def realizedTypes (c : RelationalConfiguration L V) (F : Fragment L) (n : ℕ) :
    Set (F.slice n → Prop) :=
  @Fragment.realizedTypes L F V c.toStructure n

/-- `c.realizedTypes F n` is `F.realizedTypes V n` in the decoded structure `c.toStructure`. -/
theorem realizedTypes_def (c : RelationalConfiguration L V) (F : Fragment L) (n : ℕ) :
    c.realizedTypes F n = @Fragment.realizedTypes L F V c.toStructure n :=
  (rfl)

/-- A truth assignment on `F.slice n` is realized in `c` exactly when it is `F.pointedType c a` for
some `n`-tuple `a`. -/
@[simp]
theorem mem_realizedTypes {c : RelationalConfiguration L V} {F : Fragment L}
    {p : F.slice n → Prop} :
    p ∈ c.realizedTypes F n ↔ ∃ a : Fin n → V, F.pointedType c a = p := by
  rw [realizedTypes_def, @Fragment.mem_realizedTypes L V c.toStructure F n p]
  exact exists_congr fun a => by rw [F.pointedType_eq_truthAssignment]

/-- Encoding a relational structure along a bijection preserves its realized fragment `n`-types. -/
@[simp]
theorem realizedTypes_encodeVia {M : Type w'} [L.Structure M]
    (f : M ≃ V) (F : Fragment L) (n : ℕ) :
    (f.encodeVia (L := L)).realizedTypes F n = F.realizedTypes M n := by
  rw [realizedTypes_def, Equiv.toStructure_encodeVia]
  exact (@Equiv.realizedTypes_eq L M V _ f.inducedStructure f.inducedStructureEquiv F n).symm

/-- Encoding a relational structure on its own carrier preserves its realized fragment `n`-types. -/
@[simp]
theorem realizedTypes_ofStructure {M : Type w} [L.Structure M]
    (F : Fragment L) (n : ℕ) :
    (ofStructure L M).realizedTypes F n = F.realizedTypes M n := by
  rw [← Equiv.encodeVia_refl, realizedTypes_encodeVia]

/-- Relabelling by a permutation leaves the realized fragment `n`-types unchanged. -/
@[simp]
theorem realizedTypes_perm_smul (σ : Equiv.Perm V) (c : RelationalConfiguration L V)
    (F : Fragment L) (n : ℕ) :
    (σ • c).realizedTypes F n = c.realizedTypes F n := by
  rw [perm_smul_eq_encodeVia, @realizedTypes_encodeVia L _ V V c.toStructure σ F n,
    ← c.realizedTypes_def F n]

end TauCeti.RelationalConfiguration

namespace FirstOrder.Language.Fragment

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {n : ℕ}

/-! ### Fragment type spectra across a class of configurations -/

/-- The **arity-`n` type spectrum** of a fragment `F` across a set `C` of relational configurations
on `V`: the truth assignments on `F.slice n` realized by `n`-tuples in members of `C`. -/
def typeSpectrum (F : Fragment L) (n : ℕ) (C : Set (RelationalConfiguration L V)) :
    Set (F.slice n → Prop) :=
  ⋃ c ∈ C, c.realizedTypes F n

/-- `F.typeSpectrum n C` is the union of `c.realizedTypes F n` over `c ∈ C`. -/
theorem typeSpectrum_def (F : Fragment L) (n : ℕ) (C : Set (RelationalConfiguration L V)) :
    F.typeSpectrum n C = ⋃ c ∈ C, c.realizedTypes F n :=
  (rfl)

/-- A truth assignment lies in `F.typeSpectrum n C` iff it is realized in some member of `C`. -/
theorem mem_typeSpectrum_iff_mem_realizedTypes {F : Fragment L}
    {C : Set (RelationalConfiguration L V)} {p : F.slice n → Prop} :
    p ∈ F.typeSpectrum n C ↔ ∃ c ∈ C, p ∈ c.realizedTypes F n := by
  simp only [typeSpectrum_def, Set.mem_iUnion, exists_prop]

/-- A truth assignment lies in `F.typeSpectrum n C` iff it is `F.pointedType c a` for some `c ∈ C`
and `a : Fin n → V`. -/
@[simp]
theorem mem_typeSpectrum {F : Fragment L} {C : Set (RelationalConfiguration L V)}
    {p : F.slice n → Prop} :
    p ∈ F.typeSpectrum n C ↔ ∃ c ∈ C, ∃ a : Fin n → V, F.pointedType c a = p := by
  simp only [mem_typeSpectrum_iff_mem_realizedTypes, RelationalConfiguration.mem_realizedTypes]

/-- The pointed type of a tuple in a member of `C` belongs to `F.typeSpectrum n C`. -/
theorem pointedType_mem_typeSpectrum (F : Fragment L) {C : Set (RelationalConfiguration L V)}
    {c : RelationalConfiguration L V} (hc : c ∈ C) (a : Fin n → V) :
    F.pointedType c a ∈ F.typeSpectrum n C :=
  mem_typeSpectrum.2 ⟨c, hc, a, rfl⟩

/-- The realized types of each member of `C` form a subset of `F.typeSpectrum n C`. -/
theorem realizedTypes_subset_typeSpectrum (F : Fragment L) {C : Set (RelationalConfiguration L V)}
    {c : RelationalConfiguration L V} (hc : c ∈ C) :
    c.realizedTypes F n ⊆ F.typeSpectrum n C := by
  rw [typeSpectrum_def]
  exact Set.subset_biUnion_of_mem (u := fun x => x.realizedTypes F n) hc

/-- At arity `0`, `F.typeSpectrum 0 C` is the image of `C` under `c ↦ F.pointedType c Fin.elim0`. -/
theorem typeSpectrum_zero (F : Fragment L) (C : Set (RelationalConfiguration L V)) :
    F.typeSpectrum 0 C = (fun c => F.pointedType c Fin.elim0) '' C := by
  ext p
  simp only [mem_typeSpectrum_iff_mem_realizedTypes, RelationalConfiguration.realizedTypes_def]
  refine ⟨fun ⟨c, hc, hp⟩ => ⟨c, hc, ?_⟩, fun ⟨c, hc, hp⟩ => ⟨c, hc, ?_⟩⟩
  · rwa [@Fragment.realizedTypes_zero L F V c.toStructure, ← F.pointedType_eq_truthAssignment,
      mem_singleton_iff, eq_comm] at hp
  · rwa [@Fragment.realizedTypes_zero L F V c.toStructure, ← F.pointedType_eq_truthAssignment,
      mem_singleton_iff, eq_comm]

/-- The type spectrum of the empty class is empty. -/
@[simp]
theorem typeSpectrum_empty (F : Fragment L) (n : ℕ) :
    F.typeSpectrum n (∅ : Set (RelationalConfiguration L V)) = ∅ := by
  simp [typeSpectrum_def]

/-- The type spectrum of a singleton class is the realized-type set of that configuration. -/
@[simp]
theorem typeSpectrum_singleton (F : Fragment L) (n : ℕ) (c : RelationalConfiguration L V) :
    F.typeSpectrum n {c} = c.realizedTypes F n := by
  simp [typeSpectrum_def]

/-- The type spectrum of a binary union is the union of the type spectra. -/
@[simp]
theorem typeSpectrum_union (F : Fragment L) (n : ℕ)
    (C₁ C₂ : Set (RelationalConfiguration L V)) :
    F.typeSpectrum n (C₁ ∪ C₂) = F.typeSpectrum n C₁ ∪ F.typeSpectrum n C₂ :=
  Set.biUnion_union _ _ _

/-- The type spectrum commutes with indexed unions of configuration classes. -/
theorem typeSpectrum_iUnion {ι : Sort*} (F : Fragment L) (n : ℕ)
    (C : ι → Set (RelationalConfiguration L V)) :
    F.typeSpectrum n (⋃ i, C i) = ⋃ i, F.typeSpectrum n (C i) :=
  Set.biUnion_iUnion _ _

/-- The type spectrum is monotone in the class of configurations. -/
theorem typeSpectrum_mono (F : Fragment L) (n : ℕ)
    {C₁ C₂ : Set (RelationalConfiguration L V)} (h : C₁ ⊆ C₂) :
    F.typeSpectrum n C₁ ⊆ F.typeSpectrum n C₂ :=
  Set.biUnion_subset_biUnion_left h

/-- Restricting along a fragment inclusion `A ≤ B` surjects `B.typeSpectrum n C` onto
`A.typeSpectrum n C`. -/
theorem image_restrict_typeSpectrum {A B : Fragment L} (hAB : A ≤ B) (n : ℕ)
    (C : Set (RelationalConfiguration L V)) :
    (· ∘ Set.inclusion (slice_mono hAB n)) '' B.typeSpectrum n C = A.typeSpectrum n C := by
  simp only [typeSpectrum_def, Set.image_iUnion, RelationalConfiguration.realizedTypes_def]
  refine Set.iUnion₂_congr fun c _ => ?_
  exact @Fragment.image_restrict_realizedTypes L A B hAB V c.toStructure n

/-- If `B` has a countable arity-`n` type spectrum on `C`, then so does every subfragment
`A ≤ B`. -/
theorem countable_typeSpectrum_of_le {A B : Fragment L} (hAB : A ≤ B)
    {C : Set (RelationalConfiguration L V)} (hB : (B.typeSpectrum n C).Countable) :
    (A.typeSpectrum n C).Countable := by
  rw [← image_restrict_typeSpectrum hAB n C]
  exact hB.image _

/-- Translating a class of configurations by a permutation leaves its fragment type spectrum
unchanged. -/
@[simp]
theorem typeSpectrum_perm_smul (F : Fragment L) (n : ℕ) (σ : Equiv.Perm V)
    (C : Set (RelationalConfiguration L V)) :
    F.typeSpectrum n (σ • C) = F.typeSpectrum n C := by
  ext p
  simp only [mem_typeSpectrum_iff_mem_realizedTypes, Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, hp⟩
    exact ⟨c, hc, by simpa using hp⟩
  · rintro ⟨c, hc, hp⟩
    exact ⟨σ • c, ⟨c, hc, rfl⟩, by simpa using hp⟩

/-- Saturating a class under the logic action leaves its fragment type spectrum unchanged. -/
@[simp]
theorem typeSpectrum_iUnion_perm_smul (F : Fragment L) (n : ℕ)
    (C : Set (RelationalConfiguration L V)) :
    F.typeSpectrum n (⋃ σ : Equiv.Perm V, σ • C) = F.typeSpectrum n C := by
  rw [typeSpectrum_iUnion]
  refine Set.Subset.antisymm (Set.iUnion_subset fun σ => (F.typeSpectrum_perm_smul n σ C).subset) ?_
  simpa using Set.subset_iUnion (fun σ : Equiv.Perm V => F.typeSpectrum n (σ • C)) 1

/-! ### Spectrum equivalence -/

/-- **Spectrum equivalence** of relational configurations at `(F, n)`: two configurations on `V` are
related when they realize the exact same set of `F`-types at arity `n`. -/
def typeSpectrumSetoid (F : Fragment L) (V : Type w) (n : ℕ) :
    Setoid (RelationalConfiguration L V) :=
  Setoid.ker fun c => c.realizedTypes F n

/-- `F.typeSpectrumSetoid V n` is the kernel of `c ↦ c.realizedTypes F n`. -/
theorem typeSpectrumSetoid_def (F : Fragment L) (V : Type w) (n : ℕ) :
    F.typeSpectrumSetoid V n = Setoid.ker fun c => c.realizedTypes F n :=
  (rfl)

/-- Two configurations are spectrum-equivalent at `(F, n)` iff their realized `n`-type sets
agree. -/
theorem typeSpectrumSetoid_apply {F : Fragment L} {c d : RelationalConfiguration L V} :
    F.typeSpectrumSetoid V n c d ↔ c.realizedTypes F n = d.realizedTypes F n :=
  Iff.rfl

/-- Explicit back-and-forth characterization of `F.typeSpectrumSetoid V n`: every `n`-tuple on each
side has its `F`-type matched by some `n`-tuple on the other side. -/
theorem typeSpectrumSetoid_iff {F : Fragment L} {c d : RelationalConfiguration L V} :
    F.typeSpectrumSetoid V n c d ↔
      (∀ a : Fin n → V, ∃ b : Fin n → V, F.pointedType c a = F.pointedType d b) ∧
        (∀ b : Fin n → V, ∃ a : Fin n → V, F.pointedType c a = F.pointedType d b) := by
  rw [typeSpectrumSetoid_apply, Set.Subset.antisymm_iff]
  simp only [Set.subset_def, RelationalConfiguration.mem_realizedTypes, forall_exists_index,
    forall_apply_eq_imp_iff]
  exact and_congr (forall_congr' fun a => exists_congr fun b => eq_comm) Iff.rfl

/-- At arity `0`, spectrum equivalence is equality of the pointed types of the empty tuple. -/
theorem typeSpectrumSetoid_zero_iff {F : Fragment L} {c d : RelationalConfiguration L V} :
    F.typeSpectrumSetoid V 0 c d ↔ F.pointedType c Fin.elim0 = F.pointedType d Fin.elim0 := by
  rw [typeSpectrumSetoid_apply, RelationalConfiguration.realizedTypes_def,
    RelationalConfiguration.realizedTypes_def, @Fragment.realizedTypes_zero L F V c.toStructure,
    @Fragment.realizedTypes_zero L F V d.toStructure, ← F.pointedType_eq_truthAssignment,
    ← F.pointedType_eq_truthAssignment, Set.singleton_eq_singleton_iff]

/-- Spectrum equivalence is antitone in the fragment: a larger fragment induces a finer equivalence
relation on configurations. -/
theorem typeSpectrumSetoid_anti (V : Type w) (n : ℕ) :
    Antitone fun F : Fragment L => F.typeSpectrumSetoid V n := by
  intro A B hAB c d hcd
  rw [typeSpectrumSetoid_apply, RelationalConfiguration.realizedTypes_def,
    RelationalConfiguration.realizedTypes_def,
    ← @Fragment.image_restrict_realizedTypes L A B hAB V c.toStructure n,
    ← @Fragment.image_restrict_realizedTypes L A B hAB V d.toStructure n,
    ← c.realizedTypes_def B n, ← d.realizedTypes_def B n, typeSpectrumSetoid_apply.mp hcd]

end FirstOrder.Language.Fragment

namespace TauCeti.RelationalConfiguration

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {n : ℕ}

/-! ### Arity-zero spectra and sentence truth sequences -/

/-- **Sentence truth sequences from arity-zero fragment spectra.** For any family of sentences
`θ : ι → L.Sentenceω`, if `Fragment.ofTheory (Set.range θ)` has a countable arity-`0` type spectrum
on `C`, then `θ` realizes only countably many truth sequences `i ↦ c ∈ modelsOf (θ i)` across
`C`. -/
theorem countable_image_mem_modelsOf_of_countable_typeSpectrum {ι : Type uι}
    (θ : ι → L.Sentenceω) {C : Set (RelationalConfiguration L V)}
    (h : ((Fragment.ofTheory (Set.range θ)).typeSpectrum 0 C).Countable) :
    ((fun c : RelationalConfiguration L V => fun i : ι => c ∈ modelsOf (θ i)) '' C).Countable := by
  let F := Fragment.ofTheory (Set.range θ)
  let proj : (F.slice 0 → Prop) → (ι → Prop) := fun p i =>
    p ⟨θ i, Fragment.mem_slice.2 (Fragment.mem_ofTheory ⟨i, rfl⟩)⟩
  have himg : (fun c : RelationalConfiguration L V => fun i : ι => c ∈ modelsOf (θ i)) '' C =
      proj '' F.typeSpectrum 0 C := by
    rw [F.typeSpectrum_zero, ← Set.image_comp]
    refine Set.image_congr fun c _ => funext fun i => propext ?_
    simp only [Function.comp_apply, proj, mem_modelsOf, SentenceInf.realize_def,
      FormulaInf.realize_def, Fragment.pointedType_apply,
      Subsingleton.elim (default : Fin 0 → V) Fin.elim0]
  rw [himg]
  exact h.image proj

/-! ### Refinement, Borelness, and quotient bounds for spectrum equivalence -/

/-- Isomorphism of decoded structures refines spectrum equivalence at every fragment and arity. -/
theorem isoSetoid_le_typeSpectrumSetoid (F : Fragment L) (V : Type w) (n : ℕ) :
    isoSetoid L V ≤ F.typeSpectrumSetoid V n := by
  intro c d hcd
  obtain ⟨e⟩ := isoSetoid_apply.mp hcd
  rw [Fragment.typeSpectrumSetoid_apply, realizedTypes_def, realizedTypes_def]
  exact @Equiv.realizedTypes_eq L V V c.toStructure d.toStructure e F n

/-- At `Fragment.firstOrder L` and arity `0`, spectrum equivalence is elementary equivalence of the
decoded structures. -/
theorem typeSpectrumSetoid_firstOrder_zero_iff {c d : RelationalConfiguration L V} :
    (Fragment.firstOrder L).typeSpectrumSetoid V 0 c d ↔
      @ElementarilyEquivalent L V V c.toStructure d.toStructure := by
  have hreal (e : RelationalConfiguration L V) (φ : L.Sentence) :
      @BoundedFormulaInf.Realize L ℕ Empty V e.toStructure 0 φ.toOmega Empty.elim Fin.elim0 ↔
        @Sentence.Realize L V e.toStructure φ := by
    let := e.toStructure
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def,
      Subsingleton.elim (default : Fin 0 → V) Fin.elim0] using
      Sentence.realize_toInf (ι := ℕ) φ V
  rw [Fragment.typeSpectrumSetoid_zero_iff, Fragment.pointedType_eq_iff,
    @elementarilyEquivalent_iff L V V c.toStructure d.toStructure]
  constructor
  · intro h φ
    exact (hreal c φ).symm.trans
      ((h φ.toOmega (Fragment.mem_slice.2 (Fragment.toOmega_mem_firstOrder φ))).trans (hreal d φ))
  · intro h ψ hψ
    obtain ⟨φ, rfl⟩ := Fragment.mem_firstOrder_iff.1 (Fragment.mem_slice.1 hψ)
    exact (hreal c φ).trans ((h φ).trans (hreal d φ).symm)

/-- One-sided tuple matching along `bfEquivSetoid L V (α + n)` for a slice of quantifier rank at
most `α`. -/
private theorem exists_pointedType_eq_of_bfEquivSetoid {F : Fragment L} {α : Ordinal.{0}}
    (hF : ∀ φ ∈ F.slice n, φ.qrank ≤ α) {c d : RelationalConfiguration L V}
    (hcd : bfEquivSetoid L V (α + n) c d) (a : Fin n → V) :
    ∃ b : Fin n → V, F.pointedType c a = F.pointedType d b := by
  obtain ⟨b, hb⟩ := @BFEquiv.exists_bfEquiv_append L _ V V c.toStructure d.toStructure α 0
    Fin.elim0 Fin.elim0 n (bfEquivSetoid_apply.mp hcd) a
  have hab : @BFEquiv L _ V V c.toStructure d.toStructure α n a b := by
    have hcomp := @BFEquiv.comp L _ V V c.toStructure d.toStructure (0 + n) _ _ α hb n
      (Fin.cast (Nat.zero_add n).symm)
    have hcast (x : Fin n → V) :
        Fin.append (Fin.elim0 : Fin 0 → V) x ∘ Fin.cast (Nat.zero_add n).symm = x := by
      ext i
      simp
    rwa [hcast a, hcast b] at hcomp
  refine ⟨b, Fragment.pointedType_eq_iff.2 fun φ hφ => ?_⟩
  exact @BFEquiv.realize_iff_of_qrank_le L V V c.toStructure d.toStructure _ ℕ n φ α a b hab
    (by simpa using hF φ hφ) Empty.elim Empty.elim

/-- **Back-and-forth refinement of spectrum equivalence.** If every formula in `F.slice n` has
quantifier rank at most `α`, then `bfEquivSetoid L V (α + n)` refines `F.typeSpectrumSetoid V n`. -/
theorem bfEquivSetoid_le_typeSpectrumSetoid (F : Fragment L) (V : Type w) {n : ℕ}
    {α : Ordinal.{0}} (hF : ∀ φ ∈ F.slice n, φ.qrank ≤ α) :
    bfEquivSetoid L V (α + n) ≤ F.typeSpectrumSetoid V n := by
  intro c d hcd
  exact Fragment.typeSpectrumSetoid_iff.2
    ⟨exists_pointedType_eq_of_bfEquivSetoid hF hcd, fun b =>
      (exists_pointedType_eq_of_bfEquivSetoid hF ((bfEquivSetoid L V (α + n)).symm hcd) b).imp
        fun _ h => h.symm⟩

/-- **Uniform countable back-and-forth bound for a countable slice.** If `F.slice n` is countable,
some countable level `β < ω₁` has `bfEquivSetoid L V β ≤ F.typeSpectrumSetoid V n`. No countability
assumption on `L` or `V` is required. -/
theorem exists_lt_omega_one_bfEquivSetoid_le_typeSpectrumSetoid {F : Fragment L}
    (hF : (F.slice n).Countable) (V : Type w) :
    ∃ β : Ordinal.{o}, β < ω₁ ∧ bfEquivSetoid L V β ≤ F.typeSpectrumSetoid V n := by
  obtain ⟨α, hα, hlt⟩ := hF.exists_lt_omega_one_forall_lt fun φ _ => φ.qrank_lt_omega_one
  have hβ₀ : α + n < (ω₁ : Ordinal.{0}) :=
    Ordinal.isPrincipal_add_omega 1 hα ((Ordinal.natCast_lt_omega0 n).trans omega0_lt_omega_one)
  refine ⟨Ordinal.lift.{o, 0} (α + n), Ordinal.lift_lt_omega_one.mpr hβ₀, ?_⟩
  rw [bfEquivSetoid_lift]
  exact bfEquivSetoid_le_typeSpectrumSetoid F V fun φ hφ => (hlt φ hφ).le

/-- **Spectrum equivalence has Borel graph.** On a countable carrier `V`, whenever `F.slice n` is
countable, `F.typeSpectrumSetoid V n` has measurable graph in the product σ-algebra. No countability
assumption on `L` is needed. -/
theorem measurableSet_setOf_typeSpectrumSetoid [Countable V] {F : Fragment L}
    (hF : (F.slice n).Countable) :
    MeasurableSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      F.typeSpectrumSetoid V n p.1 p.2} := by
  have : Countable (F.slice n) := hF.to_subtype
  rw [measurableSet_setOfPred]
  simp only [Fragment.typeSpectrumSetoid_iff, funext_iff, eq_iff_iff]
  have hpair (a b : Fin n → V) :
      Measurable fun p : RelationalConfiguration L V × RelationalConfiguration L V =>
        ∀ φ : F.slice n, F.pointedType p.1 a φ ↔ F.pointedType p.2 b φ :=
    Measurable.forall fun φ =>
      (((measurable_pi_apply φ).comp ((F.measurable_pointedType_left a).comp measurable_fst)).iff
        ((measurable_pi_apply φ).comp ((F.measurable_pointedType_left b).comp measurable_snd)))
  exact (Measurable.forall fun a => Measurable.exists fun b => hpair a b).and
    (Measurable.forall fun b => Measurable.exists fun a => hpair a b)

/-- At arity `0`, `F.typeSpectrum 0 C` is countable if and only if `C` meets countably many classes
of `F.typeSpectrumSetoid V 0`. -/
theorem countable_typeSpectrum_zero_iff_countable_quotient {F : Fragment L}
    {C : Set (RelationalConfiguration L V)} :
    (F.typeSpectrum 0 C).Countable ↔
      Countable (Quotient ((F.typeSpectrumSetoid V 0).comap (Subtype.val : C → _))) := by
  have hker : (F.typeSpectrumSetoid V 0).comap (Subtype.val : C → _) =
      Setoid.ker fun c : C => F.pointedType c.val Fin.elim0 :=
    Setoid.ext fun _ _ => Fragment.typeSpectrumSetoid_zero_iff
  rw [F.typeSpectrum_zero, Set.image_eq_range, ← Set.countable_coe_iff, hker,
    (Setoid.quotientKerEquivRange _).countable_iff]

/-- On a countable carrier `V`, if `C` meets countably many classes of `F.typeSpectrumSetoid V n`,
then `F.typeSpectrum n C` is countable: each class contributes one countable realized-type set. -/
theorem countable_typeSpectrum_of_countable_quotient [Countable V] {F : Fragment L}
    {C : Set (RelationalConfiguration L V)}
    (h : Countable (Quotient ((F.typeSpectrumSetoid V n).comap (Subtype.val : C → _)))) :
    (F.typeSpectrum n C).Countable := by
  have hker : (F.typeSpectrumSetoid V n).comap (Subtype.val : C → _) =
      Setoid.ker fun c : C => c.val.realizedTypes F n :=
    Setoid.ext fun _ _ => Fragment.typeSpectrumSetoid_apply
  have hrange : (Set.range fun c : C => c.val.realizedTypes F n).Countable :=
    Set.countable_coe_iff.2 ((Setoid.quotientKerEquivRange _).symm.countable_iff.2 (hker ▸ h))
  rw [F.typeSpectrum_def, ← Set.sUnion_image, Set.image_eq_range]
  refine hrange.sUnion ?_
  rintro _ ⟨c, rfl⟩
  simpa only [realizedTypes_def] using @Fragment.countable_realizedTypes L F V c.val.toStructure _ n

/-- **Countable back-and-forth levels imply countable fragment spectra.** On a countable carrier
`V`, if `C` meets countably many classes at every countable back-and-forth level, then
`F.typeSpectrum n C` is countable whenever `F.slice n` is countable. Neither Borelness of `C` nor
countability of `L` is assumed. -/
theorem countable_typeSpectrum_of_countable_bfEquivSetoid [Countable V]
    {C : Set (RelationalConfiguration L V)} {F : Fragment L} (hF : (F.slice n).Countable)
    (hlevels : ∀ α : Ordinal.{o}, α < ω₁ →
      Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : C → _)))) :
    (F.typeSpectrum n C).Countable := by
  obtain ⟨β, hβ, hle⟩ := exists_lt_omega_one_bfEquivSetoid_le_typeSpectrumSetoid.{u, v, w, o} hF V
  have := hlevels β hβ
  have hcomap : (bfEquivSetoid L V β).comap (Subtype.val : C → _) ≤
      (F.typeSpectrumSetoid V n).comap Subtype.val := fun _ _ h => hle h
  exact countable_typeSpectrum_of_countable_quotient (Setoid.map_of_le_surjective hcomap).countable

/-! ### Silver dichotomies for spectrum equivalence on Borel classes -/

section SilverDichotomy

variable [Countable V] [∀ k, Countable (L.Relations k)]

/-- **Silver dichotomy for spectrum equivalence (Cantor form).** On a countable carrier in a
vocabulary with countably many relation symbols of each arity, if `C` is Borel and `F.slice n` is
countable, then either `C` meets countably many classes of `F.typeSpectrumSetoid V n` or `C` carries
a Cantor antichain of pairwise non-isomorphic configurations. -/
theorem countable_quotient_comap_typeSpectrumSetoid_or_hasCantorAntichainOn
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) {F : Fragment L}
    (hF : (F.slice n).Countable) :
    Countable (Quotient ((F.typeSpectrumSetoid V n).comap (Subtype.val : C → _))) ∨
      (isoSetoid L V).HasCantorAntichainOn C :=
  Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V)
    ((F.typeSpectrumSetoid V n).comap Subtype.val)
    (fun _ _ h => isoSetoid_le_typeSpectrumSetoid F V n h)
    ((measurableSet_setOf_typeSpectrumSetoid hF).preimage
      (measurable_subtypeVal.prodMap measurable_subtypeVal))

/-- **Silver dichotomy for spectrum equivalence (perfect-set form).** Under the same hypotheses,
`C` either meets countably many classes of `F.typeSpectrumSetoid V n` or contains a nonempty perfect
set of pairwise non-isomorphic configurations. -/
theorem countable_quotient_comap_typeSpectrumSetoid_or_hasPerfectAntichainOn
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) {F : Fragment L}
    (hF : (F.slice n).Countable) :
    Countable (Quotient ((F.typeSpectrumSetoid V n).comap (Subtype.val : C → _))) ∨
      (isoSetoid L V).HasPerfectAntichainOn C :=
  (countable_quotient_comap_typeSpectrumSetoid_or_hasCantorAntichainOn hC hF).imp_right
    Setoid.HasCantorAntichainOn.hasPerfectAntichainOn

/-- **Silver dichotomy for spectrum equivalence (cardinal form).** Under the same hypotheses,
`F.typeSpectrumSetoid V n` restricted to `C` has either at most `ℵ₀` or exactly `𝔠` classes. -/
theorem mk_quotient_comap_typeSpectrumSetoid_le_aleph0_or_eq_continuum
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) {F : Fragment L}
    (hF : (F.slice n).Countable) :
    #(Quotient ((F.typeSpectrumSetoid V n).comap (Subtype.val : C → _))) ≤ ℵ₀ ∨
      #(Quotient ((F.typeSpectrumSetoid V n).comap (Subtype.val : C → _))) = 𝔠 := by
  have := hC.standardBorel
  exact Setoid.mk_quotient_le_aleph0_or_eq_continuum ((F.typeSpectrumSetoid V n).comap Subtype.val)
    ((measurableSet_setOf_typeSpectrumSetoid hF).preimage
      (measurable_subtypeVal.prodMap measurable_subtypeVal))

/-- **Silver dichotomy for fragment type spectra (Cantor form).** On a countable carrier in a
vocabulary with countably many relation symbols of each arity, for Borel `C` and countable
`F.slice n`, either `F.typeSpectrum n C` is countable or `C` carries a Cantor antichain for
isomorphism. -/
theorem countable_typeSpectrum_or_hasCantorAntichainOn {C : Set (RelationalConfiguration L V)}
    (hC : MeasurableSet C) {F : Fragment L} (hF : (F.slice n).Countable) :
    (F.typeSpectrum n C).Countable ∨ (isoSetoid L V).HasCantorAntichainOn C :=
  (countable_quotient_comap_typeSpectrumSetoid_or_hasCantorAntichainOn hC hF).imp_left
    countable_typeSpectrum_of_countable_quotient

/-- **Silver dichotomy for fragment type spectra (perfect-set form).** Under the same hypotheses,
either `F.typeSpectrum n C` is countable or `C` contains a nonempty perfect set of pairwise
non-isomorphic configurations. -/
theorem countable_typeSpectrum_or_hasPerfectAntichainOn {C : Set (RelationalConfiguration L V)}
    (hC : MeasurableSet C) {F : Fragment L} (hF : (F.slice n).Countable) :
    (F.typeSpectrum n C).Countable ∨ (isoSetoid L V).HasPerfectAntichainOn C :=
  (countable_typeSpectrum_or_hasCantorAntichainOn hC hF).imp_right
    Setoid.HasCantorAntichainOn.hasPerfectAntichainOn

/-- **Thin Borel classes have countable fragment spectra.** On a countable carrier in a countable
relational vocabulary, if a Borel class `C` is thin for isomorphism, then `F.typeSpectrum n C` is
countable whenever `F.slice n` is countable. -/
theorem countable_typeSpectrum_of_isThinOn {C : Set (RelationalConfiguration L V)}
    (hC : MeasurableSet C) (hthin : (isoSetoid L V).IsThinOn C) {F : Fragment L}
    (hF : (F.slice n).Countable) :
    (F.typeSpectrum n C).Countable :=
  (countable_typeSpectrum_or_hasPerfectAntichainOn hC hF).resolve_right
    (Setoid.isThinOn_iff.1 hthin)

end SilverDichotomy

/-! ### Converse: countable fragment spectra bound back-and-forth quotients and force thinness -/

section Converse

/-- Canonical Scott formula of a tuple `a : Fin m → V` in the structure decoded from `c`. -/
private noncomputable def configScottFormula [Countable V] [∀ k, Countable (L.Relations k)]
    (c : RelationalConfiguration L V) {m : ℕ} (a : Fin m → V) (α : Ordinal.{o}) :
    L.BoundedFormulaω Empty m :=
  @scottFormula L _ V c.toStructure _ m a α

/-- Realization of `configScottFormula` in another configuration characterizes `BFEquiv` below
`ω₁`. -/
private theorem realize_configScottFormula_iff_bfEquiv [Countable V]
    [∀ k, Countable (L.Relations k)] (c d : RelationalConfiguration L V) {m : ℕ}
    (a b : Fin m → V) {α : Ordinal.{o}} (hα : α < ω₁) :
    @BoundedFormulaInf.Realize L ℕ Empty V d.toStructure m
        (configScottFormula c a α) Empty.elim b ↔
      @BFEquiv L _ V V c.toStructure d.toStructure α m a b :=
  @realize_scottFormula_iff_bfEquiv L _ V c.toStructure _ m _ V d.toStructure a b α hα

/-- If `F` has a countable `m`-type spectrum on `C` and agreement on `F.pointedType` forces
`BFEquiv α m`, then the depth-`α` tuple quotient on `C` is countable: choosing a representative of
each class injects the quotient into `F.typeSpectrum m C`. -/
private theorem countable_quotient_bfTupleSetoid_of_fragment
    {C : Set (RelationalConfiguration L V)} {F : Fragment L} {α : Ordinal.{o}} {m : ℕ}
    (hcount : (F.typeSpectrum m C).Countable)
    (hsep : ∀ (c d : C) (a b : Fin m → V),
      F.pointedType c.val a = F.pointedType d.val b →
        @BFEquiv L _ V V c.val.toStructure d.val.toStructure α m a b) :
    Countable (Quotient (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) α m)) := by
  have : Countable (F.typeSpectrum m C) := hcount.to_subtype
  let f : Quotient (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) α m) →
      F.typeSpectrum m C :=
    fun q => ⟨F.pointedType q.out.1.val q.out.2,
      F.pointedType_mem_typeSpectrum q.out.1.property q.out.2⟩
  refine Function.Injective.countable (f := f) fun q₁ q₂ hq => ?_
  rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
  exact Quotient.sound ((@bfTupleSetoid_apply L _ C (fun _ => V) (fun c => c.val.toStructure) α m
    q₁.out q₂.out).2 (hsep q₁.out.1 q₂.out.1 q₁.out.2 q₂.out.2 (congrArg Subtype.val hq)))

/-- Agreement on `Fragment.firstOrder L` forces depth-`0` back-and-forth equivalence. -/
private theorem bfEquiv_zero_of_firstOrder_pointedType_eq
    {c d : RelationalConfiguration L V} {m : ℕ} {a b : Fin m → V}
    (hab : (Fragment.firstOrder L).pointedType c a = (Fragment.firstOrder L).pointedType d b) :
    @BFEquiv L _ V V c.toStructure d.toStructure (0 : Ordinal.{o}) m a b := by
  rw [@BFEquiv.zero L _ V V c.toStructure d.toStructure m a b,
    @sameAtomicType_def L m V V c.toStructure d.toStructure]
  intro idx
  have hmem : idx.toFormula.toOmega ∈ (Fragment.firstOrder L).slice m :=
    Fragment.mem_slice.2 (Fragment.toOmega_mem_firstOrder idx.toFormula)
  simpa only [@BoundedFormula.realize_toInf L ℕ Empty V c.toStructure m,
    @BoundedFormula.realize_toInf L ℕ Empty V d.toStructure m,
    @AtomicIdx.realize_toFormula L m V c.toStructure,
    @AtomicIdx.realize_toFormula L m V d.toStructure] using
    Fragment.pointedType_eq_iff.1 hab _ hmem

/-- For the `bfTupleSetoid` class `q` of `⟨c, a⟩` at depth `β < ω₁`, realizing the representative's
canonical Scott formula at `(d, b)` is equivalent to `BFEquiv β k a b`. -/
private theorem realize_configScottFormula_out_mk_iff_bfEquiv [Countable V]
    [∀ k, Countable (L.Relations k)] {C : Set (RelationalConfiguration L V)} {β : Ordinal.{o}}
    (hβ : β < ω₁) {k : ℕ} (c : C) (d : RelationalConfiguration L V) (a b : Fin k → V) :
    let q := Quotient.mk (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) β k) ⟨c, a⟩
    @BoundedFormulaInf.Realize L ℕ Empty V d.toStructure k
        (configScottFormula q.out.1.val q.out.2 β) Empty.elim b ↔
      @BFEquiv L _ V V c.val.toStructure d.toStructure β k a b := by
  intro q
  have hq_a : @BFEquiv L _ V V q.out.1.val.toStructure c.val.toStructure β k q.out.2 a :=
    (@bfTupleSetoid_apply L _ C (fun _ => V) (fun c => c.val.toStructure) β k q.out ⟨c, a⟩).1
      (Quotient.exact (Quotient.out_eq q))
  rw [realize_configScottFormula_iff_bfEquiv q.out.1.val d q.out.2 b hβ]
  exact ⟨fun hq_b => @BFEquiv.trans L _ V V V c.val.toStructure q.out.1.val.toStructure
    d.toStructure k a q.out.2 b β
    (@BFEquiv.symm L _ V V q.out.1.val.toStructure c.val.toStructure k q.out.2 a β hq_a) hq_b,
    fun hab => @BFEquiv.trans L _ V V V q.out.1.val.toStructure c.val.toStructure d.toStructure
      k q.out.2 a b β hq_a hab⟩

/-- If `F` contains the canonical Scott formula of the depth-`β` class representative of `⟨c, a⟩`,
then agreement on `F.pointedType` forces `BFEquiv β k a b`. -/
private theorem bfEquiv_of_pointedType_eq [Countable V] [∀ k, Countable (L.Relations k)]
    {C : Set (RelationalConfiguration L V)} {β : Ordinal.{o}} (hβ : β < ω₁) {k : ℕ}
    {F : Fragment L} {c : C} {d : RelationalConfiguration L V} {a b : Fin k → V}
    (hmem : (⟨k, configScottFormula
      (Quotient.mk (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) β k)
        ⟨c, a⟩).out.1.val
      (Quotient.mk (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) β k)
        ⟨c, a⟩).out.2 β⟩ : Σ m, L.BoundedFormulaω Empty m) ∈ F)
    (hab : F.pointedType c.val a = F.pointedType d b) :
    @BFEquiv L _ V V c.val.toStructure d.toStructure β k a b :=
  (realize_configScottFormula_out_mk_iff_bfEquiv hβ c d a b).1 <|
    (Fragment.pointedType_eq_iff.1 hab _ (Fragment.mem_slice.2 hmem)).1 <|
      (realize_configScottFormula_out_mk_iff_bfEquiv hβ c c.val a a).2
        (@BFEquiv.refl L _ V c.val.toStructure k β a)

/-- At successor depth `α + 1`, a fragment containing a canonical Scott formula for each depth-`α`
`m`-tuple class and the one-variable existential closure of a canonical Scott formula for each
depth-`α` `(m + 1)`-tuple class separates all depth-`(α + 1)` `m`-tuple classes on `C`. -/
private theorem bfEquiv_add_one_of_pointedType_eq [Countable V] [∀ k, Countable (L.Relations k)]
    {C : Set (RelationalConfiguration L V)} {α : Ordinal.{o}} (hα : α < ω₁) {m : ℕ}
    {F : Fragment L}
    (hmem₀ : ∀ q : Quotient (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) α m),
      (⟨m, configScottFormula q.out.1.val q.out.2 α⟩ : Σ k, L.BoundedFormulaω Empty k) ∈ F)
    (hmem₁ :
      ∀ q : Quotient (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) α (m + 1)),
        (⟨m, (configScottFormula q.out.1.val q.out.2 α).ex⟩ : Σ k, L.BoundedFormulaω Empty k) ∈ F)
    (c d : C) (a b : Fin m → V) (hab : F.pointedType c.val a = F.pointedType d.val b) :
    @BFEquiv L _ V V c.val.toStructure d.val.toStructure (α + 1) m a b := by
  have hstep {c' d' : C} {u v : Fin m → V}
      (huv : F.pointedType c'.val u = F.pointedType d'.val v) (x : V) :
      ∃ y : V,
        @BFEquiv L _ V V c'.val.toStructure d'.val.toStructure α (m + 1)
          (Fin.snoc u x) (Fin.snoc v y) := by
    have hex_c := (@BoundedFormulaInf.realize_ex L ℕ Empty m V c'.val.toStructure Empty.elim u _).2
      ⟨x, (realize_configScottFormula_out_mk_iff_bfEquiv hα c' c'.val (Fin.snoc u x) _).2
        (@BFEquiv.refl L _ V c'.val.toStructure (m + 1) α _)⟩
    obtain ⟨y, hy⟩ :=
      (@BoundedFormulaInf.realize_ex L ℕ Empty m V d'.val.toStructure Empty.elim v _).1
        ((Fragment.pointedType_eq_iff.1 huv _ (Fragment.mem_slice.2 (hmem₁ _))).1 hex_c)
    exact ⟨y, (realize_configScottFormula_out_mk_iff_bfEquiv hα c' d'.val _ _).1 hy⟩
  refine (@BFEquiv.add_one L _ V V c.val.toStructure d.val.toStructure m α a b).2
    ⟨bfEquiv_of_pointedType_eq hα (hmem₀ _) hab, hstep hab, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hstep hab.symm y
  exact ⟨x, @BFEquiv.symm L _ V V d.val.toStructure c.val.toStructure (m + 1)
    (Fin.snoc b y) (Fin.snoc a x) α hx⟩

/-- **Countable fragment spectra bound all countable back-and-forth tuple quotients.** On a
countable carrier `V` in a vocabulary with countably many relation symbols of each arity, if
`F.typeSpectrum m C` is countable for every countable fragment `F` and every arity `m`, then
`bfTupleSetoid` on `C` has countably many classes at every countable depth `α < ω₁` and every arity
`n`. No Borelness or isomorphism invariance of `C` is required. -/
theorem countable_quotient_bfTupleSetoid_of_countable_typeSpectrum [Countable V]
    [∀ k, Countable (L.Relations k)] {C : Set (RelationalConfiguration L V)}
    (hspec : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ m : ℕ, (F.typeSpectrum m C).Countable)
    {α : Ordinal.{o}} (hα : α < ω₁) (n : ℕ) :
    Countable (Quotient (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) α n)) := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    -- Seed fragment: `Fragment.firstOrder L` (atomic formulas).
    exact countable_quotient_bfTupleSetoid_of_fragment
      (hspec (Fragment.firstOrder L) Fragment.firstOrder_countable n) fun _ _ _ _ =>
      bfEquiv_zero_of_firstOrder_pointedType_eq
  | add_one α ih =>
    -- Seed fragment: depth-`α` Scott formulas at arity `n` and existential closures at `n + 1`.
    have hα' : α < ω₁ := (Order.lt_add_one_iff.mpr le_rfl).trans hα
    have := ih hα' n
    have := ih hα' (n + 1)
    let Q₀ := Quotient (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) α n)
    let Q₁ := Quotient (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) α (n + 1))
    let seed : Set (Σ m, L.BoundedFormulaω Empty m) :=
      (Set.range fun q : Q₀ =>
        (⟨n, configScottFormula q.out.1.val q.out.2 α⟩ : Σ m, L.BoundedFormulaω Empty m)) ∪
        Set.range fun q : Q₁ =>
          (⟨n, (configScottFormula q.out.1.val q.out.2 α).ex⟩ : Σ m, L.BoundedFormulaω Empty m)
    have hseed : seed.Countable := (Set.countable_range _).union (Set.countable_range _)
    exact countable_quotient_bfTupleSetoid_of_fragment
      (hspec (Fragment.generated seed) (Fragment.generated_countable hseed) n)
      (bfEquiv_add_one_of_pointedType_eq hα'
        (fun q => Fragment.subset_generated seed (Or.inl ⟨q, rfl⟩))
        (fun q => Fragment.subset_generated seed (Or.inr ⟨q, rfl⟩)))
  | limit α hlim ih =>
    -- Seed fragment: depth-`β` Scott formulas across all `β < α`.
    have : Countable (Set.Iio α) := (Cardinal.countable_Iio_of_lt_omega_one hα).to_subtype
    have (β : Set.Iio α) :
        Countable (Quotient
          (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) β.val n)) :=
      ih β.val β.property (β.property.trans hα) n
    let idxType :=
      Σ β : Set.Iio α,
        Quotient (@bfTupleSetoid L _ C (fun _ => V) (fun c => c.val.toStructure) β.val n)
    let seed : Set (Σ m, L.BoundedFormulaω Empty m) :=
      Set.range fun p : idxType =>
        (⟨n, configScottFormula p.2.out.1.val p.2.out.2 p.1.val⟩ : Σ m, L.BoundedFormulaω Empty m)
    refine countable_quotient_bfTupleSetoid_of_fragment
      (hspec (Fragment.generated seed) (Fragment.generated_countable (Set.countable_range _)) n)
      fun c d a b hab =>
        (@BFEquiv.limit L _ V V c.val.toStructure d.val.toStructure n α hlim a b).2 fun β hβ =>
          bfEquiv_of_pointedType_eq (hβ.trans hα)
            (Fragment.subset_generated seed ⟨⟨⟨β, hβ⟩, _⟩, rfl⟩) hab

/-- On a countable carrier `V` in a vocabulary with countably many relation symbols of each arity,
if every countable fragment has countable type spectra on `C` at all arities, then `C` meets
countably many classes of `bfEquivSetoid L V α` at every countable level `α < ω₁`. -/
theorem countable_quotient_comap_bfEquivSetoid_of_countable_typeSpectrum [Countable V]
    [∀ k, Countable (L.Relations k)] {C : Set (RelationalConfiguration L V)}
    (hspec : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ m : ℕ, (F.typeSpectrum m C).Countable)
    {α : Ordinal.{o}} (hα : α < ω₁) :
    Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : C → _))) := by
  have := countable_quotient_bfTupleSetoid_of_countable_typeSpectrum hspec hα 0
  rw [comap_bfEquivSetoid_eq_comap_bfTupleSetoid]
  exact Countable.of_equiv _ (Setoid.comapQuotientEquiv _ _).symm

/-- **Countable fragment spectra forbid Cantor antichains.** On a countable carrier `V` in a
vocabulary with countably many relation symbols of each arity, if every countable fragment has a
countable type spectrum on `C` at every arity, then `C` carries no Cantor antichain for isomorphism.
No Borelness or invariance hypothesis on `C` is needed. -/
theorem not_hasCantorAntichainOn_of_countable_typeSpectrum [Countable V]
    [∀ k, Countable (L.Relations k)] {C : Set (RelationalConfiguration L V)}
    (hspec : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ m : ℕ, (F.typeSpectrum m C).Countable) :
    ¬ (isoSetoid L V).HasCantorAntichainOn C :=
  not_hasCantorAntichainOn_of_countable_bfEquivSetoid.{u, v, w, 0} fun _ hα =>
    countable_quotient_comap_bfEquivSetoid_of_countable_typeSpectrum hspec hα

/-- **Countable fragment spectra imply thinness.** Under the same hypotheses, `C` is thin for
isomorphism, without assuming `C` is Borel or isomorphism invariant. -/
theorem isThinOn_of_countable_typeSpectrum [Countable V] [∀ k, Countable (L.Relations k)]
    {C : Set (RelationalConfiguration L V)}
    (hspec : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ m : ℕ, (F.typeSpectrum m C).Countable) :
    (isoSetoid L V).IsThinOn C :=
  isThinOn_of_countable_bfEquivSetoid.{u, v, w, 0} fun _ hα =>
    countable_quotient_comap_bfEquivSetoid_of_countable_typeSpectrum hspec hα

/-- **Thin Borel classes are exactly those with countable fragment type spectra.** On a countable
carrier `V` in a vocabulary with countably many relation symbols of each arity, a Borel class `C` of
relational configurations is thin for isomorphism if and only if every countable fragment `F` has a
countable arity-`n` type spectrum on `C` for every `n : ℕ`. -/
theorem isThinOn_iff_countable_typeSpectrum [Countable V] [∀ k, Countable (L.Relations k)]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    (isoSetoid L V).IsThinOn C ↔
      ∀ F : Fragment L,
        (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
          ∀ n : ℕ, (F.typeSpectrum n C).Countable :=
  ⟨fun hthin F hF n => countable_typeSpectrum_of_isThinOn hC hthin (F.slice_countable hF n),
    isThinOn_of_countable_typeSpectrum⟩

end Converse

end TauCeti.RelationalConfiguration
