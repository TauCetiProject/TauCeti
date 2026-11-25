/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Relabel
public import TauCeti.MeasureTheory.Constructions.Polish.Analytic
public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Isomorphism of relational configurations

For a relational language `L`, two configurations on a carrier `V` are isomorphic when the
structures they decode to are isomorphic. This is the equivalence relation whose classes are
counted when one counts the models of a sentence on a fixed carrier.

Relabelling a configuration by a permutation of `V` transports its decoded structure along that
permutation, and every isomorphism of decoded structures is such a relabelling. So isomorphism is
the orbit relation of the action of `Equiv.Perm V`, the *logic action*, on every carrier, finite
or infinite. Structures on different carriers, transported to `V` with `Equiv.encodeVia`, are
isomorphic exactly when their encodings are, and relabelling along a bijection of carriers
preserves and reflects isomorphism.

On a finite carrier the permutation group is finite and acts continuously, so the graph of
isomorphism is a finite union of graphs of continuous maps. It is therefore closed, and Borel in
a countable relational vocabulary. On a countable carrier the permutation group is Polish and
acts continuously, so the saturation of an analytic set under the logic action is analytic, for
every language, and with countably many relation symbols the orbit relation, hence the graph of
isomorphism, is analytic. The stabilizer of a configuration is the automorphism group of its
decoded structure.

A set of configurations is *isomorphism invariant* when it contains every configuration
isomorphic to one of its members. Equivalently, every permutation of the carrier maps it into
itself (Mathlib's `MulAction.IsInvariantBlock` for the logic action), or it equals its saturation
`Quotient.mk _ ⁻¹' (Quotient.mk _ '' A)` under isomorphism.

## Main definitions

* `TauCeti.RelationalConfiguration.isoSetoid L V` — isomorphism of decoded structures, as a setoid
  on the configurations on `V`.
* `TauCeti.RelationalConfiguration.IsomorphismInvariant` — a set of configurations closed under
  isomorphism.

## Main results

* `TauCeti.RelationalConfiguration.isoSetoid_iff_exists_perm_smul_eq` and
  `TauCeti.RelationalConfiguration.isoSetoid_eq_orbitRel` — isomorphism is the orbit relation of
  the relabelling action of `Equiv.Perm V`;
* `Equiv.isoSetoid_encodeVia_iff` — encodings of two structures on a common carrier are
  isomorphic exactly when the structures are;
* `TauCeti.RelationalConfiguration.isoSetoid_relabel_iff` — relabelling along a bijection of
  carriers preserves and reflects isomorphism;
* `TauCeti.RelationalConfiguration.isClosed_setOf_isoSetoid` and
  `TauCeti.RelationalConfiguration.measurableSet_setOf_isoSetoid` — on a finite carrier the graph
  of isomorphism is closed and Borel;
* `TauCeti.RelationalConfiguration.analyticSet_setOf_orbitRel` and
  `TauCeti.RelationalConfiguration.analyticSet_setOf_isoSetoid` — on a countable carrier, with
  countably many relation symbols, the orbit relation of the logic action is analytic for every
  language, and so is the graph of isomorphism;
* `TauCeti.RelationalConfiguration.isomorphismInvariant_iff_isInvariantBlock` and
  `TauCeti.RelationalConfiguration.isomorphismInvariant_iff_preimage_image_quotientMk` —
  isomorphism invariance is invariance under the logic action, and is equality with the
  saturation;
* `TauCeti.RelationalConfiguration.IsomorphismInvariant.image` — a bijection of coding spaces
  that preserves and reflects isomorphism carries invariant sets to invariant sets;
* `TauCeti.RelationalConfiguration.analyticSet_iUnion_smul` — on a countable carrier the
  saturation of an analytic set under the logic action is analytic, for every language;
* `TauCeti.RelationalConfiguration.mem_stabilizer_iff` — the stabilizer of a configuration is the
  automorphism group of its decoded structure.

## References

* Su Gao, *Invariant Descriptive Set Theory*, the logic action of the permutation group on the
  space of countable structures.
* Alexander S. Kechris, *Classical Descriptive Set Theory*.
-/

public section

universe u v u' v' w w' w''

open FirstOrder FirstOrder.Language MeasureTheory Set

open scoped Pointwise

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

variable (L V) in
/-- Isomorphism of decoded structures, as a setoid on the configurations on `V`: two
configurations are related when the structures they decode to are isomorphic. -/
def isoSetoid : Setoid (RelationalConfiguration L V) where
  r c d := Nonempty (@Language.Equiv L V V c.toStructure d.toStructure)
  iseqv :=
    { refl c := ⟨@Language.Equiv.refl L V c.toStructure⟩
      symm {c d} := fun ⟨f⟩ => ⟨@Language.Equiv.symm L V V c.toStructure d.toStructure f⟩
      trans {c d e} := fun ⟨f⟩ ⟨g⟩ =>
        ⟨@Language.Equiv.comp L V V c.toStructure d.toStructure V e.toStructure g f⟩ }

/-- Two configurations are isomorphic exactly when their decoded structures are. -/
theorem isoSetoid_apply {c d : RelationalConfiguration L V} :
    isoSetoid L V c d ↔ Nonempty (@Language.Equiv L V V c.toStructure d.toStructure) :=
  Iff.rfl

/-- Relabelling by `σ` encodes the decoded structure transported along `σ`. -/
theorem perm_smul_eq_encodeVia (σ : Equiv.Perm V) (c : RelationalConfiguration L V) :
    σ • c = @Equiv.encodeVia L V V c.toStructure σ := by
  rw [← relabel_perm, relabel_eq_encodeVia]

/-- Relabelling by `σ` decodes to the structure transported along `σ`. -/
@[simp]
theorem toStructure_perm_smul (σ : Equiv.Perm V) (c : RelationalConfiguration L V) :
    (σ • c).toStructure = @Equiv.inducedStructure L V V c.toStructure σ := by
  rw [perm_smul_eq_encodeVia]
  exact @Equiv.toStructure_encodeVia L V V c.toStructure _ σ

/-- A relabelled configuration is isomorphic to the original one. -/
theorem isoSetoid_perm_smul (σ : Equiv.Perm V) (c : RelationalConfiguration L V) :
    isoSetoid L V c (σ • c) := by
  rw [perm_smul_eq_encodeVia]
  exact @Equiv.nonempty_equiv_encodeVia L V V c.toStructure _ σ

/-- An isomorphism of decoded structures relabels the source configuration into the target. -/
private theorem toEquiv_smul {c d : RelationalConfiguration L V}
    (f : @Language.Equiv L V V c.toStructure d.toStructure) :
    @Language.Equiv.toEquiv L V V c.toStructure d.toStructure f • c = d := by
  ext a
  induction a using Atom.induction_atom with
  | h R x =>
    rw [eval_perm_smul, Atom.map_atom, Bool.eq_iff_iff, ← toStructure_relMap,
      ← toStructure_relMap]
    -- The inverse isomorphism `f.symm` has underlying bijection `f.toEquiv.symm`.
    exact @Language.Equiv.map_rel L V V d.toStructure c.toStructure
      (@Language.Equiv.symm L V V c.toStructure d.toStructure f) _ R x

/-- Isomorphism of configurations is relabelling by a permutation of the carrier. -/
theorem isoSetoid_iff_exists_perm_smul_eq {c d : RelationalConfiguration L V} :
    isoSetoid L V c d ↔ ∃ σ : Equiv.Perm V, σ • c = d :=
  ⟨fun ⟨f⟩ => ⟨_, toEquiv_smul f⟩, fun ⟨σ, hσ⟩ => hσ ▸ isoSetoid_perm_smul σ c⟩

/-- **The logic action.** Isomorphism of configurations is the orbit relation of the relabelling
action of the permutations of the carrier. -/
theorem isoSetoid_eq_orbitRel :
    isoSetoid L V = MulAction.orbitRel (Equiv.Perm V) (RelationalConfiguration L V) := by
  ext c d
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, ← (isoSetoid L V).comm',
    isoSetoid_iff_exists_perm_smul_eq]

/-- Structures transported to a common carrier have isomorphic encodings exactly when they are
isomorphic, whatever their universes. -/
theorem _root_.Equiv.isoSetoid_encodeVia_iff {M : Type w'} {N : Type w''} [L.Structure M]
    [L.Structure N] (e : M ≃ V) (f : N ≃ V) :
    isoSetoid L V (e.encodeVia (L := L)) (f.encodeVia (L := L)) ↔ Nonempty (M ≃[L] N) := by
  -- Compose with the isomorphisms `E : M ≃ e.encodeVia` and `F : N ≃ f.encodeVia`; the two
  -- decoded structures on `V` are not instances, so they are passed explicitly.
  set S := (e.encodeVia (L := L)).toStructure
  set T := (f.encodeVia (L := L)).toStructure
  obtain ⟨E⟩ := e.nonempty_equiv_encodeVia (L := L)
  obtain ⟨F⟩ := f.nonempty_equiv_encodeVia (L := L)
  rw [isoSetoid_apply]
  refine ⟨fun ⟨g⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact @Language.Equiv.comp L M V _ S N _
      (@Language.Equiv.comp L V V S T N _ (@Language.Equiv.symm L N V _ T F) g) E
  · exact @Language.Equiv.comp L V N S _ V T F
      (@Language.Equiv.comp L V M S _ N _ h (@Language.Equiv.symm L M V _ S E))

/-- Relabelling along a bijection of carriers preserves and reflects isomorphism. -/
@[simp]
theorem isoSetoid_relabel_iff {W : Type w'} (e : V ≃ W) {c d : RelationalConfiguration L V} :
    isoSetoid L W (relabel e c) (relabel e d) ↔ isoSetoid L V c d := by
  rw [relabel_eq_encodeVia, relabel_eq_encodeVia, isoSetoid_apply]
  exact @Equiv.isoSetoid_encodeVia_iff L _ W V V c.toStructure d.toStructure e e

/-- On a finite carrier the graph of isomorphism is closed: it is the union of the graphs of the
finitely many relabellings, each continuous. -/
theorem isClosed_setOf_isoSetoid [Finite V] :
    IsClosed {p : RelationalConfiguration L V × RelationalConfiguration L V |
      isoSetoid L V p.1 p.2} := by
  have h : {p : RelationalConfiguration L V × RelationalConfiguration L V |
      isoSetoid L V p.1 p.2} = ⋃ σ : Equiv.Perm V, {p | σ • p.1 = p.2} := by
    ext p
    simp [isoSetoid_iff_exists_perm_smul_eq]
  rw [h]
  exact isClosed_iUnion_of_finite fun σ =>
    isClosed_eq ((continuous_const_smul σ).comp continuous_fst) continuous_snd

/-- On a finite carrier, in a countable relational vocabulary, the graph of isomorphism is
Borel. -/
theorem measurableSet_setOf_isoSetoid [∀ n, Countable (L.Relations n)] [Finite V] :
    MeasurableSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      isoSetoid L V p.1 p.2} :=
  isClosed_setOf_isoSetoid.measurableSet

omit [L.IsRelational] in
/-- On a countable carrier, in a vocabulary with countably many relation symbols, the orbit
relation of the logic action is analytic, for every language: the permutation group of the
discrete carrier is Polish and acts continuously on the Polish coding space
(`MeasureTheory.analyticSet_setOf_orbitRel`). -/
theorem analyticSet_setOf_orbitRel [∀ n, Countable (L.Relations n)] [Countable V] :
    AnalyticSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      MulAction.orbitRel (Equiv.Perm V) _ p.1 p.2} := by
  let _ : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  exact MeasureTheory.analyticSet_setOf_orbitRel

/-- On a countable carrier, in a countable relational vocabulary, the graph of isomorphism is
analytic. -/
theorem analyticSet_setOf_isoSetoid [∀ n, Countable (L.Relations n)] [Countable V] :
    AnalyticSet {p : RelationalConfiguration L V × RelationalConfiguration L V |
      isoSetoid L V p.1 p.2} := by
  rw [isoSetoid_eq_orbitRel]
  exact analyticSet_setOf_orbitRel

/-! ### Isomorphism-invariant sets -/

/-- A set of configurations is **isomorphism invariant** when it contains every configuration
isomorphic to one of its members. -/
def IsomorphismInvariant (A : Set (RelationalConfiguration L V)) : Prop :=
  ∀ ⦃c d⦄, isoSetoid L V c d → c ∈ A → d ∈ A

variable {A B : Set (RelationalConfiguration L V)}

/-- Unfolding lemma for `IsomorphismInvariant`. -/
theorem isomorphismInvariant_iff :
    IsomorphismInvariant A ↔ ∀ ⦃c d⦄, isoSetoid L V c d → c ∈ A → d ∈ A :=
  Iff.rfl

/-- Isomorphic configurations lie in the same isomorphism-invariant sets. -/
theorem IsomorphismInvariant.mem_iff (hA : IsomorphismInvariant A)
    {c d : RelationalConfiguration L V} (h : isoSetoid L V c d) : c ∈ A ↔ d ∈ A :=
  ⟨hA h, hA ((isoSetoid L V).symm h)⟩

/-- **Isomorphism invariance is invariance under the logic action**: a set of configurations is
isomorphism invariant exactly when every permutation of the carrier maps it into itself. -/
theorem isomorphismInvariant_iff_isInvariantBlock :
    IsomorphismInvariant A ↔ MulAction.IsInvariantBlock (Equiv.Perm V) A := by
  refine ⟨fun hA σ => ?_, fun hA c d h hc => ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hA (isoSetoid_perm_smul σ c) hc
  · obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
    exact hA σ (smul_mem_smul_set hc)

/-- The saturation of a set under isomorphism is the union of its images under the logic
action. -/
theorem preimage_image_quotientMk_eq_iUnion_smul (A : Set (RelationalConfiguration L V)) :
    Quotient.mk (isoSetoid L V) ⁻¹' (Quotient.mk (isoSetoid L V) '' A) =
      ⋃ σ : Equiv.Perm V, σ • A := by
  rw [isoSetoid_eq_orbitRel]
  simp only [← image_smul]
  -- Mathlib states this with `Quotient.mk'`, which is `Quotient.mk` of the instance.
  exact MulAction.quotient_preimage_image_eq_union_mul A

/-- The preimage of any set of isomorphism classes is isomorphism invariant. -/
theorem isomorphismInvariant_preimage_quotientMk (s : Set (Quotient (isoSetoid L V))) :
    IsomorphismInvariant (Quotient.mk (isoSetoid L V) ⁻¹' s) :=
  fun _ _ h hc => by rwa [mem_preimage, ← Quotient.sound h]

/-- A set is isomorphism invariant exactly when it is its own saturation under isomorphism. -/
theorem isomorphismInvariant_iff_preimage_image_quotientMk :
    IsomorphismInvariant A ↔
      Quotient.mk (isoSetoid L V) ⁻¹' (Quotient.mk (isoSetoid L V) '' A) = A := by
  refine ⟨fun hA => (subset_preimage_image _ _).antisymm' ?_, fun h => ?_⟩
  · rintro d ⟨c, hc, hcd⟩
    exact hA (Quotient.exact hcd) hc
  · rw [← h]
    exact isomorphismInvariant_preimage_quotientMk _

/-- The union of the images of a set under the logic action is isomorphism invariant. -/
theorem isomorphismInvariant_iUnion_smul (A : Set (RelationalConfiguration L V)) :
    IsomorphismInvariant (⋃ σ : Equiv.Perm V, σ • A) := by
  rw [← preimage_image_quotientMk_eq_iUnion_smul]
  exact isomorphismInvariant_preimage_quotientMk _

/-- The empty set is isomorphism invariant. -/
@[simp]
theorem isomorphismInvariant_empty :
    IsomorphismInvariant (∅ : Set (RelationalConfiguration L V)) :=
  fun _ _ _ h => h

/-- The set of all configurations is isomorphism invariant. -/
@[simp]
theorem isomorphismInvariant_univ :
    IsomorphismInvariant (univ : Set (RelationalConfiguration L V)) :=
  fun _ _ _ _ => mem_univ _

/-- The complement of an isomorphism-invariant set is isomorphism invariant. -/
theorem IsomorphismInvariant.compl (hA : IsomorphismInvariant A) : IsomorphismInvariant Aᶜ :=
  fun _ _ h hc hd => hc (hA ((isoSetoid L V).symm h) hd)

/-- The intersection of two isomorphism-invariant sets is isomorphism invariant. -/
theorem IsomorphismInvariant.inter (hA : IsomorphismInvariant A) (hB : IsomorphismInvariant B) :
    IsomorphismInvariant (A ∩ B) :=
  fun _ _ h hc => ⟨hA h hc.1, hB h hc.2⟩

/-- The union of two isomorphism-invariant sets is isomorphism invariant. -/
theorem IsomorphismInvariant.union (hA : IsomorphismInvariant A) (hB : IsomorphismInvariant B) :
    IsomorphismInvariant (A ∪ B) :=
  fun _ _ h hc => hc.imp (hA h) (hB h)

/-- An intersection of isomorphism-invariant sets is isomorphism invariant. -/
theorem isomorphismInvariant_iInter {ι : Sort*} {A : ι → Set (RelationalConfiguration L V)}
    (hA : ∀ i, IsomorphismInvariant (A i)) : IsomorphismInvariant (⋂ i, A i) :=
  fun _ _ h hc => mem_iInter.2 fun i => hA i h (mem_iInter.1 hc i)

/-- A union of isomorphism-invariant sets is isomorphism invariant. -/
theorem isomorphismInvariant_iUnion {ι : Sort*} {A : ι → Set (RelationalConfiguration L V)}
    (hA : ∀ i, IsomorphismInvariant (A i)) : IsomorphismInvariant (⋃ i, A i) :=
  fun _ _ h hc => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hc
    exact mem_iUnion.2 ⟨i, hA i h hi⟩

/-- A bijection of coding spaces that preserves and reflects isomorphism carries
isomorphism-invariant sets to isomorphism-invariant sets. -/
theorem IsomorphismInvariant.image {L' : Language.{u', v'}} [L'.IsRelational] {W : Type w'}
    (f : RelationalConfiguration L V ≃ RelationalConfiguration L' W)
    (hf : ∀ c d, isoSetoid L' W (f c) (f d) ↔ isoSetoid L V c d) (hA : IsomorphismInvariant A) :
    IsomorphismInvariant (f '' A) := by
  rintro _ d h ⟨c, hc, rfl⟩
  obtain ⟨d, rfl⟩ := f.surjective d
  exact ⟨d, hA ((hf c d).1 h) hc, rfl⟩

/-- Relabelling along a bijection of carriers carries isomorphism-invariant classes to
isomorphism-invariant classes. -/
theorem IsomorphismInvariant.image_relabel {W : Type w'} (hA : IsomorphismInvariant A)
    (e : V ≃ W) : IsomorphismInvariant (relabel e '' A) :=
  hA.image (relabel e).toEquiv fun _ _ => isoSetoid_relabel_iff e

omit [L.IsRelational] in
/-- On a countable carrier the saturation of an analytic set of configurations under the logic
action is analytic, for every language: the permutation group of the discrete carrier is Polish
and acts continuously (`MeasureTheory.AnalyticSet.iUnion_smul`). -/
theorem analyticSet_iUnion_smul [Countable V] (hA : AnalyticSet A) :
    AnalyticSet (⋃ σ : Equiv.Perm V, σ • A) := by
  let _ : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  exact hA.iUnion_smul

/-! ### Stabilizers -/

/-- **Stabilizers are automorphism groups**: a permutation fixes a configuration under the logic
action exactly when it is an automorphism of the decoded structure. -/
theorem mem_stabilizer_iff (c : RelationalConfiguration L V) (σ : Equiv.Perm V) :
    σ ∈ MulAction.stabilizer (Equiv.Perm V) c ↔
      ∀ {l : ℕ} (R : L.Relations l) (v : Fin l → V),
        @Structure.RelMap L V c.toStructure l R (σ ∘ v) ↔
          @Structure.RelMap L V c.toStructure l R v := by
  rw [← inv_mem_iff, MulAction.mem_stabilizer_iff]
  refine ⟨fun h l R v => ?_, fun h => ext fun a => ?_⟩
  · rw [toStructure_relMap, toStructure_relMap]
    conv_rhs => rw [← h]
    rw [eval_perm_smul, Atom.map_atom]
    simp [Equiv.Perm.inv_def]
  · induction a using Atom.induction_atom with
    | h R x =>
      rw [eval_perm_smul, Atom.map_atom, Bool.eq_iff_iff, ← toStructure_relMap,
        ← toStructure_relMap]
      simpa [Equiv.Perm.inv_def] using h R x

end TauCeti.RelationalConfiguration
