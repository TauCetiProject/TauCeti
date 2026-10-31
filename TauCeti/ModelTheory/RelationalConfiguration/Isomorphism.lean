/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Structure
public import TauCeti.ModelTheory.RelationalConfiguration.Topology

/-!
# Isomorphism of relational configurations

For a relational language `L`, two configurations on a carrier `V` are isomorphic when the
structures they decode to are isomorphic. This is the equivalence relation whose classes are
counted when one counts the models of a sentence on a fixed carrier.

Relabelling a configuration by a permutation of `V` transports its decoded structure along that
permutation, and every isomorphism of decoded structures is such a relabelling. So isomorphism is
the orbit relation of the action of `Equiv.Perm V`, the *logic action*, on every carrier, finite
or infinite. Structures on different carriers, transported to `V` with `Equiv.encodeVia`, are
isomorphic exactly when their encodings are.

On a finite carrier the permutation group is finite and acts continuously, so the graph of
isomorphism is a finite union of graphs of continuous maps. It is therefore closed, and Borel in
a countable relational vocabulary.

## Main definitions

* `TauCeti.RelationalConfiguration.isoSetoid L V` — isomorphism of decoded structures, as a setoid
  on the configurations on `V`.

## Main results

* `TauCeti.RelationalConfiguration.isoSetoid_iff_exists_perm_smul_eq` and
  `TauCeti.RelationalConfiguration.isoSetoid_eq_orbitRel` — isomorphism is the orbit relation of
  the relabelling action of `Equiv.Perm V`;
* `Equiv.isoSetoid_encodeVia_iff` — encodings of two structures on a common carrier are
  isomorphic exactly when the structures are;
* `TauCeti.RelationalConfiguration.isClosed_setOf_isoSetoid` and
  `TauCeti.RelationalConfiguration.measurableSet_setOf_isoSetoid` — on a finite carrier the graph
  of isomorphism is closed and Borel.

## References

* Su Gao, *Invariant Descriptive Set Theory*, the logic action of the permutation group on the
  space of countable structures.
* Alexander S. Kechris, *Classical Descriptive Set Theory*.
-/

public section

universe u v w w' w''

open FirstOrder FirstOrder.Language

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
  classical
  let := c.toStructure
  ext a
  induction a using Atom.induction_atom with
  | h R x => simp

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

end TauCeti.RelationalConfiguration
