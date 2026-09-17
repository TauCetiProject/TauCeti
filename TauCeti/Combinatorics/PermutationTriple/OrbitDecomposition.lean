/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.DisjointSum
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Decomposing permutation triples into connected components

Every permutation triple restricts to each orbit of its monodromy group.  After numbering the
points in every orbit, the original triple is the indexed disjoint sum of these restrictions.
Thus the monodromy orbits are precisely the connected summands of a possibly disconnected
triple.

The construction uses `MulAction.selfEquivSigmaOrbits'` for the canonical decomposition of the
set of labels into its orbits.  The only choices are the finite numberings within the individual
orbits; the final reconstruction theorem is an equality because the global numbering is assembled
from those same choices.

## Main results

* `TauCeti.PermutationTriple.restrictToOrbit` restricts a triple to one monodromy orbit and
  numbers that orbit by a finite ordinal.
* `TauCeti.PermutationTriple.isConnected_restrictToOrbit` proves that every such restriction is
  connected.
* `TauCeti.PermutationTriple.indexedDisjointSum_restrictToOrbit` reconstructs the original triple
  from all its orbit restrictions.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n : ℕ}

/-! ### Restriction to monodromy orbits -/

/-- The finite type indexing the orbits of the monodromy group of a permutation triple. -/
abbrev MonodromyOrbit (t : PermutationTriple n) :=
  MulAction.orbitRel.Quotient t.monodromyGroup (Fin n)

/-- The action of the monodromy group on one of its orbits, transported to the finite ordinal
numbering that is used by `restrictToOrbit`. -/
noncomputable def orbitActionHom (t : PermutationTriple n) (O : MonodromyOrbit t) :
    t.monodromyGroup →* Perm (Fin O.orbit.ncard) :=
  (Finite.equivFinOfCardEq (Nat.card_coe_set_eq O.orbit)).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom t.monodromyGroup O.orbit)

/-- Evaluating the transported orbit action and then undoing the finite numbering recovers the
original action on the orbit. -/
@[simp] theorem orbitActionHom_apply (t : PermutationTriple n) (O : MonodromyOrbit t)
    (g : t.monodromyGroup) (i : Fin O.orbit.ncard) :
    (Finite.equivFinOfCardEq (Nat.card_coe_set_eq O.orbit)).symm
        (t.orbitActionHom O g i) =
      g • (Finite.equivFinOfCardEq (Nat.card_coe_set_eq O.orbit)).symm i := by
  simp [orbitActionHom]

/-- The restriction of a permutation triple to a monodromy orbit, numbered by
`Fin O.orbit.ncard`. -/
noncomputable def restrictToOrbit (t : PermutationTriple n) (O : MonodromyOrbit t) :
    PermutationTriple O.orbit.ncard where
  σ0 := t.orbitActionHom O ⟨t.σ0, t.σ0_mem_monodromyGroup⟩
  σ1 := t.orbitActionHom O ⟨t.σ1, t.σ1_mem_monodromyGroup⟩
  σinf := t.orbitActionHom O ⟨t.σinf, t.σinf_mem_monodromyGroup⟩
  product_eq_one := by
    rw [← map_mul, ← map_mul]
    convert map_one (t.orbitActionHom O) using 2
    exact Subtype.ext t.product_eq_one

variable (t : PermutationTriple n) (O : MonodromyOrbit t)

@[simp] theorem restrictToOrbit_σ0 : (t.restrictToOrbit O).σ0 =
    t.orbitActionHom O ⟨t.σ0, t.σ0_mem_monodromyGroup⟩ := (rfl)

@[simp] theorem restrictToOrbit_σ1 : (t.restrictToOrbit O).σ1 =
    t.orbitActionHom O ⟨t.σ1, t.σ1_mem_monodromyGroup⟩ := (rfl)

@[simp] theorem restrictToOrbit_σinf : (t.restrictToOrbit O).σinf =
    t.orbitActionHom O ⟨t.σinf, t.σinf_mem_monodromyGroup⟩ := (rfl)

/-- The monodromy group of an orbit restriction is the image of the original monodromy group on
that orbit. -/
theorem monodromyGroup_restrictToOrbit :
    (t.restrictToOrbit O).monodromyGroup = (t.orbitActionHom O).range := by
  have hgen : Subgroup.closure ({⟨t.σ0, t.σ0_mem_monodromyGroup⟩, ⟨t.σ1, t.σ1_mem_monodromyGroup⟩,
      ⟨t.σinf, t.σinf_mem_monodromyGroup⟩} : Set t.monodromyGroup) = ⊤ := by
    rw [← Subgroup.map_subtype_inj, MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype]
    rw [closure_triple_eq_monodromyGroup, ← MonoidHom.range_eq_map]
    simp
  refine (closure_triple_eq_monodromyGroup _).symm.trans ?_
  rw [restrictToOrbit_σ0, restrictToOrbit_σ1, restrictToOrbit_σinf]
  simp only [← Set.image_singleton, ← Set.image_insert_eq]
  rw [← MonoidHom.map_closure, hgen, MonoidHom.range_eq_map]

/-- Every monodromy-orbit restriction is connected. -/
theorem isConnected_restrictToOrbit : (t.restrictToOrbit O).IsConnected := by
  rw [isConnected_iff]
  constructor
  · exact Nat.card_ne_zero.mpr ⟨O.nonempty_orbit.to_subtype, inferInstance⟩
  · rw [monodromyGroup_restrictToOrbit]
    constructor
    intro i j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq t.monodromyGroup
      ((Finite.equivFinOfCardEq (Nat.card_coe_set_eq O.orbit)).symm i)
      ((Finite.equivFinOfCardEq (Nat.card_coe_set_eq O.orbit)).symm j)
    refine ⟨⟨t.orbitActionHom O g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩,
      (Finite.equivFinOfCardEq (Nat.card_coe_set_eq O.orbit)).symm.injective ?_⟩
    rw [Submonoid.mk_smul, Perm.smul_def, orbitActionHom_apply, hg]

/-! ### Reconstruction -/

/-- The numbering of the disjoint union of the numbered monodromy orbits induced by the
canonical orbit decomposition of the original labels. -/
noncomputable def orbitDecompositionEquiv (t : PermutationTriple n) :
    (Σ O : MonodromyOrbit t, Fin O.orbit.ncard) ≃ Fin n :=
  (Equiv.sigmaCongrRight fun (O : MonodromyOrbit t) ↦
      (Finite.equivFinOfCardEq (Nat.card_coe_set_eq O.orbit)).symm).trans
    (MulAction.selfEquivSigmaOrbits' t.monodromyGroup (Fin n)).symm

/-- The orbit-decomposition numbering agrees with the chosen numbering on each orbit. -/
@[simp] theorem orbitDecompositionEquiv_apply_val (t : PermutationTriple n)
    (O : MonodromyOrbit t) (i : Fin O.orbit.ncard) :
    (t.orbitDecompositionEquiv ⟨O, i⟩ : Fin n) =
      ((Finite.equivFinOfCardEq (Nat.card_coe_set_eq O.orbit)).symm i : Fin n) := by
  rfl

/-- A permutation triple is the indexed disjoint sum of its restrictions to the orbits of its
monodromy group.  In particular, every summand is connected by
`isConnected_restrictToOrbit`. -/
@[simp] theorem indexedDisjointSum_restrictToOrbit (t : PermutationTriple n) :
    indexedDisjointSum (fun O : MonodromyOrbit t ↦ t.restrictToOrbit O)
      t.orbitDecompositionEquiv = t := by
  apply ext_of_two
  · apply Equiv.ext
    intro x
    obtain ⟨⟨O, i⟩, rfl⟩ := t.orbitDecompositionEquiv.surjective x
    simp only [indexedDisjointSum_σ0, Equiv.permCongr_apply, Equiv.symm_apply_apply,
      Equiv.sigmaCongrRight_apply]
    rw [orbitDecompositionEquiv_apply_val, orbitDecompositionEquiv_apply_val]
    apply Fin.ext
    rw [restrictToOrbit_σ0]
    exact congrArg Fin.val (congrArg Subtype.val
      (orbitActionHom_apply t O ⟨t.σ0, t.σ0_mem_monodromyGroup⟩ i))
  · apply Equiv.ext
    intro x
    obtain ⟨⟨O, i⟩, rfl⟩ := t.orbitDecompositionEquiv.surjective x
    simp only [indexedDisjointSum_σ1, Equiv.permCongr_apply, Equiv.symm_apply_apply,
      Equiv.sigmaCongrRight_apply]
    rw [orbitDecompositionEquiv_apply_val, orbitDecompositionEquiv_apply_val]
    apply Fin.ext
    rw [restrictToOrbit_σ1]
    exact congrArg Fin.val (congrArg Subtype.val
      (orbitActionHom_apply t O ⟨t.σ1, t.σ1_mem_monodromyGroup⟩ i))

end PermutationTriple

end TauCeti
