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

* `TauCeti.PermutationTriple.indexedDisjointSum` assembles an indexed family of triples after a
  numbering of the disjoint union of their labels.
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

variable {n N : ℕ}

/-! ### Indexed disjoint sums -/

/-- The disjoint sum of an indexed family of permutation triples, transported along a numbering
of the sigma type of their labels.  Unlike binary `disjointSum`, this construction permits the
summand degrees to vary with the index. -/
def indexedDisjointSum {I : Type*} {d : I → ℕ} (t : ∀ i, PermutationTriple (d i))
    (e : (Σ i, Fin (d i)) ≃ Fin N) : PermutationTriple N where
  σ0 := e.permCongr (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σ0)
  σ1 := e.permCongr (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σ1)
  σinf := e.permCongr (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σinf)
  product_eq_one := by
    have h :
        (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σinf) *
            (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σ1) *
            (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σ0) = 1 := by
      rw [sigmaCongrRight_mul, sigmaCongrRight_mul, ← sigmaCongrRight_one]
      congr 1
      funext i
      exact (t i).product_eq_one
    change e.permCongrHom _ * e.permCongrHom _ * e.permCongrHom _ = 1
    simpa only [map_mul, map_one] using congrArg e.permCongrHom h

variable {I : Type*} {d : I → ℕ} (t : ∀ i, PermutationTriple (d i))
  (e : (Σ i, Fin (d i)) ≃ Fin N)

@[simp] theorem indexedDisjointSum_σ0 : (indexedDisjointSum t e).σ0 =
    e.permCongr (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σ0) := (rfl)

@[simp] theorem indexedDisjointSum_σ1 : (indexedDisjointSum t e).σ1 =
    e.permCongr (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σ1) := (rfl)

@[simp] theorem indexedDisjointSum_σinf : (indexedDisjointSum t e).σinf =
    e.permCongr (Equiv.Perm.sigmaCongrRight fun i ↦ (t i).σinf) := (rfl)

/-! ### Restriction to monodromy orbits -/

/-- The finite type indexing the orbits of the monodromy group of a permutation triple. -/
abbrev MonodromyOrbit (t : PermutationTriple n) :=
  MulAction.orbitRel.Quotient t.monodromyGroup (Fin n)

/-- The action of the monodromy group on one of its orbits, transported to the finite ordinal
numbering that is used by `restrictToOrbit`. -/
noncomputable def orbitActionHom (t : PermutationTriple n) (O : MonodromyOrbit t) :
    t.monodromyGroup →* Perm (Fin O.orbit.ncard) :=
  (Finite.equivFin O.orbit).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom t.monodromyGroup O.orbit)

/-- Evaluating the transported orbit action and then undoing the finite numbering recovers the
original action on the orbit. -/
@[simp] theorem orbitActionHom_apply (t : PermutationTriple n) (O : MonodromyOrbit t)
    (g : t.monodromyGroup) (i : Fin O.orbit.ncard) :
    @Equiv.symm O.orbit (Fin O.orbit.ncard) (Finite.equivFin O.orbit)
        (t.orbitActionHom O g i) =
      g • (Finite.equivFin O.orbit).symm i := by
  change (Finite.equivFin O.orbit).symm
    ((Finite.equivFin O.orbit) (g • (Finite.equivFin O.orbit).symm i)) = _
  exact Equiv.symm_apply_apply _ _

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
  let a : t.monodromyGroup := ⟨t.σ0, t.σ0_mem_monodromyGroup⟩
  let b : t.monodromyGroup := ⟨t.σ1, t.σ1_mem_monodromyGroup⟩
  let c : t.monodromyGroup := ⟨t.σinf, t.σinf_mem_monodromyGroup⟩
  have hgen : Subgroup.closure ({a, b, c} : Set t.monodromyGroup) = ⊤ := by
    rw [← Subgroup.map_subtype_inj, MonoidHom.map_closure]
    rw [show t.monodromyGroup.subtype '' {a, b, c} = {t.σ0, t.σ1, t.σinf} by
      ext g
      simp [a, b, c]]
    rw [closure_triple_eq_monodromyGroup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  calc
    (t.restrictToOrbit O).monodromyGroup = Subgroup.closure
        {(t.restrictToOrbit O).σ0, (t.restrictToOrbit O).σ1,
          (t.restrictToOrbit O).σinf} := (closure_triple_eq_monodromyGroup _).symm
    _ = (t.orbitActionHom O).range := by
      change Subgroup.closure
        {t.orbitActionHom O a, t.orbitActionHom O b, t.orbitActionHom O c} = _
      rw [show {t.orbitActionHom O a, t.orbitActionHom O b, t.orbitActionHom O c} =
          t.orbitActionHom O '' {a, b, c} by
        ext g
        simp]
      rw [← MonoidHom.map_closure, hgen, MonoidHom.range_eq_map]

/-- Every monodromy-orbit restriction is connected. -/
theorem isConnected_restrictToOrbit : (t.restrictToOrbit O).IsConnected := by
  rw [isConnected_iff]
  constructor
  · rw [← Nat.card_coe_set_eq]
    exact Nat.card_ne_zero.mpr ⟨O.nonempty_orbit.to_subtype, inferInstance⟩
  · rw [monodromyGroup_restrictToOrbit]
    constructor
    intro i j
    let e : O.orbit ≃ Fin O.orbit.ncard := Finite.equivFin O.orbit
    obtain ⟨g, hg⟩ :=
      MulAction.exists_smul_eq t.monodromyGroup
        (e.symm i) (e.symm j)
    refine ⟨⟨t.orbitActionHom O g, ⟨g, rfl⟩⟩, ?_⟩
    change t.orbitActionHom O g i = j
    change e (g • e.symm i) = j
    simpa only [Equiv.apply_symm_apply] using
      congrArg e hg

/-! ### Reconstruction -/

/-- The numbering of the disjoint union of the numbered monodromy orbits induced by the
canonical orbit decomposition of the original labels. -/
noncomputable def orbitDecompositionEquiv (t : PermutationTriple n) :
    (Σ O : MonodromyOrbit t, Fin O.orbit.ncard) ≃ Fin n :=
  (Equiv.sigmaCongrRight fun (O : MonodromyOrbit t) ↦ (Finite.equivFin O.orbit).symm).trans
    (MulAction.selfEquivSigmaOrbits' t.monodromyGroup (Fin n)).symm

/-- The orbit-decomposition numbering agrees with the chosen numbering on each orbit. -/
@[simp] theorem orbitDecompositionEquiv_apply_val (t : PermutationTriple n)
    (O : MonodromyOrbit t) (i : Fin O.orbit.ncard) :
    (t.orbitDecompositionEquiv ⟨O, i⟩ : Fin n) = ((Finite.equivFin O.orbit).symm i : Fin n) := by
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
