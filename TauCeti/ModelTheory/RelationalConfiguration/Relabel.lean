/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Structure
public import TauCeti.ModelTheory.RelationalConfiguration.Topology

/-!
# Relabelling configurations along a bijection of carriers

A bijection `e : α ≃ β` of carriers relabels configurations on `α` as configurations on `β`: the
atom `R(w)` of the relabelled configuration takes the value of the atom `R(e.symm ∘ w)`. The
underlying map is restriction along `e.symm`. Bundled, relabelling is a homeomorphism and a
measurable equivalence of configuration spaces, for every language and every pair of carriers,
with inverse the relabelling along `e.symm`; it is functorial in `e`, and along a permutation of
one carrier it is the logic action.

For a relational language, relabelling along `e` encodes the decoded structure transported along
`e` (`Equiv.encodeVia`), so a configuration and its relabelling decode to isomorphic structures on
the two carriers. This lets classes of configurations be moved between carriers, for instance
from a countably infinite set of vertices built by a coding to `ℕ`, without changing their
isomorphism relations up to Borel bireducibility.

## Main definitions

* `TauCeti.RelationalConfiguration.relabel e`: relabelling along `e : α ≃ β`, as a homeomorphism.
* `TauCeti.RelationalConfiguration.relabelMeasurableEquiv e`: relabelling along `e`, as a
  measurable equivalence.

## Main results

* `TauCeti.RelationalConfiguration.relabel_trans`,
  `TauCeti.RelationalConfiguration.relabel_relabel` and
  `TauCeti.RelationalConfiguration.relabel_refl`: relabelling is functorial.
* `TauCeti.RelationalConfiguration.relabel_perm`: along a permutation it is the logic action.
* `TauCeti.RelationalConfiguration.relabel_eq_encodeVia`: it encodes the transported decoded
  structure.
* `TauCeti.RelationalConfiguration.nonempty_equiv_relabel`: a configuration and its relabelling
  decode to isomorphic structures.

## References

* H. Becker and A. S. Kechris, *Borel actions of Polish groups*, Bull. Amer. Math. Soc. 28
  (1993), §2 (the logic action, which reads a configuration at the image of each tuple under the
  inverse permutation).
-/

public section

universe u v w w' w''

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-- **Relabelling** along a bijection `e : α ≃ β` of carriers: the atom `R(w)` of the relabelled
configuration takes the value of the atom `R(e.symm ∘ w)`. It is restriction along `e.symm`, a
homeomorphism of configuration spaces with inverse the relabelling along `e.symm`. -/
def relabel (e : α ≃ β) : RelationalConfiguration L α ≃ₜ RelationalConfiguration L β where
  toFun := restrict e.symm
  invFun := restrict e
  left_inv c := by rw [← restrict_comp, e.symm_comp_self, restrict_id]
  right_inv c := by rw [← restrict_comp, e.self_comp_symm, restrict_id]
  continuous_toFun := continuous_restrict _
  continuous_invFun := continuous_restrict _

/-- Relabelling along `e` is restriction along `e.symm`. -/
theorem coe_relabel (e : α ≃ β) : ⇑(relabel (L := L) e) = restrict e.symm :=
  (rfl)

/-- The relabelled configuration reads each atom at its relabelling along `e.symm`. -/
@[simp]
theorem eval_relabel (e : α ≃ β) (c : RelationalConfiguration L α) (a : Atom L β) :
    (relabel e c).eval a = c.eval (a.map e.symm) := by
  rw [coe_relabel, eval_restrict]

/-- The inverse of relabelling along `e` is relabelling along `e.symm`. -/
@[simp]
theorem relabel_symm (e : α ≃ β) : (relabel (L := L) e).symm = relabel e.symm :=
  Homeomorph.ext fun _ => (rfl)

/-- Relabelling along the identity is the identity. -/
@[simp]
theorem relabel_refl : relabel (L := L) (Equiv.refl α) = Homeomorph.refl _ :=
  Homeomorph.ext fun c => by simp [coe_relabel]

/-- Relabelling along `e` and then along `e'` is relabelling along the composite bijection. -/
@[simp]
theorem relabel_relabel (e : α ≃ β) (e' : β ≃ γ) (c : RelationalConfiguration L α) :
    relabel e' (relabel e c) = relabel (e.trans e') c := by
  simp [coe_relabel, restrict_comp]

/-- Relabelling along a composite bijection is the composite of the relabellings. -/
theorem relabel_trans (e : α ≃ β) (e' : β ≃ γ) :
    relabel (L := L) (e.trans e') = (relabel e).trans (relabel e') :=
  Homeomorph.ext fun c => (relabel_relabel e e' c).symm

/-- Relabelling along `e.symm` undoes relabelling along `e`. Not `@[simp]`: `relabel_relabel`,
`Equiv.self_trans_symm` and `relabel_refl` already simplify the round trip. -/
theorem relabel_symm_relabel (e : α ≃ β) (c : RelationalConfiguration L α) :
    relabel e.symm (relabel e c) = c :=
  (relabel e).symm_apply_apply c

/-- Relabelling along `e` undoes relabelling along `e.symm`. Not `@[simp]`: `relabel_relabel`,
`Equiv.symm_trans_self` and `relabel_refl` already simplify the round trip. -/
theorem relabel_relabel_symm (e : α ≃ β) (c : RelationalConfiguration L β) :
    relabel e (relabel e.symm c) = c :=
  (relabel e).apply_symm_apply c

/-- Relabelling along a permutation of the carrier is the logic action. Not `@[simp]`: it would
fire on every `relabel e c` with `e : α ≃ α`, before `relabel_relabel` can simplify round trips,
so `relabel` stays the simp normal form. -/
theorem relabel_perm (σ : Equiv.Perm α) (c : RelationalConfiguration L α) :
    relabel σ c = σ • c := by
  rw [perm_smul_def, Equiv.Perm.inv_def, coe_relabel]

/-- Relabelling is measurable for the product σ-algebras, on every pair of carriers. -/
@[fun_prop]
theorem measurable_relabel (e : α ≃ β) : Measurable (relabel (L := L) e) :=
  measurable_restrict _

/-- Relabelling along `e`, as a measurable equivalence of configuration spaces with inverse the
relabelling along `e.symm`. -/
def relabelMeasurableEquiv (e : α ≃ β) :
    RelationalConfiguration L α ≃ᵐ RelationalConfiguration L β where
  toEquiv := (relabel e).toEquiv
  measurable_toFun := measurable_relabel e
  measurable_invFun := measurable_relabel e.symm

/-- The measurable equivalence relabels along `e`. -/
@[simp]
theorem coe_relabelMeasurableEquiv (e : α ≃ β) :
    ⇑(relabelMeasurableEquiv (L := L) e) = relabel e :=
  (rfl)

/-- The inverse of the measurable equivalence relabels along `e.symm`. -/
@[simp]
theorem coe_relabelMeasurableEquiv_symm (e : α ≃ β) :
    ⇑(relabelMeasurableEquiv (L := L) e).symm = relabel e.symm :=
  (rfl)

/-- The relabelling of a class along a bijection of carriers is measurable exactly when the class
is. -/
@[simp]
theorem measurableSet_image_relabel_iff (e : α ≃ β) {K : Set (RelationalConfiguration L α)} :
    MeasurableSet (relabel e '' K) ↔ MeasurableSet K := by
  simpa using (relabelMeasurableEquiv (L := L) e).measurableSet_image (s := K)

variable [L.IsRelational]

/-- Relabelling along `e` encodes the decoded structure transported along `e`. -/
theorem relabel_eq_encodeVia (e : α ≃ β) (c : RelationalConfiguration L α) :
    relabel e c = @Equiv.encodeVia L α β c.toStructure e := by
  classical
  let := c.toStructure
  ext a
  induction a using Atom.induction_atom with
  | h R x => simp

/-- A configuration on `α` and its relabelling on `β` decode to isomorphic structures. -/
theorem nonempty_equiv_relabel (e : α ≃ β) (c : RelationalConfiguration L α) :
    Nonempty (@Language.Equiv L α β c.toStructure (relabel e c).toStructure) := by
  rw [relabel_eq_encodeVia]
  exact @Equiv.nonempty_equiv_encodeVia L α β c.toStructure _ e

end TauCeti.RelationalConfiguration
