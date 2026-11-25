/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
public import TauCeti.ModelTheory.Scott.NatPredicate

/-!
# Regression examples: Borel completeness

Regression examples for Borel completeness of classes of codes.

* In the language `TauCeti.natPredicateLanguage` of countably many unary predicates `P_i`, the
  class `constantClass` of codes in which each `P_i` is `∅` or `ℕ` is closed and isomorphism
  invariant, and its isomorphism types are in bijection with `ℕ → Bool`. Hence a Borel complete
  class has uncountably many isomorphism types.
* A class containing a Borel complete class, such as `K ∪ K₂`, is Borel complete.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration.BorelCompleteChecks

/-! ### Countably many unary predicates -/

/-- The atom `P_i(v)` of `natPredicateLanguage`. -/
def unaryAtom (i v : ℕ) : Atom natPredicateLanguage ℕ :=
  atom (NatPredicateRel.pred i) ![v]

/-- Relabelling the atom `P_i(v)` along `f` gives `P_i(f v)`. -/
@[simp]
theorem map_unaryAtom (f : ℕ → ℕ) (i v : ℕ) : (unaryAtom i v).map f = unaryAtom i (f v) :=
  Atom.map_atom_unary f _ v

/-- Every atom of `natPredicateLanguage` is some `P_i(v)`. -/
theorem exists_eq_unaryAtom (a : Atom natPredicateLanguage ℕ) : ∃ i v, a = unaryAtom i v := by
  induction a using Atom.induction_atom with
  | h R x =>
    cases R with
    | pred i =>
      refine ⟨i, x 0, ?_⟩
      rw [unaryAtom, Matrix.vec_single_eq_const]
      exact congrArg (atom _) (funext fun j => congrArg x (Subsingleton.elim j 0))

/-- The class of codes of `natPredicateLanguage` on `ℕ` in which each `P_i` is `∅` or `ℕ`. -/
def constantClass : Set (RelationalConfiguration natPredicateLanguage ℕ) :=
  {c | ∀ i v w, c.eval (unaryAtom i v) = c.eval (unaryAtom i w)}

/-- A code lies in `constantClass` when each `P_i` takes the same value at all points. -/
theorem mem_constantClass_iff {c : RelationalConfiguration natPredicateLanguage ℕ} :
    c ∈ constantClass ↔ ∀ i v w, c.eval (unaryAtom i v) = c.eval (unaryAtom i w) :=
  Iff.rfl

/-- The truth values of `P_0, P_1, …` at the point `0`. -/
def truthValues (c : RelationalConfiguration natPredicateLanguage ℕ) : ℕ → Bool :=
  fun i => c.eval (unaryAtom i 0)

/-- The `i`th truth value of a code is the value of `P_i` at `0`. -/
theorem truthValues_apply (c : RelationalConfiguration natPredicateLanguage ℕ) (i : ℕ) :
    truthValues c i = c.eval (unaryAtom i 0) :=
  (rfl)

/-- The value `f i` on the symbol `P_i`. -/
private def symbolValue (f : ℕ → Bool) : (Σ n, natPredicateLanguage.Relations n) → Bool
  | ⟨_, .pred i⟩ => f i

/-- The code in which `P_i` is `ℕ` when `f i` holds and `∅` otherwise. -/
def ofTruthValues (f : ℕ → Bool) : RelationalConfiguration natPredicateLanguage ℕ :=
  mk fun a => symbolValue f a.symbol

/-- The code `ofTruthValues f` reads `f i` at every atom `P_i(v)`. -/
@[simp]
theorem eval_ofTruthValues (f : ℕ → Bool) (i v : ℕ) :
    (ofTruthValues f).eval (unaryAtom i v) = f i := by
  rw [ofTruthValues, eval_mk, unaryAtom,
    Atom.symbol_atom (L := natPredicateLanguage) (NatPredicateRel.pred i), symbolValue]

/-- The truth values of `ofTruthValues f` are `f`. -/
@[simp]
theorem truthValues_ofTruthValues (f : ℕ → Bool) : truthValues (ofTruthValues f) = f :=
  funext fun i => eval_ofTruthValues f i 0

/-- The code `ofTruthValues f` lies in `constantClass`. -/
theorem ofTruthValues_mem_constantClass (f : ℕ → Bool) : ofTruthValues f ∈ constantClass :=
  fun _ _ _ => by rw [eval_ofTruthValues, eval_ofTruthValues]

/-- A code in `constantClass` is determined by its truth values. -/
theorem eq_of_truthValues_eq {c d : RelationalConfiguration natPredicateLanguage ℕ}
    (hc : c ∈ constantClass) (hd : d ∈ constantClass) (h : truthValues c = truthValues d) :
    c = d := by
  ext a
  obtain ⟨i, v, rfl⟩ := exists_eq_unaryAtom a
  rw [hc i v 0, hd i v 0]
  exact congrFun h i

/-- `constantClass` is closed. -/
theorem isClosed_constantClass : IsClosed constantClass := by
  simp only [constantClass, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun v => isClosed_iInter fun w =>
    isClosed_eq (continuous_eval _) (continuous_eval _)

/-- `constantClass` is Borel. -/
theorem measurableSet_constantClass : MeasurableSet constantClass :=
  isClosed_constantClass.measurableSet

/-- Relabelling preserves the truth values of a code in `constantClass`. -/
theorem truthValues_perm_smul {c : RelationalConfiguration natPredicateLanguage ℕ}
    (hc : c ∈ constantClass) (σ : Equiv.Perm ℕ) : truthValues (σ • c) = truthValues c := by
  funext i
  rw [truthValues, eval_perm_smul, map_unaryAtom]
  exact hc i _ 0

/-- `constantClass` is isomorphism invariant. -/
theorem isomorphismInvariant_constantClass : IsomorphismInvariant constantClass := by
  rw [isomorphismInvariant_iff]
  intro c d h hc i v w
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  rw [eval_perm_smul, eval_perm_smul, map_unaryAtom, map_unaryAtom]
  exact hc i _ _

/-- Two codes in `constantClass` are isomorphic exactly when they have the same truth values. -/
theorem classIso_constantClass_iff {c d : constantClass} :
    classIso constantClass c d ↔ truthValues c = truthValues d := by
  rw [classIso_apply, isoSetoid_iff_exists_perm_smul_eq]
  refine ⟨fun ⟨σ, h⟩ => ?_, fun h => ⟨1, ?_⟩⟩
  · rw [← h, truthValues_perm_smul c.property]
  · rw [one_smul, eq_of_truthValues_eq c.property d.property h]

/-- **The isomorphism types of `constantClass` are the points of `ℕ → Bool`.** -/
def quotientClassIsoConstantClassEquiv :
    Quotient (classIso constantClass) ≃ (ℕ → Bool) :=
  (Quotient.congr (Equiv.refl _) fun _ _ =>
    classIso_constantClass_iff.trans Setoid.ker_def.symm).trans
    (Setoid.quotientKerEquivOfRightInverse (truthValues ∘ Subtype.val)
      (fun f => ⟨ofTruthValues f, ofTruthValues_mem_constantClass f⟩) truthValues_ofTruthValues)

/-- The isomorphism type of a code in `constantClass` corresponds to its truth values. -/
@[simp]
theorem quotientClassIsoConstantClassEquiv_mk (c : constantClass) :
    quotientClassIsoConstantClassEquiv ⟦c⟧ = truthValues c := by
  simp [quotientClassIsoConstantClassEquiv]

/-- The isomorphism type corresponding to `f` is that of `ofTruthValues f`. -/
@[simp]
theorem quotientClassIsoConstantClassEquiv_symm_apply (f : ℕ → Bool) :
    quotientClassIsoConstantClassEquiv.symm f =
      ⟦⟨ofTruthValues f, ofTruthValues_mem_constantClass f⟩⟧ := by
  rw [Equiv.symm_apply_eq, quotientClassIsoConstantClassEquiv_mk, truthValues_ofTruthValues]

-- A Borel complete class has uncountably many isomorphism types: isomorphism on `constantClass`,
-- with `ℕ → Bool` as its isomorphism types, reduces to it. So a class with countably many
-- isomorphism types, such as all codes of one unary predicate, is not Borel complete.
example {L : Language} [L.IsRelational] {K : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) : ¬ Countable (Quotient (classIso K)) := by
  intro h
  have hle := (hK.borelReducible measurableSet_constantClass
    isomorphismInvariant_constantClass).lift_mk_quotient_le
  rw [Cardinal.mk_congr quotientClassIsoConstantClassEquiv] at hle
  have hlt : Cardinal.aleph0 < Cardinal.mk (ℕ → Bool) := by
    simpa using Cardinal.aleph0_lt_continuum
  exact hlt.not_ge (Cardinal.lift_le_aleph0.1
    (hle.trans (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0)))

/-! ### Unions -/

-- A union with a Borel complete class is Borel complete.
example {L : Language} [L.IsRelational] {K K₂ : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) : BorelComplete (K ∪ K₂) :=
  hK.mono subset_union_left

end TauCeti.RelationalConfiguration.BorelCompleteChecks
