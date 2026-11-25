/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
public import TauCeti.ModelTheory.Scott.NatPredicate

/-!
# Regression examples: relabelling on small carriers and Borel completeness

Regression examples for relabelling of relational configurations and for Borel completeness of
classes of codes.

* Relabelling the code of `P = {0}` along the transposition of `0` and `1` gives the code of
  `P = {1}`, and agrees with the logic action of that transposition.
* On the carrier `Fin 0`, a language without nullary symbols has a single code, and its
  isomorphism relation has one class; with one nullary symbol there are two codes, both fixed by
  relabelling, in two classes.
* In the language `TauCeti.natPredicateLanguage` of countably many unary predicates `P_i`, the
  class `constantClass` of codes in which each `P_i` is `∅` or `ℕ` is closed and isomorphism
  invariant, and its isomorphism types are in bijection with `ℕ → Bool`. Hence a Borel complete
  class has uncountably many isomorphism types.
* A class containing a Borel complete class, such as `K ∪ K₂`, is Borel complete.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration.BorelCompleteChecks

/-! ### Relabelling along a transposition -/

/-- Relabelling a unary atom `R(v)` along `f` gives `R(f v)`. -/
private theorem map_atom_unary {L : Language} {V W : Type*} (f : V → W) (R : L.Relations 1)
    (v : V) : (atom R ![v]).map f = atom R ![f v] := by
  rw [Atom.map_atom, Matrix.vec_single_eq_const, Matrix.vec_single_eq_const]
  rfl

-- Relabelling the code of `P = {0}` along the transposition `(0 1)` gives the code of `P = {1}`.
example {L : Language} (R : L.Relations 1) (c : RelationalConfiguration L ℕ)
    (hc : ∀ v, c.eval (atom R ![v]) = decide (v = 0)) (v : ℕ) :
    (relabel (Equiv.swap 0 1) c).eval (atom R ![v]) = decide (v = 1) := by
  rw [eval_relabel, map_atom_unary, Equiv.symm_swap, hc]
  simp [Equiv.swap_apply_eq_iff]

-- Relabelling along a permutation is the logic action of that permutation.
example {L : Language} (c : RelationalConfiguration L ℕ) :
    relabel (Equiv.swap 0 1) c = Equiv.swap 0 1 • c :=
  relabel_perm _ c

/-! ### The carrier `Fin 0` -/

/-- A configuration is its truth-value function on atoms, through `eval` and `mk`. -/
private def equivAtomFun {L : Language} {V : Type*} :
    RelationalConfiguration L V ≃ (Atom L V → Bool) where
  toFun c := c.eval
  invFun := mk
  left_inv _ := ext fun a => eval_mk _ a
  right_inv f := funext (eval_mk f)

/-- Over the empty carrier, the only atoms are nullary. -/
private theorem atom_fin_zero {L : Language} (a : Atom L (Fin 0)) :
    ∃ R : L.Relations 0, a = atom R Fin.elim0 := by
  obtain ⟨n, R, x⟩ := a
  cases n with
  | zero => exact ⟨R, by rw [Subsingleton.elim x Fin.elim0]; exact (Atom.eta _).symm⟩
  | succ n => exact (x 0).elim0

/-- Over the empty carrier, every configuration is fixed by every relabelling. -/
private theorem relabel_fin_zero {L : Language} (e : Fin 0 ≃ Fin 0)
    (c : RelationalConfiguration L (Fin 0)) : relabel e c = c := by
  rw [Subsingleton.elim e (Equiv.refl _), relabel_refl]
  rfl

/-- Two configurations on the empty carrier are isomorphic only when they are equal. -/
private theorem isoSetoid_fin_zero_iff {L : Language} [L.IsRelational]
    {c d : RelationalConfiguration L (Fin 0)} : isoSetoid L (Fin 0) c d ↔ c = d := by
  rw [isoSetoid_iff_exists_perm_smul_eq]
  refine ⟨fun ⟨σ, h⟩ => ?_, fun h => ⟨1, by rw [h, one_smul]⟩⟩
  rwa [← relabel_perm, relabel_fin_zero] at h

/-- On the empty carrier, the classes of `classIso univ` are the codes. -/
private theorem card_quotient_classIso_univ_fin_zero {L : Language} [L.IsRelational] :
    Nat.card (Quotient (classIso (univ : Set (RelationalConfiguration L (Fin 0))))) =
      Nat.card (RelationalConfiguration L (Fin 0)) :=
  Nat.card_congr ((Setoid.quotientTrivialEquiv _ fun _ _ h =>
    Subtype.ext (isoSetoid_fin_zero_iff.1 h)).trans (Equiv.Set.univ _))

-- Without nullary symbols there is a single code on `Fin 0`, and a single class.
example {L : Language} [L.IsRelational] [IsEmpty (L.Relations 0)] :
    Nat.card (RelationalConfiguration L (Fin 0)) = 1 ∧
      Nat.card (Quotient (classIso (univ : Set (RelationalConfiguration L (Fin 0))))) = 1 := by
  have : IsEmpty (Atom L (Fin 0)) :=
    ⟨fun a => (atom_fin_zero a).elim fun R _ => IsEmpty.elim inferInstance R⟩
  have : Unique (RelationalConfiguration L (Fin 0)) := equivAtomFun.unique
  rw [card_quotient_classIso_univ_fin_zero, Nat.card_unique]
  exact ⟨rfl, rfl⟩

/-- The language with a single nullary relation symbol and no other symbols. -/
@[expose] def nullaryLanguage : Language.{0, 0} where
  Functions _ := Empty
  Relations
    | 0 => Unit
    | _ + 1 => Empty

/-- `nullaryLanguage` has no function symbols. -/
instance isRelational_nullaryLanguage : nullaryLanguage.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

-- With one nullary symbol there are two codes on `Fin 0`, both fixed by relabelling, and two
-- classes: the nullary symbol holds in one code and fails in the other.
example : Nat.card (RelationalConfiguration nullaryLanguage (Fin 0)) = 2 ∧
    (∀ (e : Fin 0 ≃ Fin 0) (c : RelationalConfiguration nullaryLanguage (Fin 0)),
      relabel e c = c) ∧
    Nat.card (Quotient (classIso (univ : Set (RelationalConfiguration nullaryLanguage (Fin 0))))) =
      2 := by
  have e : Atom nullaryLanguage (Fin 0) ≃ Unit :=
    { toFun _ := ()
      invFun _ := atom (L := nullaryLanguage) (n := 0) () Fin.elim0
      left_inv a := by
        obtain ⟨R, rfl⟩ := atom_fin_zero a
        rfl
      right_inv _ := rfl }
  have hcard : Nat.card (RelationalConfiguration nullaryLanguage (Fin 0)) = 2 := by
    rw [Nat.card_congr (equivAtomFun.trans (e.arrowCongr (Equiv.refl Bool)))]
    simp
  exact ⟨hcard, relabel_fin_zero, by rw [card_quotient_classIso_univ_fin_zero, hcard]⟩

/-! ### Countably many unary predicates -/

/-- The language of countably many unary predicates has countably many relation symbols of each
arity. -/
instance countable_relations_natPredicateLanguage (n : ℕ) :
    Countable (natPredicateLanguage.Relations n) :=
  Function.Injective.countable (f := Sigma.mk n) sigma_mk_injective

/-- The atom `P_i(v)` of `natPredicateLanguage`. -/
def unaryAtom (i v : ℕ) : Atom natPredicateLanguage ℕ :=
  atom (NatPredicateRel.pred i) ![v]

/-- Relabelling the atom `P_i(v)` along `f` gives `P_i(f v)`. -/
@[simp]
theorem map_unaryAtom (f : ℕ → ℕ) (i v : ℕ) : (unaryAtom i v).map f = unaryAtom i (f v) :=
  map_atom_unary f _ v

/-- Every atom of `natPredicateLanguage` is some `P_i(v)`. -/
theorem exists_eq_unaryAtom (a : Atom natPredicateLanguage ℕ) : ∃ i v, a = unaryAtom i v := by
  induction a using Atom.induction_atom with
  | h R x =>
    cases R with
    | pred i =>
      refine ⟨i, x 0, congrArg _ ?_⟩
      rw [Matrix.vec_single_eq_const]
      exact funext fun j => congrArg x (Subsingleton.elim j 0)

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
  rw [ofTruthValues, eval_mk]
  exact congrArg (symbolValue f) (Atom.symbol_atom _ _)

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
  (Quotient.congrRight fun _ _ => classIso_constantClass_iff).trans
    (Setoid.quotientKerEquivOfRightInverse (truthValues ∘ Subtype.val)
      (fun f => ⟨ofTruthValues f, ofTruthValues_mem_constantClass f⟩) truthValues_ofTruthValues)

/-- The isomorphism type of a code in `constantClass` corresponds to its truth values. -/
@[simp]
theorem quotientClassIsoConstantClassEquiv_mk (c : constantClass) :
    quotientClassIsoConstantClassEquiv ⟦c⟧ = truthValues c :=
  (rfl)

/-- The isomorphism type corresponding to `f` is that of `ofTruthValues f`. -/
@[simp]
theorem quotientClassIsoConstantClassEquiv_symm_apply (f : ℕ → Bool) :
    quotientClassIsoConstantClassEquiv.symm f =
      ⟦⟨ofTruthValues f, ofTruthValues_mem_constantClass f⟩⟧ :=
  (rfl)

-- A Borel complete class has uncountably many isomorphism types: isomorphism on `constantClass`,
-- with `ℕ → Bool` as its isomorphism types, reduces to it. So a class with countably many
-- isomorphism types, such as all codes of one unary predicate, is not Borel complete.
example {L : Language} [L.IsRelational] {K : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) : ¬ Countable (Quotient (classIso K)) := by
  intro h
  obtain ⟨g, -, hg⟩ := (hK.borelReducible measurableSet_constantClass
    isomorphismInvariant_constantClass).exists_measurable_injective_quotient
  have hlt : Cardinal.aleph0 < Cardinal.mk (ℕ → Bool) := by
    simpa using Cardinal.aleph0_lt_continuum
  exact hlt.not_ge (Cardinal.mk_le_aleph0_iff.2
    (hg.comp quotientClassIsoConstantClassEquiv.symm.injective).countable)

/-! ### Unions -/

-- A union with a Borel complete class is Borel complete.
example {L : Language} [L.IsRelational] {K K₂ : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) : BorelComplete (K ∪ K₂) :=
  hK.mono subset_union_left

end TauCeti.RelationalConfiguration.BorelCompleteChecks
