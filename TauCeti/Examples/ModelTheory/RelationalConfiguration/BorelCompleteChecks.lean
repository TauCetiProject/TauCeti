/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete

/-!
# Regression examples: relabelling on small carriers and Borel completeness

These are CountableStructureSpacesPartII §§1.1-1.2 Checks.

* Relabelling the code of `P = {0}` along the transposition of `0` and `1` gives the code of
  `P = {1}`, and agrees with the logic action of that transposition.
* On the carrier `Fin 0`, a language without nullary symbols has a single code, and its
  isomorphism relation has one class; with one nullary symbol there are two codes, both fixed by
  relabelling, in two classes.
* In the language `unaryFamily` of countably many unary predicates `P_i`, the class
  `constantClass` of codes in which each `P_i` is `∅` or `ℕ` is closed and isomorphism invariant,
  and its isomorphism types are in bijection with `ℕ → Bool`. Hence a Borel complete class has
  uncountably many isomorphism types.
* A class containing a Borel complete class, such as `K ∪ K₂`, is Borel complete.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration.BorelCompleteChecks

/-! ### Relabelling along a transposition -/

-- Relabelling the code of `P = {0}` along the transposition `(0 1)` gives the code of `P = {1}`.
example {L : Language} (R : L.Relations 1) (c : RelationalConfiguration L ℕ)
    (hc : ∀ v, c.eval (atom R ![v]) = decide (v = 0)) (v : ℕ) :
    (relabel (Equiv.swap 0 1) c).eval (atom R ![v]) = decide (v = 1) := by
  rw [eval_relabel, Atom.map_atom, Equiv.symm_swap]
  have : (Equiv.swap (0 : ℕ) 1 ∘ ![v]) = ![Equiv.swap 0 1 v] := by
    ext i
    fin_cases i
    rfl
  rw [this, hc]
  simp [Equiv.swap_apply_eq_iff]

-- Relabelling along a permutation is the logic action of that permutation.
example {L : Language} (c : RelationalConfiguration L ℕ) :
    relabel (Equiv.swap 0 1) c = Equiv.swap 0 1 • c :=
  relabel_perm _ c

/-! ### The carrier `Fin 0` -/

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
      Nat.card (RelationalConfiguration L (Fin 0)) := by
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift (fun c => c.val) fun c d h =>
    congrArg Subtype.val ?_) ⟨fun a b hab => ?_, fun c => ⟨⟦⟨c, mem_univ c⟩⟧, rfl⟩⟩)
  · exact Subtype.ext (isoSetoid_fin_zero_iff.1 h)
  · induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound (isoSetoid_fin_zero_iff.2 hab)

-- Without nullary symbols there is a single code on `Fin 0`, and a single class.
example {L : Language} [L.IsRelational] [IsEmpty (L.Relations 0)] :
    Nat.card (RelationalConfiguration L (Fin 0)) = 1 ∧
      Nat.card (Quotient (classIso (univ : Set (RelationalConfiguration L (Fin 0))))) = 1 := by
  have : IsEmpty (Atom L (Fin 0)) :=
    ⟨fun a => (atom_fin_zero a).elim fun R _ => IsEmpty.elim inferInstance R⟩
  have : Unique (RelationalConfiguration L (Fin 0)) :=
    inferInstanceAs (Unique (Atom L (Fin 0) → Bool))
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
    rw [show RelationalConfiguration nullaryLanguage (Fin 0) = (Atom nullaryLanguage (Fin 0) →
      Bool) from rfl, Nat.card_congr (e.arrowCongr (Equiv.refl Bool))]
    simp
  exact ⟨hcard, relabel_fin_zero, by rw [card_quotient_classIso_univ_fin_zero, hcard]⟩

/-! ### Countably many unary predicates -/

/-- The language with one unary relation symbol `P_i` for each `i : ℕ`, and no other symbols. -/
@[expose] def unaryFamily : Language.{0, 0} where
  Functions _ := Empty
  Relations
    | 0 => Empty
    | 1 => ℕ
    | _ + 2 => Empty

/-- `unaryFamily` has no function symbols. -/
instance isRelational_unaryFamily : unaryFamily.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- `unaryFamily` has countably many relation symbols of each arity. -/
instance countable_relations_unaryFamily : ∀ n, Countable (unaryFamily.Relations n)
  | 0 => inferInstanceAs (Countable Empty)
  | 1 => inferInstanceAs (Countable ℕ)
  | _ + 2 => inferInstanceAs (Countable Empty)

/-- The unary symbol `P_i` of `unaryFamily`. -/
def unarySymbol (i : ℕ) : unaryFamily.Relations 1 := i

/-- The atom `P_i(v)` of `unaryFamily`. -/
def unaryAtom (i v : ℕ) : Atom unaryFamily ℕ :=
  atom (unarySymbol i) ![v]

/-- Relabelling the atom `P_i(v)` along `f` gives `P_i(f v)`. -/
@[simp]
theorem map_unaryAtom (f : ℕ → ℕ) (i v : ℕ) : (unaryAtom i v).map f = unaryAtom i (f v) := by
  rw [unaryAtom, unaryAtom, Atom.map_atom]
  congr 1
  funext j
  fin_cases j
  rfl

/-- Every atom of `unaryFamily` is some `P_i(v)`. -/
theorem exists_eq_unaryAtom (a : Atom unaryFamily ℕ) : ∃ i v, a = unaryAtom i v := by
  induction a using Atom.induction_atom with
  | @h n R x =>
    match n, R, x with
    | 0, R, _ => exact (R : Empty).elim
    | 1, i, x =>
      refine ⟨i, x 0, (atom_eq_atom_iff (S := unarySymbol i)).2 ⟨rfl, heq_of_eq ?_⟩⟩
      funext j
      fin_cases j
      rfl
    | _ + 2, R, _ => exact (R : Empty).elim

/-- The class of codes of `unaryFamily` on `ℕ` in which each `P_i` is `∅` or `ℕ`. -/
def constantClass : Set (RelationalConfiguration unaryFamily ℕ) :=
  {c | ∀ i v w, c.eval (unaryAtom i v) = c.eval (unaryAtom i w)}

/-- The truth values of `P_0, P_1, …` at the point `0`. -/
def truthValues (c : RelationalConfiguration unaryFamily ℕ) : ℕ → Bool :=
  fun i => c.eval (unaryAtom i 0)

/-- The value `f i` on the symbol `P_i`. -/
def symbolValue (f : ℕ → Bool) : (Σ n, unaryFamily.Relations n) → Bool
  | ⟨0, R⟩ => (R : Empty).elim
  | ⟨1, i⟩ => f i
  | ⟨_ + 2, R⟩ => (R : Empty).elim

/-- The code in which `P_i` is `ℕ` when `f i` holds and `∅` otherwise. -/
def ofTruthValues (f : ℕ → Bool) : RelationalConfiguration unaryFamily ℕ :=
  mk fun a => symbolValue f a.symbol

/-- The code `ofTruthValues f` reads `f i` at every atom `P_i(v)`. -/
@[simp]
theorem eval_ofTruthValues (f : ℕ → Bool) (i v : ℕ) :
    (ofTruthValues f).eval (unaryAtom i v) = f i := by
  rw [ofTruthValues, eval_mk, unaryAtom, Atom.symbol_atom]
  rfl

/-- The code `ofTruthValues f` lies in `constantClass`. -/
theorem ofTruthValues_mem_constantClass (f : ℕ → Bool) : ofTruthValues f ∈ constantClass :=
  fun _ _ _ => by rw [eval_ofTruthValues, eval_ofTruthValues]

/-- A code in `constantClass` is determined by its truth values. -/
theorem eq_of_truthValues_eq {c d : RelationalConfiguration unaryFamily ℕ}
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

/-- Relabelling preserves the truth values. -/
theorem truthValues_perm_smul {c : RelationalConfiguration unaryFamily ℕ}
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
noncomputable def quotientClassIsoConstantClassEquiv :
    Quotient (classIso constantClass) ≃ (ℕ → Bool) :=
  Equiv.ofBijective (Quotient.lift (fun c => truthValues c) fun _ _ =>
    classIso_constantClass_iff.1)
    ⟨fun a b hab => by
      induction a using Quotient.ind
      induction b using Quotient.ind
      exact Quotient.sound (classIso_constantClass_iff.2 hab),
    fun f => ⟨⟦⟨ofTruthValues f, ofTruthValues_mem_constantClass f⟩⟧,
      funext fun i => eval_ofTruthValues f i 0⟩⟩

/-- **A Borel complete class has uncountably many isomorphism types**: isomorphism on
`constantClass`, with `ℕ → Bool` as its isomorphism types, reduces to it. So a class with countably
many isomorphism types, such as all codes of one unary predicate, is not Borel complete. -/
theorem not_countable_quotient_of_borelComplete {L : Language} [L.IsRelational]
    {K : Set (RelationalConfiguration L ℕ)} (hK : BorelComplete K) :
    ¬ Countable (Quotient (classIso K)) := by
  intro h
  obtain ⟨g, -, hg⟩ := (hK.borelReducible measurableSet_constantClass
    isomorphismInvariant_constantClass).exists_measurable_injective_quotient
  have : Countable (ℕ → Bool) :=
    (hg.comp quotientClassIsoConstantClassEquiv.symm.injective).countable
  have hle := Cardinal.mk_le_aleph0_iff.2 this
  rw [Cardinal.mk_pi, Cardinal.prod_const, Cardinal.mk_bool, Cardinal.lift_id, Cardinal.mk_nat,
    Cardinal.lift_aleph0] at hle
  exact (Cardinal.cantor _).not_ge hle

/-! ### Unions -/

-- A union with a Borel complete class is Borel complete.
example {L : Language} [L.IsRelational] {K K₂ : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) : BorelComplete (K ∪ K₂) :=
  hK.mono subset_union_left

end TauCeti.RelationalConfiguration.BorelCompleteChecks
