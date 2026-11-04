/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import TauCeti.ModelTheory.Infinitary.SubstBounds

/-!
# The constant support of a formula of `L[[γ]]`

The **constant support** of an infinitary formula of the language `L[[γ]]` is the set of `c : γ`
whose constant symbol occurs in it, read off the occurring function symbols. The truth of a
formula in an expansion of an `L`-structure depends only on how the constants in its support are
interpreted. This is what allows a constant that does not occur in a set of sentences to be
reinterpreted as a witness, the argument behind the witness clauses of consistency properties.

The support is a set rather than a `Finset`: a countable conjunction can mention infinitely many
constants. A term mentions only finitely many (`Term.finite_constantSupport`).

## Main definitions

* `FirstOrder.Language.Term.constantSupport`: the constants occurring in a term.
* `FirstOrder.Language.BoundedFormulaInf.constantSupport`: the constants occurring in an
  infinitary formula.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.realize_congr_of_eqOn_constantSupport`: expansions
  agreeing on the support of a formula give it the same truth value.
* `FirstOrder.Language.BoundedFormulaInf.constantSupport_inst_subset`: instantiating at a term adds
  at most the constants of the term.
* `FirstOrder.Language.BoundedFormulaInf.constantSupport_onBoundedFormulaInf`: a formula of `L`
  has empty support in `L[[γ]]`.

## References

* `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Methods/ConstantSupport.lean`: `sentenceJConsts` and `Term.jConsts`, the constant
  supports of formulas and terms of `L[[J]]`, likewise read off the occurring function symbols.
  Divergence from that source: the support here is defined at every carrier, not only at `ℕ`.
-/

public section

universe u v uγ uι uα w

namespace FirstOrder.Language

variable {L : Language.{u, v}} {γ : Type uγ} {ι : Type uι} {α : Type uα} {n : ℕ}

/-- Expansions of one `L`-structure interpreting the occurring constants alike agree on the
function symbols occurring in a term or formula. -/
private theorem funMap_withConstants_eq {M : Type w} [L.Structure M] {e e' : γ → M}
    {X : Set (Σ k, L[[γ]].Functions k)}
    (h : ∀ c, (⟨0, L.con c⟩ : Σ k, L[[γ]].Functions k) ∈ X → e c = e' c) {k : ℕ}
    (f : L[[γ]].Functions k) (hf : (⟨k, f⟩ : Σ k, L[[γ]].Functions k) ∈ X) (xs : Fin k → M) :
    @Structure.funMap _ M (@withConstantsStructure L M _ γ (constantsOn.structure e)) k f xs =
      @Structure.funMap _ M
        (@withConstantsStructure L M _ γ (constantsOn.structure e')) k f xs := by
  rcases f with f | c
  · rfl
  · cases k with
    | zero => exact h c hf
    | succ k => exact c.elim

namespace Term

/-- The **constant support** of a term of `L[[γ]]`: the `c : γ` whose constant symbol occurs. -/
def constantSupport (t : L[[γ]].Term α) : Set γ :=
  {c | (⟨0, L.con c⟩ : Σ k, L[[γ]].Functions k) ∈ t.functionsIn}

theorem mem_constantSupport {t : L[[γ]].Term α} {c : γ} :
    c ∈ t.constantSupport ↔ (⟨0, L.con c⟩ : Σ k, L[[γ]].Functions k) ∈ t.functionsIn :=
  Iff.rfl

/-- A term mentions finitely many constants. -/
theorem finite_constantSupport (t : L[[γ]].Term α) : t.constantSupport.Finite :=
  t.functionsIn_finite.preimage fun _ _ _ _ h => Sum.inr_injective (eq_of_heq (Sigma.mk.inj h).2)

@[simp]
theorem constantSupport_var (a : α) : (var a : L[[γ]].Term α).constantSupport = ∅ := by
  simp [constantSupport]

/-- Applying an original function symbol adds only the constants of its arguments. -/
-- Simplify before `onFunction` reduces the language inclusion to `Sum.inl`.
@[simp↓]
theorem constantSupport_func {k : ℕ} (f : L.Functions k)
    (ts : Fin k → L[[γ]].Term α) :
    (func ((L.lhomWithConstants γ).onFunction f) ts).constantSupport =
      ⋃ i, (ts i).constantSupport := by
  ext c
  simp only [Set.mem_iUnion, mem_constantSupport]
  rw [functionsIn_func]
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, or_iff_right_iff_imp]
  intro h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  exact (Sum.inr_ne_inl (eq_of_heq h)).elim

/-- A term of `L` mentions no constant of `L[[γ]]`. -/
@[simp]
theorem constantSupport_onTerm (t : L.Term α) :
    ((L.lhomWithConstants γ).onTerm t).constantSupport = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun c hc => ?_
  obtain ⟨⟨k, f⟩, -, h⟩ := (functionsIn_onTerm t (L.lhomWithConstants γ)).subset hc
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  exact Sum.inl_ne_inr (eq_of_heq h)

/-- The constant `L.con c` is the only constant occurring in its term. -/
@[simp]
theorem constantSupport_con (c : γ) :
    ((L.con c).term : L[[γ]].Term α).constantSupport = {c} := by
  ext d
  simp only [mem_constantSupport, Constants.term, functionsIn_func, Set.iUnion_of_empty,
    Set.union_empty, Set.mem_singleton_iff, Sigma.mk.injEq, heq_eq_eq, true_and]
  exact ⟨fun h => Sum.inr_injective h, fun h => h ▸ rfl⟩

/-- Expansions agreeing on the constants of a term give it the same value. -/
theorem realize_congr_of_eqOn_constantSupport {M : Type w} [L.Structure M] {e e' : γ → M}
    (t : L[[γ]].Term α) (h : Set.EqOn e e' t.constantSupport) (v : α → M) :
    @realize _ M (@withConstantsStructure L M _ γ (constantsOn.structure e)) _ v t =
      @realize _ M (@withConstantsStructure L M _ γ (constantsOn.structure e')) _ v t :=
  t.realize_congr_of_agreeOn _ _ (fun f hf xs => funMap_withConstants_eq (fun _ hc => h hc) f hf xs)
    v

end Term

namespace BoundedFormulaInf

/-- The **constant support** of an infinitary formula of `L[[γ]]`: the `c : γ` whose constant
symbol occurs. -/
def constantSupport (φ : L[[γ]].BoundedFormulaInf ι α n) : Set γ :=
  {c | (⟨0, L.con c⟩ : Σ k, L[[γ]].Functions k) ∈ φ.functionsIn}

theorem mem_constantSupport {φ : L[[γ]].BoundedFormulaInf ι α n} {c : γ} :
    c ∈ φ.constantSupport ↔ (⟨0, L.con c⟩ : Σ k, L[[γ]].Functions k) ∈ φ.functionsIn :=
  Iff.rfl

@[simp]
theorem constantSupport_falsum :
    (falsum : L[[γ]].BoundedFormulaInf ι α n).constantSupport = ∅ := by
  simp [constantSupport]

@[simp]
theorem constantSupport_bot : (⊥ : L[[γ]].BoundedFormulaInf ι α n).constantSupport = ∅ :=
  constantSupport_falsum

@[simp]
theorem constantSupport_equal (t₁ t₂ : L[[γ]].Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L[[γ]].BoundedFormulaInf ι α n).constantSupport =
      t₁.constantSupport ∪ t₂.constantSupport := by
  ext c
  simp [constantSupport, Term.constantSupport]

@[simp]
theorem constantSupport_rel {k : ℕ} (R : L[[γ]].Relations k)
    (ts : Fin k → L[[γ]].Term (α ⊕ Fin n)) :
    (rel R ts : L[[γ]].BoundedFormulaInf ι α n).constantSupport =
      ⋃ i, (ts i).constantSupport := by
  ext c
  simp [constantSupport, Term.constantSupport]

@[simp]
theorem constantSupport_imp (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    (φ.imp ψ).constantSupport = φ.constantSupport ∪ ψ.constantSupport := by
  ext c
  simp [constantSupport]

@[simp]
theorem constantSupport_not (φ : L[[γ]].BoundedFormulaInf ι α n) :
    φ.not.constantSupport = φ.constantSupport := by
  simp [BoundedFormulaInf.not]

@[simp]
theorem constantSupport_all (φ : L[[γ]].BoundedFormulaInf ι α (n + 1)) :
    φ.all.constantSupport = φ.constantSupport := by
  simp [constantSupport]

@[simp]
theorem constantSupport_iSup (φs : ι → L[[γ]].BoundedFormulaInf ι α n) :
    (iSup φs).constantSupport = ⋃ i, (φs i).constantSupport := by
  ext c
  simp [constantSupport]

@[simp]
theorem constantSupport_iInf (φs : ι → L[[γ]].BoundedFormulaInf ι α n) :
    (iInf φs).constantSupport = ⋃ i, (φs i).constantSupport := by
  ext c
  simp [constantSupport]

/-- A formula of `L` mentions no constant of `L[[γ]]`. -/
@[simp]
theorem constantSupport_onBoundedFormulaInf (φ : L.BoundedFormulaInf ι α n) :
    ((L.lhomWithConstants γ).onBoundedFormulaInf φ).constantSupport = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun c hc => ?_
  obtain ⟨⟨k, f⟩, -, h⟩ := (LHom.functionsIn_onBoundedFormulaInf _ φ).subset hc
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  exact Sum.inl_ne_inr (eq_of_heq h)

/-- Instantiating a formula at a term adds at most the constants of the term. -/
theorem constantSupport_inst_subset (φ : L[[γ]].BoundedFormulaInf ι α 1)
    (t : L[[γ]].Term (α ⊕ Fin 0)) :
    (φ.inst t).constantSupport ⊆ φ.constantSupport ∪ t.constantSupport := by
  intro c hc
  rw [inst_def] at hc
  obtain h | h := functionsIn_substBounds_subset (fun _ => t) φ (mem_constantSupport.1 hc)
  · exact .inl h
  · exact .inr (Term.mem_constantSupport.2 (by simpa using h))

/-- Every constant of a formula occurs in its instances. -/
theorem constantSupport_subset_inst (φ : L[[γ]].BoundedFormulaInf ι α 1)
    (t : L[[γ]].Term (α ⊕ Fin 0)) : φ.constantSupport ⊆ (φ.inst t).constantSupport := by
  rw [inst_def]
  exact fun _ hc => functionsIn_subset_functionsIn_substBounds (fun _ => t) φ hc

/-- **Constant locality.** Expansions of one `L`-structure which interpret the constants in the
support of a formula alike give it the same truth value. -/
theorem realize_congr_of_eqOn_constantSupport {M : Type w} [L.Structure M] {e e' : γ → M}
    (φ : L[[γ]].BoundedFormulaInf ι α n) (h : Set.EqOn e e' φ.constantSupport) (v : α → M)
    (xs : Fin n → M) :
    @Realize _ ι α M (@withConstantsStructure L M _ γ (constantsOn.structure e)) n φ v xs ↔
      @Realize _ ι α M (@withConstantsStructure L M _ γ (constantsOn.structure e')) n φ v xs := by
  refine φ.realize_congr_of_agreeOn _ _
    (fun f hf xs => funMap_withConstants_eq (fun _ hc => h hc) f hf xs) (fun R _ xs => ?_) v xs
  rcases R with R | R
  · rfl
  · exact R.elim

end BoundedFormulaInf

end FirstOrder.Language
