/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Sublanguage
public import TauCeti.ModelTheory.Infinitary.SubstBounds
public import TauCeti.ModelTheory.Infinitary.Substitution
public import TauCeti.ModelTheory.Infinitary.ConstantAbstraction
public import TauCeti.ModelTheory.Infinitary.Theory

/-!
# Signed relation occurrences and polarity monotonicity in `L_{∞ω}`

`BoundedFormulaInf.relationsInSigned s φ` records the arity-tagged relation symbols that occur in an
infinitary formula `φ` with syntactic polarity `s : Bool` (`true` for positive occurrences, `false`
for negative occurrences). Logical equality is treated as a logical symbol and contributes to
neither polarity. An implication `φ.imp ψ` flips the polarity of its antecedent `φ` and keeps that
of its consequent `ψ`; universal quantification and infinitary disjunctions and conjunctions keep
the polarity of their subformulas. Together the positive and negative occurrences partition — with
possible overlap when a symbol appears in both positions — the unsigned occurrence set
`BoundedFormulaInf.relationsIn`.

Syntactic polarity governs semantic monotonicity
(`BoundedFormulaInf.realize_mono_of_agreeOn_functionsIn` and, for relational languages,
`BoundedFormulaInf.realize_mono_of_signed`): on a common carrier, if two structures interpret every
occurring function symbol of `φ` in the same way, every positively occurring relation symbol of `φ`
is only enlarged from `S` to `S'`, and every negatively occurring relation symbol of `φ` is only
shrunk from `S` to `S'`, then realization of `φ` transfers from `S` to `S'`.

Language homomorphisms carry signed occurrence sets to their exact images. Conversely, a formula
whose occurring function symbols, positive relation symbols, and negative relation symbols lie in
the images of three sets `F`, `P`, and `N` under an arbitrary language homomorphism `g : L →ᴸ L'`
pulls back along `g` to a formula respecting `F`, `P`, and `N` separately
(`LHom.exists_eq_onBoundedFormulaInf_of_relationsInSigned_subset`), even when `g` identifies
distinct relation symbols of opposite polarity.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.relationsInSigned`: arity-tagged relation symbols occurring
  in a formula with a given syntactic polarity.
* `FirstOrder.Language.BoundedFormulaInf.positiveRelationsIn` and
  `FirstOrder.Language.BoundedFormulaInf.negativeRelationsIn`: abbreviations for positive (`true`)
  and negative (`false`) occurrences.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.relationsInSigned_union_not`: occurrences at opposite
  polarities together recover `BoundedFormulaInf.relationsIn`.
* `FirstOrder.Language.BoundedFormulaInf.relationsInSigned_countable`: at a countable branching
  carrier, each signed occurrence set is countable.
* `FirstOrder.Language.BoundedFormulaInf.realize_mono_of_agreeOn_functionsIn` and
  `FirstOrder.Language.BoundedFormulaInf.realize_mono_of_signed` (with sentence forms
  `FirstOrder.Language.SentenceInf.realize_mono_of_agreeOn_functionsIn` and
  `FirstOrder.Language.SentenceInf.realize_mono_of_signed`): realization is monotone in positively
  occurring relations and antitone in negatively occurring relations.
* `FirstOrder.Language.LHom.relationsInSigned_onBoundedFormulaInf` and
  `FirstOrder.Language.LHom.exists_eq_onBoundedFormulaInf_of_relationsInSigned_subset`: image law
  and polarity-preserving pullback along an arbitrary language homomorphism.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapter 4.
* Adapted from `InfinitaryLogic/Lomega1omega/Polarity.lean` and
  `InfinitaryLogic/Lomega1omega/PolaritySemantics.lean` in `cameronfreer/infinitary-logic` at
  commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`.
  Divergences from that source: signed occurrences and monotonicity are developed at an arbitrary
  branching carrier `ι` and in arbitrary universes; `positiveRelationsIn` and `negativeRelationsIn`
  are reducible specializations of `relationsInSigned` so one simp family serves both polarities;
  monotonicity is proved first under agreement on `φ.functionsIn` before specializing to
  `[L.IsRelational]`; and polarity-preserving pullback along non-injective language homomorphisms
  is included.
-/

public section

universe u v u' v' uα uβ uγ uι uκ w

namespace FirstOrder.Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}

/-- The relation symbols occurring in an infinitary formula with syntactic polarity `s` (`true` for
positive, `false` for negative), tagged by arity.

Logical equality contributes to neither polarity. An implication flips the polarity of its
antecedent and keeps that of its consequent; universal quantification and infinitary disjunctions
and conjunctions keep the polarity of their subformulas. -/
def relationsInSigned : ∀ {n : ℕ}, Bool → L.BoundedFormulaInf ι α n → Set (Σ k, L.Relations k)
  | _, _, .falsum => ∅
  | _, _, .equal _ _ => ∅
  | _, s, .rel R _ => if s then {⟨_, R⟩} else ∅
  | _, s, .imp φ ψ => relationsInSigned (!s) φ ∪ relationsInSigned s ψ
  | _, s, .all φ => relationsInSigned s φ
  | _, s, .iSup φs => ⋃ i, relationsInSigned s (φs i)
  | _, s, .iInf φs => ⋃ i, relationsInSigned s (φs i)

/-- The relation symbols occurring positively in an infinitary formula, tagged by arity. -/
abbrev positiveRelationsIn (φ : L.BoundedFormulaInf ι α n) : Set (Σ k, L.Relations k) :=
  φ.relationsInSigned true

/-- The relation symbols occurring negatively in an infinitary formula, tagged by arity. -/
abbrev negativeRelationsIn (φ : L.BoundedFormulaInf ι α n) : Set (Σ k, L.Relations k) :=
  φ.relationsInSigned false

/-! ### Constructor and derived-connective equations -/

@[simp]
theorem relationsInSigned_falsum (s : Bool) :
    (falsum : L.BoundedFormulaInf ι α n).relationsInSigned s = ∅ := (rfl)

@[simp]
theorem relationsInSigned_equal (s : Bool) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).relationsInSigned s = ∅ := (rfl)

@[simp]
theorem relationsInSigned_rel (s : Bool) {k : ℕ} (R : L.Relations k)
    (ts : Fin k → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaInf ι α n).relationsInSigned s =
      if s then {⟨k, R⟩} else ∅ := (rfl)

@[simp]
theorem relationsInSigned_imp (s : Bool) (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.imp ψ).relationsInSigned s = φ.relationsInSigned (!s) ∪ ψ.relationsInSigned s := (rfl)

@[simp]
theorem relationsInSigned_all (s : Bool) (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.all.relationsInSigned s = φ.relationsInSigned s := (rfl)

@[simp]
theorem relationsInSigned_iSup (s : Bool) (φs : ι → L.BoundedFormulaInf ι α n) :
    (iSup φs).relationsInSigned s = ⋃ i, (φs i).relationsInSigned s := (rfl)

@[simp]
theorem relationsInSigned_iInf (s : Bool) (φs : ι → L.BoundedFormulaInf ι α n) :
    (iInf φs).relationsInSigned s = ⋃ i, (φs i).relationsInSigned s := (rfl)

/-- Negation swaps positive and negative relation occurrences. -/
@[simp]
theorem relationsInSigned_not (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    φ.not.relationsInSigned s = φ.relationsInSigned (!s) := by
  simp [BoundedFormulaInf.not]

@[simp]
theorem relationsInSigned_bot (s : Bool) :
    (⊥ : L.BoundedFormulaInf ι α n).relationsInSigned s = ∅ := by
  rw [bot_def, relationsInSigned_falsum]

@[simp]
theorem relationsInSigned_top (s : Bool) :
    (⊤ : L.BoundedFormulaInf ι α n).relationsInSigned s = ∅ := by
  rw [top_def, relationsInSigned_not, relationsInSigned_falsum]

@[simp]
theorem relationsInSigned_inf (s : Bool) (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊓ ψ).relationsInSigned s = φ.relationsInSigned s ∪ ψ.relationsInSigned s := by
  simp [inf_def]

@[simp]
theorem relationsInSigned_sup (s : Bool) (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊔ ψ).relationsInSigned s = φ.relationsInSigned s ∪ ψ.relationsInSigned s := by
  simp [sup_def]

@[simp]
theorem relationsInSigned_ex (s : Bool) (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.ex.relationsInSigned s = φ.relationsInSigned s := by
  simp [BoundedFormulaInf.ex]

@[simp]
theorem relationsInSigned_alls (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    φ.alls.relationsInSigned s = φ.relationsInSigned s := by
  induction n with
  | zero => simp
  | succ n ih => rw [alls_succ, ih, relationsInSigned_all]

@[simp]
theorem relationsInSigned_exs (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    φ.exs.relationsInSigned s = φ.relationsInSigned s := by
  induction n with
  | zero => simp
  | succ n ih => rw [exs_succ, ih, relationsInSigned_ex]

@[simp]
theorem relationsInSigned_exsLast (s : Bool) {k : ℕ} (φ : L.BoundedFormulaInf ι α (n + k)) :
    (exsLast φ).relationsInSigned s = φ.relationsInSigned s := by
  induction k with
  | zero => rw [exsLast_zero]
  | succ k ih => rw [exsLast_succ, ih, relationsInSigned_ex]

/-- Coded conjunction adds no signed relation occurrences through its `⊤`-padding. -/
@[simp]
theorem relationsInSigned_iInfAlong (s : Bool) {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    (iInfAlong c φs).relationsInSigned s = ⋃ i, (φs i).relationsInSigned s := by
  rw [iInfAlong_def, relationsInSigned_iInf,
    c.iUnion_pad_of_eq_empty (relationsInSigned_top s)]

/-- Coded disjunction adds no signed relation occurrences through its `⊥`-padding. -/
@[simp]
theorem relationsInSigned_iSupAlong (s : Bool) {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    (iSupAlong c φs).relationsInSigned s = ⋃ i, (φs i).relationsInSigned s := by
  rw [iSupAlong_def, relationsInSigned_iSup,
    c.iUnion_pad_of_eq_empty (relationsInSigned_bot s)]

/-! ### Relation to unsigned occurrences and countability -/

/-- Every signed occurrence of a relation symbol is an occurrence of that symbol. -/
theorem relationsInSigned_subset_relationsIn (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    φ.relationsInSigned s ⊆ φ.relationsIn := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => cases s <;> simp
  | imp φ ψ ihφ ihψ =>
    simp only [relationsInSigned_imp, relationsIn_imp]
    exact Set.union_subset_union (ihφ (!s)) (ihψ s)
  | all φ ih =>
    simpa only [relationsInSigned_all, relationsIn_all] using ih s
  | iSup φs ih =>
    simp only [relationsInSigned_iSup, relationsIn_iSup]
    exact Set.iUnion_mono fun i => ih i s
  | iInf φs ih =>
    simp only [relationsInSigned_iInf, relationsIn_iInf]
    exact Set.iUnion_mono fun i => ih i s

/-- Joining the occurrences of `φ` at opposite polarities recovers all occurring relation
symbols. -/
@[simp]
theorem relationsInSigned_union_not (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    φ.relationsInSigned s ∪ φ.relationsInSigned (!s) = φ.relationsIn := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => cases s <;> simp
  | imp φ ψ ihφ ihψ =>
    simp only [relationsInSigned_imp, Bool.not_not, relationsIn_imp]
    calc
      (φ.relationsInSigned (!s) ∪ ψ.relationsInSigned s) ∪
          (φ.relationsInSigned s ∪ ψ.relationsInSigned (!s)) =
          (φ.relationsInSigned (!s) ∪ φ.relationsInSigned s) ∪
            (ψ.relationsInSigned s ∪ ψ.relationsInSigned (!s)) :=
        Set.union_union_union_comm _ _ _ _
      _ = φ.relationsIn ∪ ψ.relationsIn := by
        rw [Set.union_comm (φ.relationsInSigned (!s)), ihφ s, ihψ s]
  | all φ ih =>
    simpa only [relationsInSigned_all, relationsIn_all] using ih s
  | iSup φs ih =>
    simp only [relationsInSigned_iSup, relationsIn_iSup, ← Set.iUnion_union_distrib, ih]
  | iInf φs ih =>
    simp only [relationsInSigned_iInf, relationsIn_iInf, ← Set.iUnion_union_distrib, ih]

/-- A biconditional uses both arguments in both polarities, so its signed occurrences at either
polarity are all relation symbols occurring in either side. -/
@[simp]
theorem relationsInSigned_iff (s : Bool) (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.iff ψ).relationsInSigned s = φ.relationsIn ∪ ψ.relationsIn := by
  simp only [iff_def, relationsInSigned_inf, relationsInSigned_imp]
  calc
    (φ.relationsInSigned (!s) ∪ ψ.relationsInSigned s) ∪
        (ψ.relationsInSigned (!s) ∪ φ.relationsInSigned s) =
        (φ.relationsInSigned s ∪ φ.relationsInSigned (!s)) ∪
          (ψ.relationsInSigned s ∪ ψ.relationsInSigned (!s)) := by ac_rfl
    _ = φ.relationsIn ∪ ψ.relationsIn := by simp

/-- At a countable branching carrier, the signed occurrence set at either polarity is countable. -/
theorem relationsInSigned_countable [Countable ι] (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    (φ.relationsInSigned s).Countable :=
  (relationsIn_countable φ).mono (relationsInSigned_subset_relationsIn s φ)

/-! ### Invariance under variable operations, carrier recoding, and countable conjunctions -/

/-- Relabelling bound positions preserves signed relation occurrences. -/
@[simp]
theorem relationsInSigned_mapBound (s : Bool) {m : ℕ} (f : Fin m → Fin n)
    (φ : L.BoundedFormulaInf ι α m) :
    (mapBound f φ).relationsInSigned s = φ.relationsInSigned s := by
  induction φ generalizing s n with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

@[simp]
theorem relationsInSigned_castLE (s : Bool) {m : ℕ} (h : m ≤ n)
    (φ : L.BoundedFormulaInf ι α m) :
    (castLE h φ).relationsInSigned s = φ.relationsInSigned s := by
  rw [castLE_def, relationsInSigned_mapBound]

/-- Changing the branching carrier by an index coding preserves signed relation occurrences. -/
@[simp]
theorem relationsInSigned_reindex (s : Bool) {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φ : L.BoundedFormulaInf ι α n) :
    (reindex c φ).relationsInSigned s = φ.relationsInSigned s := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Substituting terms for bound positions preserves signed relation occurrences. -/
@[simp]
theorem relationsInSigned_substBounds (s : Bool) {m k : ℕ}
    (σ : Fin m → L.Term (α ⊕ Fin k)) (φ : L.BoundedFormulaInf ι α m) :
    (substBounds σ φ).relationsInSigned s = φ.relationsInSigned s := by
  induction φ generalizing s k with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Instantiating the bound position of a formula at a term preserves signed relation
occurrences. -/
@[simp]
theorem relationsInSigned_inst (s : Bool) (φ : L.BoundedFormulaInf ι α 1)
    (t : L.Term (α ⊕ Fin 0)) :
    (φ.inst t).relationsInSigned s = φ.relationsInSigned s := by
  rw [inst_def, relationsInSigned_substBounds]

/-- Substituting terms for free variables preserves signed relation occurrences. -/
@[simp]
theorem relationsInSigned_subst {β : Type uβ} (s : Bool) (φ : L.BoundedFormulaInf ι α n)
    (f : α → L.Term β) :
    (TauCeti.BoundedFormulaInf.subst φ f).relationsInSigned s = φ.relationsInSigned s := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Relabelling free variables into free variables and new bound positions preserves signed
relation occurrences. -/
@[simp]
theorem relationsInSigned_relabel {β : Type uβ} {m : ℕ} (s : Bool) (g : α → β ⊕ Fin m)
    (φ : L.BoundedFormulaInf ι α n) :
    (TauCeti.BoundedFormulaInf.relabel g φ).relationsInSigned s = φ.relationsInSigned s := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Restoring constants in `L[[γ]]` maps signed relation occurrences along `lhomWithConstants`. -/
@[simp]
theorem relationsInSigned_constantsVarsEquiv_symm {γ : Type uγ} (s : Bool)
    (φ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    (constantsVarsEquiv.symm φ).relationsInSigned s =
      (fun r : Σ k, L.Relations k => ⟨r.1, (L.lhomWithConstants γ).onRelation r.2⟩) ''
        φ.relationsInSigned s := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel R ts =>
    rw [constantsVarsEquiv_symm_rel]
    cases s <;> simp [relationsInSigned]; rfl
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ, Set.image_union]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih, Set.image_iUnion]
  | iInf φs ih => simp [ih, Set.image_iUnion]

/-- Abstracting constants from `L[[γ]]` pulls signed relation occurrences back along
`lhomWithConstants`. -/
@[simp]
theorem relationsInSigned_constantsVarsEquiv {γ : Type uγ} (s : Bool)
    (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (constantsVarsEquiv φ).relationsInSigned s =
      (fun r : Σ k, L.Relations k => ⟨r.1, (L.lhomWithConstants γ).onRelation r.2⟩) ⁻¹'
        φ.relationsInSigned s := by
  conv_rhs =>
    rw [← constantsVarsEquiv.symm_apply_apply φ, relationsInSigned_constantsVarsEquiv_symm]
  exact ((Function.injective_id.sigma_map fun _ =>
    (L.lhomWithConstants_injective γ).onRelation).preimage_image _).symm

/-- Abstracting one constant preserves each relation polarity exactly. -/
@[simp]
theorem relationsInSigned_abstractConst {γ : Type uγ} [DecidableEq γ] (s : Bool)
    (c : γ) (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (abstractConst c φ).relationsInSigned s = φ.relationsInSigned s := by
  rw [abstractConst_def, relationsInSigned_constantsVarsEquiv_symm, relationsInSigned_mapBound,
    relationsInSigned_relabel, ← relationsInSigned_constantsVarsEquiv_symm s (constantsVarsEquiv φ),
    constantsVarsEquiv.symm_apply_apply]

/-! ### Polarity monotonicity of realization -/

/-- **Polarity monotonicity of realization.** On a single carrier `M`, if two `L`-structures `S`
and `S'` agree on every function symbol occurring in `φ`, every relation symbol occurring positively
in `φ` has `S.RelMap R ⊆ S'.RelMap R`, and every relation symbol occurring negatively in `φ` has
`S'.RelMap R ⊆ S.RelMap R`, then realization of `φ` transfers from `S` to `S'`. -/
theorem realize_mono_of_agreeOn_functionsIn {M : Type w} (φ : L.BoundedFormulaInf ι α n)
    (S S' : L.Structure M)
    (hF : ∀ {k} (f : L.Functions k), ⟨k, f⟩ ∈ φ.functionsIn →
      ∀ xs, @Structure.funMap L M S k f xs = @Structure.funMap L M S' k f xs)
    (hpos : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.positiveRelationsIn →
      ∀ xs, @Structure.RelMap L M S k R xs → @Structure.RelMap L M S' k R xs)
    (hneg : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.negativeRelationsIn →
      ∀ xs, @Structure.RelMap L M S' k R xs → @Structure.RelMap L M S k R xs)
    (v : α → M) (xs : Fin n → M) :
    @Realize L ι α M S n φ v xs → @Realize L ι α M S' n φ v xs := by
  induction φ generalizing S S' with
  | falsum => simp
  | equal t₁ t₂ =>
    rw [functionsIn_equal] at hF
    simp only [realize_equal]
    rw [t₁.realize_congr_of_agreeOn S S' (fun f hf => hF f (Set.mem_union_left _ hf)),
      t₂.realize_congr_of_agreeOn S S' (fun f hf => hF f (Set.mem_union_right _ hf))]
    exact id
  | rel R ts =>
    rw [functionsIn_rel] at hF
    simp only [realize_rel]
    have ht : ∀ i, @Term.realize L M S _ (Sum.elim v xs) (ts i) =
        @Term.realize L M S' _ (Sum.elim v xs) (ts i) := fun i =>
      (ts i).realize_congr_of_agreeOn S S'
        (fun f hf => hF f (Set.mem_iUnion.mpr ⟨i, hf⟩)) _
    simp_rw [ht]
    exact hpos R (by simp) _
  | imp φ ψ ihφ ihψ =>
    rw [functionsIn_imp] at hF
    simp only [realize_imp]
    intro h hφ'
    -- The antecedent `φ` flips `S` and `S'`: its positive occurrences lie in `negativeRelationsIn`
    -- of `φ.imp ψ`, and its negative occurrences lie in `positiveRelationsIn` of `φ.imp ψ`.
    refine ihψ S S' (fun f hf => hF f (Set.mem_union_right _ hf))
      (fun R hR => hpos R (Set.mem_union_right _ hR))
      (fun R hR => hneg R (Set.mem_union_right _ hR)) xs (h ?_)
    exact ihφ S' S (fun f hf xs' => (hF f (Set.mem_union_left _ hf) xs').symm)
      (fun R hR => hneg R (Set.mem_union_left _ hR))
      (fun R hR => hpos R (Set.mem_union_left _ hR)) xs hφ'
  | all φ ih =>
    rw [functionsIn_all] at hF
    simp only [realize_all]
    exact fun h y => ih S S' hF hpos hneg (Fin.snoc xs y) (h y)
  | iSup φs ih =>
    rw [functionsIn_iSup] at hF
    simp only [realize_iSup]
    exact Exists.imp fun i => ih i S S'
      (fun f hf => hF f (Set.mem_iUnion.mpr ⟨i, hf⟩))
      (fun R hR => hpos R (Set.mem_iUnion.mpr ⟨i, hR⟩))
      (fun R hR => hneg R (Set.mem_iUnion.mpr ⟨i, hR⟩)) xs
  | iInf φs ih =>
    rw [functionsIn_iInf] at hF
    simp only [realize_iInf]
    exact fun h i => ih i S S'
      (fun f hf => hF f (Set.mem_iUnion.mpr ⟨i, hf⟩))
      (fun R hR => hpos R (Set.mem_iUnion.mpr ⟨i, hR⟩))
      (fun R hR => hneg R (Set.mem_iUnion.mpr ⟨i, hR⟩)) xs (h i)

/-- **Polarity monotonicity for relational languages.** When `L` has no function symbols, enlarging
positively occurring relations and shrinking negatively occurring relations preserves
realization. -/
theorem realize_mono_of_signed [L.IsRelational] {M : Type w} (φ : L.BoundedFormulaInf ι α n)
    (S S' : L.Structure M)
    (hpos : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.positiveRelationsIn →
      ∀ xs, @Structure.RelMap L M S k R xs → @Structure.RelMap L M S' k R xs)
    (hneg : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.negativeRelationsIn →
      ∀ xs, @Structure.RelMap L M S' k R xs → @Structure.RelMap L M S k R xs)
    (v : α → M) (xs : Fin n → M) :
    @Realize L ι α M S n φ v xs → @Realize L ι α M S' n φ v xs :=
  φ.realize_mono_of_agreeOn_functionsIn S S' (fun f => isEmptyElim f) hpos hneg v xs

end BoundedFormulaInf

namespace SentenceInf

variable {L : Language.{u, v}} {ι : Type uι}

/-- Sentence-level polarity monotonicity under agreement on occurring function symbols. -/
theorem realize_mono_of_agreeOn_functionsIn {M : Type w} (φ : L.SentenceInf ι)
    (S S' : L.Structure M)
    (hF : ∀ {k} (f : L.Functions k), ⟨k, f⟩ ∈ φ.functionsIn →
      ∀ xs, @Structure.funMap L M S k f xs = @Structure.funMap L M S' k f xs)
    (hpos : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.positiveRelationsIn →
      ∀ xs, @Structure.RelMap L M S k R xs → @Structure.RelMap L M S' k R xs)
    (hneg : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.negativeRelationsIn →
      ∀ xs, @Structure.RelMap L M S' k R xs → @Structure.RelMap L M S k R xs) :
    @Realize L ι φ M S → @Realize L ι φ M S' := by
  rw [@SentenceInf.realize_def L ι φ M S, @FormulaInf.realize_def L ι Empty M S φ,
    @SentenceInf.realize_def L ι φ M S', @FormulaInf.realize_def L ι Empty M S' φ]
  exact BoundedFormulaInf.realize_mono_of_agreeOn_functionsIn φ S S' hF hpos hneg
    Empty.elim default

/-- Sentence-level polarity monotonicity for relational languages. -/
theorem realize_mono_of_signed [L.IsRelational] {M : Type w} (φ : L.SentenceInf ι)
    (S S' : L.Structure M)
    (hpos : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.positiveRelationsIn →
      ∀ xs, @Structure.RelMap L M S k R xs → @Structure.RelMap L M S' k R xs)
    (hneg : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.negativeRelationsIn →
      ∀ xs, @Structure.RelMap L M S' k R xs → @Structure.RelMap L M S k R xs) :
    @Realize L ι φ M S → @Realize L ι φ M S' :=
  realize_mono_of_agreeOn_functionsIn φ S S' (fun f => isEmptyElim f) hpos hneg

end SentenceInf

namespace Theoryω

variable {L : Language.{u, v}}

/-- The signed relation occurrences of the conjunction of a countable theory are the union of the
signed occurrences of its member sentences. -/
@[simp]
theorem relationsInSigned_conjunction (s : Bool) {T : L.Theoryω} (hT : T.Countable) :
    (T.conjunction hT).relationsInSigned s = ⋃ φ ∈ T, φ.relationsInSigned s := by
  rw [conjunction_def, BoundedFormulaInf.relationsInSigned_iInfAlong, Set.biUnion_eq_iUnion]

end Theoryω

/-! ### Language homomorphisms, symbol sublanguages, and signed pullback -/

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι : Type uι} {α : Type uα}

/-- Language translation takes signed relation occurrences to their exact image. -/
@[simp]
theorem relationsInSigned_onBoundedFormulaInf {n : ℕ} (g : L →ᴸ L') (s : Bool)
    (φ : L.BoundedFormulaInf ι α n) :
    (g.onBoundedFormulaInf φ).relationsInSigned s =
      (fun r : Σ k, L.Relations k => ⟨r.1, g.onRelation r.2⟩) '' φ.relationsInSigned s := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel R ts => cases s <;> simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ, Set.image_union]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih, Set.image_iUnion]
  | iInf φs ih => simp [ih, Set.image_iUnion]

/-- Along a language homomorphism injective on relation symbols, pulling back the signed
occurrences of a translated formula recovers the signed occurrences of the original formula. -/
theorem preimage_relationsInSigned_onBoundedFormulaInf {n : ℕ} (g : L →ᴸ L')
    (hg : ∀ k, Function.Injective (g.onRelation (n := k))) (s : Bool)
    (φ : L.BoundedFormulaInf ι α n) :
    (fun r : Σ k, L.Relations k => ⟨r.1, g.onRelation r.2⟩) ⁻¹'
        (g.onBoundedFormulaInf φ).relationsInSigned s =
      φ.relationsInSigned s := by
  rw [relationsInSigned_onBoundedFormulaInf]
  exact (Function.injective_id.sigma_map hg).preimage_image _

/-- **Signed pullback along a language homomorphism.** An infinitary formula `φ` of `L'` whose
occurring function symbols, positive relation symbols, and negative relation symbols lie in the
images under `g : L →ᴸ L'` of `F`, `P`, and `N` is the image under `g` of a formula `ψ` of `L`
whose occurring function symbols, positive relation symbols, and negative relation symbols lie in
`F`, `P`, and `N` respectively.

No injectivity of `g` is assumed: distinct relation symbols in `P` and `N` mapping to the same
symbol of `L'` are chosen separately at positive and negative occurrences. -/
theorem exists_eq_onBoundedFormulaInf_of_relationsInSigned_subset {n : ℕ} (g : L →ᴸ L')
    {F : Set (Σ k, L.Functions k)} {P N : Set (Σ k, L.Relations k)}
    (φ : L'.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ (fun s : Σ k, L.Functions k => ⟨s.1, g.onFunction s.2⟩) '' F)
    (hP : φ.positiveRelationsIn ⊆ (fun s : Σ k, L.Relations k => ⟨s.1, g.onRelation s.2⟩) '' P)
    (hN : φ.negativeRelationsIn ⊆ (fun s : Σ k, L.Relations k => ⟨s.1, g.onRelation s.2⟩) '' N) :
    ∃ ψ : L.BoundedFormulaInf ι α n,
      g.onBoundedFormulaInf ψ = φ ∧ ψ.functionsIn ⊆ F ∧
        ψ.positiveRelationsIn ⊆ P ∧ ψ.negativeRelationsIn ⊆ N := by
  induction φ generalizing P N with
  | falsum => exact ⟨.falsum, by simp, by simp, by simp, by simp⟩
  | equal t₁ t₂ =>
    rw [BoundedFormulaInf.functionsIn_equal] at hF
    obtain ⟨t₁₀, ht₁, ht₁F⟩ := g.exists_eq_onTerm_of_functionsIn_subset t₁
      (Set.Subset.trans Set.subset_union_left hF)
    obtain ⟨t₂₀, ht₂, ht₂F⟩ := g.exists_eq_onTerm_of_functionsIn_subset t₂
      (Set.Subset.trans Set.subset_union_right hF)
    refine ⟨.equal t₁₀ t₂₀, by simp [ht₁, ht₂], ?_, by simp, by simp⟩
    rw [BoundedFormulaInf.functionsIn_equal]
    exact Set.union_subset ht₁F ht₂F
  | @rel m k R ts =>
    rw [BoundedFormulaInf.functionsIn_rel] at hF
    obtain ⟨⟨k₀, R₀⟩, hR₀P, hRk⟩ := hP rfl
    cases hRk
    have hts : ∀ i, ∃ t₀ : L.Term (α ⊕ Fin m), g.onTerm t₀ = ts i ∧ t₀.functionsIn ⊆ F :=
      fun i => g.exists_eq_onTerm_of_functionsIn_subset (ts i)
        ((Set.subset_iUnion (fun j => (ts j).functionsIn) i).trans hF)
    choose ts₀ hts₀ hts₀F using hts
    refine ⟨.rel R₀ ts₀, by simp [hts₀], ?_, Set.singleton_subset_iff.mpr hR₀P, by simp⟩
    rw [BoundedFormulaInf.functionsIn_rel]
    exact Set.iUnion_subset hts₀F
  | imp φ₁ φ₂ ih₁ ih₂ =>
    rw [BoundedFormulaInf.functionsIn_imp] at hF
    -- The antecedent swaps `P` and `N`, matching the flipped polarity of `relationsInSigned_imp`.
    obtain ⟨ψ₁, hψ₁, hψ₁F, hψ₁N, hψ₁P⟩ := ih₁
      (Set.Subset.trans Set.subset_union_left hF)
      (Set.Subset.trans Set.subset_union_left hN)
      (Set.Subset.trans Set.subset_union_left hP)
    obtain ⟨ψ₂, hψ₂, hψ₂F, hψ₂P, hψ₂N⟩ := ih₂
      (Set.Subset.trans Set.subset_union_right hF)
      (Set.Subset.trans Set.subset_union_right hP)
      (Set.Subset.trans Set.subset_union_right hN)
    refine ⟨ψ₁.imp ψ₂, by simp [hψ₁, hψ₂], ?_,
      Set.union_subset hψ₁P hψ₂P, Set.union_subset hψ₁N hψ₂N⟩
    rw [BoundedFormulaInf.functionsIn_imp]
    exact Set.union_subset hψ₁F hψ₂F
  | all φ ih =>
    rw [BoundedFormulaInf.functionsIn_all] at hF
    obtain ⟨ψ, hψ, hψF, hψP, hψN⟩ := ih hF hP hN
    refine ⟨ψ.all, by simp [hψ], ?_, hψP, hψN⟩
    rwa [BoundedFormulaInf.functionsIn_all]
  | @iSup m φs ih =>
    rw [BoundedFormulaInf.functionsIn_iSup] at hF
    have hbranch : ∀ i, ∃ ψ : L.BoundedFormulaInf ι α m,
        g.onBoundedFormulaInf ψ = φs i ∧ ψ.functionsIn ⊆ F ∧
          ψ.positiveRelationsIn ⊆ P ∧ ψ.negativeRelationsIn ⊆ N := fun i =>
      ih i ((Set.subset_iUnion (fun j => (φs j).functionsIn) i).trans hF)
        ((Set.subset_iUnion (fun j => (φs j).positiveRelationsIn) i).trans hP)
        ((Set.subset_iUnion (fun j => (φs j).negativeRelationsIn) i).trans hN)
    choose ψs hψs hψsF hψsP hψsN using hbranch
    refine ⟨.iSup ψs, by rw [onBoundedFormulaInf_iSup, funext hψs], ?_,
      Set.iUnion_subset hψsP, Set.iUnion_subset hψsN⟩
    rw [BoundedFormulaInf.functionsIn_iSup]
    exact Set.iUnion_subset hψsF
  | @iInf m φs ih =>
    rw [BoundedFormulaInf.functionsIn_iInf] at hF
    have hbranch : ∀ i, ∃ ψ : L.BoundedFormulaInf ι α m,
        g.onBoundedFormulaInf ψ = φs i ∧ ψ.functionsIn ⊆ F ∧
          ψ.positiveRelationsIn ⊆ P ∧ ψ.negativeRelationsIn ⊆ N := fun i =>
      ih i ((Set.subset_iUnion (fun j => (φs j).functionsIn) i).trans hF)
        ((Set.subset_iUnion (fun j => (φs j).positiveRelationsIn) i).trans hP)
        ((Set.subset_iUnion (fun j => (φs j).negativeRelationsIn) i).trans hN)
    choose ψs hψs hψsF hψsP hψsN using hbranch
    refine ⟨.iInf ψs, by rw [onBoundedFormulaInf_iInf, funext hψs], ?_,
      Set.iUnion_subset hψsP, Set.iUnion_subset hψsN⟩
    rw [BoundedFormulaInf.functionsIn_iInf]
    exact Set.iUnion_subset hψsF

end LHom

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}

/-- Restricting a formula to a symbol sublanguage pulls its signed relation occurrences back along
the sublanguage inclusion. -/
@[simp]
theorem relationsInSigned_restrictSymbols {F : Set (Σ k, L.Functions k)}
    {R : Set (Σ k, L.Relations k)} (s : Bool) (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) :
    (φ.restrictSymbols hF hR).relationsInSigned s =
      (fun r : Σ k, (symbSublang F R).Relations k => (⟨r.1, r.2.1⟩ : Σ k, L.Relations k)) ⁻¹'
        φ.relationsInSigned s := by
  have h := (symbSublangIncl F R).preimage_relationsInSigned_onBoundedFormulaInf
    (fun _ => (symbSublangIncl_injective F R).onRelation) s (φ.restrictSymbols hF hR)
  rw [onBoundedFormulaInf_restrictSymbols] at h
  simpa only [symbSublangIncl_onRelation] using h.symm

end BoundedFormulaInf

end FirstOrder.Language
