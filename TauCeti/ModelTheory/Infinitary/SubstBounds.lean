/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Symbols
public import TauCeti.ModelTheory.Term.Substitution

/-!
# Substitution for bound positions of infinitary formulas

`BoundedFormulaInf.substBounds σ φ` replaces the bound position `i` of an infinitary formula
`φ` with `m` bound positions by the term `σ i`, whose variables are the free variables `α` and
`k` bound positions. Free variables are left in place. Past a quantifier the substitution is
lifted by `BoundedFormulaInf.liftSubst`: the old positions of the substituted terms shift by
`Fin.castSucc`, and the newly quantified position goes to the new last position, so no
substituted term is captured by a binder.

Bound substitution generalizes the relabelling `BoundedFormulaInf.mapBound`, which substitutes
bound positions for bound positions. It instantiates a formula with a bound position at a closed
term (`BoundedFormulaInf.inst`), as the quantifier clauses of a consistency property require,
and more generally instantiates the `n` bound positions of a formula at a tuple of terms.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.liftSubst`: a bound substitution lifted past a
  quantifier.
* `FirstOrder.Language.BoundedFormulaInf.substBounds`: substitution of terms for bound positions.
* `FirstOrder.Language.BoundedFormulaInf.inst`: instantiation of the single bound position of a
  formula at a term.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.realize_substBounds`: the substituted formula is
  realized at `xs` exactly when the original is realized at the values of the substituted terms.
* `FirstOrder.Language.BoundedFormulaInf.substBounds_var` and
  `FirstOrder.Language.BoundedFormulaInf.substBounds_substBounds`: identity and composition.
* `FirstOrder.Language.BoundedFormulaInf.mapBound_eq_substBounds`: relabelling is substitution of
  bound positions for bound positions.
* `FirstOrder.Language.BoundedFormulaInf.inst_substBounds_liftSubst`: instantiating the body of a
  quantified formula after substituting closed terms extends the tuple of substituted terms.
* `FirstOrder.Language.BoundedFormulaInf.IsAtomic.substBounds`: bound substitution keeps atomic
  formulas atomic.
* `FirstOrder.Language.LHom.onBoundedFormulaInf_substBounds`: language maps commute with bound
  substitution.
* `FirstOrder.Language.BoundedFormulaInf.relationsIn_substBounds`,
  `FirstOrder.Language.BoundedFormulaInf.functionsIn_subset_functionsIn_substBounds` and
  `FirstOrder.Language.BoundedFormulaInf.functionsIn_substBounds_subset`: bound substitution keeps
  the relation symbols, keeps the function symbols, and adds at most the function symbols of the
  substituted terms.

## References

* The construction follows Mathlib's finitary `BoundedFormula.subst`, which substitutes terms for
  free variables through `Term.subst`, with binders handled as in `BoundedFormulaInf.mapBound`.
-/

public section

universe u v u' v' uι uα w

namespace FirstOrder.Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα}

open Term

/-- Lift a substitution for bound positions past a quantifier: each substituted term has its
bound positions shifted by `Fin.castSucc`, and the newly quantified position goes to the new last
position. -/
def liftSubst {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) :
    Fin (m + 1) → L.Term (α ⊕ Fin (k + 1)) :=
  Fin.snoc (fun i => (σ i).relabel (Sum.map id Fin.castSucc)) (var (Sum.inr (Fin.last k)))

/-- A lifted substitution shifts the bound positions of each old substituted term. -/
@[simp]
theorem liftSubst_castSucc {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) (i : Fin m) :
    liftSubst σ i.castSucc = (σ i).relabel (Sum.map id Fin.castSucc) := by
  simp [liftSubst]

/-- A lifted substitution sends the newly quantified position to the new last position. -/
@[simp]
theorem liftSubst_last {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) :
    liftSubst σ (Fin.last m) = var (Sum.inr (Fin.last k)) := by
  simp [liftSubst]

/-- **Substitute terms for the bound positions** of an infinitary formula: bound position `i` is
replaced by `σ i`, and free variables are kept. Past a quantifier, `σ` is lifted by
`liftSubst`, so the substituted terms are not captured. -/
def substBounds : ∀ {m k : ℕ}, (Fin m → L.Term (α ⊕ Fin k)) → L.BoundedFormulaInf ι α m →
    L.BoundedFormulaInf ι α k
  | _, _, _, .falsum => .falsum
  | _, _, σ, .equal t₁ t₂ =>
    .equal (t₁.subst (Sum.elim (var ∘ Sum.inl) σ)) (t₂.subst (Sum.elim (var ∘ Sum.inl) σ))
  | _, _, σ, .rel R ts => .rel R fun i => (ts i).subst (Sum.elim (var ∘ Sum.inl) σ)
  | _, _, σ, .imp φ ψ => (substBounds σ φ).imp (substBounds σ ψ)
  | _, _, σ, .all φ => (substBounds (liftSubst σ) φ).all
  | _, _, σ, .iSup φs => .iSup fun i => substBounds σ (φs i)
  | _, _, σ, .iInf φs => .iInf fun i => substBounds σ (φs i)

section SubstBoundsEqs

variable {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k))

@[simp]
theorem substBounds_falsum : substBounds σ (.falsum : L.BoundedFormulaInf ι α m) = .falsum :=
  (rfl)

@[simp]
theorem substBounds_equal (t₁ t₂ : L.Term (α ⊕ Fin m)) :
    substBounds σ (.equal t₁ t₂ : L.BoundedFormulaInf ι α m) =
      .equal (t₁.subst (Sum.elim (var ∘ Sum.inl) σ)) (t₂.subst (Sum.elim (var ∘ Sum.inl) σ)) :=
  (rfl)

@[simp]
theorem substBounds_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin m)) :
    substBounds σ (.rel R ts : L.BoundedFormulaInf ι α m) =
      .rel R fun i => (ts i).subst (Sum.elim (var ∘ Sum.inl) σ) :=
  (rfl)

@[simp]
theorem substBounds_imp (φ ψ : L.BoundedFormulaInf ι α m) :
    substBounds σ (φ.imp ψ) = (substBounds σ φ).imp (substBounds σ ψ) := (rfl)

@[simp]
theorem substBounds_all (φ : L.BoundedFormulaInf ι α (m + 1)) :
    substBounds σ φ.all = (substBounds (liftSubst σ) φ).all := (rfl)

@[simp]
theorem substBounds_iSup (φs : ι → L.BoundedFormulaInf ι α m) :
    substBounds σ (.iSup φs) = .iSup fun i => substBounds σ (φs i) := (rfl)

@[simp]
theorem substBounds_iInf (φs : ι → L.BoundedFormulaInf ι α m) :
    substBounds σ (.iInf φs) = .iInf fun i => substBounds σ (φs i) := (rfl)

@[simp]
theorem substBounds_not (φ : L.BoundedFormulaInf ι α m) :
    substBounds σ φ.not = (substBounds σ φ).not := (rfl)

@[simp]
theorem substBounds_ex (φ : L.BoundedFormulaInf ι α (m + 1)) :
    substBounds σ φ.ex = (substBounds (liftSubst σ) φ).ex := (rfl)

@[simp]
theorem substBounds_bot : substBounds σ (⊥ : L.BoundedFormulaInf ι α m) = ⊥ := (rfl)

@[simp]
theorem substBounds_top : substBounds σ (⊤ : L.BoundedFormulaInf ι α m) = ⊤ := by
  rw [top_def, top_def, substBounds_not, substBounds_falsum]

@[simp]
theorem substBounds_inf (φ ψ : L.BoundedFormulaInf ι α m) :
    substBounds σ (φ ⊓ ψ) = substBounds σ φ ⊓ substBounds σ ψ := by
  simp [inf_def]

@[simp]
theorem substBounds_sup (φ ψ : L.BoundedFormulaInf ι α m) :
    substBounds σ (φ ⊔ ψ) = substBounds σ φ ⊔ substBounds σ ψ := by
  simp [sup_def]

@[simp]
theorem substBounds_iff (φ ψ : L.BoundedFormulaInf ι α m) :
    substBounds σ (φ.iff ψ) = (substBounds σ φ).iff (substBounds σ ψ) := by
  simp [iff_def]

end SubstBoundsEqs

/-- The valuation of an atom's variables after bound substitution. -/
private theorem realize_sumElim_comp {M : Type w} [L.Structure M] {m k : ℕ}
    (σ : Fin m → L.Term (α ⊕ Fin k)) (v : α → M) (xs : Fin k → M) :
    (fun a => (Sum.elim (var ∘ Sum.inl) σ a).realize (Sum.elim v xs)) =
      Sum.elim v fun i => (σ i).realize (Sum.elim v xs) := by
  funext a
  cases a <;> rfl

/-- The values of a lifted substitution, at an extended valuation. -/
private theorem realize_liftSubst {M : Type w} [L.Structure M] {m k : ℕ}
    (σ : Fin m → L.Term (α ⊕ Fin k)) (v : α → M) (xs : Fin k → M) (y : M) :
    (fun i => (liftSubst σ i).realize (Sum.elim v (Fin.snoc xs y))) =
      Fin.snoc (fun i => (σ i).realize (Sum.elim v xs)) y := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [Sum.elim_comp_map]

/-- **Bound substitution is realization at the substituted values**: the substituted formula is
realized at `xs` exactly when the original is realized at the values of the substituted terms. -/
@[simp]
theorem realize_substBounds {M : Type w} [L.Structure M] :
    ∀ {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) (φ : L.BoundedFormulaInf ι α m) (v : α → M)
      (xs : Fin k → M),
      (substBounds σ φ).Realize v xs ↔ φ.Realize v fun i => (σ i).realize (Sum.elim v xs) := by
  intro m k σ φ
  induction φ generalizing k with
  | falsum => intro v xs; simp
  | equal t₁ t₂ =>
    intro v xs
    simp only [substBounds_equal, realize_equal, realize_subst, realize_sumElim_comp]
  | rel R ts =>
    intro v xs
    simp only [substBounds_rel, realize_rel, realize_subst, realize_sumElim_comp]
  | imp φ ψ ihφ ihψ => intro v xs; simp only [substBounds_imp, realize_imp, ihφ, ihψ]
  | all φ ih => intro v xs; simp only [substBounds_all, realize_all, ih, realize_liftSubst]
  | iSup φs ih => intro v xs; simp only [substBounds_iSup, realize_iSup, ih]
  | iInf φs ih => intro v xs; simp only [substBounds_iInf, realize_iInf, ih]

/-- Substituting each bound position by itself is the identity. -/
@[simp]
theorem substBounds_var : ∀ {m : ℕ} (φ : L.BoundedFormulaInf ι α m),
    substBounds (fun i => var (Sum.inr i)) φ = φ := by
  have hvar {m : ℕ} :
      (Sum.elim (var ∘ Sum.inl) fun i => var (Sum.inr i) : α ⊕ Fin m → L.Term (α ⊕ Fin m)) =
        var := by
    funext a
    cases a <;> rfl
  have hlift {m : ℕ} :
      liftSubst (fun i => var (Sum.inr i) : Fin m → L.Term (α ⊕ Fin m)) =
        fun i => var (Sum.inr i) := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  intro m φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [hvar]
  | rel R ts => simp [hvar]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp only [substBounds_all, hlift, ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Two successive bound substitutions are one: substitute `σ`, then `τ` into the terms of `σ`. -/
@[simp]
theorem substBounds_substBounds : ∀ {m k l : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k))
    (τ : Fin k → L.Term (α ⊕ Fin l)) (φ : L.BoundedFormulaInf ι α m),
    substBounds τ (substBounds σ φ) =
      substBounds (fun i => (σ i).subst (Sum.elim (var ∘ Sum.inl) τ)) φ := by
  have hcomp {m k l : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) (τ : Fin k → L.Term (α ⊕ Fin l)) :
      (fun a => (Sum.elim (var ∘ Sum.inl) σ a).subst (Sum.elim (var ∘ Sum.inl) τ)) =
        Sum.elim (var ∘ Sum.inl) fun i => (σ i).subst (Sum.elim (var ∘ Sum.inl) τ) := by
    funext a
    cases a <;> rfl
  have hlift {m k l : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) (τ : Fin k → L.Term (α ⊕ Fin l)) :
      (fun i => (liftSubst σ i).subst (Sum.elim (var ∘ Sum.inl) (liftSubst τ))) =
        liftSubst fun i => (σ i).subst (Sum.elim (var ∘ Sum.inl) τ) := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [liftSubst_castSucc, subst_relabel, relabel_subst]
      congr 1
      funext a
      cases a <;> simp
  intro m k l σ τ φ
  induction φ generalizing k l with
  | falsum => rfl
  | equal t₁ t₂ => simp [hcomp]
  | rel R ts => simp [hcomp]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp only [substBounds_all, ih, hlift]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- **Relabelling is bound substitution** of bound positions for bound positions. -/
theorem mapBound_eq_substBounds : ∀ {m n : ℕ} (f : Fin m → Fin n) (φ : L.BoundedFormulaInf ι α m),
    mapBound f φ = substBounds (fun i => var (Sum.inr (f i))) φ := by
  have hvar {m n : ℕ} (f : Fin m → Fin n) :
      (var ∘ Sum.map id f : α ⊕ Fin m → L.Term (α ⊕ Fin n)) =
        Sum.elim (var ∘ Sum.inl) fun i => var (Sum.inr (f i)) := by
    funext a
    cases a <;> rfl
  have hlift {m n : ℕ} (f : Fin m → Fin n) :
      liftSubst (fun i => var (Sum.inr (f i)) : Fin m → L.Term (α ⊕ Fin n)) =
        fun i => var (Sum.inr (Fin.snoc (α := fun _ => Fin (n + 1)) (fun i => (f i).castSucc)
          (Fin.last n) i)) := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  intro m n f φ
  induction φ generalizing n with
  | falsum => simp
  | equal t₁ t₂ => simp [relabel_eq_subst, hvar]
  | rel R ts => simp [relabel_eq_subst, hvar]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp only [mapBound_all, substBounds_all, ih, hlift]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-! ### Instantiation -/

/-- **Instantiate** the single bound position of `φ` at the term `t`. For a sentence-level
`φ : L.BoundedFormulaInf ι Empty 1` and a closed term `t`, this is the sentence `φ[t]`. -/
def inst (φ : L.BoundedFormulaInf ι α 1) (t : L.Term (α ⊕ Fin 0)) : L.FormulaInf ι α :=
  substBounds (fun _ => t) φ

theorem inst_def (φ : L.BoundedFormulaInf ι α 1) (t : L.Term (α ⊕ Fin 0)) :
    φ.inst t = substBounds (fun _ => t) φ := (rfl)

/-- An instance `φ[t]` holds exactly when `φ` holds at the value of `t`. -/
@[simp]
theorem realize_inst {M : Type w} [L.Structure M] (φ : L.BoundedFormulaInf ι α 1)
    (t : L.Term (α ⊕ Fin 0)) (v : α → M) :
    (φ.inst t).Realize v ↔ φ.Realize v fun _ => t.realize (Sum.elim v default) :=
  (FormulaInf.realize_def _ v).trans (realize_substBounds _ φ v default)

/-- Instantiating at `t` the body of a quantified formula whose outer bound positions were
substituted by the closed terms `σ` substitutes the extended tuple `Fin.snoc σ t`. -/
theorem inst_substBounds_liftSubst {n : ℕ} (σ : Fin n → L.Term (α ⊕ Fin 0))
    (φ : L.BoundedFormulaInf ι α (n + 1)) (t : L.Term (α ⊕ Fin 0)) :
    (substBounds (liftSubst σ) φ).inst t = substBounds (Fin.snoc σ t) φ := by
  rw [inst_def, substBounds_substBounds]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i =>
    rw [liftSubst_castSucc, subst_relabel, Fin.snoc_castSucc]
    conv_rhs => rw [← subst_var (σ i)]
    congr 1
    funext a
    rcases a with a | a
    · rfl
    · exact a.elim0

/-- Bound substitution sends atomic formulas to atomic formulas. -/
theorem IsAtomic.substBounds {m k : ℕ} {φ : L.BoundedFormulaInf ι α m} (h : φ.IsAtomic)
    (σ : Fin m → L.Term (α ⊕ Fin k)) : (BoundedFormulaInf.substBounds σ φ).IsAtomic := by
  cases h with
  | equal t₁ t₂ => exact .equal _ _
  | rel R ts => exact .rel _ _

/-! ### Occurring symbols -/

/-- Bound substitution keeps exactly the relation symbols of the formula. -/
@[simp]
theorem relationsIn_substBounds : ∀ {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k))
    (φ : L.BoundedFormulaInf ι α m), (substBounds σ φ).relationsIn = φ.relationsIn := by
  intro m k σ φ
  induction φ generalizing k with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Bound substitution keeps every function symbol of the formula. -/
theorem functionsIn_subset_functionsIn_substBounds : ∀ {m k : ℕ}
    (σ : Fin m → L.Term (α ⊕ Fin k)) (φ : L.BoundedFormulaInf ι α m),
    φ.functionsIn ⊆ (substBounds σ φ).functionsIn := by
  intro m k σ φ
  induction φ generalizing k with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [substBounds_equal, functionsIn_equal]
    exact Set.union_subset_union (t₁.functionsIn_subset_functionsIn_subst _)
      (t₂.functionsIn_subset_functionsIn_subst _)
  | rel R ts =>
    simp only [substBounds_rel, functionsIn_rel]
    exact Set.iUnion_mono fun i => (ts i).functionsIn_subset_functionsIn_subst _
  | imp φ ψ ihφ ihψ =>
    simp only [substBounds_imp, functionsIn_imp]
    exact Set.union_subset_union (ihφ σ) (ihψ σ)
  | all φ ih =>
    simp only [substBounds_all, functionsIn_all]
    exact ih _
  | iSup φs ih =>
    simp only [substBounds_iSup, functionsIn_iSup]
    exact Set.iUnion_mono fun i => ih i σ
  | iInf φs ih =>
    simp only [substBounds_iInf, functionsIn_iInf]
    exact Set.iUnion_mono fun i => ih i σ

/-- Bound substitution adds at most the function symbols of the substituted terms. -/
theorem functionsIn_substBounds_subset : ∀ {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k))
    (φ : L.BoundedFormulaInf ι α m),
    (substBounds σ φ).functionsIn ⊆ φ.functionsIn ∪ ⋃ i, (σ i).functionsIn := by
  -- the function symbols of the substitution used at an atom
  have hatom {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) (t : L.Term (α ⊕ Fin m)) :
      (t.subst (Sum.elim (var ∘ Sum.inl) σ)).functionsIn ⊆
        t.functionsIn ∪ ⋃ i, (σ i).functionsIn := by
    refine (t.functionsIn_subst_subset _).trans (Set.union_subset_union_right _ ?_)
    refine Set.iUnion_subset fun a => ?_
    cases a with
    | inl a => simp
    | inr i => exact Set.subset_iUnion (fun i => (σ i).functionsIn) i
  have hlift {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) :
      ⋃ i, (liftSubst σ i).functionsIn ⊆ ⋃ i, (σ i).functionsIn := by
    refine Set.iUnion_subset fun i => ?_
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa using Set.subset_iUnion (fun i => (σ i).functionsIn) i
  intro m k σ φ
  induction φ generalizing k with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [substBounds_equal, functionsIn_equal]
    refine Set.union_subset ((hatom σ t₁).trans ?_) ((hatom σ t₂).trans ?_) <;>
      exact Set.union_subset_union_left _ (by simp)
  | rel R ts =>
    simp only [substBounds_rel, functionsIn_rel]
    refine Set.iUnion_subset fun i => (hatom σ (ts i)).trans ?_
    exact Set.union_subset_union_left _ (Set.subset_iUnion (fun i => (ts i).functionsIn) i)
  | imp φ ψ ihφ ihψ =>
    simp only [substBounds_imp, functionsIn_imp]
    refine Set.union_subset ((ihφ σ).trans ?_) ((ihψ σ).trans ?_) <;>
      exact Set.union_subset_union_left _ (by simp)
  | all φ ih =>
    simp only [substBounds_all, functionsIn_all]
    exact (ih _).trans (Set.union_subset_union_right _ (hlift σ))
  | iSup φs ih =>
    simp only [substBounds_iSup, functionsIn_iSup]
    refine Set.iUnion_subset fun i => (ih i σ).trans ?_
    exact Set.union_subset_union_left _ (Set.subset_iUnion (fun i => (φs i).functionsIn) i)
  | iInf φs ih =>
    simp only [substBounds_iInf, functionsIn_iInf]
    refine Set.iUnion_subset fun i => (ih i σ).trans ?_
    exact Set.union_subset_union_left _ (Set.subset_iUnion (fun i => (φs i).functionsIn) i)

end BoundedFormulaInf

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι : Type uι} {α : Type uα}

open Term BoundedFormulaInf

/-- **Language maps commute with bound substitution**, acting on the substituted terms. -/
@[simp]
theorem onBoundedFormulaInf_substBounds (g : L →ᴸ L') : ∀ {m k : ℕ}
    (σ : Fin m → L.Term (α ⊕ Fin k)) (φ : L.BoundedFormulaInf ι α m),
    g.onBoundedFormulaInf (substBounds σ φ) =
      substBounds (fun i => g.onTerm (σ i)) (g.onBoundedFormulaInf φ) := by
  have hatom {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) :
      (fun a => g.onTerm (Sum.elim (var ∘ Sum.inl) σ a)) =
        Sum.elim (var ∘ Sum.inl) fun i => g.onTerm (σ i) := by
    funext a
    cases a <;> rfl
  have hlift {m k : ℕ} (σ : Fin m → L.Term (α ⊕ Fin k)) :
      (fun i => g.onTerm (liftSubst σ i)) = liftSubst fun i => g.onTerm (σ i) := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  intro m k σ φ
  induction φ generalizing k with
  | falsum => simp
  | equal t₁ t₂ => simp [hatom]
  | rel R ts => simp [hatom]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp only [substBounds_all, onBoundedFormulaInf_all, ih, hlift]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

end LHom

end FirstOrder.Language
