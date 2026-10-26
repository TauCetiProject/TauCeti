/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.CodedConnectives

/-!
# Carrier transport for infinitary formulas

An infinitary formula branches over one fixed carrier. Along an index coding
`c : IndexCoding ι κ`, a formula at carrier `ι` is transported to carrier `κ` by replacing each
`ι`-indexed conjunction or disjunction with the corresponding coded connective at `κ`.

Transport is functorial: along the identity coding it is the identity, and along a composite
coding it is the composite of the transports, both syntactically. It preserves realization, and
it fixes the image of the finitary embedding. Along an equivalence of carriers it is a bijection of
syntax, `reindexEquiv`. Along `IndexCoding.ofEncodable`, it recodes a formula over an encodable
carrier into `L_{ω₁ω}`.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.reindex`: transport along an index coding.
* `FirstOrder.Language.BoundedFormulaInf.reindexEquiv`: transport along a carrier equivalence, as
  an equivalence of syntax.
* `FirstOrder.Language.BoundedFormulaInf.toOmega`: recoding a formula over an encodable carrier
  into `L_{ω₁ω}`.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.reindex_id` and
  `FirstOrder.Language.BoundedFormulaInf.reindex_trans`: functoriality.
* `FirstOrder.Language.BoundedFormulaInf.realize_reindex` and
  `FirstOrder.Language.BoundedFormulaInf.realize_toOmega`: transport preserves realization.
* `FirstOrder.Language.BoundedFormulaInf.reindex_toInf`: transport fixes finitary formulas.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, whose carrier transport is
  `Mathlib/ModelTheory/Infinitary/Reindex.lean` in `cameronfreer/mathlib4` at commit
  `346a4bd3f95e8591976c91259badc6d2c300f638`.
* Divergences from these sources: the coded connectives are in a separate module; the body of
  `reindex` is not exposed and is used through its constructor equations; the round trip along an
  equivalence is derived from `IndexCoding.ofEquiv_trans_ofEquiv_symm`.
-/

public section

universe u v u' uι uκ uμ w

namespace FirstOrder

namespace Language

open TauCeti

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {μ : Type uμ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- **Transport a formula along a coding of its carrier**: each `ι`-indexed conjunction or
disjunction becomes the corresponding coded connective at carrier `κ`. -/
def reindex (c : IndexCoding ι κ) : ∀ {n}, L.BoundedFormulaInf ι α n → L.BoundedFormulaInf κ α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel R ts => .rel R ts
  | _, .imp φ ψ => (reindex c φ).imp (reindex c ψ)
  | _, .all φ => (reindex c φ).all
  | _, .iSup φs => iSupAlong c fun i ↦ reindex c (φs i)
  | _, .iInf φs => iInfAlong c fun i ↦ reindex c (φs i)

section ReindexEqs

variable (c : IndexCoding ι κ)

/-- Transport fixes the false formula. -/
@[simp]
theorem reindex_falsum : reindex c (.falsum : L.BoundedFormulaInf ι α n) = .falsum :=
  (rfl)

/-- Transport fixes equations. -/
@[simp]
theorem reindex_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    reindex c (.equal t₁ t₂ : L.BoundedFormulaInf ι α n) = .equal t₁ t₂ :=
  (rfl)

/-- Transport fixes relational atoms. -/
@[simp]
theorem reindex_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    reindex c (.rel R ts : L.BoundedFormulaInf ι α n) = .rel R ts :=
  (rfl)

/-- Transport commutes with implication. -/
@[simp]
theorem reindex_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    reindex c (φ.imp ψ) = (reindex c φ).imp (reindex c ψ) :=
  (rfl)

/-- Transport commutes with universal quantification. -/
@[simp]
theorem reindex_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    reindex c φ.all = (reindex c φ).all :=
  (rfl)

/-- Transport turns a disjunction over the carrier into the coded disjunction. -/
@[simp]
theorem reindex_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    reindex c (.iSup φs) = iSupAlong c fun i ↦ reindex c (φs i) :=
  (rfl)

/-- Transport turns a conjunction over the carrier into the coded conjunction. -/
@[simp]
theorem reindex_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    reindex c (.iInf φs) = iInfAlong c fun i ↦ reindex c (φs i) :=
  (rfl)

/-- Transport commutes with negation. -/
@[simp]
theorem reindex_not (φ : L.BoundedFormulaInf ι α n) :
    reindex c φ.not = (reindex c φ).not :=
  (rfl)

/-- Transport commutes with existential quantification. -/
@[simp]
theorem reindex_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    reindex c φ.ex = (reindex c φ).ex :=
  (rfl)

/-- Transport fixes `⊤`. -/
@[simp]
theorem reindex_top : reindex c (⊤ : L.BoundedFormulaInf ι α n) = ⊤ := by
  rw [top_def, top_def]
  rfl

/-- Transport fixes `⊥`. -/
@[simp]
theorem reindex_bot : reindex c (⊥ : L.BoundedFormulaInf ι α n) = ⊥ := by
  rw [bot_def, bot_def]
  rfl

end ReindexEqs

/-- **Transport along the identity coding is the identity**, syntactically. -/
@[simp]
theorem reindex_id : ∀ {n} (φ : L.BoundedFormulaInf ι α n), reindex (.id ι) φ = φ := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => rw [reindex_imp, ihφ, ihψ]
  | all φ ih => rw [reindex_all, ih]
  | iSup φs ih =>
    rw [reindex_iSup, iSupAlong_def, IndexCoding.id_pad]
    exact congrArg BoundedFormulaInf.iSup (funext fun i ↦ ih i)
  | iInf φs ih =>
    rw [reindex_iInf, iInfAlong_def, IndexCoding.id_pad]
    exact congrArg BoundedFormulaInf.iInf (funext fun i ↦ ih i)

/-- Transport commutes with the universal closure of all bound-variable slots. -/
@[simp]
theorem reindex_alls (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n), reindex c φ.alls = (reindex c φ).alls
  | 0, φ => by rw [alls_zero, alls_zero]
  | _ + 1, φ => by rw [alls_succ, alls_succ, reindex_alls c φ.all, reindex_all]

/-- Transport commutes with the existential closure of all bound-variable slots. -/
@[simp]
theorem reindex_exs (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n), reindex c φ.exs = (reindex c φ).exs
  | 0, φ => by rw [exs_zero, exs_zero]
  | _ + 1, φ => by rw [exs_succ, exs_succ, reindex_exs c φ.ex, reindex_ex]

/-- **Transport along a composite coding is the composite of the transports**, syntactically. -/
theorem reindex_trans (c₁ : IndexCoding ι κ) (c₂ : IndexCoding κ μ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n),
      reindex (c₁.trans c₂) φ = reindex c₂ (reindex c₁ φ) := by
  -- The padding of the composite coding is iterated padding (`IndexCoding.pad_trans`), and
  -- transport commutes with padding because it fixes `⊤` and `⊥` (`IndexCoding.comp_pad`).
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => rw [reindex_imp, reindex_imp, reindex_imp, ihφ, ihψ]
  | all φ ih => rw [reindex_all, reindex_all, reindex_all, ih]
  | iSup φs ih =>
    simp only [reindex_iSup, iSupAlong_def]
    refine congrArg BoundedFormulaInf.iSup ?_
    calc (c₁.trans c₂).pad ⊥ (fun i ↦ reindex (c₁.trans c₂) (φs i))
        = c₂.pad ⊥ (c₁.pad ⊥ (reindex c₂ ∘ fun i ↦ reindex c₁ (φs i))) := by
          rw [IndexCoding.pad_trans]
          exact congrArg _ (congrArg _ (funext fun i ↦ ih i))
      _ = c₂.pad ⊥ (reindex c₂ ∘ c₁.pad ⊥ fun i ↦ reindex c₁ (φs i)) := by
          rw [IndexCoding.comp_pad, reindex_bot]
      _ = _ := rfl
  | iInf φs ih =>
    simp only [reindex_iInf, iInfAlong_def]
    refine congrArg BoundedFormulaInf.iInf ?_
    calc (c₁.trans c₂).pad ⊤ (fun i ↦ reindex (c₁.trans c₂) (φs i))
        = c₂.pad ⊤ (c₁.pad ⊤ (reindex c₂ ∘ fun i ↦ reindex c₁ (φs i))) := by
          rw [IndexCoding.pad_trans]
          exact congrArg _ (congrArg _ (funext fun i ↦ ih i))
      _ = c₂.pad ⊤ (reindex c₂ ∘ c₁.pad ⊤ fun i ↦ reindex c₁ (φs i)) := by
          rw [IndexCoding.comp_pad, reindex_top]
      _ = _ := rfl

/-- **Transport along an equivalence and back is the identity**, syntactically. -/
@[simp]
theorem reindex_ofEquiv_symm_reindex_ofEquiv (e : ι ≃ κ) (φ : L.BoundedFormulaInf ι α n) :
    reindex (.ofEquiv e.symm) (reindex (.ofEquiv e) φ) = φ := by
  rw [← reindex_trans, IndexCoding.ofEquiv_trans_ofEquiv_symm, reindex_id]

/-- **A carrier equivalence is an equivalence of syntax**: transport along it and along its
inverse are mutually inverse. -/
def reindexEquiv (e : ι ≃ κ) : L.BoundedFormulaInf ι α n ≃ L.BoundedFormulaInf κ α n where
  toFun := reindex (.ofEquiv e)
  invFun := reindex (.ofEquiv e.symm)
  left_inv φ := reindex_ofEquiv_symm_reindex_ofEquiv e φ
  right_inv φ := by simpa using reindex_ofEquiv_symm_reindex_ofEquiv e.symm φ

@[simp]
theorem reindexEquiv_apply (e : ι ≃ κ) (φ : L.BoundedFormulaInf ι α n) :
    reindexEquiv e φ = reindex (.ofEquiv e) φ := (rfl)

@[simp]
theorem reindexEquiv_symm_apply (e : ι ≃ κ) (φ : L.BoundedFormulaInf κ α n) :
    (reindexEquiv e).symm φ = reindex (.ofEquiv e.symm) φ := (rfl)

/-- **Recode a formula over an encodable carrier into `L_{ω₁ω}`**, by transport along the coding
`IndexCoding.ofEncodable`. -/
def toOmega [Encodable ι] (φ : L.BoundedFormulaInf ι α n) : L.BoundedFormulaω α n :=
  reindex (.ofEncodable ι) φ

/-- The recoding into `L_{ω₁ω}` is transport along `IndexCoding.ofEncodable`. -/
theorem toOmega_def [Encodable ι] (φ : L.BoundedFormulaInf ι α n) :
    toOmega φ = reindex (.ofEncodable ι) φ := (rfl)

section Realize

variable {M : Type w} [L.Structure M]

/-- **Transport preserves realization.** -/
@[simp]
theorem realize_reindex (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M),
      (reindex c φ).Realize v xs ↔ φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => intro v xs; simp only [reindex_falsum, realize_falsum]
  | equal t₁ t₂ => intro v xs; simp only [reindex_equal, realize_equal]
  | rel R ts => intro v xs; simp only [reindex_rel, realize_rel]
  | imp φ ψ ihφ ihψ =>
    intro v xs
    simp only [reindex_imp, realize_imp]
    exact imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    simp only [reindex_all, realize_all]
    exact forall_congr' fun y ↦ ih v (Fin.snoc xs y)
  | iSup φs ih =>
    intro v xs
    simp only [reindex_iSup, realize_iSupAlong, realize_iSup]
    exact exists_congr fun i ↦ ih i v xs
  | iInf φs ih =>
    intro v xs
    simp only [reindex_iInf, realize_iInfAlong, realize_iInf]
    exact forall_congr' fun i ↦ ih i v xs

/-- **Recoding into `L_{ω₁ω}` preserves realization.** -/
@[simp]
theorem realize_toOmega [Encodable ι] (φ : L.BoundedFormulaInf ι α n) (v : α → M)
    (xs : Fin n → M) : (toOmega φ).Realize v xs ↔ φ.Realize v xs := by
  rw [toOmega_def, realize_reindex]

end Realize

/-- **Transport fixes finitary formulas**: the finitary embedding at carrier `κ` factors through
every coding into `κ`. -/
@[simp]
theorem reindex_toInf (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormula α n), reindex c (BoundedFormula.toInf φ) = BoundedFormula.toInf φ
  := by
  intro n φ
  induction φ with
  | falsum => rw [BoundedFormula.toInf_falsum, BoundedFormula.toInf_falsum, reindex_falsum]
  | equal t₁ t₂ => rw [BoundedFormula.toInf_equal, BoundedFormula.toInf_equal, reindex_equal]
  | rel R ts => rw [BoundedFormula.toInf_rel, BoundedFormula.toInf_rel, reindex_rel]
  | imp φ ψ ihφ ihψ =>
    rw [BoundedFormula.toInf_imp, BoundedFormula.toInf_imp, reindex_imp, ihφ, ihψ]
  | all φ ih => rw [BoundedFormula.toInf_all, BoundedFormula.toInf_all, reindex_all, ih]

end BoundedFormulaInf

end Language

end FirstOrder
