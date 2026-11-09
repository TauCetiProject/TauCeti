/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FormationClosed
import Mathlib.ModelTheory.Encoding

/-!
# The first-order image fragment

The finitary formulas of a language `L`, embedded into `L_{ω₁ω}` by `BoundedFormula.toOmega`,
form a fragment: a component of the image of a finitary formula is the image of a finitary
formula, and the image contains no infinitary conjunction or disjunction. This fragment is
formation-closed, since it contains every atomic formula and `⊥` and is closed under implication,
universal quantification and relabelling of bound positions. It is the least formation-closed
fragment, since every formation-closed fragment contains the image of every finitary formula.
Over a language with countably many function and relation symbols it is countable, because there
are countably many finitary formulas.

The first-order image is how results about countable formation-closed fragments, such as the
omitting types theorem, specialize to first-order logic.

## Main definitions

* `FirstOrder.Language.Fragment.firstOrder`: the fragment of images of finitary formulas.

## Main results

* `FirstOrder.Language.Fragment.mem_firstOrder_iff`: the members of the first-order image are
  exactly the images of finitary formulas.
* `FirstOrder.Language.Fragment.formationClosed_firstOrder`: the first-order image is
  formation-closed.
* `FirstOrder.Language.Fragment.FormationClosed.firstOrder_le` and
  `FirstOrder.Language.Fragment.formationClosure_empty`: the first-order image lies below every
  formation-closed fragment, so it is the least one, the formation closure of the empty set.
* `FirstOrder.Language.Fragment.firstOrder_countable`: over a language with countably many
  function and relation symbols, the first-order image is countable.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1.
* The first-order image fragment also appears in `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Lomega1omega/FirstOrderImage.lean`.
-/

public section

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

namespace BoundedFormula

open BoundedFormulaInf

variable {ι : Type*} {α : Type u'} {n : ℕ}

/-- A finitary formula whose image is an implication is an implication. -/
private theorem exists_of_toInf_eq_imp {χ : L.BoundedFormula α n}
    {φ ψ : L.BoundedFormulaInf ι α n} (h : χ.toInf = φ.imp ψ) :
    ∃ χ₁ χ₂ : L.BoundedFormula α n, χ₁.toInf = φ ∧ χ₂.toInf = ψ := by
  cases χ <;> simp only [toInf_falsum, toInf_equal, toInf_rel, toInf_imp, toInf_all,
    reduceCtorEq, BoundedFormulaInf.imp.injEq] at h
  exact ⟨_, _, h⟩

/-- A finitary formula whose image is a universal quantification is one. -/
private theorem exists_of_toInf_eq_all {χ : L.BoundedFormula α n}
    {φ : L.BoundedFormulaInf ι α (n + 1)} (h : χ.toInf = φ.all) :
    ∃ χ₁ : L.BoundedFormula α (n + 1), χ₁.toInf = φ := by
  cases χ <;> simp only [toInf_falsum, toInf_equal, toInf_rel, toInf_imp, toInf_all,
    reduceCtorEq, BoundedFormulaInf.all.injEq] at h
  exact ⟨_, h⟩

/-- The image of a finitary formula is not a countable conjunction. -/
private theorem toInf_ne_iInf (χ : L.BoundedFormula α n) (φs : ι → L.BoundedFormulaInf ι α n) :
    χ.toInf ≠ .iInf φs := by
  cases χ <;> simp only [toInf_falsum, toInf_equal, toInf_rel, toInf_imp, toInf_all, ne_eq,
    reduceCtorEq, not_false_eq_true]

/-- The image of a finitary formula is not a countable disjunction. -/
private theorem toInf_ne_iSup (χ : L.BoundedFormula α n) (φs : ι → L.BoundedFormulaInf ι α n) :
    χ.toInf ≠ .iSup φs := by
  cases χ <;> simp only [toInf_falsum, toInf_equal, toInf_rel, toInf_imp, toInf_all, ne_eq,
    reduceCtorEq, not_false_eq_true]

/-- Relabelling the bound positions of the image of a finitary formula gives the image of a
finitary formula. -/
private theorem exists_toInf_eq_mapBound :
    ∀ {m : ℕ} (φ : L.BoundedFormula α m) {k : ℕ} (f : Fin m → Fin k),
      ∃ ψ : L.BoundedFormula α k, (ψ.toInf : L.BoundedFormulaInf ι α k) = mapBound f φ.toInf
  | _, falsum, _, f => ⟨falsum, by rw [toInf_falsum, toInf_falsum, mapBound_falsum]⟩
  | _, equal t₁ t₂, _, f =>
    ⟨equal (t₁.relabel (Sum.map id f)) (t₂.relabel (Sum.map id f)), by
      rw [toInf_equal, toInf_equal, mapBound_equal]⟩
  | _, rel R ts, _, f => ⟨rel R fun i => (ts i).relabel (Sum.map id f), by
      rw [toInf_rel, toInf_rel, mapBound_rel]⟩
  | _, imp φ₁ φ₂, _, f => by
    obtain ⟨ψ₁, h₁⟩ := exists_toInf_eq_mapBound φ₁ f
    obtain ⟨ψ₂, h₂⟩ := exists_toInf_eq_mapBound φ₂ f
    exact ⟨ψ₁.imp ψ₂, by rw [toInf_imp, toInf_imp, mapBound_imp, h₁, h₂]⟩
  | _, all φ, k, f => by
    obtain ⟨ψ, h⟩ := exists_toInf_eq_mapBound φ
      (Fin.snoc (fun i => (f i).castSucc) (Fin.last k))
    exact ⟨ψ.all, by rw [toInf_all, toInf_all, mapBound_all, h]⟩

end BoundedFormula

namespace Fragment

open BoundedFormula BoundedFormulaInf

variable (L) in
/-- The **first-order image**: the fragment of `L_{ω₁ω}` formulas that are images of finitary
formulas under `BoundedFormula.toOmega`. -/
def firstOrder : Fragment L where
  toSet := {p | ∃ φ : L.BoundedFormula Empty p.1, φ.toOmega = p.2}
  imp_left_mem' := fun ⟨_, h⟩ => by
    obtain ⟨χ, -, h, -⟩ := exists_of_toInf_eq_imp h
    exact ⟨χ, h⟩
  imp_right_mem' := fun ⟨_, h⟩ => by
    obtain ⟨-, χ, -, h⟩ := exists_of_toInf_eq_imp h
    exact ⟨χ, h⟩
  all_mem' := fun ⟨_, h⟩ => exists_of_toInf_eq_all h
  iInf_mem' := fun ⟨χ, h⟩ => (toInf_ne_iInf χ _ h).elim
  iSup_mem' := fun ⟨χ, h⟩ => (toInf_ne_iSup χ _ h).elim

/-- A formula belongs to the first-order image exactly when it is the image of a finitary
formula. -/
theorem mem_firstOrder_iff {n : ℕ} {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ firstOrder L ↔
      ∃ ψ : L.BoundedFormula Empty n, ψ.toOmega = φ :=
  Iff.rfl

/-- The image of a finitary formula belongs to the first-order image. -/
@[simp]
theorem toOmega_mem_firstOrder {n : ℕ} (φ : L.BoundedFormula Empty n) :
    (⟨n, φ.toOmega⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ firstOrder L :=
  ⟨φ, rfl⟩

/-- The first-order image is formation-closed. -/
theorem formationClosed_firstOrder : (firstOrder L).FormationClosed where
  bot_mem n := mem_firstOrder_iff.2 ⟨falsum, toInf_falsum⟩
  atomic_mem h := by
    cases h with
    | equal t₁ t₂ => exact mem_firstOrder_iff.2 ⟨equal t₁ t₂, toInf_equal t₁ t₂⟩
    | rel R ts => exact mem_firstOrder_iff.2 ⟨rel R ts, toInf_rel R ts⟩
  imp_mem hφ hψ := by
    obtain ⟨φ, rfl⟩ := mem_firstOrder_iff.1 hφ
    obtain ⟨ψ, rfl⟩ := mem_firstOrder_iff.1 hψ
    exact mem_firstOrder_iff.2 ⟨φ.imp ψ, toInf_imp φ ψ⟩
  all_mem hφ := by
    obtain ⟨φ, rfl⟩ := mem_firstOrder_iff.1 hφ
    exact mem_firstOrder_iff.2 ⟨φ.all, toInf_all φ⟩
  mapBound_mem f hφ := by
    obtain ⟨φ, rfl⟩ := mem_firstOrder_iff.1 hφ
    exact mem_firstOrder_iff.2 (BoundedFormula.exists_toInf_eq_mapBound φ f)

/-- Every formation-closed fragment contains the image of every finitary formula. -/
theorem FormationClosed.toOmega_mem {A : Fragment L} (hA : A.FormationClosed) :
    ∀ {n : ℕ} (φ : L.BoundedFormula Empty n),
      (⟨n, φ.toOmega⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A
  | n, .falsum => by simpa only [toInf_falsum, bot_def] using hA.bot_mem n
  | _, .equal t₁ t₂ => by simpa only [toInf_equal] using hA.atomic_mem (.equal t₁ t₂)
  | _, .rel R ts => by simpa only [toInf_rel] using hA.atomic_mem (.rel R ts)
  | _, .imp φ ψ => by
    simpa only [toInf_imp] using hA.imp_mem (hA.toOmega_mem φ) (hA.toOmega_mem ψ)
  | _, .all φ => by simpa only [toInf_all] using hA.all_mem (hA.toOmega_mem φ)

/-- The first-order image lies below every formation-closed fragment. -/
theorem FormationClosed.firstOrder_le {A : Fragment L} (hA : A.FormationClosed) :
    firstOrder L ≤ A := by
  rintro ⟨n, _⟩ hφ
  obtain ⟨φ, rfl⟩ := mem_firstOrder_iff.1 hφ
  exact hA.toOmega_mem φ

/-- **The first-order image is the least formation-closed fragment**: it is the formation closure
of the empty set. -/
theorem formationClosure_empty : formationClosure (∅ : Set (Σ n, L.BoundedFormulaω Empty n)) =
    firstOrder L :=
  le_antisymm ((formationClosure_le_iff formationClosed_firstOrder).2 (Set.empty_subset _))
    (formationClosed_formationClosure ∅).firstOrder_le

/-- Over a language with countably many function and relation symbols, the first-order image is
countable. -/
theorem firstOrder_countable [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)] :
    (firstOrder L : Set (Σ n, L.BoundedFormulaω Empty n)).Countable := by
  refine (Set.countable_range fun p : Σ n, L.BoundedFormula Empty n => (⟨p.1, p.2.toOmega⟩ :
    Σ n, L.BoundedFormulaω Empty n)).mono ?_
  rintro ⟨n, φ⟩ hφ
  obtain ⟨ψ, rfl⟩ := mem_firstOrder_iff.1 hφ
  exact ⟨⟨n, ψ⟩, rfl⟩

end Fragment

end Language

end FirstOrder
