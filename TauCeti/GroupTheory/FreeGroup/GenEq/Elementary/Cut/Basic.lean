/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import TauCeti.GroupTheory.FreeGroup.GenEq.Parametric
public import TauCeti.GroupTheory.FreeGroup.GenEq.Surgery
public import TauCeti.GroupTheory.FreeGroup.GenEq.Tied
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Cutting a base at a boundary connection: combinatorics and formal consistency

Given a boundary connection `(p, μ, q)` of a generalised equation `Ω` on a variable base
`μ ≠ Δ(μ)`, the elementary transformation ET1 of Makanin's process (Kharlampovich–Myasnikov, §5.1)
cuts `μ` at `p` into two variable bases `μ₁ = [α(μ), p]` and `μ₂ = [p, β(μ)]` with the sign of `μ`,
cuts the dual base `Δ(μ)` at `q` into `[α(Δμ), q]` and `[q, β(Δμ)]` with the sign of `Δ(μ)`, pairs
`μ₁, μ₂` with those two pieces in the same order when `ε(μ) = ε(Δμ)` and in opposite order when
`ε(μ) ≠ ε(Δμ)`, and retains each boundary connection whose boundaries lie strictly inside a dual
pair of pieces (`TauCeti.GenEq.cutBase`). Since `TauCeti.GenEq` only requires `dual` to be an
involution without ruling out fixed points, `cutBase` takes `hμ : μ ≠ Ω.dual μ` so that
`{μ, Δ(μ)}` is a genuine pair of distinct dual bases replaced by four pieces.

Writing `Ω′ = Ω.cutBase p μ q hc hμ`:

* `Ω′` has the same items and constant bases as `Ω`, two more variable bases
  (`TauCeti.GenEq.numBases_cutBase`), the same item degrees (`TauCeti.GenEq.degree_cutBase`), fewer
  bases crossing `p` (`TauCeti.GenEq.card_crosses_cutBase_lt`), and—when `Ω` is formally
  consistent—two fewer boundary connections (`TauCeti.GenEq.card_connections_cutBase`, deleting
  `(p, μ, q)` and `(q, Δ(μ), p)` and restricting every other connection to a unique piece).
* Every closed boundary of `Ω` remains closed (`TauCeti.GenEq.IsClosedBoundary.cutBase`), so
  parametric section partitions and standard form carry over unchanged
  (`TauCeti.GenEq.SectionPartition.cutBase`,
  `TauCeti.GenEq.SectionPartition.isStandardForm_cutBase_iff`).
* Given that `Ω` is formally consistent, `Ω′` is formally consistent if and only if, whenever
  `p = q` and `ε(μ) = ε(Δμ)`, every connection `(p′, μ, q′)` strictly to the right of `p` satisfies
  `p′ = q′` (`TauCeti.GenEq.isFormallyConsistent_cutBase_iff`). In particular, `Ω′` is formally
  consistent whenever `p ≠ q` or `ε(μ) ≠ ε(Δμ)`; a five-item unsolvable example at the end of the
  file shows how formal consistency can fail when `p = q`.

Group solutions, coordinate-group isomorphisms, graphical solutions, and the `Transformation`
packaging of ET1 are developed in `TauCeti.GroupTheory.FreeGroup.GenEq.Elementary.Cut.Solution`.

## Main definitions

* `TauCeti.GenEq.cutSurv`, `TauCeti.GenEq.cutPiece`: indices in `Ω′` of surviving bases outside
  `{μ, Δ(μ)}` and of the four split pieces replacing `μ` and `Δ(μ)`.
* `TauCeti.GenEq.cutBase`: cut a dual pair `μ, Δ(μ)` (`μ ≠ Δ(μ)`) at `(p, μ, q)`.
* `TauCeti.GenEq.SectionPartition.cutBase`: transport of a parametric section partition to `Ω′`.

## Main results

* `TauCeti.GenEq.numBases_cutBase`, `TauCeti.GenEq.card_connections_cutBase`,
  `TauCeti.GenEq.card_crosses_cutBase_lt`, `TauCeti.GenEq.degree_cutBase`: combinatorial invariants
  of `cutBase`.
* `TauCeti.GenEq.isFormallyConsistent_cutBase_iff`: characterisation of formal consistency of `Ω′`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1, ET1.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005), §5.1,
  ET1.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §11.3, ET1.
-/

public section

namespace TauCeti

namespace GenEq

open Finset

section CutData

variable {A : Type*} (Ω : GenEq A)

/-- The number of variable bases of `Ω` outside `{μ, Δ(μ)}` (definitionally
`(Ω.removePair μ).numBases`, exposed as an `abbrev` so `simp` matches `Ω.dualCompl` at reducible
transparency). -/
abbrev cutSurvCard (μ : Fin Ω.numBases) : ℕ :=
  ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))ᶜ.card

variable {Ω} in
/-- Removing a pair of distinct dual bases `{μ, Δ(μ)}` and adding four split pieces increases
`numBases` by `2`. -/
theorem cutSurvCard_add_four {μ : Fin Ω.numBases} (hμ : μ ≠ Ω.dual μ) :
    Ω.cutSurvCard μ + 4 = Ω.numBases + 2 := by
  have hle : 2 ≤ Ω.numBases := by
    rw [← Fintype.card_fin Ω.numBases, ← Finset.card_pair hμ]
    exact Finset.card_le_univ _
  simp only [cutSurvCard, Finset.card_compl, Finset.card_pair hμ, Fintype.card_fin]
  omega

/-- The variable base of `Ω` corresponding to the `ν`-th surviving base outside `{μ, Δ(μ)}`. -/
def cutSurvEmb (μ : Fin Ω.numBases) (ν : Fin (Ω.cutSurvCard μ)) : Fin Ω.numBases :=
  ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))ᶜ.orderEmbOfFin rfl ν

/-- The index in `Ω.cutBase p μ q hc hμ` of a surviving variable base `ν` of `Ω.removePair μ`. -/
def cutSurv (μ : Fin Ω.numBases) (hμ : μ ≠ Ω.dual μ) (ν : Fin (Ω.cutSurvCard μ)) :
    Fin (Ω.numBases + 2) :=
  (Fin.castAdd 4 ν).cast (Ω.cutSurvCard_add_four hμ)

/-- The index in `Ω.cutBase p μ q hc hμ` of one of the four new variable bases replacing `μ` and
`Δ(μ)`: `0` and `1` are the left and right pieces `[α(μ), p]` and `[p, β(μ)]` of `μ`, and `2` and
`3` are their respective duals in `Δ(μ)`. -/
def cutPiece (μ : Fin Ω.numBases) (hμ : μ ≠ Ω.dual μ) (i : Fin 4) : Fin (Ω.numBases + 2) :=
  (Fin.natAdd (Ω.cutSurvCard μ) i).cast (Ω.cutSurvCard_add_four hμ)

/-- For each variable base of `Ω.cutBase p μ q hc hμ`, the variable base of `Ω` from which it
arises: a surviving base outside `{μ, Δ(μ)}` maps to itself, the pieces `0` and `1` map to `μ`, and
their duals `2` and `3` map to `Δ(μ)`. -/
def cutOrigBase (μ : Fin Ω.numBases) (hμ : μ ≠ Ω.dual μ) (β : Fin (Ω.numBases + 2)) :
    Fin Ω.numBases :=
  Fin.append (Ω.cutSurvEmb μ) ![μ, μ, Ω.dual μ, Ω.dual μ]
    (β.cast (Ω.cutSurvCard_add_four hμ).symm)

/-- The initial boundaries of the variable bases after cutting `μ` at `(p, μ, q)`. -/
def cutLeft (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) (q : Fin (Ω.numItems + 1))
    (hμ : μ ≠ Ω.dual μ) (β : Fin (Ω.numBases + 2)) : Fin (Ω.numItems + 1) :=
  Fin.append (fun ν => Ω.left (Ω.cutSurvEmb μ ν))
    ![Ω.left μ, p,
      if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.left (Ω.dual μ) else q,
      if Ω.sign μ = Ω.sign (Ω.dual μ) then q else Ω.left (Ω.dual μ)]
    (β.cast (Ω.cutSurvCard_add_four hμ).symm)

/-- The terminal boundaries of the variable bases after cutting `μ` at `(p, μ, q)`. -/
def cutRight (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) (q : Fin (Ω.numItems + 1))
    (hμ : μ ≠ Ω.dual μ) (β : Fin (Ω.numBases + 2)) : Fin (Ω.numItems + 1) :=
  Fin.append (fun ν => Ω.right (Ω.cutSurvEmb μ ν))
    ![p, Ω.right μ,
      if Ω.sign μ = Ω.sign (Ω.dual μ) then q else Ω.right (Ω.dual μ),
      if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.right (Ω.dual μ) else q]
    (β.cast (Ω.cutSurvCard_add_four hμ).symm)

/-- The duality involution on the variable bases after cutting `μ`: surviving bases keep their
duals in `Ω.removePair μ`, while the four new pieces are paired as `0 ↔ 2` and `1 ↔ 3`. -/
def cutDual (μ : Fin Ω.numBases) (hμ : μ ≠ Ω.dual μ) (β : Fin (Ω.numBases + 2)) :
    Fin (Ω.numBases + 2) :=
  Fin.append (fun ν => Ω.cutSurv μ hμ ((Ω.removePair μ).dual ν))
    (fun i => Ω.cutPiece μ hμ (![2, 3, 0, 1] i))
    (β.cast (Ω.cutSurvCard_add_four hμ).symm)

variable {Ω} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} {q : Fin (Ω.numItems + 1)}

@[simp]
theorem cutSurvEmb_inj {ν₁ ν₂ : Fin (Ω.cutSurvCard μ)} :
    Ω.cutSurvEmb μ ν₁ = Ω.cutSurvEmb μ ν₂ ↔ ν₁ = ν₂ :=
  EmbeddingLike.apply_eq_iff_eq _

@[simp]
theorem cutSurv_inj (hμ : μ ≠ Ω.dual μ) {ν₁ ν₂ : Fin (Ω.cutSurvCard μ)} :
    Ω.cutSurv μ hμ ν₁ = Ω.cutSurv μ hμ ν₂ ↔ ν₁ = ν₂ := by
  simp [cutSurv]

@[simp]
theorem cutPiece_inj (hμ : μ ≠ Ω.dual μ) {i₁ i₂ : Fin 4} :
    Ω.cutPiece μ hμ i₁ = Ω.cutPiece μ hμ i₂ ↔ i₁ = i₂ := by
  simp [cutPiece]

@[simp]
theorem cutSurv_ne_cutPiece (hμ : μ ≠ Ω.dual μ) (ν : Fin (Ω.cutSurvCard μ)) (i : Fin 4) :
    Ω.cutSurv μ hμ ν ≠ Ω.cutPiece μ hμ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cutSurv, cutPiece, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

@[simp]
theorem cutPiece_ne_cutSurv (hμ : μ ≠ Ω.dual μ) (i : Fin 4) (ν : Fin (Ω.cutSurvCard μ)) :
    Ω.cutPiece μ hμ i ≠ Ω.cutSurv μ hμ ν :=
  (cutSurv_ne_cutPiece hμ ν i).symm

/-- Case split on a variable base of `Ω.cutBase`: it is either a surviving base `cutSurv μ hμ ν` or
one of the four new pieces `cutPiece μ hμ i`. -/
@[elab_as_elim]
theorem cutBase_cases (hμ : μ ≠ Ω.dual μ) {P : Fin (Ω.numBases + 2) → Prop}
    (surv : ∀ ν, P (Ω.cutSurv μ hμ ν)) (piece : ∀ i, P (Ω.cutPiece μ hμ i))
    (β : Fin (Ω.numBases + 2)) : P β := by
  have hβ : (β.cast (Ω.cutSurvCard_add_four hμ).symm).cast (Ω.cutSurvCard_add_four hμ) = β := by
    simp
  rw [← hβ]
  obtain ⟨ν | i, h⟩ := finSumFinEquiv.surjective (β.cast (Ω.cutSurvCard_add_four hμ).symm)
  · rw [← h]; exact surv ν
  · rw [← h]; exact piece i

theorem forall_cutBase (hμ : μ ≠ Ω.dual μ) {P : Fin (Ω.numBases + 2) → Prop} :
    (∀ β, P β) ↔ (∀ ν, P (Ω.cutSurv μ hμ ν)) ∧ ∀ i, P (Ω.cutPiece μ hμ i) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨h₁, h₂⟩ => cutBase_cases hμ h₁ h₂⟩

theorem exists_cutBase (hμ : μ ≠ Ω.dual μ) {P : Fin (Ω.numBases + 2) → Prop} :
    (∃ β, P β) ↔ (∃ ν, P (Ω.cutSurv μ hμ ν)) ∨ ∃ i, P (Ω.cutPiece μ hμ i) :=
  ⟨fun ⟨β, hβ⟩ => cutBase_cases hμ (fun _ h => Or.inl ⟨_, h⟩) (fun _ h => Or.inr ⟨_, h⟩) β hβ,
    fun h => h.elim (fun ⟨_, hν⟩ => ⟨_, hν⟩) (fun ⟨_, hi⟩ => ⟨_, hi⟩)⟩

/-- Case split on an index `i : Fin 4` of one of the four split pieces. -/
@[elab_as_elim]
theorem cutPiece_cases {P : Fin 4 → Prop} (h₀ : P 0) (h₁ : P 1) (h₂ : P 2) (h₃ : P 3)
    (i : Fin 4) : P i := by
  fin_cases i <;> assumption

private theorem exists_fin_four {P : Fin 4 → Prop} :
    (∃ i, P i) ↔ (P 0 ∨ P 1) ∨ (P 2 ∨ P 3) :=
  ⟨fun ⟨i, h⟩ => cutPiece_cases (fun h => Or.inl (Or.inl h)) (fun h => Or.inl (Or.inr h))
      (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)) i h,
    by rintro ((h | h) | (h | h)) <;> exact ⟨_, h⟩⟩

@[simp]
theorem cutSurvEmb_dualCompl
    (h : ∀ x ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases)), Ω.dual x ∈ {μ, Ω.dual μ})
    (ν : Fin (Ω.cutSurvCard μ)) :
    Ω.cutSurvEmb μ (Ω.dualCompl {μ, Ω.dual μ} h ν) = Ω.dual (Ω.cutSurvEmb μ ν) :=
  orderEmbOfFin_dualCompl h ν

theorem cutSurvEmb_dual (ν : Fin (Ω.cutSurvCard μ)) :
    Ω.cutSurvEmb μ ((Ω.removePair μ).dual ν) = Ω.dual (Ω.cutSurvEmb μ ν) :=
  cutSurvEmb_dualCompl (Ω.dual_mem_pair μ) ν

theorem cutSurvEmb_notMem (ν : Fin (Ω.cutSurvCard μ)) :
    Ω.cutSurvEmb μ ν ∉ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases)) :=
  Finset.mem_compl.1 (Finset.orderEmbOfFin_mem ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))ᶜ rfl ν)

@[simp]
theorem cutSurvEmb_ne_self (ν : Fin (Ω.cutSurvCard μ)) : Ω.cutSurvEmb μ ν ≠ μ :=
  fun h => cutSurvEmb_notMem ν (by simp [h])

@[simp]
theorem cutSurvEmb_ne_dual (ν : Fin (Ω.cutSurvCard μ)) : Ω.cutSurvEmb μ ν ≠ Ω.dual μ :=
  fun h => cutSurvEmb_notMem ν (by simp [h])

theorem exists_cutSurvEmb_eq {ν : Fin Ω.numBases}
    (hmem : ν ∉ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) :
    ∃ ν₀, Ω.cutSurvEmb μ ν₀ = ν := by
  have hmem' : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))ᶜ := Finset.mem_compl.2 hmem
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin _ rfl, Set.mem_range] at hmem'
  simpa only [cutSurvEmb] using hmem'

section Pieces

variable (hμ : μ ≠ Ω.dual μ)

@[simp] theorem cutOrigBase_cutSurv (ν : Fin (Ω.cutSurvCard μ)) :
    Ω.cutOrigBase μ hμ (Ω.cutSurv μ hμ ν) = Ω.cutSurvEmb μ ν := by simp [cutOrigBase, cutSurv]
@[simp] theorem cutOrigBase_cutPiece_zero : Ω.cutOrigBase μ hμ (Ω.cutPiece μ hμ 0) = μ := by
  simp [cutOrigBase, cutPiece]
@[simp] theorem cutOrigBase_cutPiece_one : Ω.cutOrigBase μ hμ (Ω.cutPiece μ hμ 1) = μ := by
  simp [cutOrigBase, cutPiece]
@[simp] theorem cutOrigBase_cutPiece_two : Ω.cutOrigBase μ hμ (Ω.cutPiece μ hμ 2) = Ω.dual μ := by
  simp [cutOrigBase, cutPiece]
@[simp] theorem cutOrigBase_cutPiece_three :
    Ω.cutOrigBase μ hμ (Ω.cutPiece μ hμ 3) = Ω.dual μ := by simp [cutOrigBase, cutPiece]

@[simp] theorem cutLeft_cutSurv (ν : Fin (Ω.cutSurvCard μ)) :
    Ω.cutLeft p μ q hμ (Ω.cutSurv μ hμ ν) = Ω.left (Ω.cutSurvEmb μ ν) := by simp [cutLeft, cutSurv]
@[simp] theorem cutLeft_cutPiece_zero : Ω.cutLeft p μ q hμ (Ω.cutPiece μ hμ 0) = Ω.left μ := by
  simp [cutLeft, cutPiece]
@[simp] theorem cutLeft_cutPiece_one : Ω.cutLeft p μ q hμ (Ω.cutPiece μ hμ 1) = p := by
  simp [cutLeft, cutPiece]
@[simp] theorem cutLeft_cutPiece_two :
    Ω.cutLeft p μ q hμ (Ω.cutPiece μ hμ 2) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.left (Ω.dual μ) else q := by simp [cutLeft, cutPiece]
@[simp] theorem cutLeft_cutPiece_three :
    Ω.cutLeft p μ q hμ (Ω.cutPiece μ hμ 3) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then q else Ω.left (Ω.dual μ) := by simp [cutLeft, cutPiece]

@[simp] theorem cutRight_cutSurv (ν : Fin (Ω.cutSurvCard μ)) :
    Ω.cutRight p μ q hμ (Ω.cutSurv μ hμ ν) = Ω.right (Ω.cutSurvEmb μ ν) := by
  simp [cutRight, cutSurv]
@[simp] theorem cutRight_cutPiece_zero : Ω.cutRight p μ q hμ (Ω.cutPiece μ hμ 0) = p := by
  simp [cutRight, cutPiece]
@[simp] theorem cutRight_cutPiece_one : Ω.cutRight p μ q hμ (Ω.cutPiece μ hμ 1) = Ω.right μ := by
  simp [cutRight, cutPiece]
@[simp] theorem cutRight_cutPiece_two :
    Ω.cutRight p μ q hμ (Ω.cutPiece μ hμ 2) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then q else Ω.right (Ω.dual μ) := by
  simp [cutRight, cutPiece]
@[simp] theorem cutRight_cutPiece_three :
    Ω.cutRight p μ q hμ (Ω.cutPiece μ hμ 3) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.right (Ω.dual μ) else q := by
  simp [cutRight, cutPiece]

@[simp] theorem cutDual_cutSurv (ν : Fin (Ω.cutSurvCard μ)) :
    Ω.cutDual μ hμ (Ω.cutSurv μ hμ ν) = Ω.cutSurv μ hμ ((Ω.removePair μ).dual ν) := by
  simp [cutDual, cutSurv]
@[simp] theorem cutDual_cutPiece_zero :
    Ω.cutDual μ hμ (Ω.cutPiece μ hμ 0) = Ω.cutPiece μ hμ 2 := by simp [cutDual, cutPiece]
@[simp] theorem cutDual_cutPiece_one :
    Ω.cutDual μ hμ (Ω.cutPiece μ hμ 1) = Ω.cutPiece μ hμ 3 := by simp [cutDual, cutPiece]
@[simp] theorem cutDual_cutPiece_two :
    Ω.cutDual μ hμ (Ω.cutPiece μ hμ 2) = Ω.cutPiece μ hμ 0 := by simp [cutDual, cutPiece]
@[simp] theorem cutDual_cutPiece_three :
    Ω.cutDual μ hμ (Ω.cutPiece μ hμ 3) = Ω.cutPiece μ hμ 1 := by simp [cutDual, cutPiece]

/-- Duality after cutting a base is an involution. -/
theorem cutDual_involutive : Function.Involutive (Ω.cutDual μ hμ) :=
  cutBase_cases hμ (fun ν => by simp [dualCompl_involutive (Ω.dual_mem_pair μ) ν])
    (cutPiece_cases (by simp) (by simp) (by simp) (by simp))

/-- Passing to the dual base in `Ω.cutBase` corresponds to passing to the dual base in `Ω`. -/
@[simp]
theorem cutOrigBase_cutDual (β : Fin (Ω.numBases + 2)) :
    Ω.cutOrigBase μ hμ (Ω.cutDual μ hμ β) = Ω.dual (Ω.cutOrigBase μ hμ β) :=
  cutBase_cases hμ (fun ν => by simp)
    (cutPiece_cases (by simp) (by simp) (by simp [Ω.dual_involutive μ])
      (by simp [Ω.dual_involutive μ])) β

/-- Distinct bases of `Ω.cutBase` mapping to the same base of `Ω` span disjoint intervals: if their
intervals overlap, the two bases coincide. -/
theorem eq_of_cutOrigBase_eq {β₁ β₂ : Fin (Ω.numBases + 2)}
    (horig : Ω.cutOrigBase μ hμ β₁ = Ω.cutOrigBase μ hμ β₂)
    (h₁₂ : Ω.cutLeft p μ q hμ β₁ < Ω.cutRight p μ q hμ β₂)
    (h₂₁ : Ω.cutLeft p μ q hμ β₂ < Ω.cutRight p μ q hμ β₁) :
    β₁ = β₂ := by
  revert horig h₁₂ h₂₁
  refine cutBase_cases hμ (fun ν₁ => ?_) (fun i₁ => ?_) β₁
  · refine cutBase_cases hμ (fun ν₂ horig _ _ => ?_) (fun i₂ horig _ _ => ?_) β₂
    · simp only [cutOrigBase_cutSurv, cutSurvEmb_inj, cutSurv_inj] at horig ⊢
      exact horig
    · exact absurd horig (cutPiece_cases (by simp) (by simp) (by simp) (by simp) i₂)
  · refine cutBase_cases hμ (fun ν₂ horig _ _ => ?_) (fun i₂ horig h₁₂ h₂₁ => ?_) β₂
    · exact absurd horig.symm (cutPiece_cases (by simp) (by simp) (by simp) (by simp) i₁)
    · revert horig h₁₂ h₂₁
      refine cutPiece_cases ?_ ?_ ?_ ?_ i₁ <;>
        refine cutPiece_cases ?_ ?_ ?_ ?_ i₂ <;> intro horig h₁₂ h₂₁
      all_goals try rfl
      all_goals try exact absurd (by simpa using horig) hμ
      all_goals try exact absurd (by simpa using horig.symm) hμ
      · simp at h₂₁
      · simp at h₁₂
      · by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
        · simp [hs] at h₂₁
        · simp [hs] at h₁₂
      · by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
        · simp [hs] at h₁₂
        · simp [hs] at h₂₁

end Pieces

/-- Every base of `Ω.cutBase` spans a nonempty interval of boundaries. -/
theorem cutLeft_lt_cutRight (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ)
    (β : Fin (Ω.numBases + 2)) : Ω.cutLeft p μ q hμ β < Ω.cutRight p μ q hμ β := by
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  exact cutBase_cases hμ (fun _ => by simp [Ω.left_lt_right])
    (cutPiece_cases (by simp [hp₁]) (by simp [hp₂])
      (by by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs, hq₁, hq₂])
      (by by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs, hq₁, hq₂])) β

/-- Every base of `Ω.cutBase` starts at or after the start of the base of `Ω` from which it
arises. -/
theorem left_cutOrigBase_le (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ)
    (β : Fin (Ω.numBases + 2)) : Ω.left (Ω.cutOrigBase μ hμ β) ≤ Ω.cutLeft p μ q hμ β := by
  obtain ⟨hp₁, -, hq₁, -⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  exact cutBase_cases hμ (fun _ => by simp)
    (cutPiece_cases (by simp) (by simp [hp₁.le])
      (by by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs, hq₁.le])
      (by by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs, hq₁.le])) β

/-- Every base of `Ω.cutBase` ends at or before the end of the base of `Ω` from which it
arises. -/
theorem cutRight_le_right_cutOrigBase (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ)
    (β : Fin (Ω.numBases + 2)) : Ω.cutRight p μ q hμ β ≤ Ω.right (Ω.cutOrigBase μ hμ β) := by
  obtain ⟨-, hp₂, -, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  exact cutBase_cases hμ (fun _ => by simp)
    (cutPiece_cases (by simp [hp₂.le]) (by simp)
      (by by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs, hq₂.le])
      (by by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs, hq₂.le])) β

-- Reducible, so that the items and base count of `cutBase` are reducibly `Ω.numItems` and
-- `Ω.numBases + 2`.
variable (Ω) in
/-- **ET1: cutting a base at a boundary connection** (Kharlampovich–Myasnikov, §5.1). Replace the
distinct dual pair `μ, Δ(μ)` (`μ ≠ Δ(μ)`) by two dual pairs splitting `μ` at `p` and `Δ(μ)` at `q`,
retaining each boundary connection whose boundaries lie strictly inside a dual pair of pieces (when
`Ω` is formally consistent, this deletes `(p, μ, q)` and `(q, Δ(μ), p)` and restricts every other
connection to a unique piece). -/
abbrev cutBase (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) (q : Fin (Ω.numItems + 1))
    (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ) : GenEq A where
  numItems := Ω.numItems
  numBases := Ω.numBases + 2
  left := Ω.cutLeft p μ q hμ
  right := Ω.cutRight p μ q hμ
  left_lt_right := cutLeft_lt_cutRight hc hμ
  sign β := Ω.sign (Ω.cutOrigBase μ hμ β)
  dual := Ω.cutDual μ hμ
  dual_involutive := cutDual_involutive hμ
  constBases := Ω.constBases
  connections := Finset.univ.filter fun c =>
    (c.1, Ω.cutOrigBase μ hμ c.2.1, c.2.2) ∈ Ω.connections ∧
      Ω.cutLeft p μ q hμ c.2.1 < c.1 ∧ c.1 < Ω.cutRight p μ q hμ c.2.1 ∧
      Ω.cutLeft p μ q hμ (Ω.cutDual μ hμ c.2.1) < c.2.2 ∧
      c.2.2 < Ω.cutRight p μ q hμ (Ω.cutDual μ hμ c.2.1)
  bounds_of_mem_connections _ hc' := (Finset.mem_filter.1 hc').2.2
  dual_mem_connections c hc' := by
    obtain ⟨hc₀, h₁, h₂, h₃, h₄⟩ := (Finset.mem_filter.1 hc').2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, h₃, h₄, ?_, ?_⟩
    · rw [cutOrigBase_cutDual]
      exact Ω.dual_mem_connections _ hc₀
    · simpa [cutDual_involutive hμ c.2.1] using h₁
    · simpa [cutDual_involutive hμ c.2.1] using h₂

end CutData

/-! ### Combinatorial invariants of `cutBase` -/

section Combinatorics

variable {A : Type*} {Ω : GenEq A} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)} (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ)

/-- Cutting a dual pair `{μ, Δ(μ)}` adds two variable bases, replacing the pair by four pieces. -/
theorem numBases_cutBase : (Ω.cutBase p μ q hc hμ).numBases = Ω.numBases + 2 :=
  (rfl)

/-- Membership in the boundary connections of `Ω.cutBase p μ q hc hμ`. -/
theorem mem_connections_cutBase
    {c : Fin (Ω.numItems + 1) × Fin (Ω.numBases + 2) × Fin (Ω.numItems + 1)} :
    c ∈ (Ω.cutBase p μ q hc hμ).connections ↔
      (c.1, Ω.cutOrigBase μ hμ c.2.1, c.2.2) ∈ Ω.connections ∧
        Ω.cutLeft p μ q hμ c.2.1 < c.1 ∧ c.1 < Ω.cutRight p μ q hμ c.2.1 ∧
        Ω.cutLeft p μ q hμ (Ω.cutDual μ hμ c.2.1) < c.2.2 ∧
        c.2.2 < Ω.cutRight p μ q hμ (Ω.cutDual μ hμ c.2.1) := by
  simp

/-- Boundary connections through bases outside `{μ, Δ(μ)}` are unchanged by `cutBase`. -/
theorem mem_connections_cutBase_cutSurv {p' q' : Fin (Ω.numItems + 1)}
    {ν : Fin (Ω.cutSurvCard μ)} :
    (p', Ω.cutSurv μ hμ ν, q') ∈ (Ω.cutBase p μ q hc hμ).connections ↔
      (p', Ω.cutSurvEmb μ ν, q') ∈ Ω.connections := by
  rw [mem_connections_cutBase]
  dsimp only
  rw [cutOrigBase_cutSurv, cutLeft_cutSurv, cutRight_cutSurv, cutDual_cutSurv, cutLeft_cutSurv,
    cutRight_cutSurv, cutSurvEmb_dual]
  exact ⟨fun h => h.1, fun h => ⟨h, Ω.bounds_of_mem_connections _ h⟩⟩

/-- The segments `h[i, j] ^ ±1` only depend on the items, which `cutBase` preserves. -/
@[simp]
theorem segment_cutBase (i j : ℕ) (s : Bool) :
    (Ω.cutBase p μ q hc hμ).segment i j s = Ω.segment i j s := by
  cases s <;> simp only [segment_false, segment_true]

/-- The basic equation of a surviving base is its basic equation in `Ω`. -/
@[simp]
theorem basicEquation_cutBase_cutSurv (ν : Fin (Ω.cutSurvCard μ)) :
    (Ω.cutBase p μ q hc hμ).basicEquation (Ω.cutSurv μ hμ ν) =
      Ω.basicEquation (Ω.cutSurvEmb μ ν) :=
  Prod.ext (by simp) (by simp)

/-- `cutBase` preserves the coefficient equations. -/
@[simp]
theorem coeffEquation_cutBase (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.cutBase p μ q hc hμ).coeffEquation b = Ω.coeffEquation b :=
  Prod.ext (by simp) (by simp)

/-- The boundary equation of a connection through a surviving base is its boundary equation in
`Ω`. -/
@[simp]
theorem boundaryEquation_cutBase_cutSurv (p' q' : Fin (Ω.numItems + 1))
    (ν : Fin (Ω.cutSurvCard μ)) :
    (Ω.cutBase p μ q hc hμ).boundaryEquation (p', Ω.cutSurv μ hμ ν, q') =
      Ω.boundaryEquation (p', Ω.cutSurvEmb μ ν, q') := by
  refine Prod.ext (by simp) ?_
  by_cases hs : Ω.sign (Ω.cutSurvEmb μ ν) = Ω.sign (Ω.dual (Ω.cutSurvEmb μ ν)) <;>
    simp [boundaryEquation_snd_of_sign_eq, boundaryEquation_snd_of_sign_ne, hs]

/-- A boundary crosses a surviving base in `Ω.cutBase` iff it crosses it in `Ω`. -/
@[simp]
theorem crosses_cutBase_cutSurv {r : Fin (Ω.numItems + 1)} {ν : Fin (Ω.cutSurvCard μ)} :
    (Ω.cutBase p μ q hc hμ).Crosses r (Ω.cutSurv μ hμ ν) ↔ Ω.Crosses r (Ω.cutSurvEmb μ ν) := by
  simp [crosses_iff]

/-- A boundary crosses one of the two pieces of `μ` iff it crosses `μ` and differs from `p`. -/
theorem crosses_cutBase_cutPiece_zero_or_one_iff {r : Fin (Ω.numItems + 1)} :
    (Ω.cutBase p μ q hc hμ).Crosses r (Ω.cutPiece μ hμ 0) ∨
        (Ω.cutBase p μ q hc hμ).Crosses r (Ω.cutPiece μ hμ 1) ↔
      Ω.Crosses r μ ∧ r ≠ p := by
  obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  simp only [crosses_iff, cutLeft_cutPiece_zero, cutRight_cutPiece_zero, cutLeft_cutPiece_one,
    cutRight_cutPiece_one]
  grind

/-- A boundary crosses one of the two pieces of `Δ(μ)` iff it crosses `Δ(μ)` and differs from
`q`. -/
theorem crosses_cutBase_cutPiece_two_or_three_iff {r : Fin (Ω.numItems + 1)} :
    (Ω.cutBase p μ q hc hμ).Crosses r (Ω.cutPiece μ hμ 2) ∨
        (Ω.cutBase p μ q hc hμ).Crosses r (Ω.cutPiece μ hμ 3) ↔
      Ω.Crosses r (Ω.dual μ) ∧ r ≠ q := by
  obtain ⟨-, -, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  simp only [crosses_iff, cutLeft_cutPiece_two, cutRight_cutPiece_two, cutLeft_cutPiece_three,
    cutRight_cutPiece_three]
  split_ifs <;> grind

/-- Open boundaries of `Ω.cutBase`: a boundary is open after cutting `μ` at `(p, μ, q)` iff it
crosses a base outside `{μ, Δ(μ)}`, crosses `μ` away from `p`, or crosses `Δ(μ)` away from `q`. -/
theorem isOpenBoundary_cutBase_iff {r : Fin (Ω.numItems + 1)} :
    (Ω.cutBase p μ q hc hμ).IsOpenBoundary r ↔
      (∃ ν ∉ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases)), Ω.Crosses r ν) ∨
        (Ω.Crosses r μ ∧ r ≠ p) ∨ (Ω.Crosses r (Ω.dual μ) ∧ r ≠ q) := by
  rw [isOpenBoundary_iff, exists_cutBase hμ, exists_fin_four]
  have hsurv : (∃ ν, (Ω.cutBase p μ q hc hμ).Crosses r (Ω.cutSurv μ hμ ν)) ↔
      ∃ ν ∉ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases)), Ω.Crosses r ν := by
    refine ⟨fun ⟨ν, hν⟩ => ⟨_, cutSurvEmb_notMem ν, (crosses_cutBase_cutSurv hc hμ).1 hν⟩,
      fun ⟨ν, hν, hcr⟩ => ?_⟩
    obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hν
    exact ⟨ν₀, (crosses_cutBase_cutSurv hc hμ).2 hcr⟩
  rw [hsurv, crosses_cutBase_cutPiece_zero_or_one_iff hc hμ,
    crosses_cutBase_cutPiece_two_or_three_iff hc hμ]

/-- Every open boundary of `Ω.cutBase` was already open in `Ω`. -/
theorem IsOpenBoundary.of_cutBase {r : Fin (Ω.numItems + 1)}
    (hr : (Ω.cutBase p μ q hc hμ).IsOpenBoundary r) : Ω.IsOpenBoundary r := by
  rcases (isOpenBoundary_cutBase_iff hc hμ).1 hr with ⟨ν, -, hν⟩ | ⟨hμ', -⟩ | ⟨hΔ, -⟩
  exacts [hν.isOpenBoundary, hμ'.isOpenBoundary, hΔ.isOpenBoundary]

/-- Every closed boundary of `Ω` remains closed in `Ω.cutBase`. -/
theorem IsClosedBoundary.cutBase {r : Fin (Ω.numItems + 1)} (hr : Ω.IsClosedBoundary r) :
    (Ω.cutBase p μ q hc hμ).IsClosedBoundary r :=
  (Ω.cutBase p μ q hc hμ).not_isOpenBoundary.1 fun hopen =>
    Ω.not_isOpenBoundary.2 hr (IsOpenBoundary.of_cutBase hc hμ hopen)

/-- Cutting `μ` at `(p, μ, q)` strictly decreases the number of variable bases crossing `p`.
Iterating this step closes open boundaries with boundary connections (derived transformation
D1). -/
theorem card_crosses_cutBase_lt :
    #{β | (Ω.cutBase p μ q hc hμ).Crosses p β} < #{ν | Ω.Crosses p ν} := by
  have hmaps : Set.MapsTo (Ω.cutOrigBase μ hμ)
      (({β | (Ω.cutBase p μ q hc hμ).Crosses p β} : Finset _) : Set _)
      (((({ν | Ω.Crosses p ν} : Finset _) \ {μ} : Finset _)) : Set _) := by
    intro β hβ
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, crosses_iff] at hβ ⊢
    refine ⟨⟨(left_cutOrigBase_le hc hμ β).trans_lt hβ.1,
      hβ.2.trans_le (cutRight_le_right_cutOrigBase hc hμ β)⟩, ?_⟩
    revert hβ
    exact cutBase_cases hμ (fun _ _ => by simp)
      (cutPiece_cases (fun hβ => by simp at hβ) (fun hβ => by simp at hβ)
        (fun _ => by simp [hμ.symm]) (fun _ => by simp [hμ.symm])) β
  have hinj : Set.InjOn (Ω.cutOrigBase μ hμ)
      (({β | (Ω.cutBase p μ q hc hμ).Crosses p β} : Finset _) : Set _) := by
    intro β₁ hβ₁ β₂ hβ₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, crosses_iff] at hβ₁ hβ₂
    exact eq_of_cutOrigBase_eq hμ heq (hβ₁.1.trans hβ₂.2) (hβ₂.1.trans hβ₁.2)
  have hle := Finset.card_le_card_of_injOn (Ω.cutOrigBase μ hμ) hmaps hinj
  have hsub : {μ} ⊆ ({ν | Ω.Crosses p ν} : Finset _) := by
    simp [Ω.crosses_fst_of_mem_connections hc]
  have hadd := Finset.card_sdiff_add_card_eq_card hsub
  simp only [Finset.card_singleton] at hadd
  omega

/-- The items of the two pieces of `μ` partition the items of `μ`. -/
theorem baseItems_cutPiece_zero_union_one :
    (Ω.cutBase p μ q hc hμ).baseItems (Ω.cutPiece μ hμ 0) ∪
        (Ω.cutBase p μ q hc hμ).baseItems (Ω.cutPiece μ hμ 1) =
      Ω.baseItems μ := by
  obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂
  ext k
  simp only [Finset.mem_union, mem_baseItems, cutLeft_cutPiece_zero, cutRight_cutPiece_zero,
    cutLeft_cutPiece_one, cutRight_cutPiece_one]
  have := Fin.lt_def.1 hp₁; have := Fin.lt_def.1 hp₂; omega

/-- The items of the two pieces of `Δ(μ)` partition the items of `Δ(μ)`. -/
theorem baseItems_cutPiece_two_union_three :
    (Ω.cutBase p μ q hc hμ).baseItems (Ω.cutPiece μ hμ 2) ∪
        (Ω.cutBase p μ q hc hμ).baseItems (Ω.cutPiece μ hμ 3) =
      Ω.baseItems (Ω.dual μ) := by
  obtain ⟨-, -, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hq₁ hq₂
  ext k
  simp only [Finset.mem_union, mem_baseItems, cutLeft_cutPiece_two, cutRight_cutPiece_two,
    cutLeft_cutPiece_three, cutRight_cutPiece_three]
  have := Fin.lt_def.1 hq₁; have := Fin.lt_def.1 hq₂; split_ifs <;> omega

/-- `cutBase` preserves constant items. -/
@[simp]
theorem isConstantItem_cutBase_iff {k : Fin Ω.numItems} :
    (Ω.cutBase p μ q hc hμ).IsConstantItem k ↔ Ω.IsConstantItem k := by
  simp only [isConstantItem_iff]

/-- `cutBase` preserves free items. -/
@[simp]
theorem isFreeItem_cutBase_iff {k : Fin Ω.numItems} :
    (Ω.cutBase p μ q hc hμ).IsFreeItem k ↔ Ω.IsFreeItem k := by
  simp only [isFreeItem_iff, isConstantItem_cutBase_iff]
  refine and_congr_left' (not_iff_not.1 ?_)
  push Not
  rw [exists_cutBase hμ, exists_fin_four]
  have h₀₁ : k ∈ (Ω.cutBase p μ q hc hμ).baseItems (Ω.cutPiece μ hμ 0) ∨
      k ∈ (Ω.cutBase p μ q hc hμ).baseItems (Ω.cutPiece μ hμ 1) ↔ k ∈ Ω.baseItems μ := by
    simpa [Finset.mem_union] using Finset.ext_iff.1 (baseItems_cutPiece_zero_union_one hc hμ) k
  have h₂₃ : k ∈ (Ω.cutBase p μ q hc hμ).baseItems (Ω.cutPiece μ hμ 2) ∨
      k ∈ (Ω.cutBase p μ q hc hμ).baseItems (Ω.cutPiece μ hμ 3) ↔ k ∈ Ω.baseItems (Ω.dual μ) := by
    simpa [Finset.mem_union] using Finset.ext_iff.1 (baseItems_cutPiece_two_union_three hc hμ) k
  refine ⟨?_, fun ⟨ν, hν⟩ => ?_⟩
  · rintro (⟨ν, hν⟩ | (h₀ | h₁) | (h₂ | h₃))
    · exact ⟨Ω.cutSurvEmb μ ν, by simpa [mem_baseItems] using hν⟩
    · exact ⟨μ, h₀₁.1 (Or.inl h₀)⟩
    · exact ⟨μ, h₀₁.1 (Or.inr h₁)⟩
    · exact ⟨Ω.dual μ, h₂₃.1 (Or.inl h₂)⟩
    · exact ⟨Ω.dual μ, h₂₃.1 (Or.inr h₃)⟩
  · by_cases hmem : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))
    · rcases Finset.mem_insert.1 hmem with hνμ | hmem
      · exact Or.inr (Or.inl (h₀₁.2 (hνμ ▸ hν)))
      · exact Or.inr (Or.inr (h₂₃.2 (Finset.mem_singleton.1 hmem ▸ hν)))
    · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
      exact Or.inl ⟨ν₀, by simpa [mem_baseItems] using hν⟩

/-- Cutting `μ` at `(p, μ, q)` preserves the degree of every item: `μ` is partitioned into two
disjoint pieces and `Δ(μ)` into two disjoint pieces. -/
theorem degree_cutBase (k : Fin Ω.numItems) :
    (Ω.cutBase p μ q hc hμ).degree k = Ω.degree k := by
  simp only [degree_def]
  refine congrArg (· + _) ?_
  refine Finset.card_bij (fun β _ => Ω.cutOrigBase μ hμ β) (fun β hβ => ?_)
    (fun β₁ h₁ β₂ h₂ h => ?_) (fun ν hν => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_baseItems] at hβ ⊢
    have hl := Fin.le_def.1 (left_cutOrigBase_le hc hμ β)
    have hr := Fin.le_def.1 (cutRight_le_right_cutOrigBase hc hμ β)
    omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_baseItems] at h₁ h₂
    exact eq_of_cutOrigBase_eq (p := p) (q := q) hμ h (Fin.lt_def.2 (by omega))
      (Fin.lt_def.2 (by omega))
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hν ⊢
    by_cases hmem : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))
    · rcases Finset.mem_insert.1 hmem with hνμ | hmem
      · rw [hνμ] at hν ⊢
        rw [← baseItems_cutPiece_zero_union_one hc hμ, Finset.mem_union] at hν
        rcases hν with h₀ | h₁
        exacts [⟨Ω.cutPiece μ hμ 0, h₀, by simp⟩, ⟨Ω.cutPiece μ hμ 1, h₁, by simp⟩]
      · rw [Finset.mem_singleton.1 hmem] at hν ⊢
        rw [← baseItems_cutPiece_two_union_three hc hμ, Finset.mem_union] at hν
        rcases hν with h₂ | h₃
        exacts [⟨Ω.cutPiece μ hμ 2, h₂, by simp⟩, ⟨Ω.cutPiece μ hμ 3, h₃, by simp⟩]
    · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
      exact ⟨Ω.cutSurv μ hμ ν₀, by simpa [mem_baseItems] using hν, by simp⟩

/-- Map a connection of `Ω.cutBase` back to the connection of `Ω` from which it came. -/
private def unliftConnection
    (c : Fin (Ω.numItems + 1) × Fin (Ω.numBases + 2) × Fin (Ω.numItems + 1)) :
    Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1) :=
  (c.1, Ω.cutOrigBase μ hμ c.2.1, c.2.2)

private theorem injOn_unliftConnection :
    Set.InjOn (unliftConnection hμ) ((Ω.cutBase p μ q hc hμ).connections : Set _) := by
  rintro ⟨p₁, β₁, q₁⟩ h₁ ⟨p₂, β₂, q₂⟩ h₂ heq
  simp only [unliftConnection, Prod.mk.injEq] at heq
  obtain ⟨rfl, hβ, rfl⟩ := heq
  obtain ⟨-, hl₁, hr₁, -⟩ := (mem_connections_cutBase hc hμ).1 h₁
  obtain ⟨-, hl₂, hr₂, -⟩ := (mem_connections_cutBase hc hμ).1 h₂
  dsimp only at hl₁ hr₁ hl₂ hr₂
  congr 2
  exact eq_of_cutOrigBase_eq hμ hβ (hl₁.trans hr₂) (hl₂.trans hr₁)

private theorem unliftConnection_mem_sdiff
    {c : Fin (Ω.numItems + 1) × Fin (Ω.numBases + 2) × Fin (Ω.numItems + 1)}
    (hc' : c ∈ (Ω.cutBase p μ q hc hμ).connections) :
    unliftConnection hμ c ∈ Ω.connections \ {(p, μ, q), (q, Ω.dual μ, p)} := by
  obtain ⟨hc₀, hl₁, hr₁, -⟩ := (mem_connections_cutBase hc hμ).1 hc'
  refine Finset.mem_sdiff.2 ⟨hc₀, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, unliftConnection, Prod.mk.injEq, not_or]
  rcases c with ⟨p', β, q'⟩
  dsimp only at hc₀ hl₁ hr₁ ⊢
  refine ⟨?_, ?_⟩
  · rintro ⟨rfl, hβ, rfl⟩
    revert hβ hl₁ hr₁
    exact cutBase_cases hμ (fun _ hβ _ _ => by simp at hβ)
      (cutPiece_cases (fun _ _ hr₁ => by simp at hr₁) (fun _ hl₁ _ => by simp at hl₁)
        (fun hβ _ _ => hμ (by simpa using hβ.symm))
        (fun hβ _ _ => hμ (by simpa using hβ.symm))) β
  · rintro ⟨rfl, hβ, rfl⟩
    revert hβ hl₁ hr₁
    exact cutBase_cases hμ (fun _ hβ _ _ => by simp at hβ)
      (cutPiece_cases (fun hβ _ _ => hμ (by simpa using hβ))
        (fun hβ _ _ => hμ (by simpa using hβ))
        (fun _ hl₁ hr₁ => by by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs] at hl₁ hr₁)
        (fun _ hl₁ hr₁ => by by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs] at hl₁ hr₁))
      β

include hc hμ in
private theorem card_connections_sdiff_pair_add_two :
    #(Ω.connections \ {(p, μ, q), (q, Ω.dual μ, p)}) + 2 = #Ω.connections := by
  have hsub : {(p, μ, q), (q, Ω.dual μ, p)} ⊆ Ω.connections := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hc
    · exact Finset.mem_singleton.1 hx ▸ Ω.dual_mem_connections _ hc
  have hpair : #({(p, μ, q), (q, Ω.dual μ, p)} : Finset _) = 2 :=
    Finset.card_pair fun h => hμ (Prod.mk.inj (Prod.mk.inj h).2).1
  rw [← hpair]
  exact Finset.card_sdiff_add_card_eq_card hsub

/-- Cutting `μ` at `(p, μ, q)` removes at least the two connections `(p, μ, q)` and
`(q, Δ(μ), p)`. -/
theorem card_connections_cutBase_add_two_le :
    #(Ω.cutBase p μ q hc hμ).connections + 2 ≤ #Ω.connections := by
  have hle := Finset.card_le_card_of_injOn (unliftConnection hμ)
    (fun _ hc' => unliftConnection_mem_sdiff hc hμ hc') (injOn_unliftConnection hc hμ)
  have hadd := card_connections_sdiff_pair_add_two hc hμ
  omega

/-- Cutting `μ` at `(p, μ, q)` strictly decreases the number of boundary connections. Iterating this
step eliminates all boundary connections (derived transformation D3, complete cut). -/
theorem card_connections_cutBase_lt :
    #(Ω.cutBase p μ q hc hμ).connections < #Ω.connections := by
  have := card_connections_cutBase_add_two_le hc hμ
  omega

/-- In a formally consistent generalised equation, a connection `(p', μ, q')` with `p' < p` becomes
a connection on `cutPiece μ hμ 0` in `Ω.cutBase`, and its dual becomes one on `cutPiece μ hμ 2`. -/
theorem mem_connections_cutBase_of_lt (hΩ : Ω.IsFormallyConsistent)
    {p' q' : Fin (Ω.numItems + 1)} (hc' : (p', μ, q') ∈ Ω.connections) (hpp' : p' < p) :
    (p', Ω.cutPiece μ hμ 0, q') ∈ (Ω.cutBase p μ q hc hμ).connections ∧
      (q', Ω.cutPiece μ hμ 2, p') ∈ (Ω.cutBase p μ q hc hμ).connections := by
  obtain ⟨hp₁, -, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p', μ, q') hc'
  have hmid : (p', Ω.cutPiece μ hμ 0, q') ∈ (Ω.cutBase p μ q hc hμ).connections := by
    rw [mem_connections_cutBase]
    dsimp only
    rw [cutOrigBase_cutPiece_zero, cutLeft_cutPiece_zero, cutRight_cutPiece_zero,
      cutDual_cutPiece_zero, cutLeft_cutPiece_two, cutRight_cutPiece_two]
    refine ⟨hc', hp₁, hpp', ?_⟩
    by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
    · simp [hs, hq₁, hΩ.lt_of_isTiedTo_of_sign_eq hs (isTiedTo_of_mem_connections hc')
        (isTiedTo_of_mem_connections hc) hpp']
    · simp [hs, hq₂, hΩ.lt_of_isTiedTo_of_sign_ne hs (isTiedTo_of_mem_connections hc')
        (isTiedTo_of_mem_connections hc) hpp']
  exact ⟨hmid, by simpa using (Ω.cutBase p μ q hc hμ).dual_mem_connections _ hmid⟩

/-- In a formally consistent generalised equation, a connection `(p', μ, q')` with `p < p'` becomes
a connection on `cutPiece μ hμ 1` in `Ω.cutBase`, and its dual becomes one on `cutPiece μ hμ 3`. -/
theorem mem_connections_cutBase_of_gt (hΩ : Ω.IsFormallyConsistent)
    {p' q' : Fin (Ω.numItems + 1)} (hc' : (p', μ, q') ∈ Ω.connections) (hpp' : p < p') :
    (p', Ω.cutPiece μ hμ 1, q') ∈ (Ω.cutBase p μ q hc hμ).connections ∧
      (q', Ω.cutPiece μ hμ 3, p') ∈ (Ω.cutBase p μ q hc hμ).connections := by
  obtain ⟨-, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p', μ, q') hc'
  have hmid : (p', Ω.cutPiece μ hμ 1, q') ∈ (Ω.cutBase p μ q hc hμ).connections := by
    rw [mem_connections_cutBase]
    dsimp only
    rw [cutOrigBase_cutPiece_one, cutLeft_cutPiece_one, cutRight_cutPiece_one,
      cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three]
    refine ⟨hc', hpp', hp₂, ?_⟩
    by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
    · simp [hs, hq₂, hΩ.lt_of_isTiedTo_of_sign_eq hs (isTiedTo_of_mem_connections hc)
        (isTiedTo_of_mem_connections hc') hpp']
    · simp [hs, hq₁, hΩ.lt_of_isTiedTo_of_sign_ne hs (isTiedTo_of_mem_connections hc)
        (isTiedTo_of_mem_connections hc') hpp']
  exact ⟨hmid, by simpa using (Ω.cutBase p μ q hc hμ).dual_mem_connections _ hmid⟩

/-- In a formally consistent generalised equation, cutting `μ` at `(p, μ, q)` decreases the number
of boundary connections by exactly `2`: `(p, μ, q)` and `(q, Δ(μ), p)` are deleted, and every other
connection is retained on a unique piece. -/
theorem card_connections_cutBase (hΩ : Ω.IsFormallyConsistent) :
    #(Ω.cutBase p μ q hc hμ).connections + 2 = #Ω.connections := by
  rw [← card_connections_sdiff_pair_add_two hc hμ]
  refine congrArg (· + 2) <| Finset.card_bij (fun c _ => unliftConnection hμ c)
    (fun c hc' => unliftConnection_mem_sdiff hc hμ hc')
    (fun c₁ h₁ c₂ h₂ h => injOn_unliftConnection hc hμ h₁ h₂ h) (fun c hc' => ?_)
  obtain ⟨hc₀, hne⟩ := Finset.mem_sdiff.1 hc'
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
  rcases c with ⟨p', ν, q'⟩
  by_cases hmem : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))
  · rcases Finset.mem_insert.1 hmem with hνμ | hmem
    · rw [hνμ] at hc₀ hne ⊢
      have hp_ne : p' ≠ p := fun hp_eq => by
        subst hp_eq
        exact hne.1 (by rw [hΩ.isTiedTo_unique (isTiedTo_of_mem_connections hc₀)
          (isTiedTo_of_mem_connections hc)])
      rcases lt_or_gt_of_ne hp_ne with hlt | hgt
      · exact ⟨(p', Ω.cutPiece μ hμ 0, q'), (mem_connections_cutBase_of_lt hc hμ hΩ hc₀ hlt).1,
          by simp [unliftConnection]⟩
      · exact ⟨(p', Ω.cutPiece μ hμ 1, q'), (mem_connections_cutBase_of_gt hc hμ hΩ hc₀ hgt).1,
          by simp [unliftConnection]⟩
    · rw [Finset.mem_singleton.1 hmem] at hc₀ hne ⊢
      have hc₀_dual : (q', μ, p') ∈ Ω.connections := by
        simpa [Ω.dual_involutive μ] using Ω.dual_mem_connections _ hc₀
      have hq_ne : q' ≠ p := fun hq_eq => by
        subst hq_eq
        exact hne.2 (by rw [hΩ.isTiedTo_unique (isTiedTo_of_mem_connections hc₀_dual)
          (isTiedTo_of_mem_connections hc)])
      rcases lt_or_gt_of_ne hq_ne with hlt | hgt
      · exact ⟨(p', Ω.cutPiece μ hμ 2, q'),
          (mem_connections_cutBase_of_lt hc hμ hΩ hc₀_dual hlt).2, by simp [unliftConnection]⟩
      · exact ⟨(p', Ω.cutPiece μ hμ 3, q'),
          (mem_connections_cutBase_of_gt hc hμ hΩ hc₀_dual hgt).2, by simp [unliftConnection]⟩
  · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
    exact ⟨(p', Ω.cutSurv μ hμ ν₀, q'), (mem_connections_cutBase_cutSurv hc hμ).2 hc₀,
      by simp [unliftConnection]⟩

/-- Transport a parametric section partition of `Ω` to `Ω.cutBase`, keeping the kind of every
item: cutting bases only closes boundaries, so open boundaries of `Ω.cutBase` were open in `Ω`. -/
def SectionPartition.cutBase (P : Ω.SectionPartition) :
    (Ω.cutBase p μ q hc hμ).SectionPartition where
  itemKind := P.itemKind
  itemKind_eq_of_isOpenBoundary k k' hk hopen :=
    P.itemKind_eq_of_isOpenBoundary k k' hk (IsOpenBoundary.of_cutBase hc hμ hopen)

/-- `SectionPartition.cutBase` preserves the kind of every item. -/
@[simp]
theorem SectionPartition.cutBase_itemKind (P : Ω.SectionPartition) :
    (P.cutBase hc hμ).itemKind = P.itemKind := (rfl)

/-- Transporting a section partition along `cutBase` preserves standard form. -/
@[simp]
theorem SectionPartition.isStandardForm_cutBase_iff (P : Ω.SectionPartition) :
    (P.cutBase hc hμ).IsStandardForm ↔ P.IsStandardForm := by
  simp only [isStandardForm_iff, cutBase_itemKind, isFreeItem_cutBase_iff]

end Combinatorics

/-! ### Formal consistency -/

section FormalConsistency

variable {A : Type*} {Ω : GenEq A} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)} (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ)

private theorem cutBase_disjoint_of_sign_ne (hΩ : Ω.IsFormallyConsistent)
    (β : Fin (Ω.cutBase p μ q hc hμ).numBases)
    (hs : (Ω.cutBase p μ q hc hμ).sign β ≠
      (Ω.cutBase p μ q hc hμ).sign ((Ω.cutBase p μ q hc hμ).dual β)) :
    (Ω.cutBase p μ q hc hμ).right β ≤
        (Ω.cutBase p μ q hc hμ).left ((Ω.cutBase p μ q hc hμ).dual β) ∨
      (Ω.cutBase p μ q hc hμ).right ((Ω.cutBase p μ q hc hμ).dual β) ≤
        (Ω.cutBase p μ q hc hμ).left β := by
  have hs₀ : Ω.sign (Ω.cutOrigBase μ hμ β) ≠ Ω.sign (Ω.dual (Ω.cutOrigBase μ hμ β)) := by
    simpa using hs
  rcases hΩ.disjoint_of_sign_ne (Ω.cutOrigBase μ hμ β) hs₀ with h | h
  · exact Or.inl <| (cutRight_le_right_cutOrigBase hc hμ β).trans <|
      h.trans (cutOrigBase_cutDual hμ β ▸ left_cutOrigBase_le hc hμ (Ω.cutDual μ hμ β))
  · exact Or.inr <|
      (cutRight_le_right_cutOrigBase hc hμ (Ω.cutDual μ hμ β)).trans <|
        (cutOrigBase_cutDual hμ β ▸ h).trans (left_cutOrigBase_le hc hμ β)

/-- Given that `Ω` is formally consistent, `Ω.cutBase p μ q hc hμ` is formally consistent if and
only if, whenever `p = q` and `ε(μ) = ε(Δμ)`, every connection `(p′, μ, q′)` of `Ω` strictly to the
right of `p` satisfies `p′ = q′` (the matched-pair condition on the right-hand pieces `[p, β(μ)]`
and `[p, β(Δμ)]`). -/
theorem isFormallyConsistent_cutBase_iff (hΩ : Ω.IsFormallyConsistent) :
    (Ω.cutBase p μ q hc hμ).IsFormallyConsistent ↔
      (p = q → Ω.sign μ = Ω.sign (Ω.dual μ) →
        ∀ c ∈ Ω.connections, c.2.1 = μ → p < c.1 → c.1 = c.2.2) := by
  refine ⟨fun hΩ' hpq hs c hc' hcμ hpc => ?_, fun H => ?_⟩
  · rcases c with ⟨p', ν, q'⟩
    dsimp only at hcμ hpc ⊢
    rw [hcμ] at hc'
    have hc'' := (mem_connections_cutBase_of_gt hc hμ hΩ hc' hpc).1
    have hleft : (Ω.cutBase p μ q hc hμ).left (Ω.cutPiece μ hμ 1) =
        (Ω.cutBase p μ q hc hμ).left ((Ω.cutBase p μ q hc hμ).dual (Ω.cutPiece μ hμ 1)) := by
      simp [hs, hpq]
    exact hΩ'.eq_of_left_eq _ hc'' hleft
  · refine
      { disjoint_of_sign_ne := cutBase_disjoint_of_sign_ne hc hμ hΩ
        connections_monotone_or_antitone := fun c₁ hc₁ c₂ hc₂ hβ hle => by
          have h₁ := ((mem_connections_cutBase hc hμ).1 hc₁).1
          have h₂ := ((mem_connections_cutBase hc hμ).1 hc₂).1
          have horig : Ω.cutOrigBase μ hμ c₁.2.1 = Ω.cutOrigBase μ hμ c₂.2.1 := congrArg _ hβ
          simpa [hβ] using hΩ.connections_monotone_or_antitone _ h₁ _ h₂ horig hle
        eq_of_left_eq := fun ⟨r₁, β, r₂⟩ hc' hleft => ?_
        label_eq := hΩ.label_eq
        connections_adjacent := fun b hb c₁ hc₁ c₂ hc₂ hβ hp₁ hp₂ => by
          have h₁ := ((mem_connections_cutBase hc hμ).1 hc₁).1
          have h₂ := ((mem_connections_cutBase hc hμ).1 hc₂).1
          have horig : Ω.cutOrigBase μ hμ c₁.2.1 = Ω.cutOrigBase μ hμ c₂.2.1 := congrArg _ hβ
          exact hΩ.connections_adjacent b hb _ h₁ _ h₂ horig hp₁ hp₂ }
    have hs_eq : (Ω.cutBase p μ q hc hμ).sign β =
        (Ω.cutBase p μ q hc hμ).sign ((Ω.cutBase p μ q hc hμ).dual β) := by
      by_contra hne
      rcases cutBase_disjoint_of_sign_ne hc hμ hΩ β hne with h | h <;>
        exact lt_irrefl _ (h.trans_lt (hleft ▸ (Ω.cutBase p μ q hc hμ).left_lt_right _))
    dsimp only at hleft ⊢
    revert hc' hleft hs_eq
    refine cutBase_cases hμ (fun ν hc' hleft _ => ?_) (fun i hc' hleft hs_eq => ?_) β
    · have hc₀ : (r₁, Ω.cutSurvEmb μ ν, r₂) ∈ Ω.connections :=
        by simpa using ((mem_connections_cutBase hc hμ).1 hc').1
      exact hΩ.eq_of_left_eq _ hc₀ (by simpa [cutSurvEmb_dualCompl] using hleft)
    · fin_cases i
      · obtain ⟨hc₀, -, -, -, -⟩ := (mem_connections_cutBase hc hμ).1 hc'
        have hs : Ω.sign μ = Ω.sign (Ω.dual μ) := by simpa using hs_eq
        exact hΩ.eq_of_left_eq (r₁, μ, r₂) (by simpa using hc₀) (by simpa [hs] using hleft)
      · obtain ⟨hc₀, hl₁, -, -, -⟩ := (mem_connections_cutBase hc hμ).1 hc'
        have hs : Ω.sign μ = Ω.sign (Ω.dual μ) := by simpa using hs_eq
        have hpq : p = q := by simpa [hs] using hleft
        exact H hpq hs (r₁, μ, r₂) (by simpa using hc₀) rfl (by simpa using hl₁)
      · obtain ⟨hc₀, -, -, -, -⟩ := (mem_connections_cutBase hc hμ).1 hc'
        have hs : Ω.sign μ = Ω.sign (Ω.dual μ) := by simpa [eq_comm] using hs_eq
        exact hΩ.eq_of_left_eq (r₁, Ω.dual μ, r₂) (by simpa using hc₀)
          (by simpa [hs, Ω.dual_involutive μ] using hleft)
      · obtain ⟨hc₀, -, -, hl₂, -⟩ := (mem_connections_cutBase hc hμ).1 hc'
        have hs : Ω.sign μ = Ω.sign (Ω.dual μ) := by simpa [eq_comm] using hs_eq
        have hpq : p = q := (by simpa [hs] using hleft : q = p).symm
        have hc₀' : (r₁, Ω.dual μ, r₂) ∈ Ω.connections := by simpa using hc₀
        have hc₀_dual : (r₂, μ, r₁) ∈ Ω.connections := by
          simpa [Ω.dual_involutive μ] using Ω.dual_mem_connections (r₁, Ω.dual μ, r₂) hc₀'
        exact (H hpq hs (r₂, μ, r₁) hc₀_dual rfl (by simpa using hl₂)).symm

/-- When `p ≠ q`, cutting `μ` at `(p, μ, q)` preserves formal consistency unconditionally. -/
theorem IsFormallyConsistent.cutBase_of_ne (hΩ : Ω.IsFormallyConsistent) (hpq : p ≠ q) :
    (Ω.cutBase p μ q hc hμ).IsFormallyConsistent :=
  (isFormallyConsistent_cutBase_iff hc hμ hΩ).2 fun h => absurd h hpq

/-- When `ε(μ) ≠ ε(Δμ)`, cutting `μ` at `(p, μ, q)` preserves formal consistency unconditionally. -/
theorem IsFormallyConsistent.cutBase_of_sign_ne (hΩ : Ω.IsFormallyConsistent)
    (hs : Ω.sign μ ≠ Ω.sign (Ω.dual μ)) : (Ω.cutBase p μ q hc hμ).IsFormallyConsistent :=
  (isFormallyConsistent_cutBase_iff hc hμ hΩ).2 fun _ h => absurd h hs

end FormalConsistency

/-! ### Combinatorial examples -/

section Examples

/-- Four items `h₀, h₁, h₂, h₃`, dual bases `μ = [0, 2]` (sign `+1`) and `Δ(μ) = [2, 4]` (sign `s`),
and the boundary connection `(1, μ, 3)` with its dual. -/
private abbrev cutPairExample (s : Bool) : GenEq (Fin 2) where
  numItems := 4
  numBases := 2
  left := ![0, 2]
  right := ![2, 4]
  left_lt_right := by decide
  sign := ![true, s]
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 3), (3, 1, 1)}
  bounds_of_mem_connections := by decide
  dual_mem_connections := by decide

private theorem cutPairExample_mem (s : Bool) : (1, 0, 3) ∈ (cutPairExample s).connections := by
  cases s <;> decide

private theorem cutPairExample_ne (s : Bool) :
    (0 : Fin (cutPairExample s).numBases) ≠ (cutPairExample s).dual 0 := by
  cases s <;> decide

/-- Cutting `(1, μ, 3)` in `cutPairExample true` (`h₀h₁ = h₂h₃`, `h₀ = h₂`) produces four bases
with no remaining boundary connections, closes the cut boundaries `1` and `3`, and pairs `[0, 1]`
with `[2, 3]` and `[1, 2]` with `[3, 4]`. -/
example :
    let Ω₀ := cutPairExample true
    let hμ := cutPairExample_ne true
    let Ω' := Ω₀.cutBase 1 0 3 (cutPairExample_mem true) hμ
    Ω'.numBases = 4 ∧ Ω'.connections = ∅ ∧
      Ω'.IsClosedBoundary 1 ∧ Ω'.IsClosedBoundary 3 ∧
      Ω'.left (Ω₀.cutPiece 0 hμ 0) = 0 ∧ Ω'.right (Ω₀.cutPiece 0 hμ 0) = 1 ∧
      Ω'.left (Ω₀.cutPiece 0 hμ 2) = 2 ∧ Ω'.right (Ω₀.cutPiece 0 hμ 2) = 3 ∧
      Ω'.left (Ω₀.cutPiece 0 hμ 1) = 1 ∧ Ω'.right (Ω₀.cutPiece 0 hμ 1) = 2 ∧
      Ω'.left (Ω₀.cutPiece 0 hμ 3) = 3 ∧ Ω'.right (Ω₀.cutPiece 0 hμ 3) = 4 := by
  decide

/-- Cutting `(1, μ, 3)` in `cutPairExample false` (`h₀h₁ = (h₂h₃)⁻¹`, `h₀ = h₃⁻¹`) pairs `[0, 1]`
with `[3, 4]` and `[1, 2]` with `[2, 3]`, reversing the order of the dual pieces. -/
example :
    let Ω₀ := cutPairExample false
    let hμ := cutPairExample_ne false
    let Ω' := Ω₀.cutBase 1 0 3 (cutPairExample_mem false) hμ
    Ω'.left (Ω₀.cutPiece 0 hμ 0) = 0 ∧ Ω'.right (Ω₀.cutPiece 0 hμ 0) = 1 ∧
      Ω'.left (Ω₀.cutPiece 0 hμ 2) = 3 ∧ Ω'.right (Ω₀.cutPiece 0 hμ 2) = 4 ∧
      Ω'.left (Ω₀.cutPiece 0 hμ 1) = 1 ∧ Ω'.right (Ω₀.cutPiece 0 hμ 1) = 2 ∧
      Ω'.left (Ω₀.cutPiece 0 hμ 3) = 2 ∧ Ω'.right (Ω₀.cutPiece 0 hμ 3) = 3 := by
  decide

/-- An unsolvable formally consistent generalised equation (`μ = [0, 4]`, `Δ(μ) = [1, 5]`, both of
sign `+1`, with connections `(2, μ, 2)` and `(3, μ, 4)`) whose cut at `(2, μ, 2)` is not formally
consistent: cutting exposes the matched pair `[2, 4] ~ [2, 5]` starting at `2`, through which the
retained connection `(3, _, 4)` violates Condition 3 of formal consistency. -/
private abbrev unsolvableCutExample : GenEq (Fin 2) where
  numItems := 5
  numBases := 2
  left := ![0, 1]
  right := ![4, 5]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(2, 0, 2), (2, 1, 2), (3, 0, 4), (4, 1, 3)}
  bounds_of_mem_connections := by decide
  dual_mem_connections := by decide

example : unsolvableCutExample.IsFormallyConsistent ∧
    ¬ (unsolvableCutExample.cutBase 2 0 2 (by decide) (by decide)).IsFormallyConsistent := by
  decide

end Examples

end GenEq

end TauCeti
