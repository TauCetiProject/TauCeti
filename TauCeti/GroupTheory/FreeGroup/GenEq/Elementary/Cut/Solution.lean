/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Constraint
public import TauCeti.GroupTheory.FreeGroup.GenEq.Elementary.Cut.Basic
public import TauCeti.GroupTheory.FreeGroup.GenEq.Transformation
import Mathlib.Data.Fin.VecNotation

/-!
# Cutting a base at a boundary connection: solutions, coordinate groups, and transformation

Continuing `TauCeti.GroupTheory.FreeGroup.GenEq.Elementary.Cut.Basic`, this file relates the group
solutions, coordinate groups, and graphical solutions of a generalised equation `Ω` to those of
`Ω′ = Ω.cutBase p μ q hc` obtained by cutting a variable base `μ` and its dual `Δ(μ)` at a boundary
connection `(p, μ, q)` (elementary transformation ET1 of Makanin's process,
Kharlampovich–Myasnikov, §5.1).

* **Group solutions and coordinate groups.** Every point of `Ω*` in an `F(A)`-group is a point of
  `Ω′*` (`TauCeti.GenEq.V_toSystem_subset_cutBase`) without any formal-consistency hypothesis. When
  `Ω` is formally consistent, `Ω*` and `Ω′*` have the exact same points
  (`TauCeti.GenEq.V_toSystem_cutBase`), and the identity on the items induces an
  `F(A)`-isomorphism `F_{R(Ω)} → F_{R(Ω′)}` of coordinate groups (`TauCeti.GenEq.cutBaseHom`,
  `TauCeti.GenEq.cutBaseHom_bijective`).
* **Graphical solutions.** Every graphical solution `U` of `Ω` transfers with the same item words to
  a graphical solution `U.cutBase hc` of `Ω′` (`TauCeti.GenEq.Solution.cutBase`), and when `Ω` is
  formally consistent it is the unique solution of `Ω′` whose homomorphism factors `U.toHom` through
  `cutBaseHom` (`TauCeti.GenEq.toHom_comp_cutBaseHom_eq_iff`). In particular, if `Ω` has a
  solution then `Ω′` is formally consistent
  (`TauCeti.GenEq.isFormallyConsistent_cutBase_of_nonempty_solution`).
* **Backward graphical equivalence and creases.** When `Ω` is formally consistent, the graphical
  solutions of `Ω` are in bijection with those graphical solutions of `Ω′` for which the word
  `U′[α(μ), β(μ)]` is reduced as written (`TauCeti.GenEq.solutionEquivCutBase`). If the cut
  boundary `p` remains open in `Ω′`, another base crosses `p` and prevents cancellation across the
  cut, so `Ω.Solution ≃ Ω′.Solution` unconditionally (`TauCeti.GenEq.solutionEquivCutBaseOfOpen`).
  When `p` becomes closed, cancellation at the crease can occur, as a four-item example at the end
  of the file demonstrates.
* **Transformation packaging.** `TauCeti.GenEq.cutBaseTransformation` packages ET1 on a formally
  consistent `Ω` as a `TauCeti.GenEq.Transformation` (retaining `Ω′` iff it is formally consistent)
  that transfers solutions uniquely (`TauCeti.GenEq.transfersUniquely_cutBaseTransformation`).

## Main definitions

* `TauCeti.GenEq.cutBaseHom`: the `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` induced by the
  identity on the items.
* `TauCeti.GenEq.Solution.cutBase`: transfer of a solution of `Ω` to `Ω′`.
* `TauCeti.GenEq.solutionEquivCutBase`, `TauCeti.GenEq.solutionEquivCutBaseOfOpen`: equivalences
  between solutions of `Ω` and solutions of `Ω′`.
* `TauCeti.GenEq.cutBaseTransformation`: ET1 packaged as a `Transformation Ω`.

## Main results

* `TauCeti.GenEq.V_toSystem_cutBase`, `TauCeti.GenEq.cutBaseHom_bijective`: ET1 preserves group
  solutions and induces an `F(A)`-isomorphism of coordinate groups when `Ω` is formally consistent.
* `TauCeti.GenEq.toHom_comp_cutBaseHom_eq_iff`,
  `TauCeti.GenEq.transfersUniquely_cutBaseTransformation`: ET1 transfers graphical solutions
  uniquely.
* `TauCeti.GenEq.isReduced_cutBase_of_isOpenBoundary`: an open cut boundary prevents cancellation
  between the two pieces of `μ`.

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

open GroupAlgGeom Monoid.Coprod
open FreeGroup (substituteVars substituteVars_append substituteVars_invRev)

section GroupSolutions

variable {A : Type*} {Ω : GenEq A} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)} (hc : (p, μ, q) ∈ Ω.connections)

private theorem lift_mk_segment_mul {H : Type*} [Group H] (f : Fin Ω.numItems ⊕ A → H)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ Ω.numItems) :
    FreeGroup.lift f (FreeGroup.mk (Ω.segment i k true)) =
      FreeGroup.lift f (FreeGroup.mk (Ω.segment i j true)) *
        FreeGroup.lift f (FreeGroup.mk (Ω.segment j k true)) := by
  rw [← Ω.segment_append hij hjk hk, ← FreeGroup.mul_mk, map_mul]

private theorem lift_mk_segment_eq_of_sign_eq {H : Type*} [Group H] {f : Fin Ω.numItems ⊕ A → H}
    {i₁ j₁ i₂ j₂ : ℕ} {s₁ s₂ : Bool} (hs : s₁ = s₂) :
    FreeGroup.lift f (FreeGroup.mk (Ω.segment i₁ j₁ s₁)) =
        FreeGroup.lift f (FreeGroup.mk (Ω.segment i₂ j₂ s₂)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.segment i₁ j₁ true)) =
        FreeGroup.lift f (FreeGroup.mk (Ω.segment i₂ j₂ true)) := by
  subst hs
  cases s₁
  · rw [Ω.lift_mk_segment f i₁ j₁ false, Ω.lift_mk_segment f i₂ j₂ false]
    exact inv_inj
  · rfl

private theorem lift_mk_segment_eq_of_sign_ne {H : Type*} [Group H] {f : Fin Ω.numItems ⊕ A → H}
    {i₁ j₁ i₂ j₂ : ℕ} {s₁ s₂ : Bool} (hs : s₁ ≠ s₂) :
    FreeGroup.lift f (FreeGroup.mk (Ω.segment i₁ j₁ s₁)) =
        FreeGroup.lift f (FreeGroup.mk (Ω.segment i₂ j₂ s₂)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.segment i₁ j₁ true)) =
        (FreeGroup.lift f (FreeGroup.mk (Ω.segment i₂ j₂ true)))⁻¹ := by
  cases s₁ <;> cases s₂ <;> simp only [ne_eq, not_true_eq_false] at hs
  · rw [Ω.lift_mk_segment f i₁ j₁ false, Ω.lift_mk_segment f i₂ j₂ true]
    dsimp only [cond]
    rw [← inv_inj, inv_inv]
  · rw [Ω.lift_mk_segment f i₁ j₁ true, Ω.lift_mk_segment f i₂ j₂ false]
    rfl

private theorem lift_boundaryEquation_of_sign_eq {H : Type*} [Group H] {f : Fin Ω.numItems ⊕ A → H}
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (hs : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1)) :
    (FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left c.2.1) c.1 true)) =
        FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual c.2.1)) c.2.2 true)) := by
  rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_eq hs]

private theorem lift_boundaryEquation_of_sign_ne {H : Type*} [Group H] {f : Fin Ω.numItems ⊕ A → H}
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (hs : Ω.sign c.2.1 ≠ Ω.sign (Ω.dual c.2.1)) :
    (FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left c.2.1) c.1 true)) =
        (FreeGroup.lift f (FreeGroup.mk (Ω.segment c.2.2 (Ω.right (Ω.dual c.2.1)) true)))⁻¹ := by
  rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_ne hs,
    Ω.lift_mk_segment f c.2.2 (Ω.right (Ω.dual c.2.1)) false]
  rfl

/-- Every point of `Ω*` in an `F(A)`-group is a point of `(Ω.cutBase p μ q hc)*`. This forward
inclusion requires no formal-consistency hypothesis on `Ω`. -/
theorem V_toSystem_subset_cutBase {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    V ι Ω.toSystem ⊆ V ι (Ω.cutBase p μ q hc).toSystem := by
  intro v hv
  rw [mem_V_toSystem_iff] at hv ⊢
  set f : Fin Ω.numItems ⊕ A → H := Sum.elim v (ι ∘ FreeGroup.of)
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂ hq₁ hq₂
  have hbasic_μ := hv _ (Ω.basicEquation_mem_equations μ)
  have hconn_p := hv _ (Ω.boundaryEquation_mem_equations hc)
  have hpiece0 : FreeGroup.lift f
      (FreeGroup.mk ((Ω.cutBase p μ q hc).basicEquation (Ω.cutPiece μ 0)).1) =
      FreeGroup.lift f
        (FreeGroup.mk ((Ω.cutBase p μ q hc).basicEquation (Ω.cutPiece μ 0)).2) := by
    simp only [basicEquation_fst, basicEquation_snd, segment_cutBase, cutLeft_cutPiece_zero,
      cutRight_cutPiece_zero, cutDual_cutPiece_zero, cutLeft_cutPiece_two, cutRight_cutPiece_two,
      cutOrigBase_cutPiece_zero, cutOrigBase_cutPiece_two]
    by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
    · simp only [hs, ↓reduceIte, lift_mk_segment_eq_of_sign_eq rfl]
      exact (lift_boundaryEquation_of_sign_eq (c := (p, μ, q)) hs).1 hconn_p
    · simp only [hs, ↓reduceIte]
      rw [lift_mk_segment_eq_of_sign_ne hs]
      exact (lift_boundaryEquation_of_sign_ne (c := (p, μ, q)) hs).1 hconn_p
  have hpiece1 : FreeGroup.lift f
      (FreeGroup.mk ((Ω.cutBase p μ q hc).basicEquation (Ω.cutPiece μ 1)).1) =
      FreeGroup.lift f
        (FreeGroup.mk ((Ω.cutBase p μ q hc).basicEquation (Ω.cutPiece μ 1)).2) := by
    simp only [basicEquation_fst, basicEquation_snd, segment_cutBase, cutLeft_cutPiece_one,
      cutRight_cutPiece_one, cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three,
      cutOrigBase_cutPiece_one, cutOrigBase_cutPiece_three]
    by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
    · simp only [hs, ↓reduceIte, lift_mk_segment_eq_of_sign_eq rfl]
      have hbas : FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true)) =
          FreeGroup.lift f
            (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)) := by
        rwa [basicEquation_fst, basicEquation_snd, lift_mk_segment_eq_of_sign_eq hs] at hbasic_μ
      have hc₀ := (lift_boundaryEquation_of_sign_eq (c := (p, μ, q)) hs).1 hconn_p
      dsimp only at hc₀
      rw [lift_mk_segment_mul f hp₁.le hp₂.le (Ω.right μ).is_le,
        lift_mk_segment_mul f hq₁.le hq₂.le (Ω.right (Ω.dual μ)).is_le, hc₀] at hbas
      exact mul_left_cancel hbas
    · simp only [hs, ↓reduceIte]
      rw [lift_mk_segment_eq_of_sign_ne hs]
      have hbas : FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true)) =
          (FreeGroup.lift f
            (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)))⁻¹ := by
        rwa [basicEquation_fst, basicEquation_snd, lift_mk_segment_eq_of_sign_ne hs] at hbasic_μ
      have hc₀ := (lift_boundaryEquation_of_sign_ne (c := (p, μ, q)) hs).1 hconn_p
      dsimp only at hc₀
      rw [lift_mk_segment_mul f hp₁.le hp₂.le (Ω.right μ).is_le,
        lift_mk_segment_mul f hq₁.le hq₂.le (Ω.right (Ω.dual μ)).is_le, mul_inv_rev, ← hc₀] at hbas
      exact mul_left_cancel hbas
  rw [forall_mem_equations]
  refine ⟨forall_cutBase.2 ⟨fun ν => ?_, ?_⟩, fun b hb => ?_, fun c' hc' => ?_⟩
  · rw [basicEquation_cutBase_cutSurv]
    exact hv _ (Ω.basicEquation_mem_equations _)
  · refine cutPiece_cases hpiece0 hpiece1 ?_ ?_
    · simpa [basicEquation_fst, basicEquation_snd] using hpiece0.symm
    · simpa [basicEquation_fst, basicEquation_snd] using hpiece1.symm
  · rw [coeffEquation_cutBase]
    exact hv _ (Ω.coeffEquation_mem_equations hb)
  · rcases c' with ⟨p', β, q'⟩
    revert hc'
    refine cutBase_cases (fun ν hc' => ?_) (fun i hc' => ?_) β
    · rw [boundaryEquation_cutBase_cutSurv]
      exact hv _ (Ω.boundaryEquation_mem_equations ((mem_connections_cutBase_cutSurv hc).1 hc'))
    · revert hc'
      refine cutPiece_cases ?_ ?_ ?_ ?_ i <;> intro hc'
      · obtain ⟨hc₀, -, -, -, -⟩ := (mem_connections_cutBase hc).1 hc'
        have hc₀' : (p', μ, q') ∈ Ω.connections := by simpa using hc₀
        have heq := hv _ (Ω.boundaryEquation_mem_equations hc₀')
        by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
        · rw [(Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_eq
            (c := (p', Ω.cutPiece μ 0, q')) (by simpa using hs)]
          simpa [hs] using (Ω.lift_boundaryEquation_of_sign_eq (c := (p', μ, q')) hs).1 heq
        · rw [(Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_ne
            (c := (p', Ω.cutPiece μ 0, q')) (by simpa using hs)]
          simpa [hs] using (Ω.lift_boundaryEquation_of_sign_ne (c := (p', μ, q')) hs).1 heq
      · obtain ⟨hc₀, hl₁, -, hl₂, hr₂⟩ := (mem_connections_cutBase hc).1 hc'
        have hc₀' : (p', μ, q') ∈ Ω.connections := by simpa using hc₀
        have heq := hv _ (Ω.boundaryEquation_mem_equations hc₀')
        have hp'_le : p ≤ p' := (by simpa using hl₁ : p < p').le
        by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
        · have hq'_le : q ≤ q' := (by simpa [hs] using hl₂ : q < q').le
          rw [(Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_eq
            (c := (p', Ω.cutPiece μ 1, q')) (by simpa using hs)]
          simp only [segment_cutBase, cutLeft_cutPiece_one, cutDual_cutPiece_one,
            cutLeft_cutPiece_three, hs, ↓reduceIte]
          have heq' := (Ω.lift_boundaryEquation_of_sign_eq (c := (p', μ, q')) hs).1 heq
          have hc₀_eq := (Ω.lift_boundaryEquation_of_sign_eq (c := (p, μ, q)) hs).1 hconn_p
          dsimp only at heq' hc₀_eq
          rw [lift_mk_segment_mul f hp₁.le hp'_le p'.is_le,
            lift_mk_segment_mul f hq₁.le hq'_le q'.is_le, hc₀_eq] at heq'
          exact mul_left_cancel heq'
        · have hq'_le : q' ≤ q := (by simpa [hs] using hr₂ : q' < q).le
          rw [(Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_ne
            (c := (p', Ω.cutPiece μ 1, q')) (by simpa using hs)]
          simp only [segment_cutBase, cutLeft_cutPiece_one, cutDual_cutPiece_one,
            cutRight_cutPiece_three, hs, ↓reduceIte]
          have heq' := (Ω.lift_boundaryEquation_of_sign_ne (c := (p', μ, q')) hs).1 heq
          have hc₀_eq := (Ω.lift_boundaryEquation_of_sign_ne (c := (p, μ, q)) hs).1 hconn_p
          dsimp only at heq' hc₀_eq
          rw [lift_mk_segment_mul f hp₁.le hp'_le p'.is_le,
            lift_mk_segment_mul f hq'_le hq₂.le (Ω.right (Ω.dual μ)).is_le, mul_inv_rev,
            ← hc₀_eq] at heq'
          exact mul_left_cancel heq'
      · obtain ⟨hc₀, hl₁, -, -, hr₂⟩ := (mem_connections_cutBase hc).1 hc'
        have hc₀' : (p', Ω.dual μ, q') ∈ Ω.connections := by simpa using hc₀
        have heq := hv _ (Ω.boundaryEquation_mem_equations hc₀')
        by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
        · have hs' : Ω.sign (Ω.dual μ) = Ω.sign (Ω.dual (Ω.dual μ)) := by
            simpa [Ω.dual_involutive μ] using hs.symm
          rw [(Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_eq
            (c := (p', Ω.cutPiece μ 2, q')) (by simpa [eq_comm] using hs)]
          have heq' := (Ω.lift_boundaryEquation_of_sign_eq (c := (p', Ω.dual μ, q')) hs').1 heq
          simpa [hs, Ω.dual_involutive μ] using heq'
        · have hs' : Ω.sign (Ω.dual μ) ≠ Ω.sign (Ω.dual (Ω.dual μ)) := by
            simpa [Ω.dual_involutive μ, ne_comm] using hs
          have hconn_q := hv _ (Ω.boundaryEquation_mem_equations (Ω.dual_mem_connections _ hc))
          have hp'_le : q ≤ p' := (by simpa [hs] using hl₁ : q < p').le
          have hq'_le : q' ≤ p := (by simpa using hr₂ : q' < p).le
          rw [(Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_ne
            (c := (p', Ω.cutPiece μ 2, q')) (by simpa [ne_comm] using hs)]
          simp only [segment_cutBase, cutLeft_cutPiece_two, cutDual_cutPiece_two,
            cutRight_cutPiece_zero, hs, ↓reduceIte]
          have heq' := (Ω.lift_boundaryEquation_of_sign_ne (c := (p', Ω.dual μ, q')) hs').1 heq
          have hconn_q' :=
            (Ω.lift_boundaryEquation_of_sign_ne (c := (q, Ω.dual μ, p)) hs').1 hconn_q
          simp only [Ω.dual_involutive μ] at heq' hconn_q'
          rw [lift_mk_segment_mul f hq₁.le hp'_le p'.is_le,
            lift_mk_segment_mul f hq'_le hp₂.le (Ω.right μ).is_le, mul_inv_rev, ← hconn_q'] at heq'
          exact mul_left_cancel heq'
      · obtain ⟨hc₀, hl₁, -, hl₂, -⟩ := (mem_connections_cutBase hc).1 hc'
        have hc₀' : (p', Ω.dual μ, q') ∈ Ω.connections := by simpa using hc₀
        have heq := hv _ (Ω.boundaryEquation_mem_equations hc₀')
        by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
        · have hs' : Ω.sign (Ω.dual μ) = Ω.sign (Ω.dual (Ω.dual μ)) := by
            simpa [Ω.dual_involutive μ] using hs.symm
          have hconn_q := hv _ (Ω.boundaryEquation_mem_equations (Ω.dual_mem_connections _ hc))
          have hp'_le : q ≤ p' := (by simpa [hs] using hl₁ : q < p').le
          have hq'_le : p ≤ q' := (by simpa using hl₂ : p < q').le
          rw [(Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_eq
            (c := (p', Ω.cutPiece μ 3, q')) (by simpa [eq_comm] using hs)]
          simp only [segment_cutBase, cutLeft_cutPiece_three, cutDual_cutPiece_three,
            cutLeft_cutPiece_one, hs, ↓reduceIte]
          have heq' := (Ω.lift_boundaryEquation_of_sign_eq (c := (p', Ω.dual μ, q')) hs').1 heq
          have hconn_q' :=
            (Ω.lift_boundaryEquation_of_sign_eq (c := (q, Ω.dual μ, p)) hs').1 hconn_q
          simp only [Ω.dual_involutive μ] at heq' hconn_q'
          rw [lift_mk_segment_mul f hq₁.le hp'_le p'.is_le,
            lift_mk_segment_mul f hp₁.le hq'_le q'.is_le, hconn_q'] at heq'
          exact mul_left_cancel heq'
        · have hs' : Ω.sign (Ω.dual μ) ≠ Ω.sign (Ω.dual (Ω.dual μ)) := by
            simpa [Ω.dual_involutive μ, ne_comm] using hs
          rw [(Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_ne
            (c := (p', Ω.cutPiece μ 3, q')) (by simpa [ne_comm] using hs)]
          have heq' := (Ω.lift_boundaryEquation_of_sign_ne (c := (p', Ω.dual μ, q')) hs').1 heq
          simpa [hs, Ω.dual_involutive μ] using heq'

/-- **ET1 on group solutions.** In a formally consistent generalised equation, cutting `μ` at
`(p, μ, q)` preserves the set of group solutions in every `F(A)`-group. -/
theorem V_toSystem_cutBase (hΩ : Ω.IsFormallyConsistent) {H : Type*} [Group H]
    (ι : FreeGroup A →* H) :
    V ι (Ω.cutBase p μ q hc).toSystem = V ι Ω.toSystem := by
  refine Set.Subset.antisymm (fun v hv => ?_) (V_toSystem_subset_cutBase hc ι)
  rw [mem_V_toSystem_iff] at hv ⊢
  set f : Fin Ω.numItems ⊕ A → H := Sum.elim v (ι ∘ FreeGroup.of)
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂ hq₁ hq₂
  have hp0 := hv _ ((Ω.cutBase p μ q hc).basicEquation_mem_equations (Ω.cutPiece μ 0))
  have hp1 := hv _ ((Ω.cutBase p μ q hc).basicEquation_mem_equations (Ω.cutPiece μ 1))
  simp only [basicEquation_fst, basicEquation_snd, segment_cutBase, cutLeft_cutPiece_zero,
    cutRight_cutPiece_zero, cutDual_cutPiece_zero, cutLeft_cutPiece_two, cutRight_cutPiece_two,
    cutOrigBase_cutPiece_zero, cutOrigBase_cutPiece_two] at hp0
  simp only [basicEquation_fst, basicEquation_snd, segment_cutBase, cutLeft_cutPiece_one,
    cutRight_cutPiece_one, cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three,
    cutOrigBase_cutPiece_one, cutOrigBase_cutPiece_three] at hp1
  have hbasic_μ : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2) := by
    rw [basicEquation_fst, basicEquation_snd]
    by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
    · simp only [hs, ↓reduceIte, lift_mk_segment_eq_of_sign_eq rfl] at hp0 hp1
      rw [lift_mk_segment_eq_of_sign_eq hs,
        lift_mk_segment_mul f hp₁.le hp₂.le (Ω.right μ).is_le,
        lift_mk_segment_mul f hq₁.le hq₂.le (Ω.right (Ω.dual μ)).is_le, hp0, hp1]
    · simp only [hs, ↓reduceIte] at hp0 hp1
      rw [lift_mk_segment_eq_of_sign_ne hs] at hp0 hp1 ⊢
      rw [lift_mk_segment_mul f hp₁.le hp₂.le (Ω.right μ).is_le,
        lift_mk_segment_mul f hq₁.le hq₂.le (Ω.right (Ω.dual μ)).is_le, mul_inv_rev, hp0, hp1]
  have hconn_μ : ∀ {p' q' : Fin (Ω.numItems + 1)}, (p', μ, q') ∈ Ω.connections →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p', μ, q')).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p', μ, q')).2) := by
    intro p' q' hc₀
    rcases lt_trichotomy p' p with hlt | rfl | hgt
    · have hc' := (mem_connections_cutBase_of_lt hc hΩ hc₀ hlt).1
      have heq := hv _ ((Ω.cutBase p μ q hc).boundaryEquation_mem_equations hc')
      by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
      · rw [lift_boundaryEquation_of_sign_eq (c := (p', μ, q')) hs]
        have heq' := ((Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_eq
          (c := (p', Ω.cutPiece μ 0, q')) (by simpa using hs)).1 heq
        simpa [hs] using heq'
      · rw [lift_boundaryEquation_of_sign_ne (c := (p', μ, q')) hs]
        have heq' := ((Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_ne
          (c := (p', Ω.cutPiece μ 0, q')) (by simpa using hs)).1 heq
        simpa [hs] using heq'
    · obtain rfl : q' = q := hΩ.isTiedTo_unique (isTiedTo_of_mem_connections hc₀)
        (isTiedTo_of_mem_connections hc)
      by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
      · simp only [hs, ↓reduceIte, lift_mk_segment_eq_of_sign_eq rfl] at hp0
        exact (lift_boundaryEquation_of_sign_eq (c := (p', μ, q')) hs).2 hp0
      · simp only [hs, ↓reduceIte] at hp0
        rw [lift_mk_segment_eq_of_sign_ne hs] at hp0
        exact (lift_boundaryEquation_of_sign_ne (c := (p', μ, q')) hs).2 hp0
    · have hc' := (mem_connections_cutBase_of_gt hc hΩ hc₀ hgt).1
      have heq := hv _ ((Ω.cutBase p μ q hc).boundaryEquation_mem_equations hc')
      by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
      · have hq_lt : q < q' := hΩ.lt_of_isTiedTo_of_sign_eq hs (isTiedTo_of_mem_connections hc)
          (isTiedTo_of_mem_connections hc₀) hgt
        simp only [hs, ↓reduceIte, lift_mk_segment_eq_of_sign_eq rfl] at hp0
        have heq' := ((Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_eq
          (c := (p', Ω.cutPiece μ 1, q')) (by simpa using hs)).1 heq
        simp only [segment_cutBase, cutLeft_cutPiece_one, cutDual_cutPiece_one,
          cutLeft_cutPiece_three, hs, ↓reduceIte] at heq'
        rw [lift_boundaryEquation_of_sign_eq (c := (p', μ, q')) hs]
        dsimp only
        rw [lift_mk_segment_mul f hp₁.le hgt.le p'.is_le,
          lift_mk_segment_mul f hq₁.le hq_lt.le q'.is_le, hp0, heq']
      · have hq_lt : q' < q := hΩ.lt_of_isTiedTo_of_sign_ne hs (isTiedTo_of_mem_connections hc)
          (isTiedTo_of_mem_connections hc₀) hgt
        simp only [hs, ↓reduceIte] at hp0
        rw [lift_mk_segment_eq_of_sign_ne hs] at hp0
        have heq' := ((Ω.cutBase p μ q hc).lift_boundaryEquation_of_sign_ne
          (c := (p', Ω.cutPiece μ 1, q')) (by simpa using hs)).1 heq
        simp only [segment_cutBase, cutLeft_cutPiece_one, cutDual_cutPiece_one,
          cutRight_cutPiece_three, hs, ↓reduceIte] at heq'
        rw [lift_boundaryEquation_of_sign_ne (c := (p', μ, q')) hs]
        dsimp only
        rw [lift_mk_segment_mul f hp₁.le hgt.le p'.is_le,
          lift_mk_segment_mul f hq_lt.le hq₂.le (Ω.right (Ω.dual μ)).is_le, mul_inv_rev, ← hp0,
          ← heq']
  rw [forall_mem_equations]
  refine ⟨fun ν => ?_, fun b hb => ?_, fun c₀ hc₀ => ?_⟩
  · by_cases hmem : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))
    · rcases Finset.mem_insert.1 hmem with rfl | hmem
      · exact hbasic_μ
      · rw [Finset.mem_singleton.1 hmem]
        simpa [basicEquation_fst, basicEquation_snd, Ω.dual_involutive μ] using hbasic_μ.symm
    · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
      rw [← basicEquation_cutBase_cutSurv hc]
      exact hv _ ((Ω.cutBase p μ q hc).basicEquation_mem_equations _)
  · rw [← coeffEquation_cutBase hc]
    exact hv _ ((Ω.cutBase p μ q hc).coeffEquation_mem_equations hb)
  · rcases c₀ with ⟨p', ν, q'⟩
    by_cases hmem : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))
    · rcases Finset.mem_insert.1 hmem with rfl | hmem
      · exact hconn_μ hc₀
      · rw [Finset.mem_singleton.1 hmem] at hc₀ ⊢
        have hc₀_dual : (q', μ, p') ∈ Ω.connections := by
          simpa [Ω.dual_involutive μ] using Ω.dual_mem_connections _ hc₀
        have heq_dual := hconn_μ hc₀_dual
        obtain ⟨hp'₁, hp'₂, hq'₁, hq'₂⟩ := Ω.bounds_of_mem_connections (q', μ, p') hc₀_dual
        dsimp only at hp'₁ hp'₂ hq'₁ hq'₂
        by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
        · have hs' : Ω.sign (Ω.dual μ) = Ω.sign (Ω.dual (Ω.dual μ)) := by
            simpa [Ω.dual_involutive μ] using hs.symm
          rw [lift_boundaryEquation_of_sign_eq (c := (p', Ω.dual μ, q')) hs']
          have heq' := (lift_boundaryEquation_of_sign_eq (c := (q', μ, p')) hs).1 heq_dual
          simpa [Ω.dual_involutive μ] using heq'.symm
        · have hs' : Ω.sign (Ω.dual μ) ≠ Ω.sign (Ω.dual (Ω.dual μ)) := by
            simpa [Ω.dual_involutive μ, ne_comm] using hs
          have hbas : FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true)) =
              (FreeGroup.lift f
                (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)))⁻¹ := by
            rwa [basicEquation_fst, basicEquation_snd, lift_mk_segment_eq_of_sign_ne hs] at hbasic_μ
          have heq' := (lift_boundaryEquation_of_sign_ne (c := (q', μ, p')) hs).1 heq_dual
          dsimp only at heq'
          rw [lift_boundaryEquation_of_sign_ne (c := (p', Ω.dual μ, q')) hs']
          simp only [Ω.dual_involutive μ]
          rw [lift_mk_segment_mul f hp'₁.le hp'₂.le (Ω.right μ).is_le,
            lift_mk_segment_mul f hq'₁.le hq'₂.le (Ω.right (Ω.dual μ)).is_le, mul_inv_rev,
            ← heq'] at hbas
          rw [← inv_inj, inv_inv]
          exact (mul_left_cancel hbas).symm
    · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
      rw [← boundaryEquation_cutBase_cutSurv hc]
      exact hv _ ((Ω.cutBase p μ q hc).boundaryEquation_mem_equations
        ((mem_connections_cutBase_cutSurv hc).2 hc₀))

/-- **ET1 on coordinate groups.** The `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` induced by the
identity on the items, where `Ω` is formally consistent and `Ω′ = Ω.cutBase p μ q hc`. -/
def cutBaseHom (hΩ : Ω.IsFormallyConsistent) :
    GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
      (CoordGroup.coeff (.id (FreeGroup A)) (Ω.cutBase p μ q hc).toSystem) :=
  CoordGroup.homOfVSubset (V_toSystem_cutBase hc hΩ _).le

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of ET1 is the identity on the words in the items. -/
-- Not `@[simp]`: the reducible `cutBase` in the codomain keeps `simp` from indexing this lemma
-- uninstantiated, so it is used through `rw`.
theorem cutBaseHom_mk (hΩ : Ω.IsFormallyConsistent) (w : GX (FreeGroup A) (Fin Ω.numItems)) :
    cutBaseHom hc hΩ (w : Ω.coordGroup) = (w : (Ω.cutBase p μ q hc).coordGroup) :=
  CoordGroup.homOfVSubset_mk _ w

/-- The coordinate-group homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of ET1 is surjective. -/
theorem cutBaseHom_surjective (hΩ : Ω.IsFormallyConsistent) :
    Function.Surjective (cutBaseHom hc hΩ) :=
  CoordGroup.homOfVSubset_surjective _

/-- **ET1 on coordinate groups.** When `Ω` is formally consistent, the identity on the items induces
an `F(A)`-isomorphism between the coordinate groups of `Ω` and `Ω.cutBase p μ q hc`. -/
theorem cutBaseHom_bijective (hΩ : Ω.IsFormallyConsistent) :
    Function.Bijective (cutBaseHom hc hΩ) :=
  ⟨CoordGroup.homOfVSubset_injective _ (V_toSystem_cutBase hc hΩ _).ge,
    cutBaseHom_surjective hc hΩ⟩

end GroupSolutions

/-! ### Graphical solutions -/

section GraphicalSolutions

variable {A : Type*} {Ω : GenEq A} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)} (hc : (p, μ, q) ∈ Ω.connections)

namespace Solution

/-- Every graphical solution `U` of `Ω` transfers to a graphical solution of `Ω.cutBase p μ q hc`
with the same item words: each new piece is a subsegment of `μ` or `Δ(μ)`, so its word in `U` is a
subword of a reduced word and therefore reduced as written. -/
def cutBase (U : Ω.Solution) : (Ω.cutBase p μ q hc).Solution :=
  Solution.ofMemV U.word U.isReduced_word U.word_ne_nil
    ((forall_mem_equations _).2
      ⟨fun β => by
        rw [basicEquation_fst, basicEquation_snd, segment_cutBase, segment_cutBase]
        exact ⟨(Ω.isReduced_substituteVars_segment_iff U.word _ _ _).2
            (U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ β)
              (left_cutOrigBase_le hc β) (cutRight_le_right_cutOrigBase hc β)),
          (Ω.isReduced_substituteVars_segment_iff U.word _ _ _).2
            (U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ (Ω.cutDual μ β))
              (left_cutOrigBase_le hc _) (cutRight_le_right_cutOrigBase hc _))⟩,
      fun b hb => by
        rw [coeffEquation_cutBase]
        exact U.isReduced_subst _ (Ω.coeffEquation_mem_equations hb),
      fun ⟨p', β, q'⟩ hc' => by
        obtain ⟨-, hl₁, hr₁, hl₂, hr₂⟩ := (mem_connections_cutBase hc).1 hc'
        dsimp only at hl₁ hr₁ hl₂ hr₂
        refine ⟨?_, ?_⟩
        · rw [boundaryEquation_fst, segment_cutBase]
          exact U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ β)
            (left_cutOrigBase_le hc β) (hr₁.le.trans (cutRight_le_right_cutOrigBase hc β))
        · by_cases hs : (Ω.cutBase p μ q hc).sign β =
              (Ω.cutBase p μ q hc).sign ((Ω.cutBase p μ q hc).dual β)
          · rw [(Ω.cutBase p μ q hc).boundaryEquation_snd_of_sign_eq hs, segment_cutBase]
            exact U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ (Ω.cutDual μ β))
              (left_cutOrigBase_le hc _) (hr₂.le.trans (cutRight_le_right_cutOrigBase hc _))
          · rw [(Ω.cutBase p μ q hc).boundaryEquation_snd_of_sign_ne hs, segment_cutBase,
              Ω.isReduced_substituteVars_segment_iff]
            exact U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ (Ω.cutDual μ β))
              ((left_cutOrigBase_le hc _).trans hl₂.le) (cutRight_le_right_cutOrigBase hc _)⟩)
    (funext U.point_apply ▸ V_toSystem_subset_cutBase hc _ U.point_mem_V)

/-- `Solution.cutBase` preserves the words of the items. -/
@[simp]
theorem cutBase_word (U : Ω.Solution) : (U.cutBase hc).word = U.word :=
  Solution.ofMemV_word ..

/-- `Solution.cutBase` preserves the point of a solution in `F(A)^ρ`. -/
@[simp]
theorem cutBase_point (U : Ω.Solution) : (U.cutBase hc).point = U.point := by
  ext
  simp

/-- `Solution.cutBase` preserves the prefix lengths of all boundaries. -/
@[simp]
theorem cutBase_prefixLength (U : Ω.Solution) : (U.cutBase hc).prefixLength = U.prefixLength := by
  ext
  simp [prefixLength_def]

/-- `Solution.cutBase` preserves alphabet constraints on the items. -/
@[simp]
theorem isConstrained_cutBase_iff (U : Ω.Solution) (D : Fin Ω.numItems → Set A) :
    (U.cutBase hc).IsConstrained D ↔ U.IsConstrained D := by
  simp [isConstrained_iff]

/-- In `U.cutBase hc`, the words of the two pieces `cutPiece μ 0` and `cutPiece μ 1` concatenate
without cancellation to the word of `μ` in `U`. -/
theorem substituteVars_cutPiece_zero_append_one (U : Ω.Solution) :
    substituteVars (U.cutBase hc).word
        ((Ω.cutBase p μ q hc).segment ((Ω.cutBase p μ q hc).left (Ω.cutPiece μ 0))
          ((Ω.cutBase p μ q hc).right (Ω.cutPiece μ 0)) true) ++
      substituteVars (U.cutBase hc).word
        ((Ω.cutBase p μ q hc).segment ((Ω.cutBase p μ q hc).left (Ω.cutPiece μ 1))
          ((Ω.cutBase p μ q hc).right (Ω.cutPiece μ 1)) true) =
      substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) := by
  obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂
  simp only [cutBase_word, segment_cutBase, cutLeft_cutPiece_zero, cutRight_cutPiece_zero,
    cutLeft_cutPiece_one, cutRight_cutPiece_one, ← substituteVars_append]
  rw [Ω.segment_append hp₁.le hp₂.le (Ω.right μ).is_le]

end Solution

/-- If `Ω` admits a graphical solution, `Ω.cutBase p μ q hc` is formally consistent;
contrapositively, if cutting a base breaks formal consistency, `Ω` has no graphical solution. -/
theorem isFormallyConsistent_cutBase_of_nonempty_solution (hne : Nonempty Ω.Solution) :
    (Ω.cutBase p μ q hc).IsFormallyConsistent :=
  let ⟨U⟩ := hne
  (U.cutBase hc).isFormallyConsistent

/-- The homomorphism `F_{R(Ω′)} → F(A)` of `U.cutBase hc` composed with `cutBaseHom` is
`U.toHom`. -/
theorem toHom_comp_cutBaseHom (hΩ : Ω.IsFormallyConsistent) (U : Ω.Solution) :
    (U.cutBase hc).toHom.comp (cutBaseHom hc hΩ) = U.toHom := by
  ext k
  rw [GHom.coe_comp, Function.comp_apply, cutBaseHom_mk]
  simp

/-- **ET1 transfers solutions uniquely.** For any solution `U` of a formally consistent `Ω`,
`U.cutBase hc` is the unique solution of `Ω.cutBase p μ q hc` whose homomorphism factors `U.toHom`
through `cutBaseHom`. -/
theorem toHom_comp_cutBaseHom_eq_iff (hΩ : Ω.IsFormallyConsistent) (U : Ω.Solution)
    (U' : (Ω.cutBase p μ q hc).Solution) :
    U'.toHom.comp (cutBaseHom hc hΩ) = U.toHom ↔ U' = U.cutBase hc := by
  refine ⟨fun h => Solution.point_injective (funext fun k => ?_), ?_⟩
  · have h' := DFunLike.congr_fun h ((inr (FreeGroup.of k) : GX (FreeGroup A) _) : Ω.coordGroup)
    rw [GHom.coe_comp, Function.comp_apply, cutBaseHom_mk, Solution.toHom_inr_of,
      Solution.toHom_inr_of] at h'
    simpa using h'
  · rintro rfl
    exact toHom_comp_cutBaseHom hc hΩ U

/-- For any solution `U′` of `Ω.cutBase p μ q hc`, the word `U′[α(Δμ), β(Δμ)]` of the dual base is
reduced as written if and only if the word `U′[α(μ), β(μ)]` of `μ` is reduced as written: the two
words are either identical (when `ε(μ) = ε(Δμ)`) or formal inverses of one another (when
`ε(μ) ≠ ε(Δμ)`). -/
theorem isReduced_substituteVars_dual_iff_of_cutBase (U' : (Ω.cutBase p μ q hc).Solution) :
    FreeGroup.IsReduced
        (substituteVars U'.word (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)) ↔
      FreeGroup.IsReduced
        (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true)) := by
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂ hq₁ hq₂
  rw [← Ω.segment_append hp₁.le hp₂.le (Ω.right μ).is_le,
    ← Ω.segment_append hq₁.le hq₂.le (Ω.right (Ω.dual μ)).is_le,
    substituteVars_append, substituteVars_append]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · have heq₀ := U'.substituteVars_segment_eq_of_sign_eq (μ := Ω.cutPiece μ 0) (by simpa using hs)
    have heq₁ := U'.substituteVars_segment_eq_of_sign_eq (μ := Ω.cutPiece μ 1) (by simpa using hs)
    simp only [segment_cutBase, cutLeft_cutPiece_zero, cutRight_cutPiece_zero,
      cutDual_cutPiece_zero, cutLeft_cutPiece_two, cutRight_cutPiece_two, cutLeft_cutPiece_one,
      cutRight_cutPiece_one, cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three,
      hs, ↓reduceIte] at heq₀ heq₁
    rw [heq₀, heq₁]
  · have heq₀ := U'.substituteVars_segment_eq_invRev_of_sign_ne (μ := Ω.cutPiece μ 0)
      (by simpa using hs)
    have heq₁ := U'.substituteVars_segment_eq_invRev_of_sign_ne (μ := Ω.cutPiece μ 1)
      (by simpa using hs)
    simp only [segment_cutBase, cutLeft_cutPiece_zero, cutRight_cutPiece_zero,
      cutDual_cutPiece_zero, cutLeft_cutPiece_two, cutRight_cutPiece_two, cutLeft_cutPiece_one,
      cutRight_cutPiece_one, cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three,
      hs, ↓reduceIte] at heq₀ heq₁
    rw [heq₀, heq₁, ← FreeGroup.invRev_append, FreeGroup.isReduced_invRev]

private theorem isReduced_subst_of_cutBase (U' : (Ω.cutBase p μ q hc).Solution)
    (hred : FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true))) :
    ∀ e ∈ Ω.equations, FreeGroup.IsReduced (substituteVars U'.word e.1) ∧
      FreeGroup.IsReduced (substituteVars U'.word e.2) := by
  have hbase : ∀ ν : Fin Ω.numBases,
      FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left ν) (Ω.right ν) true)) := by
    intro ν
    by_cases hmem : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))
    · rcases Finset.mem_insert.1 hmem with rfl | hmem
      · exact hred
      · rw [Finset.mem_singleton.1 hmem]
        exact (isReduced_substituteVars_dual_iff_of_cutBase hc U').2 hred
    · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
      simpa using U'.isReduced_substituteVars_segment (Ω.cutSurv μ ν₀)
  have hsub : ∀ (ν : Fin Ω.numBases) {i j : ℕ}, Ω.left ν ≤ i → j ≤ Ω.right ν → ∀ s : Bool,
      FreeGroup.IsReduced (substituteVars U'.word (Ω.segment i j s)) := by
    intro ν i j hi hj s
    rw [Ω.isReduced_substituteVars_segment_iff]
    rcases le_total i j with hij | hji
    · have h := hbase ν
      rw [← Ω.segment_append hi (hij.trans hj) (Ω.right ν).is_le,
        ← Ω.segment_append hij hj (Ω.right ν).is_le, substituteVars_append,
        substituteVars_append, ← List.append_assoc] at h
      exact h.infix (List.infix_append _ _ _)
    · rw [Ω.segment_eq_nil_of_le hji, FreeGroup.substituteVars_nil]
      exact FreeGroup.IsReduced.nil
  refine (forall_mem_equations _).2 ⟨fun ν => ?_, fun b hb => ?_, fun c₀ hc₀ => ?_⟩
  · rw [basicEquation_fst, basicEquation_snd]
    exact ⟨hsub ν le_rfl le_rfl _, hsub (Ω.dual ν) le_rfl le_rfl _⟩
  · rw [← coeffEquation_cutBase hc]
    exact U'.isReduced_subst _ ((Ω.cutBase p μ q hc).coeffEquation_mem_equations hb)
  · obtain ⟨-, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections c₀ hc₀
    refine ⟨?_, ?_⟩
    · rw [boundaryEquation_fst]
      exact hsub c₀.2.1 le_rfl h₂.le _
    · by_cases hs : Ω.sign c₀.2.1 = Ω.sign (Ω.dual c₀.2.1)
      · rw [Ω.boundaryEquation_snd_of_sign_eq hs]
        exact hsub (Ω.dual c₀.2.1) le_rfl h₄.le _
      · rw [Ω.boundaryEquation_snd_of_sign_ne hs]
        exact hsub (Ω.dual c₀.2.1) h₃.le le_rfl _

/-- **ET1 on graphical solutions.** When `Ω` is formally consistent, the graphical solutions of `Ω`
are in bijection with those graphical solutions of `Ω.cutBase p μ q hc` for which the word
`U′[α(μ), β(μ)]` is reduced as written. The words of the items are unchanged. -/
def solutionEquivCutBase (hΩ : Ω.IsFormallyConsistent) :
    Ω.Solution ≃ {U' : (Ω.cutBase p μ q hc).Solution //
      FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true))} where
  toFun U := ⟨U.cutBase hc, by
    rw [Solution.cutBase_word]
    exact U.isReduced_substituteVars_segment μ⟩
  invFun U' := Solution.ofMemV U'.1.word U'.1.isReduced_word U'.1.word_ne_nil
    (isReduced_subst_of_cutBase hc U'.1 U'.2)
    (funext U'.1.point_apply ▸ (V_toSystem_cutBase hc hΩ _).le U'.1.point_mem_V)
  left_inv U := Solution.ext ((Solution.ofMemV_word ..).trans (U.cutBase_word hc))
  right_inv U' := Subtype.ext (Solution.ext (by simp))

/-- `solutionEquivCutBase` sends `U` to `U.cutBase hc`. -/
@[simp]
theorem solutionEquivCutBase_apply_coe (hΩ : Ω.IsFormallyConsistent) (U : Ω.Solution) :
    (solutionEquivCutBase hc hΩ U : (Ω.cutBase p μ q hc).Solution) = U.cutBase hc :=
  (rfl)

section EquivSymm

variable (hΩ : Ω.IsFormallyConsistent)
  (U' : {U' : (Ω.cutBase p μ q hc).Solution //
    FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true))})

/-- The inverse of `solutionEquivCutBase` preserves the words of the items. -/
@[simp]
theorem solutionEquivCutBase_symm_apply_word :
    ((solutionEquivCutBase hc hΩ).symm U').word = U'.1.word :=
  Solution.ofMemV_word ..

/-- The inverse of `solutionEquivCutBase` preserves the point of a solution. -/
@[simp]
theorem solutionEquivCutBase_symm_apply_point :
    ((solutionEquivCutBase hc hΩ).symm U').point = U'.1.point := by
  ext
  simp

/-- The inverse of `solutionEquivCutBase` preserves the prefix lengths of all boundaries. -/
@[simp]
theorem solutionEquivCutBase_symm_apply_prefixLength :
    ((solutionEquivCutBase hc hΩ).symm U').prefixLength = U'.1.prefixLength := by
  ext
  simp [Solution.prefixLength_def]

/-- The homomorphism `F_{R(Ω)} → F(A)` of `(solutionEquivCutBase hc hΩ).symm U′` is `U′.1.toHom`
composed with `cutBaseHom`. -/
theorem solutionEquivCutBase_symm_apply_toHom :
    ((solutionEquivCutBase hc hΩ).symm U').toHom = U'.1.toHom.comp (cutBaseHom hc hΩ) := by
  conv_rhs => rw [← (solutionEquivCutBase hc hΩ).apply_symm_apply U']
  exact (toHom_comp_cutBaseHom hc hΩ _).symm

end EquivSymm

private theorem isReduced_append_of_overlap {u₁ u₂ v₁ v₂ : List (A × Bool)}
    (hu : FreeGroup.IsReduced (u₁ ++ u₂)) (hv : FreeGroup.IsReduced (v₁ ++ v₂))
    (hmid : FreeGroup.IsReduced (u₂ ++ v₁)) (hu₂ : u₂ ≠ []) (hv₁ : v₁ ≠ []) :
    FreeGroup.IsReduced ((u₁ ++ u₂) ++ (v₁ ++ v₂)) := by
  refine List.isChain_append.2 ⟨hu, hv, fun x hx y hy => ?_⟩
  rw [List.getLast?_append_of_ne_nil _ hu₂] at hx
  rw [List.head?_append_of_ne_nil _ hv₁] at hy
  exact (List.isChain_append.1 hmid).2.2 x hx y hy

/-- If the cut boundary `p` remains open in `Ω.cutBase p μ q hc`, another variable base crosses `p`
and forces the junction between `U′.word (p - 1)` and `U′.word p` to be reduced, so
`U′[α(μ), β(μ)]` is automatically reduced as written for every solution `U′` of `Ω.cutBase`. -/
theorem isReduced_cutBase_of_isOpenBoundary
    (hp : (Ω.cutBase p μ q hc).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc).Solution) :
    FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true)) := by
  obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂
  obtain ⟨β, hβ⟩ := ((Ω.cutBase p μ q hc).isOpenBoundary_iff).1 hp
  obtain ⟨hβ₁, hβ₂⟩ := ((Ω.cutBase p μ q hc).crosses_iff).1 hβ
  have hp_pos : 0 < (p : ℕ) := Nat.lt_of_le_of_lt (Nat.zero_le _) (Fin.lt_def.1 hp₁)
  have hp_lt : (p : ℕ) < Ω.numItems :=
    Nat.lt_of_lt_of_le (Fin.lt_def.1 hp₂) (Nat.le_of_lt_succ (Ω.right μ).isLt)
  let k₀ : Fin Ω.numItems := ⟨(p : ℕ) - 1, by omega⟩
  let k₁ : Fin Ω.numItems := ⟨p, hp_lt⟩
  have hk₀_val : (k₀ : ℕ) = (p : ℕ) - 1 := rfl
  have hk₁_val : (k₁ : ℕ) = p := rfl
  have hk₀_eq : (k₀ : ℕ) + 1 = p := by omega
  have hleft_le : (Ω.left μ : ℕ) ≤ k₀ := by
    have := Fin.lt_def.1 hp₁; omega
  have hright_ge : (k₁ : ℕ) + 1 ≤ Ω.right μ := by
    have := Fin.lt_def.1 hp₂; omega
  have hβ_left : ((Ω.cutBase p μ q hc).left β : ℕ) ≤ k₀ := by
    have := Fin.lt_def.1 hβ₁; omega
  have hβ_right : (k₁ : ℕ) + 1 ≤ (Ω.cutBase p μ q hc).right β := by
    have := Fin.lt_def.1 hβ₂; omega
  have hred₀ : FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left μ) p true)) := by
    simpa using U'.isReduced_substituteVars_segment (Ω.cutPiece μ 0)
  have hred₁ : FreeGroup.IsReduced (substituteVars U'.word (Ω.segment p (Ω.right μ) true)) := by
    simpa using U'.isReduced_substituteVars_segment (Ω.cutPiece μ 1)
  have hred_mid : FreeGroup.IsReduced
      (substituteVars U'.word (Ω.segment k₀ ((k₁ : ℕ) + 1) true)) := by
    simpa using U'.isReduced_substituteVars_segment_of_le β hβ_left hβ_right
  have hseg₀ : Ω.segment (Ω.left μ) p true =
      Ω.segment (Ω.left μ) k₀ true ++ Ω.segment k₀ ((k₀ : ℕ) + 1) true := by
    conv_lhs => rw [← hk₀_eq]
    exact (Ω.segment_append hleft_le (Nat.le_succ _) (by omega)).symm
  have hseg₁ : Ω.segment p (Ω.right μ) true =
      Ω.segment k₁ ((k₁ : ℕ) + 1) true ++ Ω.segment ((k₁ : ℕ) + 1) (Ω.right μ) true :=
    (Ω.segment_append (Nat.le_succ _) hright_ge (Ω.right μ).is_le).symm
  have hseg_mid : Ω.segment k₀ ((k₁ : ℕ) + 1) true =
      Ω.segment k₀ ((k₀ : ℕ) + 1) true ++ Ω.segment k₁ ((k₁ : ℕ) + 1) true := by
    have hk₀₁ : (k₀ : ℕ) + 1 = k₁ := by omega
    conv_lhs => rw [← Ω.segment_append (i := k₀) (j := (k₀ : ℕ) + 1) (k := (k₁ : ℕ) + 1)
      (Nat.le_succ _) (by omega) (by omega)]
    rw [hk₀₁]
  rw [← Ω.segment_append hp₁.le hp₂.le (Ω.right μ).is_le, hseg₀, hseg₁,
    substituteVars_append, substituteVars_append, substituteVars_append]
  rw [hseg₀, substituteVars_append] at hred₀
  rw [hseg₁, substituteVars_append] at hred₁
  rw [hseg_mid, substituteVars_append] at hred_mid
  exact isReduced_append_of_overlap hred₀ hred₁ hred_mid
    (by simp [segment_succ, U'.word_ne_nil k₀]) (by simp [segment_succ, U'.word_ne_nil k₁])

/-- **ET1 when the cut boundary stays open.** If `Ω` is formally consistent and `p` remains an open
boundary in `Ω.cutBase p μ q hc`, graphical solutions of `Ω` and of `Ω.cutBase p μ q hc` are in
unconditional bijection with the same item words. -/
def solutionEquivCutBaseOfOpen (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc).IsOpenBoundary p) :
    Ω.Solution ≃ (Ω.cutBase p μ q hc).Solution :=
  (solutionEquivCutBase hc hΩ).trans
    (Equiv.subtypeUnivEquiv (isReduced_cutBase_of_isOpenBoundary hc hp))

@[simp]
theorem solutionEquivCutBaseOfOpen_apply (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc).IsOpenBoundary p) (U : Ω.Solution) :
    solutionEquivCutBaseOfOpen hc hΩ hp U = U.cutBase hc :=
  (rfl)

@[simp]
theorem solutionEquivCutBaseOfOpen_symm_apply_word (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc).Solution) :
    ((solutionEquivCutBaseOfOpen hc hΩ hp).symm U').word = U'.word :=
  Solution.ofMemV_word ..

@[simp]
theorem solutionEquivCutBaseOfOpen_symm_apply_point (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc).Solution) :
    ((solutionEquivCutBaseOfOpen hc hΩ hp).symm U').point = U'.point := by
  ext
  simp

@[simp]
theorem solutionEquivCutBaseOfOpen_symm_apply_prefixLength (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc).Solution) :
    ((solutionEquivCutBaseOfOpen hc hΩ hp).symm U').prefixLength = U'.prefixLength := by
  ext
  simp [Solution.prefixLength_def]

theorem solutionEquivCutBaseOfOpen_symm_apply_toHom (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc).Solution) :
    ((solutionEquivCutBaseOfOpen hc hΩ hp).symm U').toHom = U'.toHom.comp (cutBaseHom hc hΩ) :=
  solutionEquivCutBase_symm_apply_toHom hc hΩ ⟨U', isReduced_cutBase_of_isOpenBoundary hc hp U'⟩

end GraphicalSolutions

/-! ### Packaging ET1 as a `Transformation` -/

section Transformation

variable {A : Type*} {Ω : GenEq A} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)} (hc : (p, μ, q) ∈ Ω.connections) (hΩ : Ω.IsFormallyConsistent)

/-- **ET1 as a `Transformation`.** The transformation of a formally consistent `Ω` determined by
cutting `μ` at `(p, μ, q)`: its family of successors consists of `Ω.cutBase p μ q hc` whenever that
cut is formally consistent (and is empty otherwise, in which case `Ω` has no graphical solution by
`isFormallyConsistent_cutBase_of_nonempty_solution`). -/
@[expose] def cutBaseTransformation : Transformation Ω :=
  Transformation.ofFamily (κ := Unit) (fun _ => Ω.cutBase p μ q hc) (fun _ => cutBaseHom hc hΩ)
    (fun _ => cutBaseHom_surjective hc hΩ) (fun U => ⟨(), U.cutBase hc⟩)
    (fun U => toHom_comp_cutBaseHom hc hΩ U)

@[simp]
theorem cutBaseTransformation_target (i : (cutBaseTransformation hc hΩ).ι) :
    (cutBaseTransformation hc hΩ).target i = Ω.cutBase p μ q hc :=
  (rfl)

@[simp]
theorem cutBaseTransformation_hom (i : (cutBaseTransformation hc hΩ).ι) :
    (cutBaseTransformation hc hΩ).hom i = cutBaseHom hc hΩ :=
  (rfl)

@[simp]
theorem cutBaseTransformation_transfer (U : Ω.Solution) :
    (cutBaseTransformation hc hΩ).transfer U =
      ⟨⟨(), (U.cutBase hc).isFormallyConsistent⟩, U.cutBase hc⟩ :=
  (rfl)

/-- `cutBaseTransformation hc hΩ` has a successor if and only if `Ω.cutBase p μ q hc` is formally
consistent. -/
theorem nonempty_cutBaseTransformation_iff :
    Nonempty (cutBaseTransformation hc hΩ).ι ↔ (Ω.cutBase p μ q hc).IsFormallyConsistent :=
  ⟨fun ⟨i⟩ => i.2, fun h => ⟨⟨(), h⟩⟩⟩

/-- **ET1 transfers solutions uniquely.** -/
theorem transfersUniquely_cutBaseTransformation :
    (cutBaseTransformation hc hΩ).TransfersUniquely := by
  have : Subsingleton (cutBaseTransformation hc hΩ).ι :=
    inferInstanceAs (Subsingleton { _x : Unit // (Ω.cutBase p μ q hc).IsFormallyConsistent })
  exact Transformation.transfersUniquely_of_subsingleton _

end Transformation

/-! ### Examples -/

section Examples

/-- The formally consistent generalised equation `h₀h₁ = h₂h₃` with connection `(1, μ, 3)`
(`h₀ = h₂`): after cutting `μ = [0, 2]` at `1`, the cut boundaries `1` and `3` become closed
(a *crease*). -/
private abbrev creaseExample : GenEq (Fin 2) where
  numItems := 4
  numBases := 2
  left := ![0, 2]
  right := ![2, 4]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 3), (3, 1, 1)}
  bounds_of_mem_connections := by decide
  dual_mem_connections := by decide

private theorem creaseExample_mem : (1, 0, 3) ∈ creaseExample.connections := by decide

private theorem creaseExample_isFormallyConsistent : creaseExample.IsFormallyConsistent := by
  decide

private theorem creaseExample_cutBase_connections :
    (creaseExample.cutBase 1 0 3 creaseExample_mem).connections = ∅ := by
  have hcard := card_connections_cutBase creaseExample_mem creaseExample_isFormallyConsistent
    (by decide)
  have h₂ : creaseExample.connections.card = 2 := by decide
  exact Finset.card_eq_zero.1 (by omega)

private def creaseWords : Fin 4 → List (Fin 2 × Bool) :=
  ![[(0, true)], [(0, false)], [(0, true)], [(0, false)]]

/-- The words `(a, a⁻¹, a, a⁻¹)` define a graphical solution of `creaseExample.cutBase 1 0 3 _`
(and hence a group solution in `V (.id _) creaseExample.toSystem`), yet `creaseExample` has no
graphical solution with those item words because `U[0, 2] = a a⁻¹` cancels across the closed
boundary `1`. This shows that the reducedness condition in `solutionEquivCutBase` cannot be dropped
when `p` becomes closed. -/
example :
    (∃ U' : (creaseExample.cutBase 1 0 3 creaseExample_mem).Solution, U'.word = creaseWords) ∧
      ¬ ∃ U : creaseExample.Solution, U.word = creaseWords := by
  refine ⟨?_, ?_⟩
  · have hsurv : creaseExample.cutSurvCard 0 = 0 := by decide
    refine ⟨⟨creaseWords, by unfold FreeGroup.IsReduced creaseWords; decide,
        by unfold creaseWords; decide, ?_, ?_⟩, rfl⟩
    · refine (forall_mem_equations _).2 ⟨forall_cutBase.2 ⟨fun ν => Fin.elim0 (hsurv ▸ ν), ?_⟩,
        fun _ hb => absurd hb (Finset.notMem_empty _),
        fun _ hc' => absurd (creaseExample_cutBase_connections ▸ hc') (Finset.notMem_empty _)⟩
      refine cutPiece_cases ?_ ?_ ?_ ?_ <;>
        · simp only [basicEquation_fst, basicEquation_snd, cutLeft_cutPiece_zero,
            cutRight_cutPiece_zero, cutDual_cutPiece_zero, cutLeft_cutPiece_two,
            cutRight_cutPiece_two, cutLeft_cutPiece_one, cutRight_cutPiece_one,
            cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three,
            cutDual_cutPiece_two, cutDual_cutPiece_three, ↓reduceIte, segment_true, Fin.isValue]
          unfold FreeGroup.IsReduced creaseWords
          decide
    · refine (forall_mem_equations _).2 ⟨forall_cutBase.2 ⟨fun ν => Fin.elim0 (hsurv ▸ ν), ?_⟩,
        fun _ hb => absurd hb (Finset.notMem_empty _),
        fun _ hc' => absurd (creaseExample_cutBase_connections ▸ hc') (Finset.notMem_empty _)⟩
      refine cutPiece_cases ?_ ?_ ?_ ?_ <;>
        · simp only [basicEquation_fst, basicEquation_snd, cutLeft_cutPiece_zero,
            cutRight_cutPiece_zero, cutDual_cutPiece_zero, cutLeft_cutPiece_two,
            cutRight_cutPiece_two, cutLeft_cutPiece_one, cutRight_cutPiece_one,
            cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three,
            cutDual_cutPiece_two, cutDual_cutPiece_three, ↓reduceIte, segment_true, Fin.isValue]
          unfold creaseWords
          decide
  · rintro ⟨U, hU⟩
    have hred := U.isReduced_substituteVars_segment 0
    rw [hU, segment_true] at hred
    revert hred
    unfold FreeGroup.IsReduced creaseWords
    decide

end Examples

end GenEq

end TauCeti
