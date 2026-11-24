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
`Ω′ = Ω.cutBase p μ q hc hμ` obtained by cutting a non-self-dual variable base `μ` (`μ ≠ Δ(μ)`) and
its dual `Δ(μ)` at a boundary connection `(p, μ, q)` (elementary transformation ET1 of Makanin's
process, Kharlampovich–Myasnikov, §5.1).

* **Group solutions and coordinate groups.** Every point of `Ω*` in an `F(A)`-group is a point of
  `Ω′*` (`TauCeti.GenEq.V_toSystem_subset_cutBase`) without any formal-consistency hypothesis. When
  `Ω` is formally consistent, `Ω*` and `Ω′*` have the exact same points
  (`TauCeti.GenEq.V_toSystem_cutBase`), and the identity on the items induces an
  `F(A)`-isomorphism `F_{R(Ω)} → F_{R(Ω′)}` of coordinate groups (`TauCeti.GenEq.cutBaseHom`,
  `TauCeti.GenEq.cutBaseHom_bijective`).
* **Graphical solutions.** Every graphical solution `U` of `Ω` transfers with the same item words to
  a graphical solution `U.cutBase hc hμ` of `Ω′` (`TauCeti.GenEq.Solution.cutBase`), and when `Ω` is
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
* `TauCeti.GenEq.cutBaseTransformation`, `TauCeti.GenEq.cutBaseTransformationIndex`: ET1 packaged
  as a `Transformation Ω` together with its successor-index constructor.

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

section Evaluation

variable {A : Type*} (Ω : GenEq A)

-- Not `@[simp]`: Mathlib's `FreeGroup.lift_mk` is `@[simp]` and simplifies `FreeGroup.lift f
-- (FreeGroup.mk _)`, so these evaluation lemmas are used through `rw` like `lift_mk_segment`.

/-- Two signed segments with equal signs have equal images under `FreeGroup.lift f` if and only if
their positive versions have equal images. -/
theorem lift_mk_segment_eq_iff_of_eq {H : Type*} [Group H] {f : Fin Ω.numItems ⊕ A → H}
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

/-- Two signed segments with opposite signs have equal images under `FreeGroup.lift f` if and only
if the image of the first positive segment equals the inverse of the image of the second. -/
theorem lift_mk_segment_eq_iff_of_ne {H : Type*} [Group H] {f : Fin Ω.numItems ⊕ A → H}
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

/-- Under `FreeGroup.lift f`, the basic equation of a base `μ` with `ε(μ) = ε(Δμ)` reduces to
equality of the positive segments `h[α(μ), β(μ)]` and `h[α(Δμ), β(Δμ)]`. -/
theorem lift_mk_basicEquation_eq_iff_of_sign_eq {H : Type*} [Group H]
    {f : Fin Ω.numItems ⊕ A → H} {μ : Fin Ω.numBases} (hs : Ω.sign μ = Ω.sign (Ω.dual μ)) :
    (FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true)) =
        FreeGroup.lift f
          (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)) := by
  rw [basicEquation_fst, basicEquation_snd, Ω.lift_mk_segment_eq_iff_of_eq hs]

/-- Under `FreeGroup.lift f`, the basic equation of a base `μ` with `ε(μ) ≠ ε(Δμ)` reduces to
`h[α(μ), β(μ)] = h[α(Δμ), β(Δμ)]⁻¹`. -/
theorem lift_mk_basicEquation_eq_iff_of_sign_ne {H : Type*} [Group H]
    {f : Fin Ω.numItems ⊕ A → H} {μ : Fin Ω.numBases} (hs : Ω.sign μ ≠ Ω.sign (Ω.dual μ)) :
    (FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true)) =
        (FreeGroup.lift f
          (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)))⁻¹ := by
  rw [basicEquation_fst, basicEquation_snd, Ω.lift_mk_segment_eq_iff_of_ne hs]

/-- Under `FreeGroup.lift f`, the basic equation of `Δ(μ)` is equivalent to that of `μ`. -/
theorem lift_mk_basicEquation_dual_eq_iff {H : Type*} [Group H]
    {f : Fin Ω.numItems ⊕ A → H} (μ : Fin Ω.numBases) :
    (FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation (Ω.dual μ)).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation (Ω.dual μ)).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2) := by
  simp only [basicEquation_fst, basicEquation_snd, Ω.dual_involutive μ, eq_comm]

/-- Under `FreeGroup.lift f`, the boundary equation of `(p, μ, q)` with `ε(μ) = ε(Δμ)` reduces to
`h[α(μ), p] = h[α(Δμ), q]`. -/
theorem lift_mk_boundaryEquation_eq_iff_of_sign_eq {H : Type*} [Group H]
    {f : Fin Ω.numItems ⊕ A → H}
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (hs : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1)) :
    (FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left c.2.1) c.1 true)) =
        FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual c.2.1)) c.2.2 true)) := by
  rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_eq hs]

/-- Under `FreeGroup.lift f`, the boundary equation of `(p, μ, q)` with `ε(μ) ≠ ε(Δμ)` reduces to
`h[α(μ), p] = h[q, β(Δμ)]⁻¹`. -/
theorem lift_mk_boundaryEquation_eq_iff_of_sign_ne {H : Type*} [Group H]
    {f : Fin Ω.numItems ⊕ A → H}
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (hs : Ω.sign c.2.1 ≠ Ω.sign (Ω.dual c.2.1)) :
    (FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left c.2.1) c.1 true)) =
        (FreeGroup.lift f
          (FreeGroup.mk (Ω.segment c.2.2 (Ω.right (Ω.dual c.2.1)) true)))⁻¹ := by
  rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_ne hs,
    Ω.lift_mk_segment f c.2.2 (Ω.right (Ω.dual c.2.1)) false]
  rfl

/-- Under `FreeGroup.lift f`, given the basic equation of `μ`, the boundary equation of the dual
triple `(q, Δ(μ), p)` is equivalent to that of `(p, μ, q)` for any boundaries
`p ∈ [α(μ), β(μ)]` and `q ∈ [α(Δμ), β(Δμ)]`. -/
theorem lift_mk_boundaryEquation_dual_eq_iff {H : Type*} [Group H]
    {f : Fin Ω.numItems ⊕ A → H} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
    {q : Fin (Ω.numItems + 1)} (hp₁ : Ω.left μ ≤ p) (hp₂ : p ≤ Ω.right μ)
    (hq₁ : Ω.left (Ω.dual μ) ≤ q) (hq₂ : q ≤ Ω.right (Ω.dual μ))
    (hbasic : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2)) :
    (FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (q, Ω.dual μ, p)).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (q, Ω.dual μ, p)).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).2) := by
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · have hs' : Ω.sign (Ω.dual μ) = Ω.sign (Ω.dual (Ω.dual μ)) := by
      simpa [Ω.dual_involutive μ] using hs.symm
    rw [Ω.lift_mk_boundaryEquation_eq_iff_of_sign_eq (c := (q, Ω.dual μ, p)) hs',
      Ω.lift_mk_boundaryEquation_eq_iff_of_sign_eq (c := (p, μ, q)) hs, Ω.dual_involutive μ,
      eq_comm]
  · have hs' : Ω.sign (Ω.dual μ) ≠ Ω.sign (Ω.dual (Ω.dual μ)) := by
      simpa [Ω.dual_involutive μ, ne_comm] using hs
    rw [Ω.lift_mk_boundaryEquation_eq_iff_of_sign_ne (c := (q, Ω.dual μ, p)) hs',
      Ω.lift_mk_boundaryEquation_eq_iff_of_sign_ne (c := (p, μ, q)) hs, Ω.dual_involutive μ]
    have hbas := (Ω.lift_mk_basicEquation_eq_iff_of_sign_ne hs).1 hbasic
    rw [Ω.lift_mk_segment_eq_mul f hp₁ hp₂,
      Ω.lift_mk_segment_eq_mul f hq₁ hq₂, mul_inv_rev] at hbas
    constructor
    · intro h
      have h' : FreeGroup.lift f (FreeGroup.mk (Ω.segment p (Ω.right μ) true)) =
          (FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) q true)))⁻¹ := by
        rw [← inv_inj, inv_inv, h]
      rw [h'] at hbas
      exact mul_right_cancel hbas
    · intro h
      rw [h] at hbas
      have h' := mul_left_cancel hbas
      rw [← inv_inj, inv_inv, h']

end Evaluation

section GroupSolutions

variable {A : Type*} {Ω : GenEq A} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)} (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ)

private theorem boundaryEquation_cutBase_cutPiece_zero (p' q' : Fin (Ω.numItems + 1)) :
    (Ω.cutBase p μ q hc hμ).boundaryEquation (p', Ω.cutPiece μ hμ 0, q') =
      Ω.boundaryEquation (p', μ, q') := by
  refine Prod.ext (by simp) ?_
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [(Ω.cutBase p μ q hc hμ).boundaryEquation_snd_of_sign_eq (by simpa using hs),
      Ω.boundaryEquation_snd_of_sign_eq (c := (p', μ, q')) hs]
    simp [hs]
  · rw [(Ω.cutBase p μ q hc hμ).boundaryEquation_snd_of_sign_ne (by simpa using hs),
      Ω.boundaryEquation_snd_of_sign_ne (c := (p', μ, q')) hs]
    simp [hs]

private theorem lift_basicEquation_cutPiece_zero_iff {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H) :
    (FreeGroup.lift f
        (FreeGroup.mk ((Ω.cutBase p μ q hc hμ).basicEquation (Ω.cutPiece μ hμ 0)).1) =
      FreeGroup.lift f
        (FreeGroup.mk ((Ω.cutBase p μ q hc hμ).basicEquation (Ω.cutPiece μ hμ 0)).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).2) := by
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [(Ω.cutBase p μ q hc hμ).lift_mk_basicEquation_eq_iff_of_sign_eq (by simpa using hs),
      Ω.lift_mk_boundaryEquation_eq_iff_of_sign_eq (c := (p, μ, q)) hs]
    simp [hs]
  · rw [(Ω.cutBase p μ q hc hμ).lift_mk_basicEquation_eq_iff_of_sign_ne (by simpa using hs),
      Ω.lift_mk_boundaryEquation_eq_iff_of_sign_ne (c := (p, μ, q)) hs]
    simp [hs]

private theorem lift_basicEquation_cutPiece_one_iff {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H)
    (hconn : FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).2)) :
    (FreeGroup.lift f
        (FreeGroup.mk ((Ω.cutBase p μ q hc hμ).basicEquation (Ω.cutPiece μ hμ 1)).1) =
      FreeGroup.lift f
        (FreeGroup.mk ((Ω.cutBase p μ q hc hμ).basicEquation (Ω.cutPiece μ hμ 1)).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2) := by
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂ hq₁ hq₂
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [(Ω.cutBase p μ q hc hμ).lift_mk_basicEquation_eq_iff_of_sign_eq (by simpa using hs),
      Ω.lift_mk_basicEquation_eq_iff_of_sign_eq hs]
    simp only [segment_cutBase, cutLeft_cutPiece_one, cutRight_cutPiece_one, cutDual_cutPiece_one,
      cutLeft_cutPiece_three, cutRight_cutPiece_three, hs, ↓reduceIte]
    have hc₀ := (Ω.lift_mk_boundaryEquation_eq_iff_of_sign_eq (c := (p, μ, q)) hs).1 hconn
    dsimp only at hc₀
    rw [Ω.lift_mk_segment_eq_mul f hp₁.le hp₂.le,
      Ω.lift_mk_segment_eq_mul f hq₁.le hq₂.le, hc₀, mul_right_inj]
  · rw [(Ω.cutBase p μ q hc hμ).lift_mk_basicEquation_eq_iff_of_sign_ne (by simpa using hs),
      Ω.lift_mk_basicEquation_eq_iff_of_sign_ne hs]
    simp only [segment_cutBase, cutLeft_cutPiece_one, cutRight_cutPiece_one, cutDual_cutPiece_one,
      cutLeft_cutPiece_three, cutRight_cutPiece_three, hs, ↓reduceIte]
    have hc₀ := (Ω.lift_mk_boundaryEquation_eq_iff_of_sign_ne (c := (p, μ, q)) hs).1 hconn
    dsimp only at hc₀
    rw [Ω.lift_mk_segment_eq_mul f hp₁.le hp₂.le,
      Ω.lift_mk_segment_eq_mul f hq₁.le hq₂.le, mul_inv_rev, ← hc₀,
      mul_right_inj]

private theorem lift_boundaryEquation_cutPiece_one_iff {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H) {p' q' : Fin (Ω.numItems + 1)} (hp' : p ≤ p')
    (hq' : if Ω.sign μ = Ω.sign (Ω.dual μ) then q ≤ q' else q' ≤ q)
    (hconn : FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).2)) :
    (FreeGroup.lift f (FreeGroup.mk
        ((Ω.cutBase p μ q hc hμ).boundaryEquation (p', Ω.cutPiece μ hμ 1, q')).1) =
      FreeGroup.lift f (FreeGroup.mk
        ((Ω.cutBase p μ q hc hμ).boundaryEquation (p', Ω.cutPiece μ hμ 1, q')).2)) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p', μ, q')).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p', μ, q')).2) := by
  obtain ⟨hp₁, -, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hq₁ hq₂
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · simp only [hs, ↓reduceIte] at hq'
    rw [(Ω.cutBase p μ q hc hμ).lift_mk_boundaryEquation_eq_iff_of_sign_eq
        (c := (p', Ω.cutPiece μ hμ 1, q')) (by simpa using hs),
      Ω.lift_mk_boundaryEquation_eq_iff_of_sign_eq (c := (p', μ, q')) hs]
    simp only [segment_cutBase, cutLeft_cutPiece_one, cutDual_cutPiece_one, cutLeft_cutPiece_three,
      hs, ↓reduceIte]
    have hc₀ := (Ω.lift_mk_boundaryEquation_eq_iff_of_sign_eq (c := (p, μ, q)) hs).1 hconn
    dsimp only at hc₀
    rw [Ω.lift_mk_segment_eq_mul f hp₁.le hp',
      Ω.lift_mk_segment_eq_mul f hq₁.le hq', hc₀, mul_right_inj]
  · simp only [hs, ↓reduceIte] at hq'
    rw [(Ω.cutBase p μ q hc hμ).lift_mk_boundaryEquation_eq_iff_of_sign_ne
        (c := (p', Ω.cutPiece μ hμ 1, q')) (by simpa using hs),
      Ω.lift_mk_boundaryEquation_eq_iff_of_sign_ne (c := (p', μ, q')) hs]
    simp only [segment_cutBase, cutLeft_cutPiece_one, cutDual_cutPiece_one, cutRight_cutPiece_three,
      hs, ↓reduceIte]
    have hc₀ := (Ω.lift_mk_boundaryEquation_eq_iff_of_sign_ne (c := (p, μ, q)) hs).1 hconn
    dsimp only at hc₀
    rw [Ω.lift_mk_segment_eq_mul f hp₁.le hp',
      Ω.lift_mk_segment_eq_mul f hq' hq₂.le, mul_inv_rev, ← hc₀,
      mul_right_inj]

/-- Every point of `Ω*` in an `F(A)`-group is a point of `(Ω.cutBase p μ q hc hμ)*`. This forward
inclusion requires no formal-consistency hypothesis on `Ω`. -/
theorem V_toSystem_subset_cutBase {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    V ι Ω.toSystem ⊆ V ι (Ω.cutBase p μ q hc hμ).toSystem := by
  intro v hv
  rw [mem_V_toSystem_iff] at hv ⊢
  set f : Fin Ω.numItems ⊕ A → H := Sum.elim v (ι ∘ FreeGroup.of)
  have hbasic_μ := hv _ (Ω.basicEquation_mem_equations μ)
  have hconn_p := hv _ (Ω.boundaryEquation_mem_equations hc)
  have hpiece0 := (lift_basicEquation_cutPiece_zero_iff hc hμ f).2 hconn_p
  have hpiece1 := (lift_basicEquation_cutPiece_one_iff hc hμ f hconn_p).2 hbasic_μ
  have hconn0 : ∀ {p' q' : Fin (Ω.numItems + 1)},
      (p', Ω.cutPiece μ hμ 0, q') ∈ (Ω.cutBase p μ q hc hμ).connections →
      FreeGroup.lift f (FreeGroup.mk
          ((Ω.cutBase p μ q hc hμ).boundaryEquation (p', Ω.cutPiece μ hμ 0, q')).1) =
        FreeGroup.lift f (FreeGroup.mk
          ((Ω.cutBase p μ q hc hμ).boundaryEquation (p', Ω.cutPiece μ hμ 0, q')).2) := by
    intro p' q' hc'
    rw [boundaryEquation_cutBase_cutPiece_zero]
    exact hv _ (Ω.boundaryEquation_mem_equations
      (by simpa using ((mem_connections_cutBase hc hμ).1 hc').1))
  have hconn1 : ∀ {p' q' : Fin (Ω.numItems + 1)},
      (p', Ω.cutPiece μ hμ 1, q') ∈ (Ω.cutBase p μ q hc hμ).connections →
      FreeGroup.lift f (FreeGroup.mk
          ((Ω.cutBase p μ q hc hμ).boundaryEquation (p', Ω.cutPiece μ hμ 1, q')).1) =
        FreeGroup.lift f (FreeGroup.mk
          ((Ω.cutBase p μ q hc hμ).boundaryEquation (p', Ω.cutPiece μ hμ 1, q')).2) := by
    intro p' q' hc'
    obtain ⟨hc₀, hl₁, -, hl₂, hr₂⟩ := (mem_connections_cutBase hc hμ).1 hc'
    have hc₀' : (p', μ, q') ∈ Ω.connections := by simpa using hc₀
    have hp' : p ≤ p' := (by simpa using hl₁ : p < p').le
    have hq' : if Ω.sign μ = Ω.sign (Ω.dual μ) then q ≤ q' else q' ≤ q := by
      split_ifs with hs
      · exact (by simpa [hs] using hl₂ : q < q').le
      · exact (by simpa [hs] using hr₂ : q' < q).le
    exact (lift_boundaryEquation_cutPiece_one_iff hc hμ f hp' hq' hconn_p).2
      (hv _ (Ω.boundaryEquation_mem_equations hc₀'))
  rw [forall_mem_equations]
  refine ⟨(forall_cutBase hμ).2 ⟨fun ν => ?_, ?_⟩, fun b hb => ?_, fun ⟨p', β, q'⟩ hc' => ?_⟩
  · rw [basicEquation_cutBase_cutSurv]
    exact hv _ (Ω.basicEquation_mem_equations _)
  · refine cutPiece_cases hpiece0 hpiece1 ?_ ?_
    · simpa only [cutDual_cutPiece_zero] using
        ((Ω.cutBase p μ q hc hμ).lift_mk_basicEquation_dual_eq_iff (Ω.cutPiece μ hμ 0)).2 hpiece0
    · simpa only [cutDual_cutPiece_one] using
        ((Ω.cutBase p μ q hc hμ).lift_mk_basicEquation_dual_eq_iff (Ω.cutPiece μ hμ 1)).2 hpiece1
  · rw [coeffEquation_cutBase]
    exact hv _ (Ω.coeffEquation_mem_equations hb)
  · revert hc'
    refine cutBase_cases hμ (fun ν hc' => ?_) (fun i hc' => ?_) β
    · rw [boundaryEquation_cutBase_cutSurv]
      exact hv _ (Ω.boundaryEquation_mem_equations ((mem_connections_cutBase_cutSurv hc hμ).1 hc'))
    · revert hc'
      refine cutPiece_cases (fun hc' => hconn0 hc') (fun hc' => hconn1 hc') ?_ ?_ i
      · intro hc'
        have hc_dual : (q', Ω.cutPiece μ hμ 0, p') ∈ (Ω.cutBase p μ q hc hμ).connections := by
          simpa using (Ω.cutBase p μ q hc hμ).dual_mem_connections _ hc'
        obtain ⟨h₁, h₂, h₃, h₄⟩ := (Ω.cutBase p μ q hc hμ).bounds_of_mem_connections _ hc_dual
        simpa only [cutDual_cutPiece_zero] using
          ((Ω.cutBase p μ q hc hμ).lift_mk_boundaryEquation_dual_eq_iff
            h₁.le h₂.le h₃.le h₄.le hpiece0).2 (hconn0 hc_dual)
      · intro hc'
        have hc_dual : (q', Ω.cutPiece μ hμ 1, p') ∈ (Ω.cutBase p μ q hc hμ).connections := by
          simpa using (Ω.cutBase p μ q hc hμ).dual_mem_connections _ hc'
        obtain ⟨h₁, h₂, h₃, h₄⟩ := (Ω.cutBase p μ q hc hμ).bounds_of_mem_connections _ hc_dual
        simpa only [cutDual_cutPiece_one] using
          ((Ω.cutBase p μ q hc hμ).lift_mk_boundaryEquation_dual_eq_iff
            h₁.le h₂.le h₃.le h₄.le hpiece1).2 (hconn1 hc_dual)

/-- **ET1 on group solutions.** In a formally consistent generalised equation, cutting `μ` at
`(p, μ, q)` preserves the set of group solutions in every `F(A)`-group. -/
theorem V_toSystem_cutBase (hΩ : Ω.IsFormallyConsistent) {H : Type*} [Group H]
    (ι : FreeGroup A →* H) :
    V ι (Ω.cutBase p μ q hc hμ).toSystem = V ι Ω.toSystem := by
  refine Set.Subset.antisymm (fun v hv => ?_) (V_toSystem_subset_cutBase hc hμ ι)
  rw [mem_V_toSystem_iff] at hv ⊢
  set f : Fin Ω.numItems ⊕ A → H := Sum.elim v (ι ∘ FreeGroup.of)
  have hconn_p := (lift_basicEquation_cutPiece_zero_iff hc hμ f).1
    (hv _ ((Ω.cutBase p μ q hc hμ).basicEquation_mem_equations (Ω.cutPiece μ hμ 0)))
  have hbasic_μ := (lift_basicEquation_cutPiece_one_iff hc hμ f hconn_p).1
    (hv _ ((Ω.cutBase p μ q hc hμ).basicEquation_mem_equations (Ω.cutPiece μ hμ 1)))
  have hconn_μ : ∀ {p' q' : Fin (Ω.numItems + 1)}, (p', μ, q') ∈ Ω.connections →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p', μ, q')).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p', μ, q')).2) := by
    intro p' q' hc₀
    rcases lt_trichotomy p' p with hlt | rfl | hgt
    · have hc' := (mem_connections_cutBase_of_lt hc hμ hΩ hc₀ hlt).1
      rw [← boundaryEquation_cutBase_cutPiece_zero hc hμ]
      exact hv _ ((Ω.cutBase p μ q hc hμ).boundaryEquation_mem_equations hc')
    · obtain rfl : q' = q := hΩ.isTiedTo_unique (isTiedTo_of_mem_connections hc₀)
        (isTiedTo_of_mem_connections hc)
      exact hconn_p
    · have hc' := (mem_connections_cutBase_of_gt hc hμ hΩ hc₀ hgt).1
      have hq' : if Ω.sign μ = Ω.sign (Ω.dual μ) then q ≤ q' else q' ≤ q := by
        split_ifs with hs
        · exact (hΩ.lt_of_isTiedTo_of_sign_eq hs (isTiedTo_of_mem_connections hc)
            (isTiedTo_of_mem_connections hc₀) hgt).le
        · exact (hΩ.lt_of_isTiedTo_of_sign_ne hs (isTiedTo_of_mem_connections hc)
            (isTiedTo_of_mem_connections hc₀) hgt).le
      exact (lift_boundaryEquation_cutPiece_one_iff hc hμ f hgt.le hq' hconn_p).1
        (hv _ ((Ω.cutBase p μ q hc hμ).boundaryEquation_mem_equations hc'))
  rw [forall_mem_equations]
  refine ⟨fun ν => ?_, fun b hb => ?_, fun ⟨p', ν, q'⟩ hc₀ => ?_⟩
  · by_cases hmem : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))
    · rcases Finset.mem_insert.1 hmem with rfl | hmem
      · exact hbasic_μ
      · rw [Finset.mem_singleton.1 hmem]
        exact (Ω.lift_mk_basicEquation_dual_eq_iff μ).2 hbasic_μ
    · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
      rw [← basicEquation_cutBase_cutSurv hc hμ]
      exact hv _ ((Ω.cutBase p μ q hc hμ).basicEquation_mem_equations _)
  · rw [← coeffEquation_cutBase hc hμ]
    exact hv _ ((Ω.cutBase p μ q hc hμ).coeffEquation_mem_equations hb)
  · by_cases hmem : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))
    · rcases Finset.mem_insert.1 hmem with rfl | hmem
      · exact hconn_μ hc₀
      · rw [Finset.mem_singleton.1 hmem] at hc₀ ⊢
        have hc₀_dual : (q', μ, p') ∈ Ω.connections := by
          simpa [Ω.dual_involutive μ] using Ω.dual_mem_connections _ hc₀
        obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections (q', μ, p') hc₀_dual
        exact (Ω.lift_mk_boundaryEquation_dual_eq_iff h₁.le h₂.le h₃.le h₄.le hbasic_μ).2
          (hconn_μ hc₀_dual)
    · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
      rw [← boundaryEquation_cutBase_cutSurv hc hμ]
      exact hv _ ((Ω.cutBase p μ q hc hμ).boundaryEquation_mem_equations
        ((mem_connections_cutBase_cutSurv hc hμ).2 hc₀))

/-- **ET1 on coordinate groups.** The `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` induced by the
identity on the items, where `Ω` is formally consistent and `Ω′ = Ω.cutBase p μ q hc hμ`. -/
def cutBaseHom (hΩ : Ω.IsFormallyConsistent) :
    GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
      (CoordGroup.coeff (.id (FreeGroup A)) (Ω.cutBase p μ q hc hμ).toSystem) :=
  CoordGroup.homOfVSubset (V_toSystem_cutBase hc hμ hΩ _).le

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of ET1 is the identity on the words in the items. -/
-- Not `@[simp]`: the reducible `cutBase` in the codomain keeps `simp` from indexing this lemma
-- uninstantiated, so it is used through `rw`.
theorem cutBaseHom_mk (hΩ : Ω.IsFormallyConsistent) (w : GX (FreeGroup A) (Fin Ω.numItems)) :
    cutBaseHom hc hμ hΩ (w : Ω.coordGroup) = (w : (Ω.cutBase p μ q hc hμ).coordGroup) :=
  CoordGroup.homOfVSubset_mk _ w

/-- The coordinate-group homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of ET1 is surjective. -/
theorem cutBaseHom_surjective (hΩ : Ω.IsFormallyConsistent) :
    Function.Surjective (cutBaseHom hc hμ hΩ) :=
  CoordGroup.homOfVSubset_surjective _

/-- **ET1 on coordinate groups.** When `Ω` is formally consistent, the identity on the items induces
an `F(A)`-isomorphism between the coordinate groups of `Ω` and `Ω.cutBase p μ q hc hμ`. -/
theorem cutBaseHom_bijective (hΩ : Ω.IsFormallyConsistent) :
    Function.Bijective (cutBaseHom hc hμ hΩ) :=
  ⟨CoordGroup.homOfVSubset_injective _ (V_toSystem_cutBase hc hμ hΩ _).ge,
    cutBaseHom_surjective hc hμ hΩ⟩

end GroupSolutions

/-! ### Graphical solutions -/

section GraphicalSolutions

variable {A : Type*} {Ω : GenEq A} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)} (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ)

namespace Solution

/-- Every graphical solution `U` of `Ω` transfers to a graphical solution of
`Ω.cutBase p μ q hc hμ` with the same item words: each new piece is a subsegment of `μ` or `Δ(μ)`,
so its word in `U` is a subword of a reduced word and therefore reduced as written. -/
def cutBase (U : Ω.Solution) : (Ω.cutBase p μ q hc hμ).Solution :=
  Solution.ofMemV U.word U.isReduced_word U.word_ne_nil
    ((forall_mem_equations _).2
      ⟨fun β => by
        rw [basicEquation_fst, basicEquation_snd, segment_cutBase, segment_cutBase]
        exact ⟨(Ω.isReduced_substituteVars_segment_iff U.word _ _ _).2
            (U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ hμ β)
              (left_cutOrigBase_le hc hμ β) (cutRight_le_right_cutOrigBase hc hμ β)),
          (Ω.isReduced_substituteVars_segment_iff U.word _ _ _).2
            (U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ hμ (Ω.cutDual μ hμ β))
              (left_cutOrigBase_le hc hμ _) (cutRight_le_right_cutOrigBase hc hμ _))⟩,
      fun b hb => by
        rw [coeffEquation_cutBase]
        exact U.isReduced_subst _ (Ω.coeffEquation_mem_equations hb),
      fun ⟨p', β, q'⟩ hc' => by
        obtain ⟨-, hl₁, hr₁, hl₂, hr₂⟩ := (mem_connections_cutBase hc hμ).1 hc'
        dsimp only at hl₁ hr₁ hl₂ hr₂
        refine ⟨?_, ?_⟩
        · rw [boundaryEquation_fst, segment_cutBase]
          exact U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ hμ β)
            (left_cutOrigBase_le hc hμ β) (hr₁.le.trans (cutRight_le_right_cutOrigBase hc hμ β))
        · by_cases hs : (Ω.cutBase p μ q hc hμ).sign β =
              (Ω.cutBase p μ q hc hμ).sign ((Ω.cutBase p μ q hc hμ).dual β)
          · rw [(Ω.cutBase p μ q hc hμ).boundaryEquation_snd_of_sign_eq hs, segment_cutBase]
            exact U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ hμ (Ω.cutDual μ hμ β))
              (left_cutOrigBase_le hc hμ _) (hr₂.le.trans (cutRight_le_right_cutOrigBase hc hμ _))
          · rw [(Ω.cutBase p μ q hc hμ).boundaryEquation_snd_of_sign_ne hs, segment_cutBase,
              Ω.isReduced_substituteVars_segment_iff]
            exact U.isReduced_substituteVars_segment_of_le (Ω.cutOrigBase μ hμ (Ω.cutDual μ hμ β))
              ((left_cutOrigBase_le hc hμ _).trans hl₂.le) (cutRight_le_right_cutOrigBase hc hμ _)⟩)
    (funext U.point_apply ▸ V_toSystem_subset_cutBase hc hμ _ U.point_mem_V)

/-- `Solution.cutBase` preserves the words of the items. -/
@[simp]
theorem cutBase_word (U : Ω.Solution) : (U.cutBase hc hμ).word = U.word :=
  Solution.ofMemV_word ..

/-- `Solution.cutBase` preserves the point of a solution in `F(A)^ρ`. -/
@[simp]
theorem cutBase_point (U : Ω.Solution) : (U.cutBase hc hμ).point = U.point := by
  ext
  simp

/-- `Solution.cutBase` preserves the prefix lengths of all boundaries. -/
@[simp]
theorem cutBase_prefixLength (U : Ω.Solution) :
    (U.cutBase hc hμ).prefixLength = U.prefixLength := by
  ext
  simp [prefixLength_def]

/-- `Solution.cutBase` preserves alphabet constraints on the items. -/
@[simp]
theorem isConstrained_cutBase_iff (U : Ω.Solution) (D : Fin Ω.numItems → Set A) :
    (U.cutBase hc hμ).IsConstrained D ↔ U.IsConstrained D := by
  simp [isConstrained_iff]

/-- In `U.cutBase hc hμ`, the words of the two pieces `cutPiece μ hμ 0` and `cutPiece μ hμ 1`
concatenate without cancellation to the word of `μ` in `U`. -/
theorem substituteVars_cutPiece_zero_append_one (U : Ω.Solution) :
    substituteVars (U.cutBase hc hμ).word
        ((Ω.cutBase p μ q hc hμ).segment ((Ω.cutBase p μ q hc hμ).left (Ω.cutPiece μ hμ 0))
          ((Ω.cutBase p μ q hc hμ).right (Ω.cutPiece μ hμ 0)) true) ++
      substituteVars (U.cutBase hc hμ).word
        ((Ω.cutBase p μ q hc hμ).segment ((Ω.cutBase p μ q hc hμ).left (Ω.cutPiece μ hμ 1))
          ((Ω.cutBase p μ q hc hμ).right (Ω.cutPiece μ hμ 1)) true) =
      substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) := by
  obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂
  simp only [cutBase_word, segment_cutBase, cutLeft_cutPiece_zero, cutRight_cutPiece_zero,
    cutLeft_cutPiece_one, cutRight_cutPiece_one, ← substituteVars_append]
  rw [Ω.segment_append hp₁.le hp₂.le]

end Solution

/-- If `Ω` admits a graphical solution, `Ω.cutBase p μ q hc hμ` is formally consistent;
contrapositively, if cutting a base breaks formal consistency, `Ω` has no graphical solution. -/
theorem isFormallyConsistent_cutBase_of_nonempty_solution (hne : Nonempty Ω.Solution) :
    (Ω.cutBase p μ q hc hμ).IsFormallyConsistent :=
  let ⟨U⟩ := hne
  (U.cutBase hc hμ).isFormallyConsistent

/-- The homomorphism `F_{R(Ω′)} → F(A)` of `U.cutBase hc hμ` composed with `cutBaseHom` is
`U.toHom`. -/
theorem toHom_comp_cutBaseHom (hΩ : Ω.IsFormallyConsistent) (U : Ω.Solution) :
    (U.cutBase hc hμ).toHom.comp (cutBaseHom hc hμ hΩ) = U.toHom := by
  ext k
  rw [GHom.coe_comp, Function.comp_apply, cutBaseHom_mk]
  simp

/-- **ET1 transfers solutions uniquely.** For any solution `U` of a formally consistent `Ω`,
`U.cutBase hc hμ` is the unique solution of `Ω.cutBase p μ q hc hμ` whose homomorphism factors
`U.toHom` through `cutBaseHom`. -/
theorem toHom_comp_cutBaseHom_eq_iff (hΩ : Ω.IsFormallyConsistent) (U : Ω.Solution)
    (U' : (Ω.cutBase p μ q hc hμ).Solution) :
    U'.toHom.comp (cutBaseHom hc hμ hΩ) = U.toHom ↔ U' = U.cutBase hc hμ := by
  refine ⟨fun h => Solution.point_injective (funext fun k => ?_), ?_⟩
  · have h' := DFunLike.congr_fun h ((inr (FreeGroup.of k) : GX (FreeGroup A) _) : Ω.coordGroup)
    rw [GHom.coe_comp, Function.comp_apply, cutBaseHom_mk, Solution.toHom_inr_of,
      Solution.toHom_inr_of] at h'
    simpa using h'
  · rintro rfl
    exact toHom_comp_cutBaseHom hc hμ hΩ U

/-- For any solution `U′` of `Ω.cutBase p μ q hc hμ`, the word `U′[α(Δμ), β(Δμ)]` of the dual base
is reduced as written if and only if the word `U′[α(μ), β(μ)]` of `μ` is reduced as written: the two
words are either identical (when `ε(μ) = ε(Δμ)`) or formal inverses of one another (when
`ε(μ) ≠ ε(Δμ)`). -/
theorem isReduced_substituteVars_dual_iff_of_cutBase (U' : (Ω.cutBase p μ q hc hμ).Solution) :
    FreeGroup.IsReduced
        (substituteVars U'.word (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)) ↔
      FreeGroup.IsReduced
        (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true)) := by
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections (p, μ, q) hc
  dsimp only at hp₁ hp₂ hq₁ hq₂
  rw [← Ω.segment_append hp₁.le hp₂.le,
    ← Ω.segment_append hq₁.le hq₂.le,
    substituteVars_append, substituteVars_append]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · have heq₀ :=
      U'.substituteVars_segment_eq_of_sign_eq (μ := Ω.cutPiece μ hμ 0) (by simpa using hs)
    have heq₁ :=
      U'.substituteVars_segment_eq_of_sign_eq (μ := Ω.cutPiece μ hμ 1) (by simpa using hs)
    simp only [segment_cutBase, cutLeft_cutPiece_zero, cutRight_cutPiece_zero,
      cutDual_cutPiece_zero, cutLeft_cutPiece_two, cutRight_cutPiece_two, cutLeft_cutPiece_one,
      cutRight_cutPiece_one, cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three,
      hs, ↓reduceIte] at heq₀ heq₁
    rw [heq₀, heq₁]
  · have heq₀ := U'.substituteVars_segment_eq_invRev_of_sign_ne (μ := Ω.cutPiece μ hμ 0)
      (by simpa using hs)
    have heq₁ := U'.substituteVars_segment_eq_invRev_of_sign_ne (μ := Ω.cutPiece μ hμ 1)
      (by simpa using hs)
    simp only [segment_cutBase, cutLeft_cutPiece_zero, cutRight_cutPiece_zero,
      cutDual_cutPiece_zero, cutLeft_cutPiece_two, cutRight_cutPiece_two, cutLeft_cutPiece_one,
      cutRight_cutPiece_one, cutDual_cutPiece_one, cutLeft_cutPiece_three, cutRight_cutPiece_three,
      hs, ↓reduceIte] at heq₀ heq₁
    rw [heq₀, heq₁, ← FreeGroup.invRev_append, FreeGroup.isReduced_invRev]

private theorem isReduced_subst_of_cutBase (U' : (Ω.cutBase p μ q hc hμ).Solution)
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
        exact (isReduced_substituteVars_dual_iff_of_cutBase hc hμ U').2 hred
    · obtain ⟨ν₀, rfl⟩ := exists_cutSurvEmb_eq hmem
      simpa using U'.isReduced_substituteVars_segment (Ω.cutSurv μ hμ ν₀)
  have hsub : ∀ (ν : Fin Ω.numBases) {i j : ℕ}, Ω.left ν ≤ i → j ≤ Ω.right ν → ∀ s : Bool,
      FreeGroup.IsReduced (substituteVars U'.word (Ω.segment i j s)) := by
    intro ν i j hi hj s
    rw [Ω.isReduced_substituteVars_segment_iff]
    rcases le_total i j with hij | hji
    · have h := hbase ν
      rw [← Ω.segment_append hi (hij.trans hj),
        ← Ω.segment_append hij hj, substituteVars_append,
        substituteVars_append, ← List.append_assoc] at h
      exact h.infix (List.infix_append _ _ _)
    · rw [Ω.segment_eq_nil_of_le hji, FreeGroup.substituteVars_nil]
      exact FreeGroup.IsReduced.nil
  refine (forall_mem_equations _).2 ⟨fun ν => ?_, fun b hb => ?_, fun c₀ hc₀ => ?_⟩
  · rw [basicEquation_fst, basicEquation_snd]
    exact ⟨hsub ν le_rfl le_rfl _, hsub (Ω.dual ν) le_rfl le_rfl _⟩
  · rw [← coeffEquation_cutBase hc hμ]
    exact U'.isReduced_subst _ ((Ω.cutBase p μ q hc hμ).coeffEquation_mem_equations hb)
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
are in bijection with those graphical solutions of `Ω.cutBase p μ q hc hμ` for which the word
`U′[α(μ), β(μ)]` is reduced as written. The words of the items are unchanged. -/
def solutionEquivCutBase (hΩ : Ω.IsFormallyConsistent) :
    Ω.Solution ≃ {U' : (Ω.cutBase p μ q hc hμ).Solution //
      FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true))} where
  toFun U := ⟨U.cutBase hc hμ, by
    rw [Solution.cutBase_word]
    exact U.isReduced_substituteVars_segment μ⟩
  invFun U' := Solution.ofMemV U'.val.word U'.val.isReduced_word U'.val.word_ne_nil
    (isReduced_subst_of_cutBase hc hμ U'.val U'.property)
    (funext U'.val.point_apply ▸ (V_toSystem_cutBase hc hμ hΩ _).le U'.val.point_mem_V)
  left_inv U := Solution.ext ((Solution.ofMemV_word ..).trans (U.cutBase_word hc hμ))
  right_inv U' := Subtype.ext (Solution.ext (by simp))

/-- `solutionEquivCutBase` sends `U` to `U.cutBase hc hμ`. -/
@[simp]
theorem solutionEquivCutBase_apply_coe (hΩ : Ω.IsFormallyConsistent) (U : Ω.Solution) :
    (solutionEquivCutBase hc hμ hΩ U : (Ω.cutBase p μ q hc hμ).Solution) = U.cutBase hc hμ :=
  (rfl)

section EquivSymm

variable (hΩ : Ω.IsFormallyConsistent)
  (U' : {U' : (Ω.cutBase p μ q hc hμ).Solution //
    FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true))})

/-- The inverse of `solutionEquivCutBase` preserves the words of the items. -/
@[simp]
theorem solutionEquivCutBase_symm_apply_word :
    ((solutionEquivCutBase hc hμ hΩ).symm U').word = U'.val.word :=
  Solution.ofMemV_word ..

/-- The inverse of `solutionEquivCutBase` preserves the point of a solution. -/
@[simp]
theorem solutionEquivCutBase_symm_apply_point :
    ((solutionEquivCutBase hc hμ hΩ).symm U').point = U'.val.point := by
  ext
  simp

/-- The inverse of `solutionEquivCutBase` preserves the prefix lengths of all boundaries. -/
@[simp]
theorem solutionEquivCutBase_symm_apply_prefixLength :
    ((solutionEquivCutBase hc hμ hΩ).symm U').prefixLength = U'.val.prefixLength := by
  ext
  simp [Solution.prefixLength_def]

/-- The homomorphism `F_{R(Ω)} → F(A)` of `(solutionEquivCutBase hc hμ hΩ).symm U′` is `U′.1.toHom`
composed with `cutBaseHom`. -/
theorem solutionEquivCutBase_symm_apply_toHom :
    ((solutionEquivCutBase hc hμ hΩ).symm U').toHom = U'.val.toHom.comp (cutBaseHom hc hμ hΩ) := by
  conv_rhs => rw [← (solutionEquivCutBase hc hμ hΩ).apply_symm_apply U']
  exact (toHom_comp_cutBaseHom hc hμ hΩ _).symm

end EquivSymm

/-- If the cut boundary `p` remains open in `Ω.cutBase p μ q hc hμ`, another variable base crosses
`p`, so the two cut pieces of `μ` glue without cancellation and `U′[α(μ), β(μ)]` is automatically
reduced as written for every solution `U′` of `Ω.cutBase`. -/
theorem isReduced_cutBase_of_isOpenBoundary
    (hp : (Ω.cutBase p μ q hc hμ).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc hμ).Solution) :
    FreeGroup.IsReduced (substituteVars U'.word (Ω.segment (Ω.left μ) (Ω.right μ) true)) := by
  have h₀ : FreeGroup.IsReduced
      (substituteVars U'.word ((Ω.cutBase p μ q hc hμ).segment (Ω.left μ) p true)) := by
    simpa only [cutLeft_cutPiece_zero, cutRight_cutPiece_zero] using
      U'.isReduced_substituteVars_segment (Ω.cutPiece μ hμ 0)
  have h₁ : FreeGroup.IsReduced
      (substituteVars U'.word ((Ω.cutBase p μ q hc hμ).segment p (Ω.right μ) true)) := by
    simpa only [cutLeft_cutPiece_one, cutRight_cutPiece_one] using
      U'.isReduced_substituteVars_segment (Ω.cutPiece μ hμ 1)
  rw [← segment_cutBase hc hμ]
  exact U'.isReduced_substituteVars_segment_of_isOpenBoundary hp h₀ h₁

/-- **ET1 when the cut boundary stays open.** If `Ω` is formally consistent and `p` remains an open
boundary in `Ω.cutBase p μ q hc hμ`, graphical solutions of `Ω` and of `Ω.cutBase p μ q hc hμ` are
in unconditional bijection with the same item words. -/
def solutionEquivCutBaseOfOpen (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc hμ).IsOpenBoundary p) :
    Ω.Solution ≃ (Ω.cutBase p μ q hc hμ).Solution :=
  (solutionEquivCutBase hc hμ hΩ).trans
    (Equiv.subtypeUnivEquiv (isReduced_cutBase_of_isOpenBoundary hc hμ hp))

/-- `solutionEquivCutBaseOfOpen` sends `U` to `U.cutBase hc hμ`. -/
@[simp]
theorem solutionEquivCutBaseOfOpen_apply (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc hμ).IsOpenBoundary p) (U : Ω.Solution) :
    solutionEquivCutBaseOfOpen hc hμ hΩ hp U = U.cutBase hc hμ :=
  (rfl)

/-- The inverse of `solutionEquivCutBaseOfOpen` preserves the words of the items. -/
@[simp]
theorem solutionEquivCutBaseOfOpen_symm_apply_word (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc hμ).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc hμ).Solution) :
    ((solutionEquivCutBaseOfOpen hc hμ hΩ hp).symm U').word = U'.word :=
  Solution.ofMemV_word ..

/-- The inverse of `solutionEquivCutBaseOfOpen` preserves the point of a solution. -/
@[simp]
theorem solutionEquivCutBaseOfOpen_symm_apply_point (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc hμ).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc hμ).Solution) :
    ((solutionEquivCutBaseOfOpen hc hμ hΩ hp).symm U').point = U'.point := by
  ext
  simp

/-- The inverse of `solutionEquivCutBaseOfOpen` preserves the prefix lengths of all boundaries. -/
@[simp]
theorem solutionEquivCutBaseOfOpen_symm_apply_prefixLength (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc hμ).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc hμ).Solution) :
    ((solutionEquivCutBaseOfOpen hc hμ hΩ hp).symm U').prefixLength = U'.prefixLength := by
  ext
  simp [Solution.prefixLength_def]

/-- The homomorphism `F_{R(Ω)} → F(A)` of `(solutionEquivCutBaseOfOpen hc hμ hΩ hp).symm U′` is
`U′.toHom` composed with `cutBaseHom`. -/
theorem solutionEquivCutBaseOfOpen_symm_apply_toHom (hΩ : Ω.IsFormallyConsistent)
    (hp : (Ω.cutBase p μ q hc hμ).IsOpenBoundary p) (U' : (Ω.cutBase p μ q hc hμ).Solution) :
    ((solutionEquivCutBaseOfOpen hc hμ hΩ hp).symm U').toHom =
      U'.toHom.comp (cutBaseHom hc hμ hΩ) :=
  solutionEquivCutBase_symm_apply_toHom hc hμ hΩ
    ⟨U', isReduced_cutBase_of_isOpenBoundary hc hμ hp U'⟩

end GraphicalSolutions

/-! ### Packaging ET1 as a `Transformation` -/

section Transformation

variable {A : Type*} {Ω : GenEq A} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)} (hc : (p, μ, q) ∈ Ω.connections) (hμ : μ ≠ Ω.dual μ)
  (hΩ : Ω.IsFormallyConsistent)

/-- **ET1 as a `Transformation`.** The transformation of a formally consistent `Ω` determined by
cutting `μ` at `(p, μ, q)`: its family of successors consists of `Ω.cutBase p μ q hc hμ` whenever
that cut is formally consistent (and is empty otherwise, in which case `Ω` has no graphical solution
by `isFormallyConsistent_cutBase_of_nonempty_solution`). -/
-- `@[expose]` is required by Lean 4's module system (as on `Transformation.id`,
-- `Transformation.bind`, and `Transformation.ofFamily`): the codomain of `Transformation.hom i`
-- and the fibre of `Transformation.transfer U` depend on `target i`, so `cutBaseTransformation_hom`
-- and `cutBaseTransformation_transfer` need `target i` to reduce to `Ω.cutBase p μ q hc hμ`, and
-- compiling `cutBaseTransformationIndex` also requires the `ι` field to be exposed.
@[expose] def cutBaseTransformation : Transformation Ω :=
  Transformation.ofFamily (κ := Unit) (fun _ => Ω.cutBase p μ q hc hμ)
    (fun _ => cutBaseHom hc hμ hΩ) (fun _ => cutBaseHom_surjective hc hμ hΩ)
    (fun U => ⟨(), U.cutBase hc hμ⟩) (fun U => toHom_comp_cutBaseHom hc hμ hΩ U)

/-- The unique successor index of `cutBaseTransformation hc hμ hΩ` when `Ω.cutBase p μ q hc hμ` is
formally consistent. -/
def cutBaseTransformationIndex (h : (Ω.cutBase p μ q hc hμ).IsFormallyConsistent) :
    (cutBaseTransformation hc hμ hΩ).ι :=
  ⟨(), h⟩

/-- `cutBaseTransformation hc hμ hΩ` has at most one successor. -/
instance : Subsingleton (cutBaseTransformation hc hμ hΩ).ι :=
  inferInstanceAs (Subsingleton { _x : Unit // (Ω.cutBase p μ q hc hμ).IsFormallyConsistent })

/-- Every successor in `cutBaseTransformation` is `Ω.cutBase p μ q hc hμ`. -/
@[simp]
theorem cutBaseTransformation_target (i : (cutBaseTransformation hc hμ hΩ).ι) :
    (cutBaseTransformation hc hμ hΩ).target i = Ω.cutBase p μ q hc hμ :=
  (rfl)

/-- Every coordinate-group homomorphism in `cutBaseTransformation` is `cutBaseHom`. -/
@[simp]
theorem cutBaseTransformation_hom (i : (cutBaseTransformation hc hμ hΩ).ι) :
    (cutBaseTransformation hc hμ hΩ).hom i = cutBaseHom hc hμ hΩ :=
  (rfl)

/-- `cutBaseTransformation` transfers `U` to `U.cutBase hc hμ`. -/
@[simp]
theorem cutBaseTransformation_transfer (U : Ω.Solution) :
    (cutBaseTransformation hc hμ hΩ).transfer U =
      ⟨cutBaseTransformationIndex hc hμ hΩ (U.cutBase hc hμ).isFormallyConsistent,
        U.cutBase hc hμ⟩ :=
  (rfl)

/-- `cutBaseTransformation hc hμ hΩ` has a successor if and only if `Ω.cutBase p μ q hc hμ` is
formally consistent. -/
theorem nonempty_cutBaseTransformation_iff :
    Nonempty (cutBaseTransformation hc hμ hΩ).ι ↔ (Ω.cutBase p μ q hc hμ).IsFormallyConsistent :=
  ⟨fun ⟨i⟩ => (cutBaseTransformation hc hμ hΩ).isFormallyConsistent_target i,
    fun h => ⟨cutBaseTransformationIndex hc hμ hΩ h⟩⟩

/-- **ET1 transfers solutions uniquely.** -/
theorem transfersUniquely_cutBaseTransformation :
    (cutBaseTransformation hc hμ hΩ).TransfersUniquely :=
  Transformation.transfersUniquely_of_subsingleton _

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

private theorem creaseExample_ne :
    (0 : Fin creaseExample.numBases) ≠ creaseExample.dual 0 := by decide

private theorem creaseExample_isFormallyConsistent : creaseExample.IsFormallyConsistent := by
  decide

private theorem creaseExample_cutBase_connections :
    (creaseExample.cutBase 1 0 3 creaseExample_mem creaseExample_ne).connections = ∅ := by
  have hcard := card_connections_cutBase creaseExample_mem creaseExample_ne
    creaseExample_isFormallyConsistent
  have h₂ : creaseExample.connections.card = 2 := by decide
  exact Finset.card_eq_zero.1 (by omega)

private def creaseWords : Fin 4 → List (Fin 2 × Bool) :=
  ![[(0, true)], [(0, false)], [(0, true)], [(0, false)]]

/-- The words `(a, a⁻¹, a, a⁻¹)` define a graphical solution of `creaseExample.cutBase 1 0 3 _ _`
(and hence a group solution in `V (.id _) creaseExample.toSystem`), yet `creaseExample` has no
graphical solution with those item words because `U[0, 2] = a a⁻¹` cancels across the closed
boundary `1`. This shows that the reducedness condition in `solutionEquivCutBase` cannot be dropped
when `p` becomes closed. -/
example :
    (∃ U' : (creaseExample.cutBase 1 0 3 creaseExample_mem creaseExample_ne).Solution,
        U'.word = creaseWords) ∧
      ¬ ∃ U : creaseExample.Solution, U.word = creaseWords := by
  refine ⟨?_, ?_⟩
  · have hsurv : creaseExample.cutSurvCard 0 = 0 := by decide
    refine ⟨⟨creaseWords, by unfold FreeGroup.IsReduced creaseWords; decide,
        by unfold creaseWords; decide, ?_, ?_⟩, rfl⟩
    · refine (forall_mem_equations _).2
        ⟨(forall_cutBase creaseExample_ne).2 ⟨fun ν => Fin.elim0 (hsurv ▸ ν), ?_⟩,
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
    · refine (forall_mem_equations _).2
        ⟨(forall_cutBase creaseExample_ne).2 ⟨fun ν => Fin.elim0 (hsurv ▸ ν), ?_⟩,
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
