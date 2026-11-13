/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Face
public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic

/-!
# Rational presentations of polyhedral faces

Making selected inequalities of a rational-normal presentation active retains the original rows
and adds their negatives at the selected indices, which keeps the linear parts rational. This also
preserves rational offsets when they are present.

The active-constraint classification of convex extreme subsets
(`IsExtreme.eq_setOf_active`) therefore gives actual rational presentations of all faces of a
rational-normal polyhedron (`IsExtreme.isRationalNormalPolyhedron`), and of a rational polyhedron
(`IsExtreme.isRationalPolyhedron`). The argument does not assume that an independently chosen
exposing functional is rational. Arbitrary real offsets, unbounded polyhedra and lineality are
allowed.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Face.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace RationalAffinePolyhedron

/-- Impose equality in the selected rows by retaining the original inequalities
and adding their negatives, giving an actual finite rational-normal presentation. -/
noncomputable def activeFace (P : RationalAffinePolyhedron h)
    (I : Finset (Fin P.numConstraints)) : RationalAffinePolyhedron h :=
  ofFinite (Sum.elim P.inequality (fun j : I => -P.inequality j.val)) (by
    intro j
    cases j with
    | inl j => exact P.rational_linear j
    | inr j => exact (P.rational_linear j.val).neg)

/-- The active presentation is exactly the original carrier with all selected
inequalities made equalities. This statement does not require nonemptiness. -/
@[simp]
theorem carrier_activeFace (P : RationalAffinePolyhedron h)
    (I : Finset (Fin P.numConstraints)) :
    (P.activeFace I).carrier = {x : V | x ∈ P.carrier ∧ ∀ j ∈ I, P.inequality j x = 0} := by
  ext x
  rw [activeFace, mem_carrier_ofFinite]
  simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, ContinuousAffineMap.neg_apply,
    neg_nonpos, Set.mem_ofPred_eq, mem_carrier]
  constructor
  · rintro ⟨hx, hxI⟩
    exact ⟨hx, fun j hj => le_antisymm (hx j) (hxI ⟨j, hj⟩)⟩
  · rintro ⟨hx, hxI⟩
    exact ⟨hx, fun j => (hxI j.val j.property).ge⟩

/-- An active presentation has rational offsets exactly when the original does. -/
@[simp]
theorem hasRationalOffsets_activeFace_iff {P : RationalAffinePolyhedron h}
    (I : Finset (Fin P.numConstraints)) :
    (P.activeFace I).HasRationalOffsets ↔ P.HasRationalOffsets := by
  rw [activeFace, hasRationalOffsets_ofFinite_iff]
  constructor
  · intro hP
    exact hasRationalOffsets_iff.mpr fun j => hP (Sum.inl j)
  · intro hP j
    cases j with
    | inl j => exact hasRationalOffsets_iff.mp hP j
    | inr j =>
      obtain ⟨q, hq⟩ := hasRationalOffsets_iff.mp hP j.val
      refine ⟨-q, ?_⟩
      simp only [Sum.elim_inr, ContinuousAffineMap.neg_apply, hq, Rat.cast_neg]

/-- Every nonempty convex extreme subset of the carrier is the carrier of one
of its active rational-normal presentations. -/
theorem exists_activeFace_of_isExtreme (P : RationalAffinePolyhedron h) {F : Set V}
    (hF : IsExtreme ℝ P.carrier F) (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ I : Finset (Fin P.numConstraints), (P.activeFace I).carrier = F := by
  have hcarrier : P.carrier = {x : V | ∀ j, P.inequality j x ≤ 0} :=
    Set.ext fun _ => mem_carrier
  rw [hcarrier] at hF
  obtain ⟨I, hI⟩ := hF.eq_setOf_active (fun j => (P.inequality j).toAffineMap) hconv hne
  exact ⟨I, by simpa using hI.symm⟩

end RationalAffinePolyhedron

end TauCeti

/-- Every convex extreme subset of a rational-normal polyhedron is
rational-normal, including the empty subset. -/
theorem IsExtreme.isRationalNormalPolyhedron {N V : Type*} [AddCommGroup N] [AddCommGroup V]
    [Module ℝ V] [TopologicalSpace V] {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
    {P F : Set V} (hF : IsExtreme ℝ P F) (hP : TauCeti.IsRationalNormalPolyhedron h P)
    (hconv : Convex ℝ F) : TauCeti.IsRationalNormalPolyhedron h F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact TauCeti.isRationalNormalPolyhedron_iff.mpr
      ⟨.empty h, TauCeti.RationalAffinePolyhedron.carrier_empty h⟩
  obtain ⟨Q, rfl⟩ := TauCeti.isRationalNormalPolyhedron_iff.mp hP
  obtain ⟨I, hI⟩ := Q.exists_activeFace_of_isExtreme hF hconv hne
  exact TauCeti.isRationalNormalPolyhedron_iff.mpr ⟨Q.activeFace I, hI⟩

/-- Every convex extreme subset of a polyhedron with rational normals and
rational offsets has both properties. No rational exposing functional is assumed. -/
theorem IsExtreme.isRationalPolyhedron {N V : Type*} [AddCommGroup N] [AddCommGroup V]
    [Module ℝ V] [TopologicalSpace V] {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
    {P F : Set V} (hF : IsExtreme ℝ P F) (hP : TauCeti.IsRationalPolyhedron h P)
    (hconv : Convex ℝ F) : TauCeti.IsRationalPolyhedron h F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact .empty h
  obtain ⟨Q, rfl, hQ⟩ := TauCeti.isRationalPolyhedron_iff.mp hP
  obtain ⟨I, hI⟩ := Q.exists_activeFace_of_isExtreme hF hconv hne
  exact TauCeti.isRationalPolyhedron_iff.mpr
    ⟨Q.activeFace I, hI,
      (TauCeti.RationalAffinePolyhedron.hasRationalOffsets_activeFace_iff I).mpr hQ⟩
