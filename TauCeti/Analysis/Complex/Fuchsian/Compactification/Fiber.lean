/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Map
public import TauCeti.GroupTheory.DoubleCoset.Fiber

/-!
# Fibres of compactified quotient maps

For a finite-index inclusion of projective subgroups, the map on compactified
quotients has finite fibres. Both the coarse and cusp fibres are covered by the
finite set of subgroup cosets. The same argument works for the boundary action
even though its stabilizers need not be trivial.

Over an interior point `z` the fibre is identified with the orbit space of the stabilizer of
`z` in the larger group acting on the subgroup cosets, which counts it exactly whenever it is
finite; for an infinite fibre both sides of the cardinality formula are zero by the convention
for `Nat.card`. At a free point the stabilizer action is trivial and the count is the subgroup
index; in general stabilizer orbits record exactly which cosets represent the same fibre point.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- Over an interior point, the ordinary orbit fibre is equivalent to the compactified fibre. -/
def orbitFiberEquivCompactifiedFiber (h : Δ ≤ Γ) (p : orbitRel.Quotient Γ ℍ) :
    {q : orbitRel.Quotient Δ ℍ //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) q = p} ≃
    {y : Δ.CompactifiedQuotient //
      compactifiedQuotientMap h y = .ofQuotient p} where
  toFun q := ⟨CompactifiedQuotient.ofQuotient q.1, by
    simpa only [compactifiedQuotientMap_ofQuotient] using
      congrArg CompactifiedQuotient.ofQuotient q.2
  ⟩
  invFun y := by
    obtain ⟨y, hy⟩ := y
    cases y with
    | ofQuotient p =>
        simp only [compactifiedQuotientMap_ofQuotient] at hy
        exact ⟨p, CompactifiedQuotient.ofQuotient.inj hy⟩
    | ofCusp C =>
        simp only [compactifiedQuotientMap_ofCusp] at hy
        cases hy
  left_inv q := by cases q; rfl
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    cases y with
    | ofQuotient p => rfl
    | ofCusp C =>
        simp only [compactifiedQuotientMap_ofCusp] at hy
        cases hy

/-- The interior-fibre equivalence inserts an ordinary orbit into the compactification. -/
@[simp]
theorem orbitFiberEquivCompactifiedFiber_apply (h : Δ ≤ Γ)
    (p : orbitRel.Quotient Γ ℍ)
    (q : {q : orbitRel.Quotient Δ ℍ //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) q = p}) :
    (orbitFiberEquivCompactifiedFiber h p q).1 = .ofQuotient q.1 :=
  (rfl)

/-- The fibre of a compactified Fuchsian quotient map over the interior orbit of `z` is the
orbit space of the stabilizer of `z` acting on the subgroup cosets. -/
noncomputable def stabilizerOrbitRelQuotientEquivCompactifiedFiber (h : Δ ≤ Γ) (z : ℍ) :
    orbitRel.Quotient (stabilizer Γ z) (Γ ⧸ Δ.subgroupOf Γ) ≃
      {y : Δ.CompactifiedQuotient //
        compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)} :=
  (TauCeti.stabilizerOrbitRelQuotientEquivOrbitRelMapFiber h z).trans
    (orbitFiberEquivCompactifiedFiber h (Quotient.mk'' z))

/-- The stabilizer-orbit equivalence sends the orbit of a coset to the compactified point
represented by the corresponding inverse translate of `z`. -/
@[simp]
theorem stabilizerOrbitRelQuotientEquivCompactifiedFiber_mk (h : Δ ≤ Γ) (z : ℍ)
    (q : Γ ⧸ Δ.subgroupOf Γ) :
    (stabilizerOrbitRelQuotientEquivCompactifiedFiber h z (Quotient.mk'' q)).1 =
      .ofQuotient (TauCeti.orbitOfCosetTranslate z q) := by
  simp [stabilizerOrbitRelQuotientEquivCompactifiedFiber]

/-- The cardinality of a compactified interior fibre is the number of stabilizer-orbits on
the subgroup coset space. In particular, this counts elliptic fibres without treating the
quotient map as a covering at a ramified point. -/
theorem card_fiber_compactifiedQuotientMap_eq_card_stabilizerOrbitRelQuotient
    (h : Δ ≤ Γ) (z : ℍ) :
    Nat.card {y : Δ.CompactifiedQuotient //
      compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)} =
      Nat.card (orbitRel.Quotient (stabilizer Γ z) (Γ ⧸ Δ.subgroupOf Γ)) :=
  Nat.card_congr (stabilizerOrbitRelQuotientEquivCompactifiedFiber h z).symm

variable (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]

/-- A finite-index inclusion induces a map with finite fibres on cusp orbits. -/
theorem finite_fiber_cuspOrbitMap (C : Γ.CuspOrbit) :
    Finite {D : Δ.CuspOrbit // cuspOrbitMap h D = C} := by
  have : Finite {q : Δ.BoundaryOrbit //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le
        (X := OnePoint ℝ) h) q = C.1} :=
    TauCeti.finite_fiber_orbitRel_map_of_isFiniteRelIndex h C.1
  let f : {D : Δ.CuspOrbit // cuspOrbitMap h D = C} →
      {q : Δ.BoundaryOrbit //
        Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le
          (X := OnePoint ℝ) h) q = C.1} :=
    fun D => ⟨D.1.1, by simpa only [cuspOrbitMap_val] using congrArg Subtype.val D.2⟩
  apply Finite.of_injective f
  intro D E hDE
  have hval : D.1.1 = E.1.1 :=
    congrArg (fun q : {q : Δ.BoundaryOrbit //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le
        (X := OnePoint ℝ) h) q = C.1} => q.1) hDE
  exact Subtype.ext (Subtype.ext hval)

/-- Every fibre of the map of compactified quotients for a finite-index inclusion is finite. -/
theorem finite_fiber_compactifiedQuotientMap (x : Γ.CompactifiedQuotient) :
    Finite {y : Δ.CompactifiedQuotient // compactifiedQuotientMap h y = x} := by
  cases x with
  | ofQuotient p =>
      have := TauCeti.finite_fiber_orbitRel_map_of_isFiniteRelIndex h p
      exact Finite.of_equiv _ (orbitFiberEquivCompactifiedFiber h p)
  | ofCusp C =>
      have := finite_fiber_cuspOrbitMap h C
      let f : {y : Δ.CompactifiedQuotient //
          compactifiedQuotientMap h y = .ofCusp C} →
          {D : Δ.CuspOrbit // cuspOrbitMap h D = C} := fun y => by
        obtain ⟨y, hy⟩ := y
        cases y with
        | ofQuotient q =>
            simp only [compactifiedQuotientMap_ofQuotient] at hy
            cases hy
        | ofCusp D =>
            simp only [compactifiedQuotientMap_ofCusp] at hy
            exact ⟨D, CompactifiedQuotient.ofCusp.inj hy⟩
      apply Finite.of_injective f
      intro y z hyz
      obtain ⟨y, hy⟩ := y
      obtain ⟨z, hz⟩ := z
      cases y with
      | ofQuotient q =>
          simp only [compactifiedQuotientMap_ofQuotient] at hy
          cases hy
      | ofCusp D =>
          cases z with
          | ofQuotient q =>
              simp only [compactifiedQuotientMap_ofQuotient] at hz
              cases hz
          | ofCusp E =>
              apply Subtype.ext
              exact congrArg CompactifiedQuotient.ofCusp
                (congrArg Subtype.val hyz)

end Subgroup
