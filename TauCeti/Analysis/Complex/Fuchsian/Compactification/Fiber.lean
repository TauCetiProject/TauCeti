/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Map
public import TauCeti.GroupTheory.DoubleCoset.Fiber

/-!
# Finite fibres of compactified quotient maps

For a finite-index inclusion of projective subgroups, the map on compactified
quotients has finite fibres. Both the coarse and cusp fibres are covered by the
finite set of subgroup cosets. The same argument works for the boundary action
even though its stabilizers need not be trivial.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)} (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]

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
      let f : {y : Δ.CompactifiedQuotient //
          compactifiedQuotientMap h y = .ofQuotient p} →
          {q : orbitRel.Quotient Δ ℍ //
            Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) q = p} :=
        fun y => by
          obtain ⟨y, hy⟩ := y
          cases y with
          | ofQuotient q =>
              simp only [compactifiedQuotientMap_ofQuotient] at hy
              exact ⟨q, CompactifiedQuotient.ofQuotient.inj hy⟩
          | ofCusp C =>
              simp only [compactifiedQuotientMap_ofCusp] at hy
              cases hy
      apply Finite.of_injective f
      intro y z hyz
      obtain ⟨y, hy⟩ := y
      obtain ⟨z, hz⟩ := z
      cases y with
      | ofQuotient q =>
          cases z with
          | ofQuotient r =>
              apply Subtype.ext
              exact congrArg CompactifiedQuotient.ofQuotient
                (congrArg Subtype.val hyz)
          | ofCusp C =>
              simp only [compactifiedQuotientMap_ofCusp] at hz
              cases hz
      | ofCusp C =>
          simp only [compactifiedQuotientMap_ofCusp] at hy
          cases hy
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
