/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.ProjectiveLine
public import TauCeti.Geometry.Toric.Analytic.Fan.Compact
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Proper

/-!
# Compactness and properness of the projective-line fan realization

The two standard rank-one rays cover the real line. The completeness criterion therefore makes
their regular fan's analytic realization compact, as expected of the projective line. The collapse
of this fan to the zero-dimensional fan is proper by the cone-by-cone criterion.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.3--3.4.
-/

public section

namespace TauCeti.Toric

/-- The fan of a point, on the zero-dimensional lattice. -/
abbrev toricPointFan : Fan ((Int.castAddHom ℝ).compLeft (Fin 0)) :=
  Fan.ofCone (isIntegralLattice_intCast 0)
    (isToricCone_bot ((Int.castAddHom ℝ).compLeft (Fin 0)))

/-- The fan of a point is regular. -/
theorem isRegular_toricPointFan : toricPointFan.IsRegular :=
  Fan.isRegular_ofCone (isIntegralLattice_intCast 0)
    (isRegularCone_bot (isIntegralLattice_intCast 0))

/-- The morphism from the projective-line fan to the fan of a point. -/
noncomputable def projectiveLineFanToPoint :
    FanHom projectiveLineFan toricPointFan :=
  FanHom.ofLatticeMap projectiveLineFan toricPointFan
    (0 : (Fin 1 → ℤ) →+ (Fin 0 → ℤ)) <| by
      intro σ hσ
      refine ⟨⊥, ?_, ?_⟩
      · exact (Fan.mem_ofCone_cones (isIntegralLattice_intCast 0)
          (isToricCone_bot ((Int.castAddHom ℝ).compLeft (Fin 0)))).2
          (PointedCone.IsFaceOf.refl _)
      · have hzero : projectiveLineFan.lattice.extend
            ((Int.castAddHom ℝ).compLeft (Fin 0))
            (0 : (Fin 1 → ℤ) →+ (Fin 0 → ℤ)) = 0 := by
          symm
          apply projectiveLineFan.lattice.eq_extend
          intro n
          exact Subsingleton.elim _ _
        rw [hzero]
        simp

/-- The toric map from the projective-line fan to a point is proper. -/
theorem isProperMap_projectiveLineFanToPoint :
    IsProperMap
      (projectiveLineFanToPoint.analyticMap isRegular_projectiveLineFan
        isRegular_toricPointFan) := by
  apply (projectiveLineFanToPoint.isProperMap_analyticMap_iff
    isRegular_projectiveLineFan isRegular_toricPointFan ⟨affineRayCone,
      affineRayCone_mem_projectiveLineFan⟩).2
  intro τ
  have hτ : (τ.1 : PointedCone ℝ (Fin 0 → ℝ)) = ⊥ := Subsingleton.elim _ _
  rw [hτ]
  have hreal : projectiveLineFanToPoint.realMap = 0 := by
    rw [projectiveLineFanToPoint, FanHom.ofLatticeMap_realMap]
    symm
    apply projectiveLineFan.lattice.eq_extend
    intro n
    exact Subsingleton.elim _ _
  ext x
  rw [hreal]
  constructor
  · intro _
    obtain ⟨σ, hσ, hx⟩ :=
      (projectiveLineFan.isComplete_iff.mp isComplete_projectiveLineFan) x
    refine Set.mem_iUnion.2 ⟨⟨σ, hσ⟩, Set.mem_iUnion.2 ⟨?_, hx⟩⟩
    simp
  · intro _
    simp

/-- The analytic realization of the standard complete rank-one fan is compact. -/
theorem compactSpace_projectiveLineFan_analyticRealization :
    CompactSpace (projectiveLineFan.analyticRealization isRegular_projectiveLineFan) :=
  projectiveLineFan.compactSpace_analyticRealization_of_isComplete
    isRegular_projectiveLineFan isComplete_projectiveLineFan

end TauCeti.Toric
