/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.TorusAction

/-!
# Compactness of toric projective space

The fan of projective space `TauCeti.Toric.Fan.projectiveSpace` is regular and complete. Its
analytic realization, the space glued from the affine toric charts of its cones, is therefore
compact. So are the complex points of its fan scheme, with their affine-chart topology, through
the algebraic–analytic comparison.

## Main declarations

* `TauCeti.Toric.Fan.compactSpace_analyticRealization_projectiveSpace`: the analytic realization
  of the fan of projective space is compact.
* `TauCeti.Toric.Fan.compactSpace_algebraicComplexPoint_projectiveSpace`: the complex points of
  the scheme of the fan of projective space form a compact space.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

namespace TauCeti.Toric.Fan

universe u

/-- The analytic realization of the fan of projective space is compact. -/
instance compactSpace_analyticRealization_projectiveSpace {N V ι : Type u} [AddCommGroup N]
    [AddCommGroup V] [Module ℝ V] {i : N →+ V} [Fintype ι] (b : Module.Basis ι ℤ N)
    (hi : IsIntegralLattice i) :
    CompactSpace ((projectiveSpace b hi).analyticRealization (isRegular_projectiveSpace b hi)) :=
  compactSpace_analyticRealization_of_isComplete _ _ (isComplete_projectiveSpace b hi)

/-- The complex points of the scheme of the fan of projective space, with the topology glued from
the affine charts, form a compact space. -/
instance compactSpace_algebraicComplexPoint_projectiveSpace {N V ι : Type} [AddCommGroup N]
    [AddCommGroup V] [Module ℝ V] {i : N →+ V} [Fintype ι] (b : Module.Basis ι ℤ N)
    (hi : IsIntegralLattice i) : CompactSpace (projectiveSpace b hi).AlgebraicComplexPoint :=
  (compactSpace_algebraicComplexPoint_iff_isComplete (isRegular_projectiveSpace b hi)
    ⟨⟨⊥, bot_mem_projectiveSpace_cones b hi⟩⟩).2 (isComplete_projectiveSpace b hi)

end TauCeti.Toric.Fan
