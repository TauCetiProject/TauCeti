/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.CompositeCorrespondence.Basic
public import TauCeti.AlgebraicGeometry.Birational.Graph.Degree

/-!
# The topological degree of `(q_Y, q_Z)`

Let `f : X ⤏ Y` be dominant and `g : Y ⤏ Z` a rational map over a separated base `S`, with
`W_{f,g}` the correspondence of the composite and `(q_X, q_Y) : W_{f,g} → Γ_f`,
`(q_Y, q_Z) : W_{f,g} → Γ_g` its morphisms to the graphs. Both composites
`π_2 ∘ (q_X, q_Y)` and `π_1 ∘ (q_Y, q_Z)` are the projection `q_Y`. For integral schemes proper over
`S`, `(q_X, q_Y)` is a modification and `π_1 : Γ_g → Y` has topological degree `1`, while `π_2 :
Γ_f → Y` has topological degree `e(f)`. By multiplicativity, `(q_Y, q_Z)` has topological degree
`e(f)`: its function-field extension is `K(Γ_g) ≅ K(Y) → K(X) ≅ K(W_{f,g})`, which is `f^*`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_compositeCorrespondenceToGraphYZ`:
  `(q_Y, q_Z) : W_{f,g} → Γ_g` has topological degree `e(f)`.

## References

* N.-B. Dang, *Degrees of iterates of rational maps on normal projective varieties*, Proc. London
  Math. Soc. 121 (2020), [arXiv:1701.07760](https://arxiv.org/abs/1701.07760), §5 and
  diagram (5.1).
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
  [IsIntegral X] [IsIntegral Y] [Y.IsSeparated] [Z.IsSeparated]
  (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
  [S.IsSeparated] [f.IsOver sX sY] [(f.comp g).IsOver sX sZ]

/-- **The topological degree of `(q_Y, q_Z)`.** Let `f : X ⤏ Y` be dominant and `g : Y ⤏ Z` a
rational map over a separated base `S`, with `X`, `Y` integral and `X`, `Y`, `Z` proper over `S`.
Assume the inclusion of the open `U = compositeDomain f g` on which `g ∘ f` is defined, the
inclusions of the domains of definition of `f` and `g`, and `γ_f`, `γ_g` quasi-compact (all of
this holds for `X` and `Y` Noetherian). Then
`(q_Y, q_Z) : W_{f,g} → Γ_g` has topological degree `e(f)`. -/
theorem topologicalDegree_compositeCorrespondenceToGraphYZ [IsProper sX] [IsProper sY]
    [IsProper sZ] [QuasiCompact (compositeDomain f g).ι] [QuasiCompact f.domain.ι]
    [QuasiCompact g.domain.ι] [QuasiCompact (graphLift f)] [QuasiCompact (graphLift g)] :
    (compositeCorrespondenceToGraphYZ sX sY sZ f g).toRationalMap.topologicalDegree =
      f.topologicalDegree := by
  have := isModification_compositeCorrespondenceToGraphXY sX sY sZ f g
  -- `π_2 ∘ (q_X, q_Y)` has degree `1 · e(f)`
  have e₁ : (compositeCorrespondenceToGraphXY sX sY sZ f g ≫
      graphSnd f).toRationalMap.topologicalDegree = f.topologicalDegree := by
    rw [Hom.topologicalDegree_comp, IsModification.topologicalDegree_toRationalMap,
      topologicalDegree_graphSnd, one_mul]
  -- `π_1 ∘ (q_Y, q_Z)` has degree `e((q_Y, q_Z)) · 1`
  have e₂ : (compositeCorrespondenceToGraphYZ sX sY sZ f g ≫
      graphFst g).toRationalMap.topologicalDegree =
      (compositeCorrespondenceToGraphYZ sX sY sZ f g).toRationalMap.topologicalDegree := by
    rw [Hom.topologicalDegree_comp, topologicalDegree_graphFst, mul_one]
  rw [← e₂, ← e₁]
  -- both composites are `q_Y`
  exact topologicalDegree_congr (by
    rw [compositeCorrespondenceToGraphYZ_graphFst, compositeCorrespondenceToGraphXY_graphSnd])

end AlgebraicGeometry.Scheme.RationalMap
