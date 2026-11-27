/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Finiteness
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# The topological degree after extension of the base field

Let `K'/K` be a field extension and `X' = X ×_K K'`, `Y' = Y ×_K K'` the base changes of integral
schemes `X`, `Y` locally of finite type over `K`, given by cartesian squares (Mathlib's
`CategoryTheory.IsPullback`) along `Spec K' ⟶ Spec K`, with `X'` and `Y'` integral (as when `X`
and `Y` are geometrically integral). For a dominant `K`-rational map `f : X ⤏ Y` and a dominant
`K'`-rational map `f' : X' ⤏ Y'`, for instance the base change `f_{K'}`, the topological degree
`e(f')` is the junk value `0` exactly when `e(f)` is.

Indeed `e(f) = 0` exactly when `dim X ≠ dim Y`
(`AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_zero_iff`), and extending the base
field does not change the dimension of a scheme locally of finite type over a field
(`TauCeti.AlgebraicGeometry.topologicalKrullDim_pullback_Spec_map_of_field`). In particular
`e(f_{K'}) = e(f)` when `dim X ≠ dim Y`: this is the case of the identity `e(f_{K'}) = e(f)` in
which `K(X)` is infinite-dimensional over `f^*K(Y)` and both degrees are the junk value. When
`dim X = dim Y` both degrees are positive.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_zero_iff_of_isPullback`:
  `e(f') = 0 ↔ e(f) = 0`.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_of_isPullback_of_ne`:
  `e(f') = e(f)` when `dim X ≠ dim Y`.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K']
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [X'.Over (Spec (.of K'))] [Y'.Over (Spec (.of K'))]
  [IsIntegral X] [IsIntegral Y] [IsIntegral X'] [IsIntegral Y']
  [LocallyOfFiniteType (X ↘ Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))]
  {πX : X' ⟶ X} {πY : Y' ⟶ Y}
  (hX : IsPullback πX (X' ↘ Spec (.of K')) (X ↘ Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
  (hY : IsPullback πY (Y' ↘ Spec (.of K')) (Y ↘ Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
  (f : X ⤏ Y) [f.IsDominant] [f.IsOver (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))]
  (f' : X' ⤏ Y') [f'.IsDominant] [f'.IsOver (X' ↘ Spec (.of K')) (Y' ↘ Spec (.of K'))]

include hX hY in
/-- **The junk value of the topological degree is stable under extension of the base field.**
For a dominant `K`-rational map `f : X ⤏ Y` and a dominant `K'`-rational map `f' : X' ⤏ Y'`
between the base changes, for instance the base change `f_{K'}`, `e(f') = 0` exactly when
`e(f) = 0`: both mean `dim X ≠ dim Y`. -/
theorem RationalMap.topologicalDegree_eq_zero_iff_of_isPullback :
    f'.topologicalDegree = 0 ↔ f.topologicalDegree = 0 := by
  have : LocallyOfFiniteType (X' ↘ Spec (.of K')) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hX inferInstance
  have : LocallyOfFiniteType (Y' ↘ Spec (.of K')) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hY inferInstance
  rw [topologicalDegree_eq_zero_iff K' f', topologicalDegree_eq_zero_iff K f,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_isPullback_Spec_map_of_field hX,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_isPullback_Spec_map_of_field hY]

include hX hY in
/-- **`e(f_{K'}) = e(f)` when the dimensions differ.** If `dim X ≠ dim Y`, then a dominant
`K'`-rational map `f'` between the base changes, for instance the base change `f_{K'}`, has the
topological degree of `f`: both are the junk value `0`. -/
theorem RationalMap.topologicalDegree_eq_of_isPullback_of_ne
    (h : topologicalKrullDim X ≠ topologicalKrullDim Y) :
    f'.topologicalDegree = f.topologicalDegree := by
  have hf : f.topologicalDegree = 0 := (topologicalDegree_eq_zero_iff K f).mpr h
  rw [hf, topologicalDegree_eq_zero_iff_of_isPullback hX hY f f', hf]

include hX hY in
/-- **Positivity of the topological degree is stable under extension of the base field.**
`0 < e(f')` exactly when `0 < e(f)`: both mean `dim X = dim Y`. -/
theorem RationalMap.topologicalDegree_pos_iff_of_isPullback :
    0 < f'.topologicalDegree ↔ 0 < f.topologicalDegree := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero,
    Ne, Ne, topologicalDegree_eq_zero_iff_of_isPullback hX hY f f']

end AlgebraicGeometry.Scheme
