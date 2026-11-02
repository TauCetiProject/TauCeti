/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Restricting an orientation to an open subset

An open subset `U` of a manifold `M`, charted by the restrictions of the charts of `M`, includes
into `M` by a local diffeomorphism (`TauCeti.isLocalDiffeomorph_subtype_val`). So every orientation
of `M` pulls back to an orientation of `U` (`TauCeti.Manifold.Orientation.restrict`), the unique
one for which the inclusion preserves orientation.

## Main definitions

* `TauCeti.Manifold.Orientation.restrict`: the restriction of an orientation to an open subset.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict`: the inclusion of the open
  subset preserves orientation from the restriction.
* `TauCeti.Manifold.Orientation.eq_restrict_iff`: this property characterizes the restriction.
* `TauCeti.Manifold.Orientation.restrict_neg`: restriction commutes with taking the opposite
  orientation.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {ι : Type*} [Fintype ι]

/-- The restriction of an orientation of `M` to the open subset `U`: its pullback along the
inclusion `U → M`. -/
def restrict (o : Orientation I M ι) (U : Opens M) : Orientation I U ι :=
  o.pullback contMDiff_subtype_val
    (fun x ↦ (isLocalDiffeomorph_subtype_val (n := 1) x).isInvertible_mfderiv one_ne_zero)
    o.card_eq

/-- The inclusion of an open subset preserves orientation from the restricted orientation. -/
@[simp]
theorem isOrientationPreservingAt_restrict (o : Orientation I M ι) (U : Opens M) (x : U) :
    IsOrientationPreservingAt (o.restrict U) o Subtype.val x :=
  isOrientationPreservingAt_pullback _ _ _ _ x

/-- Restricting the opposite orientation gives the opposite of the restriction. -/
@[simp]
theorem restrict_neg (o : Orientation I M ι) (U : Opens M) : (-o).restrict U = -o.restrict U :=
  pullback_neg ..

/-- The restriction is the only orientation of `U` from which the inclusion into `M` preserves
orientation at every point. -/
theorem eq_restrict_iff {o : Orientation I M ι} {U : Opens M} {o' : Orientation I U ι} :
    o' = o.restrict U ↔ ∀ x, IsOrientationPreservingAt o' o Subtype.val x :=
  eq_pullback_iff _ _ _ _

end TauCeti.Manifold.Orientation
