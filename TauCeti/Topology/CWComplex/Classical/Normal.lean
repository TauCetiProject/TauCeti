/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Separation.Regular
import TauCeti.Topology.CWComplex.Abstract.Normal
import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex

/-!
# Classical CW complexes are normal

Every classical relative CW complex `C` in a Hausdorff space over a normal base `D` is a normal
topological space (`TauCeti.normalSpace_of_relCWComplex`); in particular every classical CW complex
in a Hausdorff space is normal (`TauCeti.instNormalSpaceCWComplex` and
`TauCeti.instNormalSpaceOfCWComplexUniv`).

Passing to the categorical presentation `TauCeti.toRelativeCWComplex C` expresses `C` as the
sequential colimit of its skeleta `skeletonLT C n`, each obtained from the previous one by
attaching Euclidean disks along their boundary spheres, so `TopCat.RelativeCWComplex.normalSpace`
applies directly.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Proposition A.3.
-/

public section

open Set Topology

universe u

namespace TauCeti

/-- **A classical relative CW complex in a Hausdorff space over a normal base is normal.** -/
theorem normalSpace_of_relCWComplex {X : Type u} [TopologicalSpace X] {C D : Set X}
    [RelCWComplex C D] [T2Space X] [NormalSpace D] : NormalSpace C :=
  (toRelativeCWComplex C).normalSpace

/-- **Every classical CW complex in a Hausdorff space is a normal space.** -/
instance instNormalSpaceCWComplex {X : Type u} [TopologicalSpace X] {C : Set X}
    [CWComplex C] [T2Space X] : NormalSpace C :=
  normalSpace_of_relCWComplex (D := ∅)

/-- **Every Hausdorff space carrying a classical CW structure on `Set.univ` is a normal space.** -/
instance instNormalSpaceOfCWComplexUniv {X : Type u} [TopologicalSpace X]
    [CWComplex (univ : Set X)] [T2Space X] : NormalSpace X :=
  (Homeomorph.Set.univ X).normalSpace

end TauCeti
