/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SurfaceGroup.Basic
import TauCeti.GroupTheory.FreeGroup.Centralizer
import TauCeti.GroupTheory.HNNExtension.Torsion
import TauCeti.GroupTheory.SurfaceGroup.HNN
import TauCeti.GroupTheory.SurfaceGroup.LowGenus

/-!
# Orientable surface groups are torsion-free

Every orientable surface group `S⁺(g, m)` is torsion-free. With nonempty boundary, `m ≥ 1`, the
group is free. The sphere group `S⁺(0, 0)` is trivial. A closed orientable surface of genus
`g + 1 ≥ 1`, that is of Euler characteristic `χ ≤ 0`, is cut by a non-separating simple closed
curve into a surface of genus `g` with two boundary circles, so that `S⁺(g + 1, 0)` is an HNN
extension of the free group `S⁺(g, 2)` (`TauCeti.SurfaceGroup.Orientable.equivHNNExtension`): the
fundamental group of a loop of groups with a free vertex group. A finite subgroup of the
fundamental group of a graph of groups fixes a vertex of the Bass–Serre tree, hence lies in a
conjugate of a vertex group, so an HNN extension of a torsion-free group is torsion-free
(`HNNExtension.instIsMulTorsionFree`).

For nonorientable surfaces the condition `χ ≤ 0` matters: the group `S⁻(1, 0)` of the projective
plane, of Euler characteristic `1`, has order two
(`TauCeti.SurfaceGroup.Nonorientable.projectivePlaneEquiv`). The closed nonorientable surface
groups `S⁻(g, 0)` with `g ≥ 2` are torsion-free too, being amalgams of free groups over `ℤ`, but
are not treated in this file.

## Main results

* `TauCeti.SurfaceGroup.Orientable.instIsMulTorsionFree`: `S⁺(g, m)` is torsion-free.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.2, p. 16
  (finite groups fix a point in every tree) and §5.1.2 (cyclic splittings of surface groups dual
  to simple closed curves).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, §1.B, Example 1B.14, and §2.2, Proposition 2.45 (closed
  surfaces other than the sphere and the projective plane have torsion-free fundamental group).
* J.-P. Serre, *Trees*, Springer, 1980, Chapter I, §5.1 and §6.5.
-/

public section

namespace TauCeti

namespace SurfaceGroup

namespace Orientable

/-- **Orientable surface groups are torsion-free.** Every orientable surface group `S⁺(g, m)` is
torsion-free; in particular so is every closed orientable surface group `S⁺(g, 0)`. -/
instance instIsMulTorsionFree (g m : ℕ) : IsMulTorsionFree (Orientable g m) :=
  match g, m with
  -- The sphere group is trivial and a surface group with boundary is free.
  | 0, 0 | 0, _ + 1 => inferInstance
  -- A closed or bordered surface of positive genus is an HNN extension of a free group.
  | g + 1, m =>
    (equivHNNExtension g m).injective.isMulTorsionFree (equivHNNExtension g m).toMonoidHom

end Orientable

end SurfaceGroup

end TauCeti
