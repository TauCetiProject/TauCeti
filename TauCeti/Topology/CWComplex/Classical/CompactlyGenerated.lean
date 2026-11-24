/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.DeltaGenerated
public import TauCeti.Topology.Convenient.CompactlyGenerated

/-!
# Compact generation of relative CW complexes

Every Hausdorff relative CW complex over a `u`-compactly generated base is `u`-compactly generated
for every universe `u` (`TauCeti.uCompactlyGeneratedSpace_of_relCWComplex`), generalizing the
delta-generated base case (`TauCeti.deltaGeneratedSpace_of_relCWComplex`) to arbitrary
`u`-compactly generated bases.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Proposition A.2.
-/

public section

universe u w

open Topology

/-- A Hausdorff relative CW complex over a `u`-compactly generated base is `u`-compactly generated
for every test universe `u`. -/
theorem TauCeti.uCompactlyGeneratedSpace_of_relCWComplex {X : Type w} [TopologicalSpace X]
    [T2Space X] {C D : Set X} [RelCWComplex C D] [UCompactlyGeneratedSpace.{u} D] :
    UCompactlyGeneratedSpace.{u} C :=
  (Topology.isGeneratedBy_compHaus_iff.{u} C).1 isQuotientMap_sumElim_base_map.isGeneratedBy

end
