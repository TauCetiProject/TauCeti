/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Augmentation
public import TauCeti.Topology.PathSpace.Moore.From

/-!
# The chains on the based path space as a left module over the loop algebra

For a pointed space `(B, b)`, the Moore loops at `b` act on the Moore paths starting at `b` by
concatenation in front (`TauCeti.MoorePathFrom`). So the normalized cubical chains `C_*(P_b B; R)`
form a differential graded **left** module over the DG algebra `C_*(Ω_b B; R)`
(`TauCeti.pathFromChain_isDGLeftModule`).

The based path space is contractible, by truncation of paths
(`TauCeti.MoorePathFrom.truncateHomotopy`). Hence the augmentation `ε : C_*(P_b B; R) → R` is a
quasi-isomorphism onto `R` with the action of `C_*(Ω_b B; R)` through its augmentation:

* it is linear over the augmentation of the loop algebra,
  `ε (a · m) = ε(a) ε(m)` (`TauCeti.pathFromChainAugmentation_smul`);
* it vanishes on boundaries (`TauCeti.cubicalChainModuleAugmentation_differential`) and is onto
  (`TauCeti.cubicalChainModuleAugmentation_surjective`);
* a cycle of augmentation zero is a boundary
  (`TauCeti.exists_pathFromChainDifferential_eq_of_augmentation_eq_zero`).

The contracting homotopy is the cone along the truncation homotopy
(`TauCeti.cubicalChainModuleCone`). It is linear over `R` but not over `C_*(Ω_b B; R)`, since
truncation does not commute with concatenation in front.

This is the augmentation of the path fibration `Ω_b B → P_b B → B` against which a semi-free
resolution of `R` over `C_*(Ω_b B; R)` is compared, as in Brown's twisted tensor products.

The monoid `H` is the phantom parameter of `TauCeti.cubicalChainModule`: no monoid acts on the free
end point of a path from `b`, and it plays no role.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
-/

public section

namespace TauCeti

variable (B : Type*) [TopologicalSpace B] (b : B) (H : Type*) (R : Type*) [CommRing R]

/-- **The chains on the Moore paths from `b` form a differential graded left module over
`C_*(Ω_b B; R)`**: the loops at `b` act by concatenation in front, the chains of dimension `n` lie
in cohomological degree `-n`, and the boundary is the differential. -/
theorem pathFromChain_isDGLeftModule :
    IsDGLeftModule (loopChain_isDGAlgebra B b R)
      (cubicalChainModuleGrading (MoorePathFrom B b) H R)
      (cubicalChainModuleDifferential (MoorePathFrom B b) H R) :=
  cubicalChainModule_isDGLeftModule (MooreLoopSpace B b) (MoorePathFrom B b) H R

variable {B b H R}

/-- **The augmentation of the chains on the based path space is linear over the augmentation of
the loop algebra**: `ε (a · m) = ε(a) ε(m)`. -/
theorem pathFromChainAugmentation_smul (a : loopChainAlgebra B b R)
    (m : cubicalChainModule (MoorePathFrom B b) H R) :
    cubicalChainModuleAugmentation (MoorePathFrom B b) H R (a • m) =
      loopChainAugmentation B b R a * cubicalChainModuleAugmentation (MoorePathFrom B b) H R m := by
  rw [loopChainAugmentation_def]
  exact cubicalChainModuleAugmentation_smul a m

/-- **The augmented chains on the based path space are acyclic**: a cycle of `C_*(P_b B; R)` of
augmentation zero is a boundary. -/
theorem exists_pathFromChainDifferential_eq_of_augmentation_eq_zero
    {m : cubicalChainModule (MoorePathFrom B b) H R}
    (hd : cubicalChainModuleDifferential (MoorePathFrom B b) H R m = 0)
    (hε : cubicalChainModuleAugmentation (MoorePathFrom B b) H R m = 0) :
    ∃ n, cubicalChainModuleDifferential (MoorePathFrom B b) H R n = m :=
  exists_cubicalChainModuleDifferential_eq_of_augmentation_eq_zero hd hε

end TauCeti
