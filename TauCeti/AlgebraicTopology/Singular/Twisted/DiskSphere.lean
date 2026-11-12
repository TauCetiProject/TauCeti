/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DiskSphere
public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative

/-!
# Relative homology of a disk with local coefficients

The disk `Dⁿ` is contractible, so every local coefficient system `L` on it is constant
(`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy`), and the relative homology of the disk
pair `(Dⁿ, Sⁿ⁻¹)` with coefficients in `L` is ordinary relative singular homology with coefficients
in a fibre of `L` (`TopPair.twistedHomologyIsoOfHomotopy`). This carries over the vanishing outside
degree `n`: `Hₖ(Dⁿ, Sⁿ⁻¹; L) = 0` for `k ≠ n`. This is the disk computation behind cellular
homology with local coefficients, where the characteristic maps of the `n`-cells of a CW complex
identify the relative homology of consecutive skeleta with that of a disjoint union of disk pairs.

## Main results

* `TauCeti.isZero_twistedHomology_diskBoundaryPair_of_ne`: `Hₖ(Dⁿ, Sⁿ⁻¹; L) = 0` for `k ≠ n`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Corollary 2.24, and Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti

variable {R : Type u} [Ring R]

/-- **The relative homology of a disk with local coefficients vanishes outside its dimension**:
`Hₖ(Dⁿ, Sⁿ⁻¹; L) = 0` for `k ≠ n` and every local coefficient system `L` on `Dⁿ`. -/
theorem isZero_twistedHomology_diskBoundaryPair_of_ne {n k : ℕ} (hk : k ≠ n)
    (L : LocalCoefficientSystem.{u, v, max v w} R (diskBoundaryPair.{v} n).fst) :
    IsZero ((diskBoundaryPair.{v} n).twistedHomology L k) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic (diskBoundaryPair.{v} n).fst
  exact (isZero_singularHomology_diskBoundaryPair_of_ne _ hk).of_iso
    ((diskBoundaryPair.{v} n).twistedHomologyIsoOfHomotopy L H k)

end TauCeti
