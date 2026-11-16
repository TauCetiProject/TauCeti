/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Contractible
public import TauCeti.AlgebraicTopology.Singular.DiskSphere
public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative

/-!
# Relative homology with local coefficients of a pair with contractible ambient space

Let `(X, A)` be a pair whose ambient space `X` is contractible. Every local coefficient system `L`
on `X` is then constant: a contraction `H` of `X` onto a point `x` identifies `L` with the
constant system at its fibre `L x` (`TauCeti.LocalCoefficientSystem.isoConstantOfHomotopy`). So
relative homology with coefficients in `L` is ordinary relative singular homology with coefficients
in `L x` (`TopPair.twistedHomologyIsoOfHomotopy`).

For the disk pair `(Dⁿ, Sⁿ⁻¹)` this carries over the vanishing outside degree `n`:
`Hₖ(Dⁿ, Sⁿ⁻¹; L) = 0` for `k ≠ n` (`TopPair.isZero_twistedHomology_diskBoundaryPair_of_ne`). This is
the disk computation behind cellular homology with local coefficients, where the characteristic
maps of the `n`-cells of a CW complex identify the relative homology of consecutive skeleta with
that of a disjoint union of disk pairs.

## Main results

* `TopPair.twistedHomologyIsoOfHomotopy`: `Hₖ(X, A; L) ≅ Hₖ(X, A; L x)` for a contraction of `X`
  onto `x`.
* `TopPair.isZero_twistedHomology_diskBoundaryPair_of_ne`: `Hₖ(Dⁿ, Sⁿ⁻¹; L) = 0` for `k ≠ n`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Corollary 2.24, and Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti TauCeti.LocalCoefficientSystem

universe u v w

namespace TopPair

variable {R : Type u} [Ring R]

/-- **Relative homology with local coefficients of a pair with contractible ambient space**: a
homotopy `H` from the identity of the ambient space `X` to the constant map at `x` identifies
`Hₖ(X, A; L)` with the ordinary relative singular homology `Hₖ(X, A; L x)`, through the
identification of `L` with the constant system at `L x` by transport along the paths traced by
`H`. -/
def twistedHomologyIsoOfHomotopy (P : TopPair.{v}) {x : P.fst}
    (H : (ContinuousMap.id P.fst).Homotopy (ContinuousMap.const P.fst x))
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (k : ℕ) :
    P.twistedHomology L k ≅ P.singularHomology (L.obj (FundamentalGroupoid.mk x)) k :=
  asIso (P.twistedHomologyCoefficientMap (isoConstantOfHomotopy H L).hom k) ≪≫
    P.twistedHomologyConstantIso _ k

/-- `TopPair.twistedHomologyIsoOfHomotopy` is the change of coefficients along the identification
of `L` with a constant system, followed by the comparison of relative twisted homology with
constant coefficients and ordinary relative singular homology. -/
lemma twistedHomologyIsoOfHomotopy_hom (P : TopPair.{v}) {x : P.fst}
    (H : (ContinuousMap.id P.fst).Homotopy (ContinuousMap.const P.fst x))
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (k : ℕ) :
    (P.twistedHomologyIsoOfHomotopy H L k).hom =
      P.twistedHomologyCoefficientMap (isoConstantOfHomotopy H L).hom k ≫
        (P.twistedHomologyConstantIso _ k).hom :=
  (rfl)

/-- **The relative homology of a disk with local coefficients vanishes outside its dimension**:
`Hₖ(Dⁿ, Sⁿ⁻¹; L) = 0` for `k ≠ n` and every local coefficient system `L` on `Dⁿ`. -/
theorem isZero_twistedHomology_diskBoundaryPair_of_ne {n k : ℕ} (hk : k ≠ n)
    (L : LocalCoefficientSystem.{u, v, max v w} R (diskBoundaryPair.{v} n).fst) :
    IsZero ((diskBoundaryPair.{v} n).twistedHomology L k) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic (diskBoundaryPair.{v} n).fst
  exact (isZero_singularHomology_diskBoundaryPair_of_ne _ hk).of_iso
    ((diskBoundaryPair.{v} n).twistedHomologyIsoOfHomotopy H L k)

end TopPair
