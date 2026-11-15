/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Coproduct
public import TauCeti.AlgebraicTopology.Singular.Twisted.Additivity.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.Contractible

/-!
# Skeletal pairs of a CW complex with local coefficients

For a relative CW complex with skeleta `Xⁿ` and a local coefficient system `L` on `Xⁿ`, the
relative homology `Hₖ(Xⁿ, Xⁿ⁻¹; L)` vanishes for `k ≠ n`
(`TauCeti.isZero_twistedHomology_skeletonPair_of_ne`). The characteristic maps of the `n`-cells
identify it with the relative homology of the disjoint union `∐ⱼ (Dⁿ, Sⁿ⁻¹)` of disk pairs, with the
pulled-back system (`TauCeti.isIso_twistedHomologyMap_characteristicPairMap`). Relative twisted
homology is additive, so this is the coproduct of the groups `Hₖ(Dⁿ, Sⁿ⁻¹; Lⱼ)` of the single
disks, and each of these vanishes for `k ≠ n` because a local system on a disk is constant
(`TopPair.isZero_twistedHomology_diskBoundaryPair_of_ne`).

As for constant coefficients (`TauCeti.isZero_singularHomology_skeletonPair_of_ne`), this
vanishing is what makes the groups `Hₙ(Xⁿ, Xⁿ⁻¹; L)`, for `L` restricted from a local system on
the whole complex, with the connecting morphisms of the triples of consecutive skeleta, a chain
complex whose homology is the homology of the complex with coefficients in that system. For a
fibration over a CW complex and the local system of fibre homology, that homology is the second
page of its Serre spectral sequence.

## Main results

* `TauCeti.isZero_twistedHomology_sigmaDiskPair_of_ne`: `Hₖ(∐ᵢ (Dⁿ, Sⁿ⁻¹); L) = 0` for `k ≠ n`.
* `TauCeti.isZero_twistedHomology_skeletonPair_of_ne`: `Hₖ(Xⁿ, Xⁿ⁻¹; L) = 0` for `k ≠ n`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Lemma 2.34, and Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex TauCeti.LocalCoefficientSystem

universe w v u

namespace TauCeti

variable {R : Type u} [Ring R]

/-- **The relative homology of a disjoint union of disk pairs with local coefficients vanishes
outside their dimension**: `Hₖ(∐ᵢ (Dⁿ, Sⁿ⁻¹); L) = 0` for `k ≠ n` and every local coefficient
system `L` on `∐ᵢ Dⁿ`. -/
theorem isZero_twistedHomology_sigmaDiskPair_of_ne (ι : Type w) {n k : ℕ} (hk : k ≠ n)
    (L : LocalCoefficientSystem.{u, w, max w v} R (sigmaDiskPair ι n).fst) :
    IsZero ((sigmaDiskPair ι n).twistedHomology L k) := by
  let e := sigmaDiskBoundaryPairIso ι n
  -- On the disjoint union of the Euclidean disk pairs, use additivity and the single disks.
  have h : IsZero ((TopPair.sigma fun _ : ι ↦ diskBoundaryPair.{w} n).twistedHomology
      ((LocalCoefficientSystem.pullback (TopPair.Hom.fst e.hom).hom).obj L) k) :=
    (TopPair.isColimitCofanTwistedHomology _ _ k).isZero_pt
      (Functor.isZero _ fun _ ↦ TopPair.isZero_twistedHomology_diskBoundaryPair_of_ne hk _)
  have : IsIso (TopPair.twistedHomologyMap e.hom L k) :=
    isIso_relativeTwistedHomologyMap_of_homotopyInverse L e.hom e.inv
      ⟨e.hom_inv_id ▸ TopPair.Homotopy.refl _⟩ ⟨e.inv_hom_id ▸ TopPair.Homotopy.refl _⟩ k
  exact h.of_iso (asIso (TopPair.twistedHomologyMap e.hom L k)).symm

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- **The relative homology of consecutive skeleta with local coefficients vanishes outside their
dimension**: `Hₖ(Xⁿ, Xⁿ⁻¹; L) = 0` for `k ≠ n` and every local coefficient system `L` on the
`n`-skeleton `Xⁿ`. -/
theorem isZero_twistedHomology_skeletonPair_of_ne {n k : ℕ} (hk : k ≠ n)
    (L : LocalCoefficientSystem.{u, w, max w v} R (skeletonPair C n).fst) :
    IsZero ((skeletonPair C n).twistedHomology L k) :=
  (isZero_twistedHomology_sigmaDiskPair_of_ne (cell C n) hk _).of_iso
    (asIso (TopPair.twistedHomologyMap (characteristicPairMap C n) L k)).symm

end TauCeti
