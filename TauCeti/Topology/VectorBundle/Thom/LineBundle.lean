/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Transfer.CoveringPair
public import TauCeti.Topology.VectorBundle.SphereBundle.LocallyTrivial

/-!
# The Thom isomorphism of a real line bundle in homology

Let `E → B` be a real vector bundle of rank one whose fibre norm is continuous on the total space,
for instance a line bundle with a continuous Riemannian metric. Each fibre of its unit sphere
bundle `S(E)` is a pair of opposite unit vectors, so `S(E) → B` is a double cover
(`TauCeti.isCoveringMap_sphereBundleProj`), and the unit disc bundle `D(E)` contracts radially
onto the zero section, so that its projection to `B` is a homotopy equivalence
(`TauCeti.discBundleProjHomotopyEquiv`). The relative homology of `(D(E), S(E))` is therefore the
homology of `B` with local coefficients, shifted by one
(`TopPair.singularHomologySuccIsoTwistedHomology`), and the disc-sphere pair has the homology of
the Thom pair `(E, E₀)` (`TauCeti.isIso_singularHomologyMap_discSpherePairMap`). This gives the
**Thom isomorphism of a line bundle** in homology,

`Hₙ₊₁(E, E₀; R) ≅ Hₙ(B; L)`,

in every degree, over any ring `R` and over an arbitrary base
(`TauCeti.thomPairSingularHomologySuccIsoTwistedHomology`). Here `L` is any local system on `B`
with a short exact sequence `0 ⟶ L ⟶ R[S(E)] ⟶ R ⟶ 0` ending with the augmentation of the
permutation local system `R[S(E)]` of the double cover, which adds up the coefficients of the two
unit vectors over each point; so `L` is the kernel of the augmentation. Its fibre over `b` is a
copy of `R`, spanned by the difference of the two unit vectors of `E_b`, and transport along a loop
acts on it by the sign of the loop's action on these two vectors: `L` is the orientation local
system of `E`. In degree `0` the Thom pair has no homology, as it has none below the rank
(`TauCeti.isZero_singularHomology_thomPair`).

The isomorphism is the inverse of the comparison of the disc-sphere pair with the Thom pair,
followed by the lift of the connecting map of `(D(E), S(E))`: composed with the map
`Hₙ(B; L) ⟶ Hₙ(B; R[S(E)]) ≅ Hₙ(S(E))` induced by `L ⟶ R[S(E)]`, it is that connecting map
(`TauCeti.singularHomologyMap_discSpherePairMap_comp_thomPairSingularHomologySuccIso`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the local system of a
  covering space) and Section 4.D (the Thom isomorphism).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover).
-/

public section

noncomputable section

open Bundle CategoryTheory

universe u

namespace TauCeti

variable {B : Type u} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type u} [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) (hF : Module.finrank ℝ F = 1)

/-- The projection of the sphere bundle, as a morphism of spaces. -/
private abbrev sphereProj : (discSpherePair F E).snd ⟶ TopCat.of B :=
  TopCat.ofHom (sphereBundleProj F E)

/-- The projection of the disc bundle, as a morphism of spaces. -/
private abbrev discProj : (discSpherePair F E).fst ⟶ TopCat.of B :=
  TopCat.ofHom (discBundleProjHomotopyEquiv F E).toFun

/-- The projection of the disc bundle restricts to that of the sphere bundle. -/
private theorem map_comp_discProj :
    (discSpherePair F E).map ≫ discProj = sphereProj (F := F) (E := E) := by
  ext v
  exact (discBundleProjHomotopyEquiv_apply F E _).trans (sphereBundleProj_apply F E v).symm

variable {R : Type u} [Ring R] {L : LocalCoefficientSystem.{u, u, u} R (TopCat.of B)}
  {ι : L ⟶ (isCoveringMap_sphereBundleProj F E hnorm hF).permutationLocalSystem
    (p := TopCat.ofHom (sphereBundleProj F E)) R}
  {hι₀ : ι ≫ (isCoveringMap_sphereBundleProj F E hnorm hF).permutationLocalSystemAugmentation
    (p := TopCat.ofHom (sphereBundleProj F E)) R = 0}
  (hι : (ShortComplex.mk ι _ hι₀).ShortExact)

/-- **The Thom isomorphism of a line bundle in homology.** Let `E → B` be a real vector bundle of
rank one whose fibre norm is continuous on the total space, and let `0 ⟶ L ⟶ R[S(E)] ⟶ R ⟶ 0` be a
short exact sequence of local systems on `B` ending with the augmentation of the permutation local
system of the double cover `S(E) → B`. Then `Hₙ₊₁(E, E₀; R) ≅ Hₙ(B; L)`. -/
def thomPairSingularHomologySuccIsoTwistedHomology (n : ℕ) :
    (thomPair F E).singularHomology (ModuleCat.of R R) (n + 1) ≅ L.twistedHomology n :=
  haveI := isIso_singularHomologyMap_discSpherePairMap F E hnorm (ModuleCat.of R R) (n + 1)
  (asIso (TopPair.singularHomologyMap (discSpherePairMap F E) (ModuleCat.of R R) (n + 1))).symm ≪≫
    (discSpherePair F E).singularHomologySuccIsoTwistedHomology
      (isCoveringMap_sphereBundleProj F E hnorm hF) discProj map_comp_discProj
      (discBundleProjHomotopyEquiv F E).isWeakHomotopyEquivalence hι n

/-- On the disc-sphere pair, the Thom isomorphism of a line bundle is the isomorphism of the
pair over the double cover `S(E) → B`. -/
@[reassoc]
private theorem singularHomologyMap_discSpherePairMap_comp_hom (n : ℕ) :
    TopPair.singularHomologyMap (discSpherePairMap F E) (ModuleCat.of R R) (n + 1) ≫
        (thomPairSingularHomologySuccIsoTwistedHomology hnorm hF hι n).hom =
      ((discSpherePair F E).singularHomologySuccIsoTwistedHomology
        (isCoveringMap_sphereBundleProj F E hnorm hF) discProj map_comp_discProj
        (discBundleProjHomotopyEquiv F E).isWeakHomotopyEquivalence hι n).hom := by
  have := isIso_singularHomologyMap_discSpherePairMap F E hnorm (ModuleCat.of R R) (n + 1)
  -- The Thom isomorphism is `(asIso M).symm ≪≫ J` for the comparison `M` of the disc-sphere pair
  -- with the Thom pair, whose `hom` is `inv M ≫ J.hom` by definition.
  exact IsIso.hom_inv_id_assoc _ _

/-- The Thom isomorphism of a line bundle, read on the disc-sphere pair and followed by the map
`Hₙ(B; L) ⟶ Hₙ(B; R[S(E)]) ≅ Hₙ(S(E))` induced by `L ⟶ R[S(E)]`, is the connecting map
`Hₙ₊₁(D(E), S(E)) ⟶ Hₙ(S(E))` of the disc-sphere pair. -/
theorem singularHomologyMap_discSpherePairMap_comp_thomPairSingularHomologySuccIso (n : ℕ) :
    TopPair.singularHomologyMap (discSpherePairMap F E) (ModuleCat.of R R) (n + 1) ≫
        (thomPairSingularHomologySuccIsoTwistedHomology hnorm hF hι n).hom ≫
          LocalCoefficientSystem.twistedHomologyCoefficientMap ι n ≫
            ((isCoveringMap_sphereBundleProj F E hnorm hF).singularHomologyPermutationIso
              (p := TopCat.ofHom (sphereBundleProj F E)) R n).inv =
      (discSpherePair F E).singularHomologyδ (ModuleCat.of R R) (n + 1) n := by
  rw [singularHomologyMap_discSpherePairMap_comp_hom_assoc]
  exact TopPair.singularHomologySuccIsoTwistedHomology_hom_comp _ _ _ _ _ _ n

end TauCeti
