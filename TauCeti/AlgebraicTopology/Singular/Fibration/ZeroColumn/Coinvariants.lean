/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.EulerCharacteristic
public import TauCeti.AlgebraicTopology.Singular.Fibration.ZeroColumn.LocalCoefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coinvariants

/-!
# The column `p = 0` of the Serre spectral sequence as monodromy coinvariants

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a path-connected CW complex, with a point `b`.
The fundamental group `π₁(C, b)` acts on the homology `Hq(p⁻¹(b); R)` of the fibre over `b` by
transport along loops, the monodromy of the local system of fibre homology
(`TauCeti.TopCat.serreFiberLocalSystemOn`). This file identifies the column `p = 0` of the second
page of the Serre spectral sequence of `p` with the coinvariants of this action,

`E²_{0,q} ≅ Hq(p⁻¹(b); R)_{π₁(C, b)}`

(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoCoinvariants`), the classical reading of
`E²_{0,q} = H₀(C; Hq(F))` over a connected base. It is the composite of the identification of the
column with zeroth homology with local coefficients
(`TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoTwistedHomology`), which is relative to the
empty base of the complex, and the computation of zeroth homology with local coefficients of a
path-connected space as monodromy coinvariants
(`TauCeti.LocalCoefficientSystem.twistedHomology₀IsoCoinvariants`).

On the first page, the column is the fibre homology over the `0`-skeleton,
`E¹_{0,q} = Hq(p⁻¹(X⁰); R)`. The map from it to the coinvariants
(`TauCeti.TopCat.serreZeroChainsToCoinvariants`), through which the identification is induced
(`TauCeti.TopCat.homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCoinvariants_hom`), sends the
class of a fibre homology class `a` over a point `y` of the `0`-skeleton to the coinvariant class of
its transport `τ_γ a` along any path `γ` from `y` to `b` in `C`
(`TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsToCoinvariants`). The
input is the cellular–singular comparison in degree zero on the class of a coefficient
(`TauCeti.ιTwistedHomology₀_comp_twistedCellularSingularHomologyIso_hom`).

## Main definitions

* `TauCeti.TopCat.serreZeroChainsToCoinvariants`: the map `Hq(p⁻¹(X⁰); R) ⟶ Hq(p⁻¹(b); R)_{π₁}`.
* `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoCoinvariants`: `E²_{0,q}` is the module of
  coinvariants of the monodromy action on the fibre homology over `b`.

## Main results

* `TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsToCoinvariants`: a fibre
  homology class over a point of the `0`-skeleton goes to the coinvariant class of its transport to
  `b`.
* `TauCeti.TopCat.homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCoinvariants_hom`: the
  identification of `E²_{0,q}` with the coinvariants is induced by this map on the first page.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H (zeroth homology with local coefficients as coinvariants).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] (C : Set B) [CWComplex C]
  [PathConnectedSpace C] (R : Type u) [CommRing R] (hp : serreFibrations p) (b : C) (q : ℕ)

/-- The map from the fibre homology over the `0`-skeleton of a path-connected CW complex `C`, the
column `E¹_{0,q} = Hq(p⁻¹(X⁰); R)` of the first page of the Serre spectral sequence, to the
coinvariants of the monodromy action of `π₁(C, b)` on the fibre homology over `b`. It sends the
class of a fibre homology class over a point of the `0`-skeleton to the coinvariant class of its
transport to `b`
(`TauCeti.TopCat.fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsToCoinvariants`). -/
def serreZeroChainsToCoinvariants :
    (preimageSkeletonPair p C 0).singularHomology (ModuleCat.of R R) q ⟶
      ModuleCat.of R (LocalCoefficientSystem.monodromyRepresentation
        (serreFiberLocalSystemOn C R hp q) b).Coinvariants :=
  (serreZeroChainsIso C R hp q).hom ≫
    cokernel.π (twistedCellularDifferential.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0) ≫
    (twistedCellularChainComplexHomologyZeroIso C (serreFiberLocalSystemOn C R hp q)).inv ≫
    (twistedCellularSingularHomologyIso C (serreFiberLocalSystemOn C R hp q) 0).hom ≫
    (twistedHomologyIsoComplexBasePair.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0).inv ≫
    (LocalCoefficientSystem.twistedHomology₀IsoCoinvariants (serreFiberLocalSystemOn C R hp q)
      b).hom

/-- **A fibre homology class over the `0`-skeleton goes to the coinvariant class of its
transport.** For a point `y` of the `0`-skeleton of `C` and a path `γ` from `y` to `b` in `C`, the
map `TauCeti.TopCat.serreZeroChainsToCoinvariants` sends the class in `Hq(p⁻¹(X⁰); R)` of a
fibre homology class `a` over `y` to the coinvariant class of the transport of `a` along `γ`. -/
@[reassoc]
theorem fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsToCoinvariants
    (y : skeletonObj C 1)
    (γ : Path (Set.inclusion (skeletonLT C ((1 : ℕ) : ℕ∞)).subset_complex y) b) :
    fiberHomologyToPreimageSkeletonZero p C R q y.property ≫
        serreZeroChainsToCoinvariants C R hp b q =
      fiberHomologyTransport hp (ModuleCat.of R R) q (γ.map continuous_subtypeVal) ≫
        (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q
          (FundamentalGroupoid.mk (b : B))).inv ≫ ModuleCat.ofHom (Representation.Coinvariants.mk
            (LocalCoefficientSystem.monodromyRepresentation
              (serreFiberLocalSystemOn C R hp q) b)) := by
  -- The cellular–singular comparison in degree zero sends the class of a fibre homology class over
  -- `y` to its class with local coefficients, whose coinvariant class is that of its transport.
  have key := ιTwistedHomology₀_comp_twistedCellularSingularHomologyIso_hom C
    (serreFiberLocalSystemOn C R hp q) y =≫
      ((twistedHomologyIsoComplexBasePair.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0).inv ≫
        (LocalCoefficientSystem.twistedHomology₀IsoCoinvariants (serreFiberLocalSystemOn C R hp q)
          b).hom)
  simp only [Category.assoc] at key
  have hπ : LocalCoefficientSystem.ιTwistedHomology₀ (serreFiberLocalSystemOn C R hp q)
        (Set.inclusion (skeletonLT C ((1 : ℕ) : ℕ∞)).subset_complex y) ≫
        (complexBasePair C).twistedHomologyπ (serreFiberLocalSystemOn C R hp q) 0 ≫
        (twistedHomologyIsoComplexBasePair.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0).inv ≫
        (LocalCoefficientSystem.twistedHomology₀IsoCoinvariants (serreFiberLocalSystemOn C R hp q)
          b).hom =
      (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q (FundamentalGroupoid.mk (y : B))).hom ≫
        fiberHomologyTransport hp (ModuleCat.of R R) q (γ.map continuous_subtypeVal) ≫
        (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q
          (FundamentalGroupoid.mk (b : B))).inv ≫ ModuleCat.ofHom (Representation.Coinvariants.mk
            (LocalCoefficientSystem.monodromyRepresentation
              (serreFiberLocalSystemOn C R hp q) b)) := by
    rw [← twistedHomologyIsoComplexBasePair_hom, Iso.hom_inv_id_assoc]
    refine (LocalCoefficientSystem.ιTwistedHomology₀_isoCoinvariants_hom_of_path
      (serreFiberLocalSystemOn C R hp q) b _ γ).trans ?_
    -- On the class of a path, the restriction of the local system of fibre homology to `C` acts
    -- by transport along the image of the path in `B` (`LocalCoefficientSystem.pullback_obj_map`).
    exact (congrArg (· ≫ _) (serreFiberLocalSystem_map_mk hp (ModuleCat.of R R) q
      (b₀ := FundamentalGroupoid.mk (y : B)) (b₁ := FundamentalGroupoid.mk (b : B))
      (γ.map continuous_subtypeVal))).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
  rw [serreZeroChainsToCoinvariants,
    fiberHomologyToPreimageSkeletonZero_comp_serreZeroChainsIso_hom_assoc,
    fiberHomologyToTwistedZeroChains_def]
  -- The cellular chain group in degree zero is the relative homology of `skeletonPair C 0` only up
  -- to unfolding, so the composites are matched by unification.
  erw [Category.assoc, Category.assoc]
  refine (congrArg (_ ≫ ·) (key.trans hπ)).trans ?_
  exact Iso.inv_hom_id_assoc _ _

/-- **The column `p = 0` of the second page of the Serre spectral sequence is the module of
monodromy coinvariants.** For a Serre fibration `p : E ⟶ B` and a path-connected CW complex
`C ⊆ B` with a point `b`, the object `E²_{0,q}` of the second page (numbered `3`) of the Serre
spectral sequence over `C`, at `pq = (a, b')` with `b' = -1` and `a + b' = -q`, is the module of
coinvariants `Hq(p⁻¹(b); R)_{π₁(C, b)}` of the action of the fundamental group by transport. It is
induced by `TauCeti.TopCat.serreZeroChainsToCoinvariants` on the first page
(`TauCeti.TopCat.homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCoinvariants_hom`). -/
def serreSpectralSequenceSecondPageXZeroIsoCoinvariants (pq : ℤ × ℤ) (hb : pq.2 = -1)
    (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 3).X pq ≅
      ModuleCat.of R (LocalCoefficientSystem.monodromyRepresentation
        (serreFiberLocalSystemOn C R hp q) b).Coinvariants :=
  serreSpectralSequenceSecondPageXZeroIsoTwistedHomology C R hp q pq hb ha ≪≫
    (twistedHomologyIsoComplexBasePair.{u, u, u} C (serreFiberLocalSystemOn C R hp q) 0).symm ≪≫
    LocalCoefficientSystem.twistedHomology₀IsoCoinvariants (serreFiberLocalSystemOn C R hp q) b

/-- Under `TauCeti.TopCat.serreSpectralSequenceSecondPageXZeroIsoCoinvariants`, the projection of
the first page onto the second is the map `TauCeti.TopCat.serreZeroChainsToCoinvariants` from the
fibre homology over the `0`-skeleton to the monodromy coinvariants. -/
@[reassoc]
lemma homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoCoinvariants_hom (pq : ℤ × ℤ)
    (hb : pq.2 = -1) (ha : pq.1 + pq.2 = -q) :
    ((serreSpectralSequence C p R).page 2).homologyπ pq ≫
        ((serreSpectralSequence C p R).iso 2 3 pq rfl le_rfl).hom ≫
        (serreSpectralSequenceSecondPageXZeroIsoCoinvariants C R hp b q pq hb ha).hom =
      ((serreSpectralSequence C p R).page 2).iCycles pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl q ha).hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) q)
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair 0 pq.2 (by lia))) ≫
        serreZeroChainsToCoinvariants C R hp b q := by
  rw [serreSpectralSequenceSecondPageXZeroIsoCoinvariants, Iso.trans_hom, Iso.trans_hom,
    homologyπ_comp_serreSpectralSequenceSecondPageXZeroIsoTwistedHomology_hom_assoc,
    Iso.symm_hom, serreZeroChainsToCoinvariants]

end TopCat

end TauCeti
