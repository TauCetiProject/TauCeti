/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.AdmissibleLattice
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SerreRootGenerator
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus

/-!
# The tripled type-D4 carrier

This file feeds the explicit `24`-dimensional type-`D₄` representation `V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)`,
its admissible coordinate lattice, and its full set of weights into the Kostant toral-closure
construction. The result is an explicit affine group scheme over `ℤ`, cut out inside `GL₂₄` by
the largest Hopf ideal killed by the eight numbered simple-root subgroups and the represented
rank-four split torus, together with its matrix-valued points and the pinning equation on both.

The type-`D₄` diagram carries three families of finite groups of Lie type, and the full-weight
spin carrier `TauCeti.TypeDSpinCarrier.groupScheme` at rank four serves the untwisted and the
graph-twisted ones. It cannot serve the triality-twisted family: triality permutes the three
eight-dimensional representations of `D₄`, so neither the natural representation nor the full spin
module is stable under it, while the tripled module is a full-weight module that is. On
the twenty-four tripled weights triality acts by
`TauCeti.DynkinType.d4TripledWeight_d4TripledTrialityPerm_apply`, the equivariance
`wt (π x) (σ i) = wt x i`. That equivariance is the weight-level hypothesis of the
numbered-symmetry construction on a Kostant toral-closure carrier; its remaining inputs, a linear
automorphism of the module intertwining the Serre root generators along the permutation and
acting monomially on the lattice basis, are not constructed here.

The character by which the split torus rescales a numbered root subgroup is
`TauCeti.TypeDStd.rootGeneratorWeight`, a row of the type-`D₄` Cartan matrix, identified with the
simple roots of `TauCeti.DynkinType.simplyConnectedRootDatum` at `D 4` by
`TauCeti.TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex`; the Cartan action on the numbered
root generators is `TauCeti.TypeDStd.lie_serreH_serreRootGenerator`, and the pinning equation
below is stated against them.

No reductivity, smoothness, maximality of the torus, or identification of the carrier with the
pinned simply connected group scheme of type `D₄` is asserted here. Constructions on this carrier
transfer to that pinned group only along such an identification.

## Main declarations

* `TauCeti.D4Tripled.groupScheme`: the tripled Kostant toral-closure carrier over `ℤ`.
* `TauCeti.D4Tripled.rootSubgroup`: its eight numbered simple-root subgroup morphisms.
* `TauCeti.D4Tripled.weightTorus`: its closed rank-four split torus.
* `TauCeti.D4Tripled.points`: its matrix-valued points over a commutative ring.
* `TauCeti.D4Tripled.rootSubgroupPoints` and `TauCeti.D4Tripled.weightTorusPoints`: its
  numbered root subgroups and weight torus on matrix-valued points.
* `TauCeti.D4Tripled.weightTorus_conj_rootSubgroup` and
  `TauCeti.D4Tripled.weightTorusPoints_conj_rootSubgroupPoints`: the pinning equation on scheme
  points and on matrix-valued points.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2, for triality and the family it defines.
* The carrier API follows the formal template of `TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme`,
  specialized here to the tripled type-`D₄` representation, lattice, and weights.
* The symmetry-carrying full-weight design follows
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.GroupScheme` and its `GraphAutomorphism` module.
* The pinning section follows `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic`, and its
  named-simple-root equations follow
  `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.RootDatum`.
-/

public section

open scoped Matrix

universe v

namespace TauCeti.D4Tripled

open AlgebraicGeometry CategoryTheory
open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra
open scoped CategoryTheory.MonObj TensorProduct

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

/-! ## The pinned carrier -/

/-- The Hopf ideal cutting out the tripled type-`D₄` carrier inside `GL₂₄`. -/
noncomputable def definingIdeal :
    HopfIdeal ℤ (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ 24) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight

/-- The defining ideal is the ideal supplied by the generic Kostant toral-closure construction. -/
theorem definingIdeal_def :
    definingIdeal =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
        d4TripledWeight := by
  rw [definingIdeal]

/-- The tripled type-`D₄` carrier over `ℤ`, obtained as the smallest closed subgroup scheme of
`GL₂₄` containing the represented numbered root subgroups and weight torus. -/
noncomputable abbrev groupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight

/-- The quotient-spectrum presentation of the tripled type-`D₄` carrier. -/
theorem groupScheme_def :
    groupScheme = CommHopfAlgCat.quotientSpec
      (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal := by
  rw [groupScheme, definingIdeal]

/-- The canonical inclusion of the tripled type-`D₄` carrier into `GL₂₄`. -/
noncomputable def carrierι : groupScheme ⟶ TauCeti.GeneralLinear.groupScheme ℤ 24 :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight

/-- The carrier inclusion is the generic Kostant toral-closure inclusion. -/
theorem carrierι_def :
    carrierι = TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
      (TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
      d4TripledWeight := by
  rw [carrierι]

/-- The tripled type-`D₄` carrier is a closed subgroup scheme of `GL₂₄`. -/
instance isClosedImmersion_carrierι : IsClosedImmersion carrierι.hom.hom.left := by
  rw [carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantToralGroupSchemeι
    _ _ _ _ _ _ _ _

/-- A positive or negative numbered simple-root subgroup of the tripled type-`D₄` carrier. -/
noncomputable def rootSubgroup (k : Fin 4 ⊕ Fin 4) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight k

/-- The root subgroup is the one supplied by the generic Kostant toral-closure construction. -/
theorem rootSubgroup_def (k : Fin 4 ⊕ Fin 4) :
    rootSubgroup k =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
        d4TripledWeight k := by
  rw [rootSubgroup]

/-- Including a numbered root subgroup into `GL₂₄` recovers its represented divided-power
exponential subgroup. -/
@[simp]
theorem rootSubgroup_comp_carrierι (k : Fin 4 ⊕ Fin 4) :
    rootSubgroup k ≫ carrierι =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) latticeBasis := by
  rw [rootSubgroup, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_comp_ι
    _ _ _ _ _ _ _ _ k

/-- The represented rank-four split weight torus in the tripled type-`D₄` carrier. -/
noncomputable def weightTorus : SplitTorus.groupScheme ℤ (Fin 4) ⟶ groupScheme :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight

/-- The weight torus is the one supplied by the generic Kostant toral-closure construction. -/
theorem weightTorus_def :
    weightTorus =
      TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
        d4TripledWeight := by
  rw [weightTorus]

/-- Including the weight torus into `GL₂₄` recovers the diagonal torus of the tripled weights. -/
@[simp]
theorem weightTorus_comp_carrierι :
    weightTorus ≫ carrierι = TauCeti.GeneralLinear.weightTorus (R := ℤ) d4TripledWeight := by
  rw [weightTorus, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_comp_ι
    _ _ _ _ _ _ _ _

/-- The tripled weights make the represented split torus a closed subgroup scheme of the
carrier. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion weightTorus.hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToral
    _ _ _ _ _ _ _ _ span_range_d4TripledWeight_eq_top

/-- Two morphisms out of the tripled type-`D₄` carrier agree when they agree on its numbered
root subgroups and represented split torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (f g : groupScheme ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ k, rootSubgroup k ≫ f = rootSubgroup k ≫ g)
    (htorus : weightTorus ≫ f = weightTorus ≫ g) : f = g :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_hom_ext
    _ _ _ _ _ _ _ _ f g hroot htorus

/-! ## Matrix-valued points -/

/-- The matrix-valued points of the tripled type-`D₄` carrier. -/
noncomputable def points (A : Type v) [CommRing A] :
    Subgroup (_root_.Matrix.GeneralLinearGroup (Fin 24) A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight A

/-- The carrier points are exactly the invertible matrices cut out by the defining Hopf ideal. -/
theorem points_def (A : Type v) [CommRing A] :
    points A = TauCeti.GeneralLinear.hopfIdealPointsSubgroup 24 definingIdeal A := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def
    _ _ _ _ _ _ _ _ A

/-- A matrix is a carrier point exactly when its associated convolution point kills the defining
Hopf ideal. -/
@[simp]
theorem mem_points_iff (A : Type v) [CommRing A]
    (g : _root_.Matrix.GeneralLinearGroup (Fin 24) A) :
    g ∈ points A ↔
      ∀ x ∈ definingIdeal,
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ℤ) 24).symm g).ofConv x = 0 := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff
    _ _ _ _ _ _ _ _ A g

/-- The parametrized numbered root subgroup inside the tripled type-`D₄` carrier points. -/
noncomputable def rootSubgroupPoints (k : Fin 4 ⊕ Fin 4) (A : Type v) [CommRing A] :
    Multiplicative A →* points A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralRootSubgroupPoints
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight
    k A

/-- A numbered root-subgroup point is its represented divided-power exponential matrix. -/
@[simp]
theorem coe_rootSubgroupPoints (k : Fin 4 ⊕ Fin 4) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    (rootSubgroupPoints k A u : _root_.Matrix.GeneralLinearGroup (Fin 24) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) latticeBasis
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) :=
  TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints
    _ _ _ _ _ _ _ _ k A u

/-- The split weight torus on matrix-valued points of the tripled type-`D₄` carrier. -/
noncomputable def weightTorusPoints (A : Type v) [CommRing A] :
    (Fin 4 → Aˣ) →* points A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralWeightTorusPoints
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight A

/-- A tripled weight-torus point is the diagonal matrix obtained by evaluating each weight. -/
@[simp]
theorem coe_weightTorusPoints (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) :
    (weightTorusPoints A s : _root_.Matrix.GeneralLinearGroup (Fin 24) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
        lattice.toAddSubgroup latticeBasis d4TripledWeight s :=
  TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints
    _ _ _ _ _ _ _ _ A s

/-! ## The pinning equation -/

private theorem lie_serreH_serreRootGenerator (k : Fin 4 ⊕ Fin 4) :
    ∀ j : Fin 4,
      ⁅TauCeti.serreH ℚ weightTable.cartanMatrix j,
          TauCeti.serreRootGenerator weightTable.cartanMatrix k⁆ =
        (TypeDStd.rootGeneratorWeight 4 k j : ℚ) •
          TauCeti.serreRootGenerator weightTable.cartanMatrix k := by
  rw [weightTable_cartanMatrix]
  exact TypeDStd.lie_serreH_serreRootGenerator 4 k

/-- **Conjugation by the tripled weight torus acts on each numbered root subgroup through its
positive or negative simple-root character, on matrix-valued points.** A torus point `s` carries
the root-subgroup point of parameter `u` to the one of parameter `α_k(s) u`, where the character
`α_k` is `TauCeti.TypeDStd.rootGeneratorWeight`, the positive or negative `k`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at `D 4`. -/
@[simp]
theorem weightTorusPoints_conj_rootSubgroupPoints (k : Fin 4 ⊕ Fin 4) (A : Type v) [CommRing A]
    (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints k A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints k A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s (TypeDStd.rootGeneratorWeight 4 k) : A) *
            Multiplicative.toAdd u)) :=
  kostantToralWeightTorusPoints_conj_rootSubgroupPoints
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep
    lattice.toAddSubgroup rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator
    latticeBasis d4TripledWeight isCartanWeightVector_latticeBasis
    (lie_serreH_serreRootGenerator k) A s u

/-- **Conjugation by the tripled weight torus acts on each numbered root subgroup through its
positive or negative simple-root character, on scheme points.** -/
@[simp]
theorem weightTorus_conj_rootSubgroup (k : Fin 4 ⊕ Fin 4) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 4)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup k).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (TypeDStd.rootGeneratorWeight 4 k) : A) * u)) ≫
        (rootSubgroup k).hom.hom :=
  kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
      _ _ _ _ _ _ _ isCartanWeightVector_latticeBasis
      isNilpotent_rep_serreRootGenerator A (lie_serreH_serreRootGenerator k) s u

end TauCeti.D4Tripled
