/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.E7.Minuscule.AdmissibleLattice
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Faithful

/-!
# The full-weight E₇ minuscule Chevalley datum

The fifty-six-dimensional minuscule module, with its integral coordinate lattice and numbered
weight basis, is a faithful representation of the pinned rational E₇ Lie algebra. Its weights
span the full weight lattice, so its Chevalley datum has the simply connected character lattice.
This supplies the representation and lattice input for comparing its integral Chevalley group
with the simply connected group, without asserting that comparison here.

The action pulls back `E7Minuscule.rep` along `DynkinType.serreLiftEquiv`.
Admissibility is transported from `E7Minuscule.rep_kostantForm_mem_lattice` using
`UniversalEnvelopingAlgebra.map_kostantForm`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate VI.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

open scoped Matrix

namespace TauCeti.E7Minuscule

open DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

private theorem pinnedSerreSystem :
    IsSerreSystem ℚ E7.cartanMatrixᵀ
      (TauCeti.serreH ℚ weightTable.cartanMatrix)
      (TauCeti.serreE ℚ weightTable.cartanMatrix)
      (TauCeti.serreF ℚ weightTable.cartanMatrix) := by
  dsimp only [rank]
  rw [cartanMatrix_E7, CartanMatrix.E_isSymm 7, ← weightTable_cartanMatrix]
  exact TauCeti.isSerreSystem_serre ℚ weightTable.cartanMatrix

private def toSerre :
    E7.lieAlgebra valid_E7 →ₗ⁅ℚ⁆ Matrix.ToLieAlgebra ℚ weightTable.cartanMatrix :=
  (TauCeti.serreLift pinnedSerreSystem).comp (E7.serreLiftEquiv valid_E7).symm.toLieHom

private theorem toSerre_h (i : Fin E7.rank) :
    toSerre ((E7.lieBasis valid_E7).h i) = TauCeti.serreH ℚ weightTable.cartanMatrix i := by
  rw [toSerre, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    E7.serreLiftEquiv_symm_lieBasis_h valid_E7 i]
  exact TauCeti.serreLift_serreH pinnedSerreSystem i

private theorem toSerre_e (i : Fin E7.rank) :
    toSerre ((E7.lieBasis valid_E7).e i) = TauCeti.serreE ℚ weightTable.cartanMatrix i := by
  rw [toSerre, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    E7.serreLiftEquiv_symm_lieBasis_e valid_E7 i]
  exact TauCeti.serreLift_serreE pinnedSerreSystem i

private theorem toSerre_f (i : Fin E7.rank) :
    toSerre ((E7.lieBasis valid_E7).f i) = TauCeti.serreF ℚ weightTable.cartanMatrix i := by
  rw [toSerre, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    E7.serreLiftEquiv_symm_lieBasis_f valid_E7 i]
  exact TauCeti.serreLift_serreF pinnedSerreSystem i

private theorem toSerre_rootGenerator (k : Fin E7.rank ⊕ Fin E7.rank) :
    toSerre ((E7.lieBasis valid_E7).rootGenerator k) =
      TauCeti.serreRootGenerator weightTable.cartanMatrix k := by
  cases k with
  | inl i =>
      rw [LieAlgebra.Basis.rootGenerator_inl, toSerre_e]
      exact (TauCeti.serreRootGenerator_inl weightTable.cartanMatrix i).symm
  | inr i =>
      rw [LieAlgebra.Basis.rootGenerator_inr, toSerre_f]
      exact (TauCeti.serreRootGenerator_inr weightTable.cartanMatrix i).symm

/-- The minuscule representation of the pinned rational E₇ Lie algebra, extended to its
universal enveloping algebra. -/
def pinnedRep :
    _root_.UniversalEnvelopingAlgebra ℚ (E7.lieAlgebra valid_E7) →ₐ[ℚ]
      Module.End ℚ (Fin 56 → ℚ) :=
  rep.comp (UniversalEnvelopingAlgebra.map ℚ toSerre)

/-- The pinned Cartan generator acts diagonally with the numbered minuscule weights. -/
theorem pinnedRep_h (i : Fin E7.rank) (v : Fin 56 → ℚ) (a : Fin 56) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ ((E7.lieBasis valid_E7).h i)) v a =
      (e7MinusculeWeight a i : ℚ) * v a := by
  rw [pinnedRep, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι, toSerre_h,
    rep_def, weightTable.rep_ι_apply, weightTable.rationalSerreRepresentation_serreH i]
  dsimp only [rank] at i
  simp [Matrix.mulVec, dotProduct, MinusculeWeightTable.cartanGeneratorMatrixQ_apply]

/-- Simplifier normal form of the pinned Cartan action. -/
@[simp] theorem pinnedRep_h' (i : Fin E7.rank) (v : Fin 56 → ℚ) (a : Fin 56) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).h i))) v a =
      (e7MinusculeWeight a i : ℚ) * v a := by
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_h]

/-- The pinned positive simple-root generator acts by the integral raising matrix. -/
theorem pinnedRep_e (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ ((E7.lieBasis valid_E7).e i)) v =
      (raisingMatrix i).map (Int.castRingHom ℚ) *ᵥ v := by
  rw [pinnedRep, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι, toSerre_e,
    rep_def, weightTable.rep_ι_apply, weightTable.rationalSerreRepresentation_serreE i]
  dsimp only [rank] at i
  congr 1
  ext a b
  simp [Matrix.map_apply, raisingMatrix_apply]

/-- Simplifier normal form of the pinned positive simple-root action. -/
@[simp] theorem pinnedRep_e' (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).e i))) v =
      (raisingMatrix i).map (Int.castRingHom ℚ) *ᵥ v := by
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_e]

/-- The pinned negative simple-root generator acts by the integral lowering matrix. -/
theorem pinnedRep_f (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ ((E7.lieBasis valid_E7).f i)) v =
      (loweringMatrix i).map (Int.castRingHom ℚ) *ᵥ v := by
  rw [pinnedRep, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι, toSerre_f,
    rep_def, weightTable.rep_ι_apply, weightTable.rationalSerreRepresentation_serreF i]
  dsimp only [rank] at i
  congr 1
  ext a b
  simp [Matrix.map_apply, loweringMatrix_apply]

/-- Simplifier normal form of the pinned negative simple-root action. -/
@[simp] theorem pinnedRep_f' (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).f i))) v =
      (loweringMatrix i).map (Int.castRingHom ℚ) *ᵥ v := by
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_f]

/-- Every pinned simple-root generator acts by a square-zero endomorphism. -/
theorem pinnedRep_rootGenerator_sq (k : Fin E7.rank ⊕ Fin E7.rank) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E7.lieBasis valid_E7).rootGenerator k)) ^ 2 = 0 := by
  rw [pinnedRep, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι, toSerre_rootGenerator,
    rep_def]
  exact weightTable.rep_serreRootGenerator_pow_two k

/-- Each minuscule lattice basis vector has its recorded weight for the pinned Cartan action. -/
theorem isCartanWeightVector_pinnedRep_latticeBasis (a : Fin 56) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (E7.lieBasis valid_E7).h pinnedRep
      (e7MinusculeWeight a) (latticeBasis a : Fin 56 → ℚ) := by
  apply (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr
  intro i
  rw [pinnedRep, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι, toSerre_h]
  exact (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (isCartanWeightVector_latticeBasis a) i

/-- The pinned minuscule representation is faithful on the rational Lie algebra. -/
theorem pinnedRep_ι_injective :
    Function.Injective fun x : E7.lieAlgebra valid_E7 =>
      pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  apply representation_ι_injective_of_isCartanWeightVector_of_span_int valid_E7 pinnedRep
    (v := fun a => (latticeBasis a : Fin 56 → ℚ))
    (hwt := isCartanWeightVector_pinnedRep_latticeBasis)
    (hspan := span_range_e7MinusculeWeight_eq_top)
  intro a
  simp [coe_latticeBasis]

/-- The coordinate lattice is admissible for the pinned simple-generator Kostant form. -/
theorem pinnedRep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ (E7.lieAlgebra valid_E7))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm (E7.lieBasis valid_E7).rootGenerator
      (E7.lieBasis valid_E7).h) (v : Fin 56 → ℚ) (hv : v ∈ lattice.toAddSubgroup) :
    pinnedRep u v ∈ lattice.toAddSubgroup := by
  apply rep_kostantForm_mem_lattice _ _ v hv
  have hmap : UniversalEnvelopingAlgebra.map ℚ toSerre u ∈
      (UniversalEnvelopingAlgebra.kostantForm (E7.lieBasis valid_E7).rootGenerator
        (E7.lieBasis valid_E7).h).map
          (UniversalEnvelopingAlgebra.map ℚ toSerre).toRingHom :=
    Subring.mem_map.mpr ⟨u, hu, rfl⟩
  rw [UniversalEnvelopingAlgebra.map_kostantForm] at hmap
  rw [funext toSerre_rootGenerator, funext toSerre_h] at hmap
  exact hmap

/-- The full-weight fifty-six-dimensional minuscule Chevalley datum of type E₇, with the
standard coordinate lattice and fundamental-weight coordinates. -/
-- The actual carrier and lattice rank must compute to compare the datum's roots with the
-- represented matrices. The component equations below are the rewriting API for consumers.
@[expose] def chevalleyDatum : ChevalleyDatum E7 valid_E7 where
  carrier := Fin 56 → ℚ
  representation := pinnedRep
  injective_representation_ι := pinnedRep_ι_injective
  lattice := lattice.toAddSubgroup
  representation_mem_lattice := pinnedRep_kostantForm_mem_lattice
  span_lattice_eq_top := by
    rw [lattice_def]
    exact Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := 56
  basis := latticeBasis
  weight := e7MinusculeWeight
  isCartanWeightVector_basis := isCartanWeightVector_pinnedRep_latticeBasis
  weightLatticeBasis := ChevalleyDatum.fullWeightLatticeBasis
    (t := E7) span_range_e7MinusculeWeight_eq_top

/-- The minuscule Chevalley datum has lattice rank fifty-six. -/
@[simp] theorem chevalleyDatum_dim : chevalleyDatum.dim = 56 := (rfl)

/-- The datum uses the pinned minuscule representation. -/
@[simp] theorem chevalleyDatum_representation :
    chevalleyDatum.representation = pinnedRep := (rfl)

/-- The datum uses the integral minuscule coordinate lattice. -/
@[simp] theorem chevalleyDatum_lattice :
    chevalleyDatum.lattice = lattice.toAddSubgroup := (rfl)

/-- The datum uses the numbered coordinate basis of the minuscule lattice. -/
@[simp] theorem chevalleyDatum_basis : chevalleyDatum.basis = latticeBasis := (rfl)

/-- The weights of the datum are the native numbered minuscule weights. -/
@[simp] theorem chevalleyDatum_weight :
    chevalleyDatum.weight = e7MinusculeWeight := (rfl)

/-- The minuscule datum has the full weight lattice, not just the root lattice. -/
@[simp] theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ :=
  span_range_e7MinusculeWeight_eq_top

/-- The chosen character-lattice basis is the standard fundamental-weight basis. -/
@[simp] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin E7.rank) :
    (dsimp% only [rank] (chevalleyDatum.weightLatticeBasis i : Fin E7.rank → ℤ)) =
      Pi.single i 1 := by
  exact ChevalleyDatum.coe_fullWeightLatticeBasis
    (t := E7) span_range_e7MinusculeWeight_eq_top i

/-- Fundamental-weight torus coordinates are the original minuscule weights. -/
@[simp] theorem chevalleyDatum_coordinateWeight :
    chevalleyDatum.coordinateWeight = e7MinusculeWeight := by
  exact chevalleyDatum.coordinateWeight_eq_weight_of_coe_weightLatticeBasis
    coe_chevalleyDatum_weightLatticeBasis

/-- Root coordinates in the datum are the native simply connected root coordinates. -/
@[simp] theorem chevalleyDatum_coordinateRoot (γ : Fin E7.numRoots) :
    chevalleyDatum.coordinateRoot γ = (E7.simplyConnectedRootDatum valid_E7).root γ := by
  exact chevalleyDatum.coordinateRoot_eq_root_of_coe_weightLatticeBasis
    coe_chevalleyDatum_weightLatticeBasis γ

end

end TauCeti.E7Minuscule
