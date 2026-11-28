/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.MinusculeWeightTable
public import TauCeti.Algebra.Lie.E7.Minuscule.AdmissibleLattice

/-!
# The full-weight E₇ minuscule Chevalley datum

The fifty-six-dimensional minuscule module, with its integral coordinate lattice and numbered
weight basis, is a faithful representation of the pinned rational E₇ Lie algebra. Its weights
span the full weight lattice, so its Chevalley datum has the simply connected character lattice.
This supplies the representation and lattice input for comparing its integral Chevalley group
with the simply connected group, without asserting that comparison here.

The datum specializes `MinusculeWeightTable.chevalleyDatum` to the E₇ weight table. Its action
pulls back `E7Minuscule.rep` via `DynkinType.serreRepresentation`, which also transports
admissibility for the Kostant form.

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

/-- The minuscule table uses the transpose of the pinned E₇ Cartan matrix, as required
by Serre transport. -/
theorem weightTable_cartanMatrix_eq_transpose :
    weightTable.cartanMatrix = E7.cartanMatrixᵀ := by
  dsimp only [rank]
  rw [weightTable_cartanMatrix, cartanMatrix_E7, CartanMatrix.E_isSymm 7]

/-- The minuscule representation of the pinned rational E₇ Lie algebra, extended to its
universal enveloping algebra. -/
def pinnedRep :
    _root_.UniversalEnvelopingAlgebra ℚ (E7.lieAlgebra valid_E7) →ₐ[ℚ]
      Module.End ℚ (Fin 56 → ℚ) :=
  weightTable.pinnedRepresentation (t := E7) valid_E7 weightTable_cartanMatrix_eq_transpose

/-- The pinned minuscule action specializes the general table action. -/
theorem pinnedRep_def :
    pinnedRep = weightTable.pinnedRepresentation (t := E7) valid_E7
      weightTable_cartanMatrix_eq_transpose := (rfl)

/-- The pinned Cartan action is the existing Serre Cartan action. -/
-- This bridge is for rewriting; the matrix equation below remains the simp normal form.
theorem pinnedRep_ι_h (i : Fin E7.rank) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ ((E7.lieBasis valid_E7).h i)) =
      rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreH ℚ weightTable.cartanMatrix i)) := by
  rw [rep_def]
  exact (congrArg (fun ρ => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((E7.lieBasis valid_E7).h i)))
    (weightTable.pinnedRepresentation_def (t := E7) valid_E7
      weightTable_cartanMatrix_eq_transpose)).trans
    (serreRepresentation_ι_lieBasis_h valid_E7 weightTable_cartanMatrix_eq_transpose
      weightTable.rep i)

/-- The pinned simple-root action is the existing Serre simple-root action. -/
theorem pinnedRep_ι_rootGenerator (k : Fin E7.rank ⊕ Fin E7.rank) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E7.lieBasis valid_E7).rootGenerator k)) =
      rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix k)) := by
  rw [rep_def]
  exact weightTable.pinnedRepresentation_ι_rootGenerator (t := E7) valid_E7
    weightTable_cartanMatrix_eq_transpose k

/-- Simplifier normal form of the simple-root bridge to the Serre representation. -/
@[simp] theorem pinnedRep_ι_rootGenerator' (k : Fin E7.rank ⊕ Fin E7.rank) :
    (dsimp% only [rank] pinnedRep
      (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
        (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).rootGenerator k)))) =
      rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix k)) := by
  simpa only [rank, _root_.UniversalEnvelopingAlgebra.ι_apply] using pinnedRep_ι_rootGenerator k

/-- The pinned Cartan generator acts diagonally with the numbered minuscule weights. -/
theorem pinnedRep_ι_h_apply (i : Fin E7.rank) (v : Fin 56 → ℚ) (a : Fin 56) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ ((E7.lieBasis valid_E7).h i)) v a =
      (e7MinusculeWeight a i : ℚ) * v a := by
  refine (congrFun (weightTable.pinnedRepresentation_ι_lieBasis_h_apply (t := E7) valid_E7
    weightTable_cartanMatrix_eq_transpose i v) a).trans ?_
  dsimp only [rank] at i ⊢
  simp [Matrix.mulVec, dotProduct, MinusculeWeightTable.cartanGeneratorMatrixQ_apply]

/-- Simplifier normal form of the pinned Cartan action. -/
@[simp] theorem pinnedRep_ι_h_apply' (i : Fin E7.rank) (v : Fin 56 → ℚ) (a : Fin 56) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).h i))) v a =
      (e7MinusculeWeight a i : ℚ) * v a := by
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_ι_h_apply]

/-- The pinned positive simple-root generator acts by the integral raising matrix. -/
theorem pinnedRep_ι_e_apply (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ ((E7.lieBasis valid_E7).e i)) v =
      (raisingMatrix i).map (Int.castRingHom ℚ) *ᵥ v := by
  refine (weightTable.pinnedRepresentation_ι_lieBasis_e_apply (t := E7) valid_E7
    weightTable_cartanMatrix_eq_transpose i v).trans ?_
  dsimp only [rank] at i ⊢
  congr 1
  ext a b
  simp [Matrix.map_apply, raisingMatrix_apply]

/-- Simplifier normal form of the pinned positive simple-root action. -/
@[simp] theorem pinnedRep_ι_e_apply' (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).e i))) v =
      (raisingMatrix i).map (Int.castRingHom ℚ) *ᵥ v := by
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_ι_e_apply]

/-- The pinned negative simple-root generator acts by the integral lowering matrix. -/
theorem pinnedRep_ι_f_apply (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ ((E7.lieBasis valid_E7).f i)) v =
      (loweringMatrix i).map (Int.castRingHom ℚ) *ᵥ v := by
  refine (weightTable.pinnedRepresentation_ι_lieBasis_f_apply (t := E7) valid_E7
    weightTable_cartanMatrix_eq_transpose i v).trans ?_
  dsimp only [rank] at i ⊢
  congr 1
  ext a b
  simp [Matrix.map_apply, loweringMatrix_apply]

/-- Simplifier normal form of the pinned negative simple-root action. -/
@[simp] theorem pinnedRep_ι_f_apply' (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).f i))) v =
      (loweringMatrix i).map (Int.castRingHom ℚ) *ᵥ v := by
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_ι_f_apply]

/-- Every pinned simple-root generator acts by a square-zero endomorphism. -/
theorem pinnedRep_ι_rootGenerator_sq (k : Fin E7.rank ⊕ Fin E7.rank) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E7.lieBasis valid_E7).rootGenerator k)) ^ 2 = 0 := by
  rw [pinnedRep_ι_rootGenerator, rep_def]
  exact weightTable.rep_serreRootGenerator_pow_two k

/-- Each minuscule lattice basis vector has its recorded weight for the pinned Cartan action. -/
theorem isCartanWeightVector_pinnedRep_latticeBasis (a : Fin 56) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (E7.lieBasis valid_E7).h pinnedRep
      (e7MinusculeWeight a) (latticeBasis a : Fin 56 → ℚ) := by
  simpa only [pinnedRep_def, weightTable_weight, coe_coordinateLatticeBasis, Pi.basisFun_apply,
    coe_latticeBasis] using
    weightTable.isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis
      (t := E7) valid_E7 weightTable_cartanMatrix_eq_transpose a

/-- The pinned minuscule representation is faithful on the rational Lie algebra. -/
theorem pinnedRep_ι_injective :
    Function.Injective fun x : E7.lieAlgebra valid_E7 =>
      pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) :=
  weightTable.pinnedRepresentation_ι_injective_of_span_int (t := E7) valid_E7
    weightTable_cartanMatrix_eq_transpose (weightTable_weight ▸ span_range_e7MinusculeWeight_eq_top)

/-- The coordinate lattice is admissible for the pinned simple-generator Kostant form. -/
theorem pinnedRep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ (E7.lieAlgebra valid_E7))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm (E7.lieBasis valid_E7).rootGenerator
      (E7.lieBasis valid_E7).h) (v : Fin 56 → ℚ) (hv : v ∈ lattice.toAddSubgroup) :
    pinnedRep u v ∈ lattice.toAddSubgroup :=
  weightTable.pinnedRepresentation_kostantForm_mem_coordinateLattice (t := E7) valid_E7
    weightTable_cartanMatrix_eq_transpose u hu v hv

/-- The full-weight fifty-six-dimensional minuscule Chevalley datum of type E₇, with the
standard coordinate lattice and fundamental-weight coordinates. -/
-- The actual carrier and lattice rank must compute to compare the datum's roots with the
-- represented matrices. The component equations below are the rewriting API for consumers.
@[expose] def chevalleyDatum : ChevalleyDatum E7 valid_E7 :=
  weightTable.chevalleyDatum (t := E7) valid_E7 weightTable_cartanMatrix_eq_transpose
    (weightTable_weight ▸ span_range_e7MinusculeWeight_eq_top)

/-- The minuscule datum specializes the general full-weight table datum. -/
theorem chevalleyDatum_def :
    chevalleyDatum = weightTable.chevalleyDatum (t := E7) valid_E7
      weightTable_cartanMatrix_eq_transpose
      (weightTable_weight ▸ span_range_e7MinusculeWeight_eq_top) := (rfl)

/-- The minuscule Chevalley datum has lattice rank fifty-six. -/
@[simp] theorem chevalleyDatum_dim : chevalleyDatum.dim = 56 := (rfl)

/-- The datum uses the pinned minuscule representation. -/
@[simp] theorem chevalleyDatum_representation :
    chevalleyDatum.representation = pinnedRep := (rfl)

/-- The datum uses the integral minuscule coordinate lattice. -/
@[simp] theorem chevalleyDatum_lattice :
    chevalleyDatum.lattice = lattice.toAddSubgroup := (rfl)

/-- The datum uses the numbered coordinate basis of the minuscule lattice. -/
@[simp] theorem chevalleyDatum_basis : chevalleyDatum.basis = latticeBasis := by
  refine DFunLike.ext _ _ fun a => ?_
  apply Subtype.ext
  exact (TauCeti.coe_coordinateLatticeBasis (Fin 56) a).trans
    ((Pi.basisFun_apply ℚ (Fin 56) a).trans (coe_latticeBasis a).symm)

/-- The weights of the datum are the native numbered minuscule weights. -/
@[simp] theorem chevalleyDatum_weight :
    chevalleyDatum.weight = e7MinusculeWeight := weightTable_weight

/-- The minuscule datum has the full weight lattice, not just the root lattice. -/
@[simp] theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ := by
  rw [chevalleyDatum.weightLattice_def, chevalleyDatum_weight]
  exact span_range_e7MinusculeWeight_eq_top

/-- The chosen character-lattice basis is the standard fundamental-weight basis. -/
@[simp] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin E7.rank) :
    (dsimp% only [rank] (chevalleyDatum.weightLatticeBasis i : Fin E7.rank → ℤ)) =
      Pi.single i 1 := by
  exact weightTable.coe_chevalleyDatum_weightLatticeBasis (t := E7) valid_E7
    weightTable_cartanMatrix_eq_transpose _ i

/-- Reading the datum's character basis returns fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_weightLatticeBasis_repr
    (μ : chevalleyDatum.weightLattice) (i : Fin E7.rank) :
    (dsimp% only [rank] chevalleyDatum.weightLatticeBasis.repr μ i) =
      (μ : Fin E7.rank → ℤ) i := by
  exact weightTable.chevalleyDatum_weightLatticeBasis_repr (t := E7) valid_E7
    weightTable_cartanMatrix_eq_transpose _ μ i

/-- Fundamental-weight torus coordinates are the original minuscule weights. -/
@[simp] theorem chevalleyDatum_coordinateWeight :
    chevalleyDatum.coordinateWeight = e7MinusculeWeight := by
  exact (chevalleyDatum.coordinateWeight_eq_of_coe_weightLatticeBasis
    coe_chevalleyDatum_weightLatticeBasis).trans chevalleyDatum_weight

/-- Root coordinates in the datum are the native simply connected root coordinates. -/
@[simp] theorem chevalleyDatum_coordinateRoot (γ : Fin E7.numRoots) :
    chevalleyDatum.coordinateRoot γ = (E7.simplyConnectedRootDatum valid_E7).root γ := by
  exact chevalleyDatum.coordinateRoot_eq_of_coe_weightLatticeBasis
    coe_chevalleyDatum_weightLatticeBasis γ

end

end TauCeti.E7Minuscule
