/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.MinusculeWeightTable
public import TauCeti.Algebra.Lie.E6.Minuscule.Basic

/-!
# The full-weight minuscule Chevalley datum of E₆

Specialize `TauCeti.MinusculeWeightTable.chevalleyDatum` to the twenty-seven-dimensional
minuscule weight table. The representation of the Serre presentation is transported along
`TauCeti.DynkinType.serreLiftEquiv` to the pinned rational Lie algebra. The coordinate lattice
is admissible, and the weights span the full weight lattice, proving faithfulness.

The resulting `TauCeti.E6Minuscule.chevalleyDatum` can be used in comparisons of Chevalley data
without assuming a comparison of the associated groups. Its torus coordinates are the native
fundamental-weight coordinates of the minuscule model.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open DynkinType

noncomputable section

local notation "𝔤" => E6.lieAlgebra valid_E6
local notation "V" => Fin 27 → ℚ
local notation "𝓑" => coordinateLatticeBasis (Fin 27)

/-- The minuscule representation of the pinned rational E₆ Lie algebra, extended to its
universal enveloping algebra. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ 𝔤 →ₐ[ℚ] Module.End ℚ V :=
  weightTable.pinnedRepresentation (t := E6) valid_E6 (by
    simpa only [cartanMatrix_E6, rank] using weightTable_cartanMatrix)

/-- The numbered Cartan generator acts by the diagonal minuscule weight matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_h_apply (i : Fin E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E6.lieBasis valid_E6).h i)) v =
      weightTable.cartanGeneratorMatrixQ (Fin.cast rank_E6 i) *ᵥ v :=
  weightTable.pinnedRepresentation_ι_lieBasis_h_apply (t := E6) valid_E6 _ i v

/-- The numbered positive generator acts by the minuscule raising matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_e_apply (i : Fin E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E6.lieBasis valid_E6).e i)) v =
      weightTable.raisingMatrixQ (Fin.cast rank_E6 i) *ᵥ v :=
  weightTable.pinnedRepresentation_ι_lieBasis_e_apply (t := E6) valid_E6 _ i v

/-- The numbered negative generator acts by the minuscule lowering matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_f_apply (i : Fin E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E6.lieBasis valid_E6).f i)) v =
      weightTable.loweringMatrixQ (Fin.cast rank_E6 i) *ᵥ v :=
  weightTable.pinnedRepresentation_ι_lieBasis_f_apply (t := E6) valid_E6 _ i v

/-- The coordinate vectors are weight vectors for the pinned Cartan generators. -/
theorem isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis (a : Fin 27) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (E6.lieBasis valid_E6).h
      pinnedRepresentation (e6MinusculeWeight a) (𝓑 a : V) := by
  rw [pinnedRepresentation, ← weightTable_weight]
  exact weightTable.isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis
    (t := E6) valid_E6 _ a

/-- The minuscule representation is faithful on the pinned rational Lie algebra. -/
theorem pinnedRepresentation_ι_injective :
    Function.Injective fun x : 𝔤 =>
      pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) :=
  weightTable.pinnedRepresentation_ι_injective_of_span_int (t := E6) valid_E6 _
    (by rw [weightTable_weight]; exact span_range_e6MinusculeWeight_eq_top)

/-- The pinned root-generator action agrees with the minuscule Serre action. -/
theorem pinnedRepresentation_ι_rootGenerator (k : Fin E6.rank ⊕ Fin E6.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E6.lieBasis valid_E6).rootGenerator k)) =
      weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (serreRootGenerator weightTable.cartanMatrix
          (Sum.map (Fin.cast rank_E6) (Fin.cast rank_E6) k))) := by
  cases k <;> exact weightTable.pinnedRepresentation_ι_rootGenerator (t := E6) valid_E6 _ _

/-- The coordinate lattice is admissible for the pinned simple-generator Kostant form. -/
theorem pinnedRepresentation_kostantForm_mem_coordinateLattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ 𝔤)
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (E6.lieBasis valid_E6).rootGenerator (E6.lieBasis valid_E6).h)
    (v : V) (hv : v ∈ coordinateLattice (Fin 27)) :
    pinnedRepresentation u v ∈ coordinateLattice (Fin 27) :=
  weightTable.pinnedRepresentation_kostantForm_mem_coordinateLattice
    (t := E6) valid_E6 _ u hu v hv

/-- The full-weight Chevalley datum on the twenty-seven-dimensional minuscule E₆ module.
Its admissible lattice and basis are the existing integral coordinate lattice and basis. -/
@[expose] def chevalleyDatum : ChevalleyDatum E6 valid_E6 :=
  weightTable.chevalleyDatum (t := E6) valid_E6
    (by simpa only [cartanMatrix_E6, rank] using weightTable_cartanMatrix)
    (by rw [weightTable_weight]; exact span_range_e6MinusculeWeight_eq_top)

/-- The datum has dimension twenty-seven. -/
@[simp] theorem chevalleyDatum_dim : chevalleyDatum.dim = 27 := rfl

/-- The datum uses the pinned minuscule enveloping-algebra representation. -/
@[simp]
theorem chevalleyDatum_representation : chevalleyDatum.representation = pinnedRepresentation :=
  weightTable.chevalleyDatum_representation (t := E6) valid_E6 _ _

/-- The datum's lattice is the integral coordinate lattice of the minuscule module. -/
@[simp]
theorem chevalleyDatum_lattice :
    chevalleyDatum.lattice = (coordinateLattice (Fin 27)).toAddSubgroup := rfl

/-- The datum uses the standard integral coordinate basis. -/
@[simp]
theorem chevalleyDatum_basis : chevalleyDatum.basis = 𝓑 := rfl

/-- The datum retains the native minuscule weights in fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_weight : chevalleyDatum.weight = e6MinusculeWeight :=
  (weightTable.chevalleyDatum_weight (t := E6) valid_E6 _ _).trans weightTable_weight

/-- Evaluating a datum weight uses the table's rank-six index. -/
-- Match the native-rank application before the unapplied weight equation is simplified.
@[simp↓]
theorem chevalleyDatum_weight_apply (a : Fin 27) (i : Fin E6.rank) :
    chevalleyDatum.weight a i = e6MinusculeWeight a (Fin.cast rank_E6 i) := by
  rw [chevalleyDatum_weight]
  rfl

/-- The minuscule E₆ datum has the full weight lattice, not merely the root lattice. -/
@[simp]
theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ :=
  weightTable.chevalleyDatum_weightLattice (t := E6) valid_E6 _ _

/-- The chosen basis of the weight lattice is the basis of fundamental weights. -/
@[simp↓]
theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin E6.rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin E6.rank → ℤ) = Pi.single i 1 :=
  weightTable.coe_chevalleyDatum_weightLatticeBasis (t := E6) valid_E6 _ _ i

/-- The actual weight-torus coordinates are the native fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_coordinateWeight : chevalleyDatum.coordinateWeight = e6MinusculeWeight :=
  (weightTable.chevalleyDatum_coordinateWeight (t := E6) valid_E6 _ _).trans weightTable_weight

/-- Evaluating a coordinate weight uses the table's rank-six index. -/
@[simp↓]
theorem chevalleyDatum_coordinateWeight_apply (a : Fin 27) (i : Fin E6.rank) :
    chevalleyDatum.coordinateWeight a i = e6MinusculeWeight a (Fin.cast rank_E6 i) := by
  rw [chevalleyDatum_coordinateWeight]
  rfl

/-- The root-torus coordinates are the native fundamental-weight coordinates of the roots. -/
@[simp]
theorem chevalleyDatum_coordinateRoot : chevalleyDatum.coordinateRoot = e6Root := by
  rw [chevalleyDatum.coordinateRoot_eq_root coe_chevalleyDatum_weightLatticeBasis,
    simplyConnectedRootDatum_E6, e6SimplyConnectedRootDatum_root]
  rfl

end

end TauCeti.E6Minuscule
