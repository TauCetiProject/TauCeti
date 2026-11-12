/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.AdmissibleLattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
import all TauCeti.LinearAlgebra.RootSystem.DynkinType
import all TauCeti.Algebra.Lie.E6.DoubledMinuscule.AdmissibleLattice
import all TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Basis
import all TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre

/-!
# The doubled minuscule Chevalley datum of type E₆

The graph-stable module `V(ϖ₁) ⊕ V(ϖ₆)` gives a full-weight Chevalley datum for the
independently pinned rational type-E₆ Lie algebra. Its action is the existing doubled
Serre representation pulled back through `DynkinType.serreLiftEquiv`. Its lattice is the
existing integral coordinate lattice, and its weight lattice is the full weight lattice,
with the fundamental weights as its chosen basis.

`chevalleyDatum` makes this represented module available to comparisons of Chevalley data.
The positive and negative simple generators retain the doubled matrices, including the
negative signs on the contragredient block. This construction does not identify its group
scheme with any other group scheme.

The construction uses `E6DoubledMinuscule.rep` and its admissibility theorem,
`DynkinType.serreLiftEquiv`, and the splitting-Cartan faithfulness criterion
`TauCeti.isFaithful_of_isFaithful_cartanSubalgebra`. Faithfulness is detected by the
spanning doubled minuscule weights.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing LieRing.instLieAlgebra

noncomputable section

local notation "L" => DynkinType.E6.lieAlgebra valid_E6
local notation "V" => (Fin 27 ⊕ Fin 27) → ℚ

private def serreInverse : L →ₗ⁅ℚ⁆ Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ := by
  have f := (DynkinType.E6.serreLiftEquiv valid_E6).symm.toLieHom
  dsimp only [SerreLieAlgebra, cartanMatrix, rank] at f
  exact f

private theorem serreInverse_h (i : Fin DynkinType.E6.rank) :
    serreInverse ((DynkinType.E6.lieBasis valid_E6).h i) =
      serreH ℚ (CartanMatrix.E 6)ᵀ (Fin.cast rank_E6 i) := by
  -- Normalize the concrete Cartan matrix and its native node-index type together.
  convert DynkinType.E6.serreLiftEquiv_symm_lieBasis_h valid_E6 i using 1
  rfl

private theorem serreInverse_e (i : Fin DynkinType.E6.rank) :
    serreInverse ((DynkinType.E6.lieBasis valid_E6).e i) =
      serreE ℚ (CartanMatrix.E 6)ᵀ (Fin.cast rank_E6 i) := by
  convert DynkinType.E6.serreLiftEquiv_symm_lieBasis_e valid_E6 i using 1
  rfl

private theorem serreInverse_f (i : Fin DynkinType.E6.rank) :
    serreInverse ((DynkinType.E6.lieBasis valid_E6).f i) =
      serreF ℚ (CartanMatrix.E 6)ᵀ (Fin.cast rank_E6 i) := by
  convert DynkinType.E6.serreLiftEquiv_symm_lieBasis_f valid_E6 i using 1
  rfl

/-- The doubled minuscule action of the pinned type-E₆ Lie algebra, extended to its
universal enveloping algebra. -/
def pinnedRepresentation : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V :=
  rep.comp (UniversalEnvelopingAlgebra.map ℚ serreInverse)

private theorem pinnedRepresentation_ι_apply (x : L) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v =
      rationalSerreRepresentation (serreInverse x) *ᵥ v := by
  rw [pinnedRepresentation, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    rep_ι_apply]

/-- A pinned Cartan generator acts by the doubled diagonal Cartan matrix. -/
@[simp↓]
theorem pinnedRepresentation_h_apply (i : Fin DynkinType.E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.E6.lieBasis valid_E6).h i)) v =
      cartanGeneratorMatrixQ (Fin.cast rank_E6 i) *ᵥ v := by
  rw [pinnedRepresentation_ι_apply, serreInverse_h,
    rationalSerreRepresentation_serreH]

/-- A pinned positive generator acts by the doubled raising matrix. -/
@[simp↓]
theorem pinnedRepresentation_e_apply (i : Fin DynkinType.E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.E6.lieBasis valid_E6).e i)) v = raisingMatrixQ (Fin.cast rank_E6 i) *ᵥ v := by
  rw [pinnedRepresentation_ι_apply, serreInverse_e,
    rationalSerreRepresentation_serreE]

/-- A pinned negative generator acts by the doubled lowering matrix. -/
@[simp↓]
theorem pinnedRepresentation_f_apply (i : Fin DynkinType.E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.E6.lieBasis valid_E6).f i)) v = loweringMatrixQ (Fin.cast rank_E6 i) *ᵥ v := by
  rw [pinnedRepresentation_ι_apply, serreInverse_f,
    rationalSerreRepresentation_serreF]

private theorem pinnedRepresentation_cartanBasis_apply (i : Fin DynkinType.E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (DynkinType.E6.cartanBasis valid_E6 i : L)) v =
      cartanGeneratorMatrixQ (Fin.cast rank_E6 i) *ᵥ v := by
  rw [coe_cartanBasis, pinnedRepresentation_h_apply]

/-- The pinned doubled minuscule representation is faithful on the Lie algebra. -/
theorem pinnedRepresentation_injective :
    Function.Injective fun x : L =>
      pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  let ρ : L →ₗ⁅ℚ⁆ Module.End ℚ V :=
    pinnedRepresentation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let _ := LieRingModule.compLieHom V ρ
  let _ := LieModule.compLieHom V ρ
  have hact (x : L) (v : V) : ⁅x, v⁆ =
      pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v := rfl
  let H := DynkinType.E6.cartanSubalgebra valid_E6
  let b := DynkinType.E6.cartanBasis valid_E6
  have : LieModule.IsFaithful ℚ H V := by
    rw [LieModule.isFaithful_iff']
    intro x hx
    let f : (Fin 6 → ℤ) →ₗ[ℤ] ℚ := Fintype.linearCombination ℤ
      (fun i => b.repr x (Fin.cast rank_E6.symm i))
    have hweight (a : Fin 27 ⊕ Fin 27) : f (e6DoubledMinusculeWeight a) = 0 := by
      have hz := hx (Pi.single a 1)
      rw [← b.sum_repr x] at hz
      simp only [sum_lie, smul_lie, LieSubalgebra.coe_bracket_of_module, hact,
        b, pinnedRepresentation_cartanBasis_apply] at hz
      have hz' := congrFun hz a
      dsimp only [rank] at hz' ⊢
      simp only [Fin.cast_eq_self, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
        Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, cartanGeneratorMatrixQ_apply,
        ↓reduceIte, smul_eq_mul, mul_comm, Pi.zero_apply] at hz'
      simp only [f, Fintype.linearCombination_apply, zsmul_eq_mul, rank, Fin.cast, b]
      -- Only the concrete/native rank casts remain after evaluating the Cartan action.
      convert hz' using 1
      rfl
    have hf : f = 0 := by
      apply LinearMap.ext_on (s := Set.range e6DoubledMinusculeWeight)
        span_range_e6DoubledMinusculeWeight_eq_top
      rintro _ ⟨a, rfl⟩
      exact hweight a
    apply b.repr.injective
    rw [map_zero]
    ext i
    have hi := DFunLike.congr_fun hf (Pi.single (Fin.cast rank_E6 i) 1)
    simp only [f, Fintype.linearCombination_apply_single, one_smul,
      LinearMap.zero_apply] at hi
    dsimp only [rank, Fin.cast] at hi ⊢
    convert hi using 1
    rfl
  have : LieModule.IsFaithful ℚ L V :=
    TauCeti.isFaithful_of_isFaithful_cartanSubalgebra (H := H)
  exact (inferInstance : LieModule.IsFaithful ℚ L V).injective_toEnd

/-- The pinned Kostant form preserves the doubled minuscule coordinate lattice. -/
theorem pinnedRepresentation_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ L)
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (DynkinType.E6.lieBasis valid_E6).rootGenerator (DynkinType.E6.lieBasis valid_E6).h)
    (v : V) (hv : v ∈ lattice) : pinnedRepresentation u v ∈ lattice := by
  apply rep_serreKostantForm_mem_lattice (hv := hv)
  rw [serreKostantForm_def]
  have hm := UniversalEnvelopingAlgebra.map_kostantForm serreInverse
    (DynkinType.E6.lieBasis valid_E6).rootGenerator (DynkinType.E6.lieBasis valid_E6).h
  have he : (fun i : Fin 6 ⊕ Fin 6 => serreInverse
      ((DynkinType.E6.lieBasis valid_E6).rootGenerator i)) =
      serreRootGenerator (CartanMatrix.E 6)ᵀ := by
    funext i
    cases i with
    | inl i =>
        convert serreInverse_e (Fin.cast rank_E6.symm i) using 1 <;> rfl
    | inr i =>
        convert serreInverse_f (Fin.cast rank_E6.symm i) using 1 <;> rfl
  have hh : (fun i => serreInverse
      ((DynkinType.E6.lieBasis valid_E6).h i)) = serreH ℚ (CartanMatrix.E 6)ᵀ := by
    funext i
    exact serreInverse_h i
  dsimp only [rank] at hm he hh
  rw [he, hh] at hm
  exact hm ▸ Subring.mem_map.mpr ⟨u, hu, rfl⟩

/-- Each coordinate vector retains its doubled minuscule weight under the pinned action. -/
theorem isCartanWeightVector_pinnedRepresentation_single (a : Fin 27 ⊕ Fin 27) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector
      (DynkinType.E6.lieBasis valid_E6).h pinnedRepresentation
      (fun i => e6DoubledMinusculeWeight a (Fin.cast rank_E6 i)) (Pi.single a 1) := by
  apply (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr
  intro i
  ext c
  simp [cartanGeneratorMatrixQ_apply, Pi.single_apply]

/-- The full-weight Chevalley datum on `V(ϖ₁) ⊕ V(ϖ₆)`, with its coordinate lattice and
fundamental-weight torus coordinates. -/
-- Its carrier, lattice and dimension must compute for the dependent representation and
-- basis equations to use the original coordinate module and lattice.
@[expose] def chevalleyDatum : DynkinType.E6.ChevalleyDatum valid_E6 where
  carrier := V
  representation := pinnedRepresentation
  injective_representation_ι := pinnedRepresentation_injective
  lattice := lattice.toAddSubgroup
  representation_mem_lattice := pinnedRepresentation_mem_lattice
  span_lattice_eq_top := by
    exact Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
      (M := coordinateLattice (Fin 27 ⊕ Fin 27))
  dim := 54
  basis := latticeBasis.reindex finSumFinEquiv
  weight := fun j i => e6DoubledMinusculeWeight
    ((finSumFinEquiv : Fin 27 ⊕ Fin 27 ≃ Fin 54).symm j) (Fin.cast rank_E6 i)
  isCartanWeightVector_basis := by
    intro j
    simpa only [Module.Basis.reindex_apply, coe_latticeBasis] using
      isCartanWeightVector_pinnedRepresentation_single (finSumFinEquiv.symm j)
  weightLatticeBasis := (Pi.basisFun ℤ (Fin DynkinType.E6.rank)).map
    (LinearEquiv.ofTop _ (by
      convert (congrArg (Submodule.span ℤ) (EquivLike.range_comp
        e6DoubledMinusculeWeight
        (finSumFinEquiv : Fin 27 ⊕ Fin 27 ≃ Fin 54).symm)).trans
        span_range_e6DoubledMinusculeWeight_eq_top using 1 <;> rfl)).symm

/-- The datum has the original pinned doubled minuscule action. -/
@[simp]
theorem chevalleyDatum_representation : chevalleyDatum.representation = pinnedRepresentation :=
  (rfl)

/-- The datum uses the existing doubled minuscule coordinate lattice. -/
@[simp]
theorem chevalleyDatum_lattice : chevalleyDatum.lattice = lattice.toAddSubgroup := (rfl)

/-- The numbered basis of the datum is the coordinate basis, in block order. -/
@[simp]
theorem chevalleyDatum_basis : chevalleyDatum.basis = latticeBasis.reindex finSumFinEquiv :=
  (rfl)

/-- A basis vector of the datum is the corresponding standard coordinate vector. -/
@[simp↓]
theorem coe_chevalleyDatum_basis (j : Fin 54) :
    (chevalleyDatum.basis j : chevalleyDatum.carrier) =
      Pi.single (finSumFinEquiv.symm j) 1 := by
  have hb := Module.Basis.reindex_apply latticeBasis finSumFinEquiv j
  exact (congrArg (fun m : lattice => (m : V)) hb).trans
    (coe_latticeBasis (finSumFinEquiv.symm j))

/-- The weights of the datum are the doubled minuscule weights, in block order. -/
@[simp]
theorem chevalleyDatum_weight (j : Fin 54) (i : Fin DynkinType.E6.rank) :
    chevalleyDatum.weight j i =
      e6DoubledMinusculeWeight (finSumFinEquiv.symm j) (Fin.cast rank_E6 i) := (rfl)

/-- The doubled minuscule datum has the full weight lattice, not just the root lattice. -/
@[simp]
theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ := by
  rw [ChevalleyDatum.weightLattice_def]
  convert (congrArg (Submodule.span ℤ) (EquivLike.range_comp
    e6DoubledMinusculeWeight
    (finSumFinEquiv : Fin 27 ⊕ Fin 27 ≃ Fin 54).symm)).trans
    span_range_e6DoubledMinusculeWeight_eq_top using 1 <;> rfl

/-- Its chosen character-lattice basis is the standard basis of fundamental weights. -/
@[simp↓]
theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin DynkinType.E6.rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin DynkinType.E6.rank → ℤ) = Pi.single i 1 := by
  rw [chevalleyDatum, Module.Basis.map_apply]
  exact congrArg (fun v : Fin DynkinType.E6.rank → ℤ => v)
    (Pi.basisFun_apply ℤ (Fin DynkinType.E6.rank) i)

/-- The torus acts through the actual doubled minuscule weights in fundamental-weight
coordinates, without a lattice-index correction. -/
@[simp]
theorem chevalleyDatum_coordinateWeight (j : Fin 54) (i : Fin DynkinType.E6.rank) :
    chevalleyDatum.coordinateWeight j i =
      e6DoubledMinusculeWeight (finSumFinEquiv.symm j) (Fin.cast rank_E6 i) := by
  have h := congrFun (chevalleyDatum.sum_coordinateWeight_smul j) i
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, coe_chevalleyDatum_weightLatticeBasis, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, chevalleyDatum_weight, Finset.sum_ite_eq] using h

end

end TauCeti.E6DoubledMinuscule
