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

-- Use the public Cartan-matrix equation to interpret the concrete Serre generators
-- as a Serre system for the native E₆ presentation.
private theorem concreteSerreSystem :
    TauCeti.IsSerreSystem ℚ DynkinType.E6.cartanMatrixᵀ
      (serreH ℚ (CartanMatrix.E 6)ᵀ) (serreE ℚ (CartanMatrix.E 6)ᵀ)
      (serreF ℚ (CartanMatrix.E 6)ᵀ) := by
  rw [cartanMatrix_E6]
  exact TauCeti.isSerreSystem_serre ℚ (CartanMatrix.E 6)ᵀ

private def serreInverse : L →ₗ⁅ℚ⁆ Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ :=
  (TauCeti.serreLift concreteSerreSystem).comp
    (DynkinType.E6.serreLiftEquiv valid_E6).symm.toLieHom

private theorem serreInverse_h (i : Fin DynkinType.E6.rank) :
    serreInverse ((DynkinType.E6.lieBasis valid_E6).h i) =
      serreH ℚ (CartanMatrix.E 6)ᵀ i := by
  exact (congrArg (TauCeti.serreLift concreteSerreSystem)
    (DynkinType.E6.serreLiftEquiv_symm_lieBasis_h valid_E6 i)).trans
      (TauCeti.serreLift_serreH concreteSerreSystem i)

private theorem serreInverse_e (i : Fin DynkinType.E6.rank) :
    serreInverse ((DynkinType.E6.lieBasis valid_E6).e i) =
      serreE ℚ (CartanMatrix.E 6)ᵀ i := by
  exact (congrArg (TauCeti.serreLift concreteSerreSystem)
    (DynkinType.E6.serreLiftEquiv_symm_lieBasis_e valid_E6 i)).trans
      (TauCeti.serreLift_serreE concreteSerreSystem i)

private theorem serreInverse_f (i : Fin DynkinType.E6.rank) :
    serreInverse ((DynkinType.E6.lieBasis valid_E6).f i) =
      serreF ℚ (CartanMatrix.E 6)ᵀ i := by
  exact (congrArg (TauCeti.serreLift concreteSerreSystem)
    (DynkinType.E6.serreLiftEquiv_symm_lieBasis_f valid_E6 i)).trans
      (TauCeti.serreLift_serreF concreteSerreSystem i)

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
      cartanGeneratorMatrixQ i *ᵥ v := by
  rw [pinnedRepresentation_ι_apply, serreInverse_h i,
    rationalSerreRepresentation_serreH i]

/-- A pinned positive generator acts by the doubled raising matrix. -/
@[simp↓]
theorem pinnedRepresentation_e_apply (i : Fin DynkinType.E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.E6.lieBasis valid_E6).e i)) v = raisingMatrixQ i *ᵥ v := by
  rw [pinnedRepresentation_ι_apply, serreInverse_e i,
    rationalSerreRepresentation_serreE i]

/-- A pinned negative generator acts by the doubled lowering matrix. -/
@[simp↓]
theorem pinnedRepresentation_f_apply (i : Fin DynkinType.E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.E6.lieBasis valid_E6).f i)) v = loweringMatrixQ i *ᵥ v := by
  rw [pinnedRepresentation_ι_apply, serreInverse_f i,
    rationalSerreRepresentation_serreF i]

/-- Each coordinate vector retains its doubled minuscule weight under the pinned action. -/
theorem isCartanWeightVector_pinnedRepresentation_single (a : Fin 27 ⊕ Fin 27) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector
      (DynkinType.E6.lieBasis valid_E6).h pinnedRepresentation
      (e6DoubledMinusculeWeight a) (Pi.single a 1) := by
  apply (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr
  intro i
  have h := (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (isCartanWeightVector_single a) i
  simpa only [pinnedRepresentation, AlgHom.comp_apply,
    UniversalEnvelopingAlgebra.map_ι, serreInverse_h] using h

private theorem isFaithful_cartanSubalgebra :
    let ρ := pinnedRepresentation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
    letI := LieRingModule.compLieHom V ρ
    letI := LieModule.compLieHom V ρ
    LieModule.IsFaithful ℚ (DynkinType.E6.cartanSubalgebra valid_E6) V := by
  let ρ : L →ₗ⁅ℚ⁆ Module.End ℚ V :=
    pinnedRepresentation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let _ := LieRingModule.compLieHom V ρ
  let _ := LieModule.compLieHom V ρ
  have hact (x : L) (v : V) : ⁅x, v⁆ =
      pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v := by
    rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]
    rfl
  let H := DynkinType.E6.cartanSubalgebra valid_E6
  let b := DynkinType.E6.cartanBasis valid_E6
  suffices LieModule.IsFaithful ℚ H V from this
  rw [LieModule.isFaithful_iff']
  intro x hx
  let f : (Fin DynkinType.E6.rank → ℤ) →ₗ[ℤ] ℚ := Fintype.linearCombination ℤ
    (fun i => b.repr x i)
  have hweight (a : Fin 27 ⊕ Fin 27) : f (e6DoubledMinusculeWeight a) = 0 := by
    have hz := hx (Pi.single a 1)
    rw [← b.sum_repr x] at hz
    have hw := (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
      (isCartanWeightVector_pinnedRepresentation_single a)
    simp only [sum_lie, smul_lie, LieSubalgebra.coe_bracket_of_module, hact,
      b, coe_cartanBasis, hw] at hz
    have hz' := congrFun hz a
    simp only [rank_E6, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_comm, one_mul, Pi.zero_apply] at hz'
    have hsum := Fintype.linearCombination_apply ℤ (fun i => b.repr x i)
      (e6DoubledMinusculeWeight a)
    simp only [zsmul_eq_mul] at hsum
    exact hsum.trans hz'
  have hf : f = 0 := by
    apply LinearMap.ext_on (s := Set.range e6DoubledMinusculeWeight)
      span_range_e6DoubledMinusculeWeight_eq_top
    rintro _ ⟨a, rfl⟩
    exact hweight a
  apply b.repr.injective
  rw [map_zero]
  ext i
  have hi := DFunLike.congr_fun hf (Pi.single i 1)
  have hsingle := Fintype.linearCombination_apply_single ℤ (fun i => b.repr x i) i 1
  simp only [one_smul] at hsingle
  exact hsingle.symm.trans hi

/-- The pinned doubled minuscule representation is faithful on the Lie algebra. -/
theorem pinnedRepresentation_ι_injective :
    Function.Injective fun x : L =>
      pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  let ρ := pinnedRepresentation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let _ := LieRingModule.compLieHom V ρ
  let _ := LieModule.compLieHom V ρ
  have := isFaithful_cartanSubalgebra
  have : LieModule.IsFaithful ℚ L V :=
    TauCeti.isFaithful_of_isFaithful_cartanSubalgebra
      (H := DynkinType.E6.cartanSubalgebra valid_E6)
  exact (inferInstance : LieModule.IsFaithful ℚ L V).injective_toEnd

/-- The pinned Kostant form preserves the doubled minuscule coordinate lattice. -/
theorem pinnedRepresentation_kostantForm_mem_lattice
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
        exact (congrArg serreInverse
          (LieAlgebra.Basis.rootGenerator_inl (DynkinType.E6.lieBasis valid_E6) i)).trans
          ((serreInverse_e i).trans (TauCeti.serreRootGenerator_inl _ i).symm)
    | inr i =>
        exact (congrArg serreInverse
          (LieAlgebra.Basis.rootGenerator_inr (DynkinType.E6.lieBasis valid_E6) i)).trans
          ((serreInverse_f i).trans (TauCeti.serreRootGenerator_inr _ i).symm)
  have hh : (fun i => serreInverse
      ((DynkinType.E6.lieBasis valid_E6).h i)) = serreH ℚ (CartanMatrix.E 6)ᵀ := by
    funext i
    exact serreInverse_h i
  dsimp only [rank] at hm he hh
  rw [he, hh] at hm
  exact hm ▸ Subring.mem_map.mpr ⟨u, hu, rfl⟩

/-- The full-weight Chevalley datum on `V(ϖ₁) ⊕ V(ϖ₆)`, with its coordinate lattice and
fundamental-weight torus coordinates. -/
-- Its carrier, lattice and dimension must compute for the dependent representation and
-- basis equations to use the original coordinate module and lattice.
@[expose] def chevalleyDatum : DynkinType.E6.ChevalleyDatum valid_E6 where
  carrier := V
  representation := pinnedRepresentation
  injective_representation_ι := pinnedRepresentation_ι_injective
  lattice := lattice.toAddSubgroup
  representation_mem_lattice := pinnedRepresentation_kostantForm_mem_lattice
  span_lattice_eq_top := Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ) (M := lattice)
  dim := 54
  basis := matrixBasis
  weight := matrixWeight
  isCartanWeightVector_basis := by
    intro j
    have hcoe := (congrArg (fun m : lattice => (m : V)) (matrixBasis_apply j)).trans
      (coe_latticeBasis (matrixIndexEquiv.symm j))
    rw [hcoe, matrixWeight_apply]
    exact isCartanWeightVector_pinnedRepresentation_single (matrixIndexEquiv.symm j)
  weightLatticeBasis := (Pi.basisFun ℤ (Fin DynkinType.E6.rank)).map
    (LinearEquiv.ofTop _ span_range_matrixWeight_eq_top).symm

/-- The datum has the original pinned doubled minuscule action. -/
@[simp]
theorem chevalleyDatum_representation : chevalleyDatum.representation = pinnedRepresentation :=
  (rfl)

/-- The datum uses the existing doubled minuscule coordinate lattice. -/
@[simp]
theorem chevalleyDatum_lattice : chevalleyDatum.lattice = lattice.toAddSubgroup := (rfl)

/-- The doubled minuscule datum has dimension fifty-four. -/
@[simp]
theorem chevalleyDatum_dim : chevalleyDatum.dim = 54 := (rfl)

/-- The numbered basis of the datum is the coordinate basis, in block order. -/
@[simp]
theorem chevalleyDatum_basis : chevalleyDatum.basis = matrixBasis :=
  (rfl)

/-- A basis vector of the datum is the corresponding standard coordinate vector. -/
@[simp↓]
theorem coe_chevalleyDatum_basis (j : Fin 54) :
    (chevalleyDatum.basis j : chevalleyDatum.carrier) =
      Pi.single (matrixIndexEquiv.symm j) 1 := by
  exact (congrArg (fun m : lattice => (m : V)) (matrixBasis_apply j)).trans
    (coe_latticeBasis (matrixIndexEquiv.symm j))

/-- The weights of the datum are the doubled minuscule weights, in block order. -/
@[simp]
theorem chevalleyDatum_weight : chevalleyDatum.weight = matrixWeight := (rfl)

/-- The doubled minuscule datum has the full weight lattice, not just the root lattice. -/
@[simp]
theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ := by
  rw [ChevalleyDatum.weightLattice_def]
  exact span_range_matrixWeight_eq_top

/-- The character-lattice basis is transported from the full fundamental-weight lattice. -/
theorem chevalleyDatum_weightLatticeBasis :
    chevalleyDatum.weightLatticeBasis = (Pi.basisFun ℤ (Fin DynkinType.E6.rank)).map
      (LinearEquiv.ofTop _ chevalleyDatum_weightLattice).symm := (rfl)

/-- Its chosen character-lattice basis is the standard basis of fundamental weights. -/
@[simp↓]
theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin DynkinType.E6.rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin DynkinType.E6.rank → ℤ) = Pi.single i 1 := by
  simp only [chevalleyDatum_weightLatticeBasis, Module.Basis.map_apply,
    LinearEquiv.coe_ofTop_symm_apply, Pi.basisFun_apply]

/-- The torus acts through the actual doubled minuscule weights in fundamental-weight
coordinates, without a lattice-index correction. -/
@[simp]
theorem chevalleyDatum_coordinateWeight : chevalleyDatum.coordinateWeight = matrixWeight := by
  funext j
  rw [ChevalleyDatum.coordinateWeight_def, chevalleyDatum_weightLatticeBasis,
    Module.Basis.map_repr]
  simp only [LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.ofTop_apply]
  ext i
  exact Pi.basisFun_repr ℤ _ _ i

/-- Root characters are the original roots in fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_coordinateRoot (γ : Fin DynkinType.E6.numRoots) :
    chevalleyDatum.coordinateRoot γ =
      (DynkinType.E6.simplyConnectedRootDatum valid_E6).root γ := by
  rw [ChevalleyDatum.coordinateRoot_def, chevalleyDatum_weightLatticeBasis,
    Module.Basis.map_repr]
  simp only [LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.ofTop_apply]
  ext i
  exact Pi.basisFun_repr ℤ _ _ i

end

end TauCeti.E6DoubledMinuscule
