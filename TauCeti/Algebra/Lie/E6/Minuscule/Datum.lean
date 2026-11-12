/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.E6.Minuscule.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley

/-!
# The full-weight minuscule Chevalley datum of E₆

The twenty-seven-dimensional minuscule representation is originally a representation of the
Serre presentation. Transport it along `TauCeti.DynkinType.serreLiftEquiv` to the pinned
rational Lie algebra. Its coordinate lattice remains admissible and its coordinate vectors retain
their fundamental-weight coordinates. The weights span the full weight lattice, which also proves
faithfulness: they detect every Cartan element, and faithfulness on a splitting Cartan detects
faithfulness on the Lie algebra.

These inputs form `TauCeti.E6Minuscule.chevalleyDatum`, so the represented minuscule model can
be used in comparisons of Chevalley data without assuming a comparison of the associated groups.
The matrices and integral lattice come from `TauCeti.MinusculeWeightTable`; the Lie algebra
identification is the pinned Serre isomorphism.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

local notation "𝔤" => E6.lieAlgebra valid_E6
local notation "𝔥" => E6.cartanSubalgebra valid_E6
local notation "V" => Fin 27 → ℚ
local notation "𝓑" => coordinateLatticeBasis (Fin 27)

-- The table and the pinned presentation use propositionally equal Cartan matrices. Lifting
-- the same generators directly avoids transporting the quotient type along that equality.
private def tableRepresentation : E6.SerreLieAlgebra →ₗ⁅ℚ⁆ Matrix (Fin 27) (Fin 27) ℚ :=
  TauCeti.serreLift (by
    simpa only [cartanMatrix_E6, weightTable_cartanMatrix, rank] using
      weightTable.isSerreSystemQ)

/-- The minuscule representation of the pinned rational E₆ Lie algebra, extended to its
universal enveloping algebra. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ 𝔤 →ₐ[ℚ] Module.End ℚ V :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    ((Matrix.toLinAlgEquiv' (R := ℚ) (n := Fin 27)).toAlgHom.toLieHom.comp
      (tableRepresentation.comp (E6.serreLiftEquiv valid_E6).symm.toLieHom))

/-- The numbered Cartan generator acts by the diagonal minuscule weight matrix. -/
-- Rewrite these three equations before simp unfolds the enveloping-algebra inclusion.
@[simp↓]
theorem pinnedRepresentation_ι_h (i : Fin E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E6.lieBasis valid_E6).h i)) v =
      weightTable.cartanGeneratorMatrixQ (Fin.cast rank_E6 i) *ᵥ v := by
  simp only [pinnedRepresentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
    LieHom.comp_apply, LieEquiv.coe_toLieHom, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, Matrix.toLinAlgEquiv'_apply]
  -- The pinned nodes have type `Fin E6.rank`, definitionally `Fin 6`.
  erw [E6.serreLiftEquiv_symm_lieBasis_h valid_E6 i, tableRepresentation,
    TauCeti.serreLift_serreH]
  rfl

/-- The numbered positive generator acts by the minuscule raising matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_e (i : Fin E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E6.lieBasis valid_E6).e i)) v =
      weightTable.raisingMatrixQ (Fin.cast rank_E6 i) *ᵥ v := by
  simp only [pinnedRepresentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
    LieHom.comp_apply, LieEquiv.coe_toLieHom, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, Matrix.toLinAlgEquiv'_apply]
  -- As for the Cartan equation, reduce the native rank when matching the node.
  erw [E6.serreLiftEquiv_symm_lieBasis_e valid_E6 i, tableRepresentation,
    TauCeti.serreLift_serreE]
  rfl

/-- The numbered negative generator acts by the minuscule lowering matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_f (i : Fin E6.rank) (v : V) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E6.lieBasis valid_E6).f i)) v =
      weightTable.loweringMatrixQ (Fin.cast rank_E6 i) *ᵥ v := by
  simp only [pinnedRepresentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
    LieHom.comp_apply, LieEquiv.coe_toLieHom, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, Matrix.toLinAlgEquiv'_apply]
  -- As for the Cartan equation, reduce the native rank when matching the node.
  erw [E6.serreLiftEquiv_symm_lieBasis_f valid_E6 i, tableRepresentation,
    TauCeti.serreLift_serreF]
  rfl

/-- The coordinate vectors are weight vectors for the pinned Cartan generators. -/
theorem isCartanWeightVector_pinnedRepresentation_basis (a : Fin 27) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (E6.lieBasis valid_E6).h
      pinnedRepresentation (e6MinusculeWeight a) (𝓑 a : V) := by
  refine (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr (fun i : Fin 6 => ?_)
  have h := (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (weightTable.isCartanWeightVector_coordinateLatticeBasis a) i
  calc
    _ = weightTable.cartanGeneratorMatrixQ i *ᵥ (𝓑 a : V) := pinnedRepresentation_ι_h i _
    _ = _ := by
      simpa only [MinusculeWeightTable.rep_ι_apply,
        MinusculeWeightTable.rationalSerreRepresentation_serreH, weightTable_weight] using h

-- A rank-six view keeps dependent rank reduction out of the linear-map simplifier.
private def cartanBasis6 : Module.Basis (Fin 6) ℚ 𝔥 := E6.cartanBasis valid_E6

private theorem coe_cartanBasis6 (i : Fin 6) :
    (cartanBasis6 i : 𝔤) = (E6.lieBasis valid_E6).h i :=
  E6.coe_cartanBasis valid_E6 i

private theorem pinnedRepresentation_cartan_apply (x : 𝔥) (v : V) (a : Fin 27) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ (x : 𝔤)) v a =
      (∑ i : Fin 6, cartanBasis6.repr x i * (e6MinusculeWeight a i : ℚ)) *
        v a := by
  let F : 𝔥 →ₗ[ℚ] Module.End ℚ V := pinnedRepresentation.toLinearMap.comp
    ((_root_.UniversalEnvelopingAlgebra.ι ℚ).toLinearMap.comp
      (E6.cartanSubalgebra valid_E6).incl.toLinearMap)
  have hx := congrArg F (cartanBasis6.sum_repr x)
  rw [map_sum] at hx
  simp only [map_smul] at hx
  have h := congrArg (fun g : Module.End ℚ V => g v a) hx
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at h
  have hb (i : Fin 6) : F (cartanBasis6 i) v = weightTable.cartanGeneratorMatrixQ i *ᵥ v := by
    dsimp only [F, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LieHom.coe_toLinearMap, LieSubalgebra.coe_incl]
    rw [coe_cartanBasis6]
    exact pinnedRepresentation_ι_h i v
  simp only [hb] at h
  -- `F` is the bundled linear map of the same included action.
  calc
    _ = F x v a := rfl
    _ = _ := h.symm
    _ = _ := by
      rw [Finset.sum_mul]
      congr 1
      funext i
      simp [Matrix.mulVec, dotProduct, mul_assoc]

/-- The minuscule representation is faithful on the pinned rational Lie algebra. -/
theorem pinnedRepresentation_ι_injective :
    Function.Injective fun x : 𝔤 =>
      pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  let f : 𝔤 →ₗ⁅ℚ⁆ Module.End ℚ V :=
    pinnedRepresentation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let := LieRingModule.compLieHom V f
  let := LieModule.compLieHom V f
  have : LieModule.IsFaithful ℚ 𝔥 V := by
    rw [LieModule.isFaithful_iff']
    intro x hx
    let c : Fin 6 → ℚ := cartanBasis6.repr x
    let ev : (Fin 6 → ℤ) →ₗ[ℤ] ℚ :=
      { toFun := fun μ => ∑ i, (μ i : ℚ) * c i
        map_add' := by intros; simp [Int.cast_add, add_mul, Finset.sum_add_distrib]
        map_smul' := by intros; simp [Int.cast_mul, mul_assoc, Finset.mul_sum] }
    have heval (a : Fin 27) : ev (e6MinusculeWeight a) = 0 := by
      have h := congrFun (hx (Pi.single a 1)) a
      -- The pulled-back action is definitionally evaluation of `f`; use its matrix formula.
      change pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ (x : 𝔤))
        (Pi.single a 1) a = 0 at h
      rw [pinnedRepresentation_cartan_apply] at h
      simpa [ev, c, mul_comm] using h
    have hz : ∀ μ : Fin 6 → ℤ, ev μ = 0 := by
      intro μ
      exact LinearMap.eqOn_span (f := ev) (g := 0)
        (by rintro _ ⟨a, rfl⟩; exact heval a)
        (span_range_e6MinusculeWeight_eq_top ▸ Submodule.mem_top)
    apply cartanBasis6.repr.injective
    ext i
    simpa [ev, c, Pi.single_apply] using hz (Pi.single i 1)
  have := isFaithful_of_isFaithful_cartanSubalgebra
    (K := ℚ) (L := 𝔤) (M := (Fin 27 → ℚ)) (H := 𝔥)
  exact LieModule.IsFaithful.injective_toEnd

private theorem pinnedRepresentation_rootGenerator (k : Fin 6 ⊕ Fin 6) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E6.lieBasis valid_E6).rootGenerator k)) =
      weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (serreRootGenerator weightTable.cartanMatrix k)) := by
  apply LinearMap.ext
  intro v
  -- Match the native rank-indexed generators with their rank-six table indices.
  cases k with
  | inl i =>
    erw [LieAlgebra.Basis.rootGenerator_inl, serreRootGenerator_inl,
      pinnedRepresentation_ι_e, MinusculeWeightTable.rep_ι_apply,
      MinusculeWeightTable.rationalSerreRepresentation_serreE]
    rfl
  | inr i =>
    erw [LieAlgebra.Basis.rootGenerator_inr, serreRootGenerator_inr,
      pinnedRepresentation_ι_f, MinusculeWeightTable.rep_ι_apply,
      MinusculeWeightTable.rationalSerreRepresentation_serreF]
    rfl

/-- The coordinate lattice is admissible for the pinned minuscule representation. -/
theorem pinnedRepresentation_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ 𝔤)
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (E6.lieBasis valid_E6).rootGenerator (E6.lieBasis valid_E6).h)
    (v : V) (hv : v ∈ coordinateLattice (Fin 27)) :
    pinnedRepresentation u v ∈ coordinateLattice (Fin 27) := by
  refine UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice _ _ _
    (wt := e6MinusculeWeight) ?_ ?_ ?_ hu hv
  · intro k
    -- `k` has the native rank-indexed type; the comparison uses the concrete table type.
    erw [pinnedRepresentation_rootGenerator k]
    exact weightTable.rep_serreRootGenerator_pow_two k
  · intro k w hw
    erw [pinnedRepresentation_rootGenerator k]
    exact weightTable.rep_serreRootGenerator_mem_lattice k hw
  · intro a
    have h := isCartanWeightVector_pinnedRepresentation_basis a
    rw [coe_coordinateLatticeBasis, Pi.basisFun_apply] at h
    exact h

/-- The full-weight Chevalley datum on the twenty-seven-dimensional minuscule E₆ module.
Its admissible lattice and basis are the existing integral coordinate lattice and basis. -/
-- The carrier, lattice and dimension must compute in the types of the representation and
-- basis equations; their computational values are part of this datum's interface.
@[expose] def chevalleyDatum : ChevalleyDatum E6 valid_E6 where
  carrier := V
  representation := pinnedRepresentation
  injective_representation_ι := pinnedRepresentation_ι_injective
  lattice := (coordinateLattice (Fin 27)).toAddSubgroup
  representation_mem_lattice := pinnedRepresentation_mem_lattice
  span_lattice_eq_top := Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := 27
  basis := 𝓑
  weight := fun a i => e6MinusculeWeight a (Fin.cast rank_E6 i)
  isCartanWeightVector_basis := isCartanWeightVector_pinnedRepresentation_basis
  weightLatticeBasis := (Pi.basisFun ℤ (Fin E6.rank)).map
    (LinearEquiv.ofTop _ span_range_e6MinusculeWeight_eq_top).symm

/-- The datum uses the pinned minuscule enveloping-algebra representation. -/
@[simp]
theorem chevalleyDatum_representation : chevalleyDatum.representation = pinnedRepresentation :=
  (rfl)

/-- The datum's lattice is the integral coordinate lattice of the minuscule module. -/
@[simp]
theorem chevalleyDatum_lattice :
    chevalleyDatum.lattice = (coordinateLattice (Fin 27)).toAddSubgroup :=
  (rfl)

/-- The datum uses the standard integral coordinate basis. -/
@[simp]
theorem chevalleyDatum_basis : chevalleyDatum.basis = 𝓑 :=
  (rfl)

/-- The datum retains the native minuscule weights in fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_weight_apply (a : Fin 27) (i : Fin E6.rank) :
    chevalleyDatum.weight a i = e6MinusculeWeight a (Fin.cast rank_E6 i) :=
  (rfl)

/-- The minuscule E₆ datum has the full weight lattice, not merely the root lattice. -/
@[simp]
theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ :=
  chevalleyDatum.weightLattice_def.trans span_range_e6MinusculeWeight_eq_top

/-- The chosen basis of the weight lattice is the basis of fundamental weights. -/
-- Match before simp rewrites the weights in the subtype's defining span.
@[simp↓]
theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin E6.rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin E6.rank → ℤ) = Pi.single i 1 := by
  -- The table's weight and basis types use `Fin 6`, while the datum uses `Fin E6.rank`.
  erw [chevalleyDatum, Module.Basis.map_apply]
  erw [LinearEquiv.coe_ofTop_symm_apply, Pi.basisFun_apply]

/-- The actual weight-torus coordinates are the native fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_coordinateWeight_apply (a : Fin 27) (i : Fin E6.rank) :
    chevalleyDatum.coordinateWeight a i = e6MinusculeWeight a (Fin.cast rank_E6 i) := by
  rw [chevalleyDatum.coordinateWeight_eq_weight coe_chevalleyDatum_weightLatticeBasis]
  exact chevalleyDatum_weight_apply a i

end

end TauCeti.E6Minuscule
