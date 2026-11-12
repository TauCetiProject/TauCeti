/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.E7.Minuscule.AdmissibleLattice
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Killing
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley

/-!
# The full-weight E₇ minuscule Chevalley datum

The fifty-six-dimensional minuscule module, with its integral coordinate lattice and numbered
weight basis, is a faithful representation of the pinned rational E₇ Lie algebra. Its weights
span the full weight lattice, so its Chevalley datum has the simply connected character lattice.
This supplies the representation and lattice input for comparing its integral Chevalley group
with the simply connected group, without asserting that comparison here.

The action uses `DynkinType.serreLiftEquiv` and the rational Serre matrices of
`E7Minuscule.weightTable`. Admissibility is obtained from the square-zero simple-root operators
and the integral weights, using `kostantForm_apply_mem_coordinateLattice`.

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
      (fun i => weightTable.cartanGeneratorMatrixQ (Fin.cast rank_E7 i))
      (fun i => weightTable.raisingMatrixQ (Fin.cast rank_E7 i))
      (fun i => weightTable.loweringMatrixQ (Fin.cast rank_E7 i)) := by
  dsimp only [rank]
  rw [cartanMatrix_E7, CartanMatrix.E_isSymm 7]
  simpa only [Fin.cast_eq_self, weightTable_cartanMatrix] using weightTable.isSerreSystemQ

private def pinnedMatrixAction :
    E7.lieAlgebra valid_E7 →ₗ⁅ℚ⁆ Matrix (Fin 56) (Fin 56) ℚ :=
  (TauCeti.serreLift pinnedSerreSystem).comp (E7.serreLiftEquiv valid_E7).symm.toLieHom

private theorem pinnedMatrixAction_h (i : Fin E7.rank) :
    pinnedMatrixAction ((E7.lieBasis valid_E7).h i) =
      weightTable.cartanGeneratorMatrixQ (Fin.cast rank_E7 i) := by
  rw [pinnedMatrixAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    E7.serreLiftEquiv_symm_lieBasis_h valid_E7 i]
  exact TauCeti.serreLift_serreH pinnedSerreSystem i

private theorem pinnedMatrixAction_e (i : Fin E7.rank) :
    pinnedMatrixAction ((E7.lieBasis valid_E7).e i) =
      weightTable.raisingMatrixQ (Fin.cast rank_E7 i) := by
  rw [pinnedMatrixAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    E7.serreLiftEquiv_symm_lieBasis_e valid_E7 i]
  exact TauCeti.serreLift_serreE pinnedSerreSystem i

private theorem pinnedMatrixAction_f (i : Fin E7.rank) :
    pinnedMatrixAction ((E7.lieBasis valid_E7).f i) =
      weightTable.loweringMatrixQ (Fin.cast rank_E7 i) := by
  rw [pinnedMatrixAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    E7.serreLiftEquiv_symm_lieBasis_f valid_E7 i]
  exact TauCeti.serreLift_serreF pinnedSerreSystem i

private def pinnedAction :
    E7.lieAlgebra valid_E7 →ₗ⁅ℚ⁆ Module.End ℚ (Fin 56 → ℚ) :=
  (Matrix.toLinAlgEquiv (Pi.basisFun ℚ (Fin 56))).toAlgHom.toLieHom.comp pinnedMatrixAction

/-- The minuscule representation of the pinned rational E₇ Lie algebra, extended to its
universal enveloping algebra. -/
def pinnedRep :
    _root_.UniversalEnvelopingAlgebra ℚ (E7.lieAlgebra valid_E7) →ₐ[ℚ]
      Module.End ℚ (Fin 56 → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ pinnedAction

private theorem pinnedRep_ι_apply (x : E7.lieAlgebra valid_E7) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = pinnedMatrixAction x *ᵥ v := by
  simp only [pinnedRep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply, pinnedAction,
    LieHom.comp_apply, AlgHom.toLieHom_apply, AlgEquiv.toAlgHom_apply,
    Matrix.toLinAlgEquiv_apply]
  exact (Pi.basisFun ℚ (Fin 56)).sum_repr _

-- Normalize the inclusion and native rank in the simp keys, before simp reduces them at use sites.
/-- The pinned Cartan generator acts diagonally with the numbered minuscule weights. -/
@[simp]
theorem pinnedRep_h (i : Fin E7.rank) (v : Fin 56 → ℚ) (a : Fin 56) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).h i))) v a =
      (e7MinusculeWeight a (Fin.cast rank_E7 i) : ℚ) * v a := by
  have h := pinnedRep_ι_apply ((E7.lieBasis valid_E7).h i) v
  rw [pinnedMatrixAction_h] at h
  simpa [Matrix.mulVec, dotProduct, MinusculeWeightTable.cartanGeneratorMatrixQ_apply]
    using congrFun h a

/-- The pinned positive simple-root generator acts by the integral raising matrix. -/
@[simp]
theorem pinnedRep_e (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).e i))) v =
      (raisingMatrix (Fin.cast rank_E7 i)).map (Int.castRingHom ℚ) *ᵥ v := by
  have h := pinnedRep_ι_apply ((E7.lieBasis valid_E7).e i) v
  rw [pinnedMatrixAction_e] at h
  refine h.trans ?_
  congr 1
  ext a b
  simp [Matrix.map_apply, raisingMatrix_apply]

/-- The pinned negative simple-root generator acts by the integral lowering matrix. -/
@[simp]
theorem pinnedRep_f (i : Fin E7.rank) (v : Fin 56 → ℚ) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (E7.lieAlgebra valid_E7)
      (TensorAlgebra.ι ℚ ((E7.lieBasis valid_E7).f i))) v =
      (loweringMatrix (Fin.cast rank_E7 i)).map (Int.castRingHom ℚ) *ᵥ v := by
  have h := pinnedRep_ι_apply ((E7.lieBasis valid_E7).f i) v
  rw [pinnedMatrixAction_f] at h
  refine h.trans ?_
  congr 1
  ext a b
  simp [Matrix.map_apply, loweringMatrix_apply]

private theorem pinnedAction_apply (x : E7.lieAlgebra valid_E7) (v : Fin 56 → ℚ) :
    pinnedAction x v = pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v := by
  rw [pinnedRep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]

/-- The pinned minuscule representation is faithful on the rational Lie algebra. -/
theorem injective_pinnedRep_ι :
    Function.Injective fun x : E7.lieAlgebra valid_E7 =>
      pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  let := LieRingModule.compLieHom (Fin 56 → ℚ) pinnedAction
  let := LieModule.compLieHom (Fin 56 → ℚ) pinnedAction
  have hcartan : LieModule.IsFaithful ℚ (E7.cartanSubalgebra valid_E7) (Fin 56 → ℚ) := by
    rw [LieModule.isFaithful_iff']
    intro x hx
    let c := (E7.cartanBasis valid_E7).repr x
    let f : (Fin 7 → ℤ) →ₗ[ℤ] ℚ :=
      ∑ i : Fin E7.rank,
        (LinearMap.proj (Fin.cast rank_E7 i) : (Fin 7 → ℤ) →ₗ[ℤ] ℤ).smulRight (c i)
    have hw (a : Fin 56) : f (e7MinusculeWeight a) = 0 := by
      have h := congrFun (hx (Pi.single a 1)) a
      -- Expand the Cartan element in the pinned coroot basis before evaluating the action.
      have heq : (x : E7.lieAlgebra valid_E7) =
          ∑ i, c i • (E7.lieBasis valid_E7).h i := by
        simpa only [map_sum, map_smul, LieSubalgebra.coe_incl, coe_cartanBasis] using
          congrArg (E7.cartanSubalgebra valid_E7).incl
            ((E7.cartanBasis valid_E7).sum_repr x).symm
      simp only [LieSubalgebra.coe_bracket_of_module, LieRingModule.compLieHom_apply,
        Module.End.lie_apply, heq, map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp_rw [pinnedAction_apply, _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_h] at h
      simpa [f, Int.cast_smul_eq_zsmul, mul_comm] using h
    have hf : ∀ w, f w = 0 := by
      intro w
      exact LinearMap.eqOn_span (f := f) (g := 0) (by rintro _ ⟨a, rfl⟩; exact hw a)
        (span_range_e7MinusculeWeight_eq_top ▸ Submodule.mem_top)
    apply (E7.cartanBasis valid_E7).repr.injective
    ext i
    have h := hf (Pi.single (Fin.cast rank_E7 i) 1)
    simp only [f, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Pi.single_apply, (Fin.cast_injective rank_E7).eq_iff] at h
    simpa only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, c, map_zero, Finsupp.zero_apply] using h
  have := hcartan
  have := isFaithful_of_isFaithful_cartanSubalgebra
    (K := ℚ) (L := E7.lieAlgebra valid_E7) (M := Fin 56 → ℚ)
    (H := E7.cartanSubalgebra valid_E7)
  intro x y hxy
  apply (LieModule.IsFaithful.injective_toEnd (R := ℚ) (M := Fin 56 → ℚ))
  apply LinearMap.ext
  intro v
  exact (pinnedAction_apply x v).trans ((congrArg (fun f => f v) hxy).trans
    (pinnedAction_apply y v).symm)

private theorem pinnedRep_rootGenerator_sq (k : Fin E7.rank ⊕ Fin E7.rank) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E7.lieBasis valid_E7).rootGenerator k)) ^ 2 = 0 := by
  apply LinearMap.ext
  intro v
  cases k with
  | inl i =>
      simp only [LieAlgebra.Basis.rootGenerator_inl, pow_two, _root_.mul_apply_eq_comp,
        _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_e, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, raisingMatrix_mul_self,
        Matrix.map_zero _ (map_zero (Int.castRingHom ℚ)), Matrix.zero_mulVec,
        LinearMap.zero_apply]
  | inr i =>
      simp only [LieAlgebra.Basis.rootGenerator_inr, pow_two, _root_.mul_apply_eq_comp,
        _root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_f, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, loweringMatrix_mul_self,
        Matrix.map_zero _ (map_zero (Int.castRingHom ℚ)), Matrix.zero_mulVec,
        LinearMap.zero_apply]

private theorem pinnedRep_rootGenerator_mem_lattice (k : Fin E7.rank ⊕ Fin E7.rank)
    {v : Fin 56 → ℚ} (hv : v ∈ coordinateLattice (Fin 56)) :
    pinnedRep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((E7.lieBasis valid_E7).rootGenerator k)) v ∈ coordinateLattice (Fin 56) := by
  cases k with
  | inl i =>
      rw [LieAlgebra.Basis.rootGenerator_inl, _root_.UniversalEnvelopingAlgebra.ι_apply,
        pinnedRep_e]
      simpa only [matrixIntCastLieHom_eq_map, Int.coe_castRingHom] using
        Matrix.intCastLieHom_mulVec_mem_coordinateLattice (raisingMatrix (Fin.cast rank_E7 i)) hv
  | inr i =>
      rw [LieAlgebra.Basis.rootGenerator_inr, _root_.UniversalEnvelopingAlgebra.ι_apply,
        pinnedRep_f]
      simpa only [matrixIntCastLieHom_eq_map, Int.coe_castRingHom] using
        Matrix.intCastLieHom_mulVec_mem_coordinateLattice (loweringMatrix (Fin.cast rank_E7 i)) hv

/-- Each minuscule lattice basis vector has its recorded weight for the pinned Cartan action. -/
theorem isCartanWeightVector_pinnedRep_latticeBasis (a : Fin 56) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (E7.lieBasis valid_E7).h pinnedRep
      (fun i => e7MinusculeWeight a (Fin.cast rank_E7 i)) (latticeBasis a : Fin 56 → ℚ) := by
  rw [coe_latticeBasis]
  apply (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr
  intro i
  funext b
  rw [_root_.UniversalEnvelopingAlgebra.ι_apply, pinnedRep_h]
  simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all

/-- The coordinate lattice is admissible for the pinned simple-generator Kostant form. -/
theorem pinnedRep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ (E7.lieAlgebra valid_E7))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm (E7.lieBasis valid_E7).rootGenerator
      (E7.lieBasis valid_E7).h) (v : Fin 56 → ℚ) (hv : v ∈ lattice.toAddSubgroup) :
    pinnedRep u v ∈ lattice.toAddSubgroup := by
  rw [lattice_def] at hv ⊢
  apply UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice
    (E7.lieBasis valid_E7).rootGenerator (E7.lieBasis valid_E7).h pinnedRep
    (wt := fun a i => e7MinusculeWeight a (Fin.cast rank_E7 i))
    pinnedRep_rootGenerator_sq (fun _ _ hw => pinnedRep_rootGenerator_mem_lattice _ hw)
    _ hu hv
  intro a
  simpa only [coe_latticeBasis] using isCartanWeightVector_pinnedRep_latticeBasis a

/-- The full-weight fifty-six-dimensional minuscule Chevalley datum of type E₇, with the
standard coordinate lattice and fundamental-weight coordinates. -/
-- The actual carrier and lattice rank must compute to compare the datum's roots with the
-- represented matrices. The component equations below are the rewriting API for consumers.
@[expose] def chevalleyDatum : ChevalleyDatum E7 valid_E7 where
  carrier := Fin 56 → ℚ
  representation := pinnedRep
  injective_representation_ι := injective_pinnedRep_ι
  lattice := lattice.toAddSubgroup
  representation_mem_lattice := pinnedRep_kostantForm_mem_lattice
  span_lattice_eq_top := by
    rw [lattice_def]
    exact Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := 56
  basis := latticeBasis
  weight a i := e7MinusculeWeight a (Fin.cast rank_E7 i)
  isCartanWeightVector_basis := isCartanWeightVector_pinnedRep_latticeBasis
  weightLatticeBasis := (Pi.basisFun ℤ (Fin E7.rank)).map
    (LinearEquiv.ofTop _ span_range_e7MinusculeWeight_eq_top).symm

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
@[simp] theorem chevalleyDatum_weight (a : Fin 56) (i : Fin E7.rank) :
    chevalleyDatum.weight a i = e7MinusculeWeight a (Fin.cast rank_E7 i) := (rfl)

/-- The minuscule datum has the full weight lattice, not just the root lattice. -/
@[simp] theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ :=
  span_range_e7MinusculeWeight_eq_top

/-- The chosen character-lattice basis is the standard fundamental-weight basis. -/
@[simp] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin E7.rank) :
    (dsimp% only [rank] (chevalleyDatum.weightLatticeBasis i : Fin E7.rank → ℤ)) =
      Pi.single i 1 := by
  exact (LinearEquiv.coe_ofTop_symm_apply
    (p := Submodule.span ℤ (Set.range fun a : Fin 56 =>
      fun j : Fin E7.rank => e7MinusculeWeight a (Fin.cast rank_E7 j)))
    (h := span_range_e7MinusculeWeight_eq_top) ((Pi.basisFun ℤ (Fin E7.rank)) i)).trans
    (Pi.basisFun_apply ℤ (Fin E7.rank) i)

/-- Fundamental-weight torus coordinates are the original minuscule weights. -/
@[simp] theorem chevalleyDatum_coordinateWeight (a : Fin 56) (i : Fin E7.rank) :
    chevalleyDatum.coordinateWeight a i =
      e7MinusculeWeight a (Fin.cast rank_E7 i) := by
  have h := congrFun (chevalleyDatum.sum_coordinateWeight_smul a) i
  -- Keep the native rank in this local equation; the public simp lemma stores its reduced index.
  have hb (j : Fin E7.rank) :
      (chevalleyDatum.weightLatticeBasis j : Fin E7.rank → ℤ) = Pi.single j 1 :=
    coe_chevalleyDatum_weightLatticeBasis j
  simp only [hb, Finset.sum_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, chevalleyDatum_weight] at h
  exact h

end

end TauCeti.E7Minuscule
