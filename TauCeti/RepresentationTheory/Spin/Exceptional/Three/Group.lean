/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Exceptional.Three.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import TauCeti.RepresentationTheory.Spin.Representation
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Spin.OddStructure
import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.KostantLattice
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# The three-dimensional Spin group

Over a field with `2 ≠ 0`, a three-dimensional quadratic space equipped with polarization data
has an even Clifford algebra isomorphic to `M₂(K)`. Clifford reversal corresponds to adjugation,
so the Spin group maps into `SL₂(K)`. Explicit lifts of the two elementary root subgroups show
that this map is onto, and the polarization's spin representation is the standard representation
under this equivalence. A nondegenerate quadratic space over a separably closed field supplies the
required polarization.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

open CliffordAlgebra Module QuadraticMap

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

private noncomputable def spinThreeIndexEquiv : Finset (Fin 1) ≃ Fin 2 :=
  Fintype.equivOfCardEq (by simp)

private noncomputable def spinThreeExteriorBasis
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W) :
    Basis (Fin 2) K (ExteriorAlgebra K P.W) :=
  b.ExteriorAlgebra.reindex spinThreeIndexEquiv

private noncomputable def spinThreeEquivMatrix
    [NeZero (2 : K)] [FiniteDimensional K V]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (hV : finrank K V = 3) :
    ↥(CliffordAlgebra.even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  (P.evenCliffordEquivEnd (hV ▸ by decide)).trans
    (LinearMap.toMatrixAlgEquiv (spinThreeExteriorBasis P b))

private noncomputable def evenBivector [Invertible (2 : K)] (x y : V) :
    ↥(CliffordAlgebra.even Q) :=
  ⟨bivector Q x y, by
    rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
    exact bivector_mem_evenOdd_zero Q x y⟩

private theorem lineCoordinate_surjective [FiniteDimensional K V]
    (P : SpinPolarizationData Q)
    (hV : finrank K V = 3) : Function.Surjective P.lineCoordinate := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    P.lineCoordinate_injective
  rw [P.finrank_line_eq_one_of_finrank_eq_two_mul_add_one (l := 1) (by omega)]
  simp

private theorem add_smul_W_line_norm (P : SpinPolarizationData Q) (x : P.W)
    (z : P.line) (hz : Q (z : V) = 1) (c : K) :
    Q ((z : V) + c • (x : V)) = 1 := by
  calc
    Q ((z : V) + c • (x : V)) = Q ((c • x : P.W) + (0 : P.W') + z) := by
      congr 1
      simp [add_comm]
    _ = polar Q (c • (x : P.W) : V) (0 : P.W') + Q (z : V) :=
      P.quadraticForm_coe_add_coe_add_coe (c • x) 0 z
    _ = 1 := by simp [hz]

private theorem add_smul_line_W'_norm (P : SpinPolarizationData Q) (z : P.line)
    (y : P.W') (hz : Q (z : V) = 1) (c : K) :
    Q ((z : V) + c • (y : V)) = 1 := by
  calc
    Q ((z : V) + c • (y : V)) = Q ((0 : P.W) + (c • y : P.W') + z) := by
      congr 1
      simp [add_comm]
    _ = polar Q (0 : P.W) (c • (y : P.W') : V) + Q (z : V) :=
      P.quadraticForm_coe_add_coe_add_coe 0 (c • y) z
    _ = 1 := by simp [hz]

private noncomputable def spinThreeHom
    (hV : finrank K V = 3)
    (e : ↥(CliffordAlgebra.even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :
    spinGroup Q →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨e (spinGroupToEven Q g),
    (CliffordAlgebra.star_mul_self_eq_one_iff_det_eq_one_of_finrank_eq_three
      Q hV e (spinGroupToEven Q g)).mp (by
        rw [coe_spinGroupToEven_apply]
        exact spinGroup.star_mul_self_of_mem g.2)⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    -- `spinGroupToEven` is intentionally opaque; state equality on the matrix carriers.
    change e ((spinGroupToEven Q) (x * y)) =
      e ((spinGroupToEven Q) x) * e ((spinGroupToEven Q) y)
    simp only [map_mul]

private noncomputable def positiveRootLift
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hz : Q (z : V) = 1) (c : K) : spinGroup Q :=
  ⟨ι Q ((z : V) + c • (b 0 : V)) * ι Q (z : V),
    ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ (by
      rw [add_smul_W_line_norm P (b 0) z hz c, hz, one_mul])⟩

private noncomputable def negativeRootLift
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hz : Q (z : V) = 1) (c : K) : spinGroup Q :=
  ⟨ι Q (z : V) * ι Q ((z : V) + c • (P.dualVector b 0 : V)),
    ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ (by
      rw [hz, add_smul_line_W'_norm P z (P.dualVector b 0) hz c, one_mul])⟩

private theorem coe_positiveRootLift
    [Invertible (2 : K)]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hz : Q (z : V) = 1) (c : K) :
    (positiveRootLift P b z hz c : CliffordAlgebra Q) =
      1 + c • bivector Q (b 0 : V) (z : V) := by
  -- The lift is a Spin subtype; expose its Clifford carrier before calculating.
  change ι Q ((z : V) + c • (b 0 : V)) * ι Q (z : V) = _
  rw [map_add, map_smul, add_mul, smul_mul_assoc, ι_sq_scalar, hz,
    map_one, bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_W_line (b 0) z)]

private theorem coe_negativeRootLift
    [Invertible (2 : K)]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hz : Q (z : V) = 1) (c : K) :
    (negativeRootLift P b z hz c : CliffordAlgebra Q) =
      1 + c • bivector Q (z : V) (P.dualVector b 0 : V) := by
  -- The lift is a Spin subtype; expose its Clifford carrier before calculating.
  change ι Q (z : V) * ι Q ((z : V) + c • (P.dualVector b 0 : V)) = _
  rw [map_add, map_smul, mul_add, mul_smul_comm, ι_sq_scalar, hz,
    map_one, bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_line_W' z (P.dualVector b 0))]

private theorem spinAction_positiveRoot_empty
    [Invertible (2 : K)]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hz : Q (z : V) = 1) (hcoord : P.lineCoordinate z = 1) :
    spinAction Q P (bivector Q (b 0 : V) (z : V)) (b.ExteriorAlgebra ∅) =
      b.ExteriorAlgebra {0} := by
  have h := P.typeBSpinRep_simpleRootGenerator_last_exteriorBasis_empty b z hz hcoord
  simp only [typeBSimpleRootGeneratorFamily_inl, typeBSimpleRootGenerator_last,
    _root_.UniversalEnvelopingAlgebra.ι_apply, P.typeBSpinRep_ι] at h
  rw [P.typeBQuadraticEquiv_typeBShortRootGenerator b z hz (Fin.last 0)] at h
  simpa only [Fin.last_zero] using h

private theorem spinAction_positiveRoot_singleton
    [Invertible (2 : K)]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hcoord : P.lineCoordinate z = 1) :
    spinAction Q P (bivector Q (b 0 : V) (z : V)) (b.ExteriorAlgebra {0}) = 0 := by
  rw [bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_W_line (b 0) z), map_mul,
    Module.End.mul_apply, spinAction_ι_lineOperator, hcoord, one_smul,
    TauCeti.ExteriorAlgebra.basis_singleton, CliffordAlgebra.involute_ι,
    spinAction_ι_wedge]
  simp

private theorem spinAction_negativeRoot_empty
    [Invertible (2 : K)]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W) (z : P.line) :
    spinAction Q P (bivector Q (z : V) (P.dualVector b 0 : V))
        (b.ExteriorAlgebra ∅) = 0 := by
  rw [bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_line_W' z (P.dualVector b 0)), map_mul,
    Module.End.mul_apply, spinAction_ι_contract]
  simp [ExteriorAlgebra.basis_apply]

private theorem spinAction_negativeRoot_singleton
    [Invertible (2 : K)]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hz : Q (z : V) = 1) (hcoord : P.lineCoordinate z = 1) :
    spinAction Q P (bivector Q (z : V) (P.dualVector b 0 : V))
        (b.ExteriorAlgebra {0}) = b.ExteriorAlgebra ∅ := by
  have h := P.typeBSpinRep_simpleNegativeRootGenerator_last_exteriorBasis_singleton
    b z hz hcoord
  simp only [typeBSimpleRootGeneratorFamily_inr, typeBSimpleNegativeRootGenerator_last,
    _root_.UniversalEnvelopingAlgebra.ι_apply, P.typeBSpinRep_ι] at h
  rw [P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator b z hz (Fin.last 0)] at h
  simpa only [Fin.last_zero] using h

private noncomputable def vacuumIndex : Fin 2 := spinThreeIndexEquiv ∅

private noncomputable def occupiedIndex : Fin 2 := spinThreeIndexEquiv {0}

private theorem vacuumIndex_ne_occupiedIndex : vacuumIndex ≠ occupiedIndex := by
  intro h
  have := spinThreeIndexEquiv.injective h
  simp at this

private theorem finTwo_eq_vacuum_or_occupied (i : Fin 2) :
    i = vacuumIndex ∨ i = occupiedIndex := by
  have hs : spinThreeIndexEquiv.symm i = ∅ ∨ spinThreeIndexEquiv.symm i = {0} := by
    by_cases h : 0 ∈ spinThreeIndexEquiv.symm i
    · right
      ext j
      fin_cases j
      simp [h]
    · left
      ext j
      fin_cases j
      simp [h]
  rcases hs with hs | hs
  · left
    rw [← spinThreeIndexEquiv.apply_symm_apply i, hs]
    rfl
  · right
    rw [← spinThreeIndexEquiv.apply_symm_apply i, hs]
    rfl

private theorem spinThreeEquivMatrix_positiveRoot
    [NeZero (2 : K)] [FiniteDimensional K V] [Invertible (2 : K)]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hz : Q (z : V) = 1) (hcoord : P.lineCoordinate z = 1)
    (hV : finrank K V = 3) :
    spinThreeEquivMatrix P b hV (evenBivector (Q := Q) (b 0 : V) (z : V)) =
      Matrix.single occupiedIndex vacuumIndex 1 := by
  let bas := spinThreeExteriorBasis P b
  apply (Matrix.toLinAlgEquiv bas).injective
  simp only [spinThreeEquivMatrix, AlgEquiv.trans_apply, P.evenCliffordEquivEnd_apply]
  refine bas.ext fun i => ?_
  rcases finTwo_eq_vacuum_or_occupied i with rfl | rfl
  · rw [TauCeti.toLinAlgEquiv_single_apply_basis]
    simp only [ite_eq_left, one_smul]
    simpa [bas, spinThreeExteriorBasis, vacuumIndex, occupiedIndex, evenBivector] using
      spinAction_positiveRoot_empty P b z hz hcoord
  · rw [TauCeti.toLinAlgEquiv_single_apply_basis]
    simp only [ite_eq_right vacuumIndex_ne_occupiedIndex, zero_smul]
    simpa [bas, spinThreeExteriorBasis, occupiedIndex, evenBivector] using
      spinAction_positiveRoot_singleton P b z hcoord

private theorem spinThreeEquivMatrix_negativeRoot
    [NeZero (2 : K)] [FiniteDimensional K V] [Invertible (2 : K)]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (z : P.line) (hz : Q (z : V) = 1) (hcoord : P.lineCoordinate z = 1)
    (hV : finrank K V = 3) :
    spinThreeEquivMatrix P b hV
        (evenBivector (Q := Q) (z : V) (P.dualVector b 0 : V)) =
      Matrix.single vacuumIndex occupiedIndex 1 := by
  let bas := spinThreeExteriorBasis P b
  apply (Matrix.toLinAlgEquiv bas).injective
  simp only [spinThreeEquivMatrix, AlgEquiv.trans_apply, P.evenCliffordEquivEnd_apply]
  refine bas.ext fun i => ?_
  rcases finTwo_eq_vacuum_or_occupied i with rfl | rfl
  · rw [TauCeti.toLinAlgEquiv_single_apply_basis]
    simp only [ite_eq_right vacuumIndex_ne_occupiedIndex.symm, zero_smul]
    simpa [bas, spinThreeExteriorBasis, vacuumIndex, occupiedIndex, evenBivector] using
      spinAction_negativeRoot_empty P b z
  · rw [TauCeti.toLinAlgEquiv_single_apply_basis]
    simp only [ite_eq_left, one_smul]
    simpa [bas, spinThreeExteriorBasis, vacuumIndex, occupiedIndex, evenBivector] using
      spinAction_negativeRoot_singleton P b z hz hcoord

private theorem spinThreeHom_intertwines
    [NeZero (2 : K)] [FiniteDimensional K V]
    (P : SpinPolarizationData Q) (b : Basis (Fin 1) K P.W)
    (hV : finrank K V = 3) (g : spinGroup Q) :
    (spinThreeExteriorBasis P b).equivFun.toLinearMap.comp (spinRep Q P g) =
      (stdSLRep K 2 (spinThreeHom hV (spinThreeEquivMatrix P b hV) g)).comp
        (spinThreeExteriorBasis P b).equivFun.toLinearMap := by
  apply LinearMap.ext
  intro s
  simp only [LinearMap.comp_apply, spinRep_apply, stdSLRep_apply, Matrix.mulVecLin_apply]
  -- Expose the matrix carried by `spinThreeHom`; the remaining equality is the canonical
  -- coordinate formula for the matrix of a linear map.
  change (spinThreeExteriorBasis P b).equivFun (spinAction Q P g s) =
    Matrix.mulVec (spinThreeEquivMatrix P b hV (spinGroupToEven Q g))
      ((spinThreeExteriorBasis P b).equivFun s)
  rw [spinThreeEquivMatrix, AlgEquiv.trans_apply, P.evenCliffordEquivEnd_apply,
    coe_spinGroupToEven_apply]
  have hmatrix :
      LinearMap.toMatrixAlgEquiv (spinThreeExteriorBasis P b) (spinAction Q P g) =
        LinearMap.toMatrix (spinThreeExteriorBasis P b) (spinThreeExteriorBasis P b)
          (spinAction Q P g) := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  rw [hmatrix]
  simpa only [Basis.equivFun_apply] using
      (LinearMap.toMatrix_mulVec_repr (spinThreeExteriorBasis P b)
        (spinThreeExteriorBasis P b) (spinAction Q P g) s).symm

/-- For a three-dimensional quadratic space with polarization data over a field with `2 ≠ 0`,
there is an equivalence from its Spin group to `SL₂` under which the spin representation is the
standard two-dimensional representation. The equivalence depends on a basis of the isotropic
line. -/
theorem exists_spinGroup_mulEquiv_specialLinearGroup_and_spinRep_equiv_stdSLRep_of_finrank_eq_three
    [NeZero (2 : K)] (P : SpinPolarizationData Q) (hV : finrank K V = 3) :
    ∃ f : spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 2) K,
      Nonempty ((spinRep Q P).Equiv ((stdSLRep K 2).comp f.toMonoidHom)) := by
  let _ : FiniteDimensional K V := .of_finrank_eq_succ (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  have hW : finrank K P.W = 1 :=
    P.finrank_W_of_finrank_eq_two_mul_add_one (l := 1) (by omega)
  let b := Module.finBasisOfFinrankEq K P.W hW
  obtain ⟨z, hzcoord⟩ := lineCoordinate_surjective P hV (1 : K)
  have hz : Q (z : V) = 1 := by rw [← P.lineCoordinate_sq, hzcoord, one_mul]
  let e := spinThreeEquivMatrix P b hV
  let f := spinThreeHom hV e
  -- The even-Clifford matrix model is faithful on the Spin subgroup.
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have heven : spinGroupToEven Q x = spinGroupToEven Q y :=
      e.injective (congrArg Subtype.val hxy)
    rw [← coe_spinGroupToEven_apply Q x, ← coe_spinGroupToEven_apply Q y]
    exact congrArg Subtype.val heven
  have hpositive (c : K) :
      f (positiveRootLift P b z hz c) =
        (⟨occupiedIndex, vacuumIndex, vacuumIndex_ne_occupiedIndex.symm, c⟩ :
          Matrix.TransvectionStruct (Fin 2) K).toSpecialLinearGroup := by
    apply Subtype.ext
    -- The target is an `SL₂` subtype; compare its underlying matrices through the opaque map.
    change e (spinGroupToEven Q (positiveRootLift P b z hz c)) =
      Matrix.transvection occupiedIndex vacuumIndex c
    have heven : spinGroupToEven Q (positiveRootLift P b z hz c) =
        1 + c • evenBivector (Q := Q) (b 0 : V) (z : V) := by
      apply Subtype.ext
      simpa [evenBivector] using coe_positiveRootLift P b z hz c
    rw [heven, map_add, map_one, map_smul,
      spinThreeEquivMatrix_positiveRoot P b z hz hzcoord hV]
    simp [Matrix.transvection, smul_eq_mul]
  have hnegative (c : K) :
      f (negativeRootLift P b z hz c) =
        (⟨vacuumIndex, occupiedIndex, vacuumIndex_ne_occupiedIndex, c⟩ :
          Matrix.TransvectionStruct (Fin 2) K).toSpecialLinearGroup := by
    apply Subtype.ext
    -- The target is an `SL₂` subtype; compare its underlying matrices through the opaque map.
    change e (spinGroupToEven Q (negativeRootLift P b z hz c)) =
      Matrix.transvection vacuumIndex occupiedIndex c
    have heven : spinGroupToEven Q (negativeRootLift P b z hz c) =
        1 + c • evenBivector (Q := Q) (z : V) (P.dualVector b 0 : V) := by
      apply Subtype.ext
      simpa [evenBivector] using coe_negativeRootLift P b z hz c
    rw [heven, map_add, map_one, map_smul,
      spinThreeEquivMatrix_negativeRoot P b z hz hzcoord hV]
    simp [Matrix.transvection, smul_eq_mul]
  -- The two lifted root directions contain every elementary transvection and hence all of `SL₂`.
  have hf_surj : Function.Surjective f := by
    intro g
    let H := f.range
    have htrans : Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin 2) K → Matrix.SpecialLinearGroup (Fin 2) K) ⊆ H := by
      rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
      rcases finTwo_eq_vacuum_or_occupied i with rfl | rfl <;>
        rcases finTwo_eq_vacuum_or_occupied j with rfl | rfl
      · exact (hij rfl).elim
      · exact ⟨negativeRootLift P b z hz c, hnegative c⟩
      · exact ⟨positiveRootLift P b z hz c, hpositive c⟩
      · exact (hij rfl).elim
    have hclosure : Subgroup.closure
        (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
          Matrix.TransvectionStruct (Fin 2) K → Matrix.SpecialLinearGroup (Fin 2) K)) ≤ H :=
      (Subgroup.closure_le H).mpr htrans
    have hg : g ∈ H := by
      apply hclosure
      rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
      exact Subgroup.mem_top g
    exact MonoidHom.mem_range.mp hg
  let φ := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨φ, ⟨Representation.Equiv.mk (spinThreeExteriorBasis P b).equivFun ?_⟩⟩
  intro g
  have hφ : φ g = f g := rfl
  have hφ' : φ.toMonoidHom g = f g := hφ
  simp only [MonoidHom.comp_apply]
  rw [hφ']
  simpa only [f, e] using spinThreeHom_intertwines P b hV g

/-- A nondegenerate three-dimensional quadratic space over a separably closed field of
characteristic not two has Spin group isomorphic to `SL₂`. The equivalence is noncanonical because
its construction chooses a polarization and a basis. -/
theorem nonempty_spinGroup_mulEquiv_specialLinearGroup_of_finrank_eq_three
    [NeZero (2 : K)] [IsSepClosed K]
    (hQ : Q.Nondegenerate) (hV : finrank K V = 3) :
    Nonempty (spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  let _ : FiniteDimensional K V := .of_finrank_eq_succ (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  obtain ⟨f, -⟩ :=
    exists_spinGroup_mulEquiv_specialLinearGroup_and_spinRep_equiv_stdSLRep_of_finrank_eq_three
      (SpinPolarizationData.ofNondegenerate Q hQ) hV
  exact ⟨f⟩

end TauCeti
