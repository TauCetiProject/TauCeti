/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Flag.Torus
public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Exponential

/-!
# Root-subgroup stability of the represented modular F4 flag

The modular root exponentials conjugate the represented adjoint range and ideal into themselves.
Transporting this matrix stability to the cotangent adjoint comodule gives block triangularity for
root-subgroup generators with respect to the adapted represented flag.
-/

public section

namespace TauCeti.DynkinType

open CategoryTheory
open scoped TensorProduct
open TauCeti.F4ShortRoot

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- Local adjoint comodule used for root-subgroup stability of the cotangent flag. -/
local instance : Comodule 𝔽₂ (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
    f4ShortRootCotangentDual :=
  Derivation.adjointComodule
    (R := 𝔽₂) (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)

variable {A : Type} [CommRing A] [Algebra 𝔽₂ A]

/-- The scalar-extended short-root adjoint representation in its canonical matrix basis. -/
noncomputable def f4ShortRootBaseChangeAdjointMatrixLinearMap :
    A ⊗[ℤ] f4ChevalleyLieLattice →ₗ[A] Matrix (Fin 26) (Fin 26) A :=
  (LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
    (f4ShortRootLieIdealBasis.baseChange A)).toLinearMap.comp
      f4ShortRootBaseChangeAdjoint

/-- Evaluate the scalar-extended adjoint map in matrix coordinates. -/
@[simp] theorem f4ShortRootBaseChangeAdjointMatrixLinearMap_apply
    (x : A ⊗[ℤ] f4ChevalleyLieLattice) :
    f4ShortRootBaseChangeAdjointMatrixLinearMap x =
      LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootBaseChangeAdjoint x) := by
  simp [f4ShortRootBaseChangeAdjointMatrixLinearMap]

/-- On a pure tensor, the scalar-extended adjoint matrix is the entrywise scalar extension of the
modular adjoint matrix. -/
theorem f4ShortRootBaseChangeAdjointMatrixLinearMap_cancel_tmul
    (a : A) (X : f4ModularChevalleyLieAlgebra) :
    f4ShortRootBaseChangeAdjointMatrixLinearMap
        ((TauCeti.cancelBaseChange ℤ 𝔽₂ A
          f4ChevalleyLieLattice) (a ⊗ₜ[𝔽₂] X)) =
      a • f4ShortRootAdjointMatrixBaseChange (A := A) X := by
  let e := TauCeti.cancelBaseChange ℤ 𝔽₂ A f4ChevalleyLieLattice
  have heval : f4ShortRootBaseChangeAdjointMatrixLinearMap
      (e ((1 : A) ⊗ₜ[𝔽₂] X)) =
      f4ShortRootAdjointMatrixBaseChange (A := A) X :=
    f4ShortRootBaseChangeAdjoint_toMatrix_cancel_tmul X
  have harg : e (a ⊗ₜ[𝔽₂] X) = a • e ((1 : A) ⊗ₜ[𝔽₂] X) := by
    calc
      _ = e (a • ((1 : A) ⊗ₜ[𝔽₂] X)) :=
        congrArg e (TensorProduct.tmul_eq_smul_one_tmul a X)
      _ = _ := e.toLinearEquiv.map_smul a ((1 : A) ⊗ₜ[𝔽₂] X)
  rw [harg, map_smul, heval]

/-- Every scalar-extended represented adjoint matrix belongs to the represented range span. -/
theorem f4ShortRootBaseChangeAdjointMatrix_mem_range
    (x : A ⊗[ℤ] f4ChevalleyLieLattice) :
    f4ShortRootBaseChangeAdjointMatrixLinearMap x ∈
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  let e := TauCeti.cancelBaseChange ℤ 𝔽₂ A f4ChevalleyLieLattice
  rw [← e.apply_symm_apply x]
  generalize e.symm x = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using add_mem hx hy
  | tmul a X =>
      rw [f4ShortRootBaseChangeAdjointMatrixLinearMap_cancel_tmul]
      apply Submodule.smul_mem
      rw [f4ShortRootRepresentedRangeMatrixBaseChange_eq_span]
      exact Submodule.subset_span (Set.mem_range_self X)

/-- Conjugation by a carrier root-subgroup point, as a linear map on matrices. -/
noncomputable def f4ShortRootRootConjLinearMap
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    Matrix (Fin 26) (Fin 26) A →ₗ[A] Matrix (Fin 26) (Fin 26) A where
  toFun X :=
    ((rootSubgroupPoints k A u : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) * X *
      (((rootSubgroupPoints k A u)⁻¹ : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

omit [Algebra 𝔽₂ A] in
@[simp] theorem f4ShortRootRootConjLinearMap_apply
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (X : Matrix (Fin 26) (Fin 26) A) :
    f4ShortRootRootConjLinearMap k u X =
      ((rootSubgroupPoints k A u : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) * X *
        (((rootSubgroupPoints k A u)⁻¹ : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) := by
  unfold f4ShortRootRootConjLinearMap
  rfl

/-- Root conjugation carries a represented adjoint matrix to the adjoint matrix of the
integrally transformed ambient vector. -/
theorem f4ShortRootRootConjLinearMap_adjoint
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (x : A ⊗[ℤ] f4ChevalleyLieLattice) :
    f4ShortRootRootConjLinearMap k u
        (f4ShortRootBaseChangeAdjointMatrixLinearMap x) =
      f4ShortRootBaseChangeAdjointMatrixLinearMap
        (f4RootExponential k (Multiplicative.toAdd u) x) := by
  let B := f4ShortRootLieIdealBasis.baseChange A
  let G : GL (Fin 26) A := rootSubgroupPoints k A u
  let E := LinearMap.toMatrix B B
      (f4ShortRootExponential k (Multiplicative.toAdd u))
  let R := LinearMap.toMatrix B B (f4ShortRootBaseChangeAdjoint x)
  let R' := LinearMap.toMatrix B B
      (f4ShortRootBaseChangeAdjoint
        (f4RootExponential k (Multiplicative.toAdd u) x))
  have hcarrier := f4ShortRootExponential_toMatrix_eq_rootSubgroupPoints k u
  -- The carrier theorem uses the same base-changed basis as `E`.
  change E = (G : Matrix (Fin 26) (Fin 26) A) at hcarrier
  have hraw := f4ShortRootExponential_toMatrix_mul_adjoint k
    (Multiplicative.toAdd u) x
  -- Expand the matrix abbreviations in the intertwining identity.
  change E * R = R' * E at hraw
  have hintertwine : (G : Matrix (Fin 26) (Fin 26) A) * R =
      R' * (G : Matrix (Fin 26) (Fin 26) A) := by
    calc
      _ = E * R := congrArg (fun Z => Z * R) hcarrier.symm
      _ = R' * E := hraw
      _ = _ := congrArg (R' * ·) hcarrier
  -- The named adjoint matrix map is definitionally `toMatrix B B`.
  change (G : Matrix (Fin 26) (Fin 26) A) * R *
      ((G⁻¹ : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) = R'
  calc
    _ = (R' * (G : Matrix (Fin 26) (Fin 26) A)) *
        ((G⁻¹ : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) :=
      congrArg (fun X => X * ((G⁻¹ : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A))
        hintertwine
    _ = R' * ((G : Matrix (Fin 26) (Fin 26) A) *
        ((G⁻¹ : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)) := by
      rw [Matrix.mul_assoc]
    _ = R' := by simp

/-- Carrier root-subgroup conjugation preserves the represented range matrix span. -/
theorem f4ShortRootRootConj_mem_representedRange
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    {X : Matrix (Fin 26) (Fin 26) A}
    (hX : X ∈ f4ShortRootRepresentedRangeMatrixBaseChange (A := A)) :
    f4ShortRootRootConjLinearMap k u X ∈
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  have hX' : X ∈ Submodule.span A (Set.range fun x : f4ModularChevalleyLieAlgebra =>
      f4ShortRootAdjointMatrixBaseChange (A := A) x) :=
    (f4ShortRootRepresentedRangeMatrixBaseChange_eq_span (A := A)) ▸ hX
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hX'
  · rintro _ ⟨x, rfl⟩
    -- Rewrite the span generator as the named adjoint matrix.
    change f4ShortRootRootConjLinearMap k u
        (f4ShortRootAdjointMatrixBaseChange (A := A) x) ∈ _
    have heval : f4ShortRootBaseChangeAdjointMatrixLinearMap
        ((TauCeti.cancelBaseChange ℤ 𝔽₂ A
          f4ChevalleyLieLattice) ((1 : A) ⊗ₜ[𝔽₂] x)) =
        f4ShortRootAdjointMatrixBaseChange (A := A) x :=
      f4ShortRootBaseChangeAdjoint_toMatrix_cancel_tmul x
    rw [← heval, f4ShortRootRootConjLinearMap_adjoint]
    exact f4ShortRootBaseChangeAdjointMatrix_mem_range _
  · intro X Y _ _ hX hY
    rw [map_add]
    exact Submodule.add_mem _ hX hY
  · intro a X _ hX
    rw [map_smul]
    exact Submodule.smul_mem _ a hX

/-- The represented matrix of an element in the scalar-extended short-root ideal belongs to the
represented ideal span. -/
theorem f4ShortRootBaseChangeAdjointMatrix_mem_ideal
    (z : A ⊗[𝔽₂] f4ShortRootLieIdeal) :
    f4ShortRootBaseChangeAdjointMatrixLinearMap
        (f4ShortRootBaseChangeInclusion z) ∈
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using add_mem hx hy
  | tmul a y =>
      rw [f4ShortRootBaseChangeInclusion_tmul]
      rw [f4ShortRootBaseChangeAdjointMatrixLinearMap_cancel_tmul]
      apply Submodule.smul_mem
      rw [f4ShortRootRepresentedIdealMatrixBaseChange_eq_span]
      exact Submodule.subset_span (Set.mem_range_self y)

/-- Carrier root-subgroup conjugation preserves the represented ideal matrix span. -/
theorem f4ShortRootRootConj_mem_representedIdeal
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    {X : Matrix (Fin 26) (Fin 26) A}
    (hX : X ∈ f4ShortRootRepresentedIdealMatrixBaseChange (A := A)) :
    f4ShortRootRootConjLinearMap k u X ∈
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  have hX' : X ∈ Submodule.span A (Set.range fun y : f4ShortRootLieIdeal =>
      f4ShortRootAdjointMatrixBaseChange (A := A)
        (y : f4ModularChevalleyLieAlgebra)) :=
    (f4ShortRootRepresentedIdealMatrixBaseChange_eq_span (A := A)) ▸ hX
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hX'
  · rintro _ ⟨y, rfl⟩
    let z : A ⊗[𝔽₂] f4ShortRootLieIdeal := (1 : A) ⊗ₜ[𝔽₂] y
    have heval : f4ShortRootBaseChangeAdjointMatrixLinearMap
          (f4ShortRootBaseChangeInclusion z) =
          f4ShortRootAdjointMatrixBaseChange (A := A)
            (y : f4ModularChevalleyLieAlgebra) := by
        calc
          _ = f4ShortRootBaseChangeAdjointMatrixLinearMap
              ((TauCeti.cancelBaseChange ℤ 𝔽₂ A
                f4ChevalleyLieLattice)
                ((1 : A) ⊗ₜ[𝔽₂] (y : f4ModularChevalleyLieAlgebra))) :=
            congrArg _ (f4ShortRootBaseChangeInclusion_tmul (1 : A) y)
          _ = (1 : A) • f4ShortRootAdjointMatrixBaseChange (A := A)
              (y : f4ModularChevalleyLieAlgebra) :=
            f4ShortRootBaseChangeAdjointMatrixLinearMap_cancel_tmul _ _
          _ = _ := one_smul A _
    -- Rewrite the ideal span generator as the matrix of its scalar-extended vector.
    change f4ShortRootRootConjLinearMap k u
        (f4ShortRootAdjointMatrixBaseChange (A := A)
          (y : f4ModularChevalleyLieAlgebra)) ∈ _
    rw [← heval, f4ShortRootRootConjLinearMap_adjoint,
      f4RootExponential_intertwines]
    exact f4ShortRootBaseChangeAdjointMatrix_mem_ideal
      (f4ShortRootExponential k (Multiplicative.toAdd u) z)
  · intro X Y _ _ hX hY
    rw [map_add]
    exact Submodule.add_mem _ hX hY
  · intro a X _ hX
    rw [map_smul]
    exact Submodule.smul_mem _ a hX

private theorem root_endOfPoint_mem_ideal
    (g : HopfAlgebra.points
      (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (CommAlgCat.of 𝔽₂ A))
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26 g = rootSubgroupPoints k A u)
    {x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual}
    (hx : x ∈ cotangentFlagIdeal (A := A)) :
    Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x ∈
      cotangentFlagIdeal (A := A) := by
  let e := f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
  refine e.mem_of_preserves_map
    (cotangentFlagIdeal (A := A))
    (f4ShortRootRepresentedIdealMatrixBaseChange (A := A))
    (f4ShortRootCotangentFlagIdeal_map (A := A))
    (fun y => Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv y)
    (f4ShortRootRootConjLinearMap k u) ?_ ?_ hx
  · intro y
    rw [f4ShortRootCotangentBaseChangeMatrixEquiv_apply,
      GeneralLinear.tangentMatrix_adjointComodule_endOfPoint,
      hg, f4ShortRootRootConjLinearMap_apply,
      f4ShortRootCotangentBaseChangeMatrixEquiv_apply]
  · intro Y hY
    exact f4ShortRootRootConj_mem_representedIdeal k u hY

private theorem root_endOfPoint_mem_range
    (g : HopfAlgebra.points
      (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (CommAlgCat.of 𝔽₂ A))
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26 g = rootSubgroupPoints k A u)
    {x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual}
    (hx : x ∈ cotangentFlagRange (A := A)) :
    Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x ∈
      cotangentFlagRange (A := A) := by
  let e := f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
  refine e.mem_of_preserves_map
    (cotangentFlagRange (A := A))
    (f4ShortRootRepresentedRangeMatrixBaseChange (A := A))
    (f4ShortRootCotangentFlagRange_map (A := A))
    (fun y => Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv y)
    (f4ShortRootRootConjLinearMap k u) ?_ ?_ hx
  · intro y
    rw [f4ShortRootCotangentBaseChangeMatrixEquiv_apply,
      GeneralLinear.tangentMatrix_adjointComodule_endOfPoint,
      hg, f4ShortRootRootConjLinearMap_apply,
      f4ShortRootCotangentBaseChangeMatrixEquiv_apply]
  · intro Y hY
    exact f4ShortRootRootConj_mem_representedRange k u hY

/-- Every short-root carrier root point acts block triangularly on the represented flag. -/
theorem f4ShortRootRootSubgroup_adjoint_blockTriangular
    (g : HopfAlgebra.points
      (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (CommAlgCat.of 𝔽₂ A))
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26 g = rootSubgroupPoints k A u) :
    ((Comodule.coefficientMatrix
        (C := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
        f4ShortRootCotangentFlagBasis).map g.ofConv).BlockTriangular
      (OrderDual.toDual ∘ f4ShortRootCotangentFlagWeight) :=
  f4ShortRoot_adjoint_blockTriangular_of_preserves_flag g
    (root_endOfPoint_mem_ideal g k u hg) (root_endOfPoint_mem_range g k u hg)

end

end TauCeti.DynkinType
