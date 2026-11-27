/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.TensorProduct

/-!
# Detecting tensor intertwiners by matrix coefficients

An equivalence from a tensor product of right comodules to another comodule is colinear
exactly when its pure matrix coefficients are products of the coefficients of the factors.
The tensor product carries the native diagonal coaction. This criterion lets a multiplication
formula on coefficients supply a comodule isomorphism, as in tensor reconstruction.
For rank-one coactions attached to group-like elements `g`, `h` and `z`, the scalar tensor
equivalence is colinear precisely when `z = g * h`.

The criterion holds for arbitrary free modules over a commutative semiring, hence for all
vector spaces over a field, with no finite-dimensionality or characteristic restriction.

## References

Deligne–Milne, *Tannakian categories*, Proposition 2.16 (multiplication of matrix coefficients).
-/

public section

open Module TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace LinearEquiv

section Criterion

variable {R B M N P : Type*} [CommSemiring R] [Semiring B] [Bialgebra R B]
  [AddCommMonoid M] [Module R M] [Comodule R B M]
  [AddCommMonoid N] [Module R N] [Comodule R B N]
  [AddCommMonoid P] [Module R P] [Comodule R B P]

attribute [local instance] Comodule.tensor

private theorem map_coact_tensor_of_matrixCoefficient
    (e : M ⊗[R] N ≃ₗ[R] P) {ι κ : Type*} (b : Basis ι R M) (c : Basis κ R N)
    (h : ∀ m n α β,
      matrixCoefficient (C := B)
          ((TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β)).comp e.symm.toLinearMap)
          (e (m ⊗ₜ[R] n)) =
        matrixCoefficient (C := B) α m * matrixCoefficient (C := B) β n) :
    TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ coact (R := R) (C := B) =
      coact (R := R) (C := B) ∘ₗ e.toLinearMap := by
  classical
  have hdual (i : ι) (j : κ) :
      (b.tensorProduct c).coord (i, j) =
        TensorProduct.dualDistrib R M N (b.coord i ⊗ₜ[R] c.coord j) := by
    ext m n
    simp [Basis.coord_apply, mul_comm]
  have hcoord (i : ι) (j : κ) :
      ((b.tensorProduct c).map e).coord (i, j) =
        (TensorProduct.dualDistrib R M N (b.coord i ⊗ₜ[R] c.coord j)).comp
          e.symm.toLinearMap := by
    rw [← hdual]
    ext p
    simp [Basis.coord_apply, Basis.map_repr]
  apply (b.tensorProduct c).ext
  rintro ⟨i, j⟩
  apply (TensorProduct.equivFinsuppOfBasisLeft ((b.tensorProduct c).map e)).injective
  ext ⟨a, d⟩
  simp only [LinearMap.comp_apply, Basis.tensorProduct_apply,
    TensorProduct.equivFinsuppOfBasisLeft_apply, LinearMap.rTensor, hcoord]
  rw [TensorProduct.map_map]
  simp only [LinearMap.comp_assoc, e.symm_comp, LinearMap.comp_id]
  exact (matrixCoefficient_tensor (C := B) (b.coord a) (c.coord d) (b i) (c j)).trans
    (h (b i) (c j) (b.coord a) (c.coord d)).symm

/-- An equivalence out of the native diagonal tensor comodule is colinear if and only if
all its pure matrix coefficients multiply. Only freeness of the two tensor factors is
required; in particular the criterion applies to vector spaces of arbitrary dimension. -/
theorem map_coact_tensor_iff_matrixCoefficient [Module.Free R M] [Module.Free R N]
    (e : M ⊗[R] N ≃ₗ[R] P) :
    TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ coact (R := R) (C := B) =
        coact (R := R) (C := B) ∘ₗ e.toLinearMap ↔
      ∀ m n α β,
        matrixCoefficient (C := B)
            ((TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β)).comp e.symm.toLinearMap)
            (e (m ⊗ₜ[R] n)) =
          matrixCoefficient (C := B) α m * matrixCoefficient (C := B) β n := by
  constructor
  · intro h m n α β
    calc
      _ = matrixCoefficient (C := B)
          (((TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β)).comp e.symm.toLinearMap).comp
            e.toLinearMap) (m ⊗ₜ[R] n) :=
        matrixCoefficient_map (⟨e.toLinearMap, h⟩ : Comodule.Hom R B (M ⊗[R] N) P) _ _
      _ = _ := by
        simpa only [LinearMap.comp_assoc, e.symm_comp, LinearMap.comp_id] using
          matrixCoefficient_tensor (C := B) α β m n
  · exact map_coact_tensor_of_matrixCoefficient e (Module.Free.chooseBasis R M)
      (Module.Free.chooseBasis R N)

end Criterion

universe w

section Isomorphism

variable {R B : Type*} {M N P : Type w} [CommSemiring R] [Semiring B] [Bialgebra R B]
  [AddCommMonoid M] [Module R M] [Comodule R B M]
  [AddCommMonoid N] [Module R N] [Comodule R B N]
  [AddCommMonoid P] [Module R P] [Comodule R B P]

attribute [local instance] Comodule.tensor

/-- The comodule isomorphism induced by a tensor equivalence satisfying the multiplication
identity on pure matrix coefficients. Its underlying equivalence is the supplied `e`. -/
noncomputable def comoduleIsoOfTensorMatrixCoefficient [Module.Free R M] [Module.Free R N]
    (e : M ⊗[R] N ≃ₗ[R] P)
    (h : ∀ m n α β,
      matrixCoefficient (C := B)
          ((TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β)).comp e.symm.toLinearMap)
          (e (m ⊗ₜ[R] n)) =
        matrixCoefficient (C := B) α m * matrixCoefficient (C := B) β n) :
    ComoduleCat.of R B (M ⊗[R] N) ≅ ComoduleCat.of R B P :=
  ComoduleCat.isoOfLinearEquiv R B e ((e.map_coact_tensor_iff_matrixCoefficient).mpr h)

/-- The forward map of the coefficient-induced isomorphism is the given equivalence. -/
@[simp]
theorem comoduleIsoOfTensorMatrixCoefficient_hom_toLinearMap [Module.Free R M] [Module.Free R N]
    (e : M ⊗[R] N ≃ₗ[R] P) (h) :
    (e.comoduleIsoOfTensorMatrixCoefficient (B := B) h).hom.toLinearMap = e.toLinearMap :=
  (rfl)

/-- The inverse map of the coefficient-induced isomorphism is the inverse equivalence. -/
@[simp]
theorem comoduleIsoOfTensorMatrixCoefficient_inv_toLinearMap [Module.Free R M] [Module.Free R N]
    (e : M ⊗[R] N ≃ₗ[R] P) (h) :
    (e.comoduleIsoOfTensorMatrixCoefficient (B := B) h).inv.toLinearMap = e.symm.toLinearMap :=
  (rfl)

end Isomorphism

end LinearEquiv

namespace GroupLike

variable {R B : Type*} [CommSemiring R] [Semiring B] [Bialgebra R B]

/-- The canonical scalar tensor equivalence intertwines the rank-one coactions for
`g`, `h` and `z` exactly when `z = g * h`. The two source coactions are supplied explicitly
to the native tensor construction, so they can differ despite having the same carrier. -/
theorem tensor_lid_map_coact_iff (g h z : GroupLike R B) :
    letI : Comodule R B (R ⊗[R] R) :=
      @Comodule.tensor R B R R _ _ _ _ _ (groupLike g) _ _ (groupLike h)
    letI : Comodule R B R := groupLike z
    TensorProduct.map (TensorProduct.lid R R).toLinearMap LinearMap.id ∘ₗ
        coact (R := R) (C := B) (M := R ⊗[R] R) =
      coact (R := R) (C := B) (M := R) ∘ₗ (TensorProduct.lid R R).toLinearMap ↔
        z = g * h := by
  let : Comodule R B (R ⊗[R] R) :=
    @Comodule.tensor R B R R _ _ _ _ _ (groupLike g) _ _ (groupLike h)
  let : Comodule R B R := groupLike z
  -- All three scalar comodules have the same carrier; specify their coactions separately.
  rw [@LinearEquiv.map_coact_tensor_iff_matrixCoefficient R B R R R _ _ _
    _ _ (groupLike g) _ _ (groupLike h) _ _ (groupLike z) _ _ (TensorProduct.lid R R)]
  rw [← GroupLike.val_inj, GroupLike.val_mul]
  constructor
  · intro hc
    simpa only [matrixCoefficient_groupLike, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, TensorProduct.dualDistrib_apply,
      LinearMap.id_apply, mul_one, one_smul] using
        hc 1 1 LinearMap.id LinearMap.id
  · intro hz m n α β
    simp only [matrixCoefficient_groupLike, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, TensorProduct.dualDistrib_apply]
    rw [hz, smul_mul_smul_comm]

end GroupLike
