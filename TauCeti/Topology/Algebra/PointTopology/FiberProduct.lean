/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Functoriality
public import TauCeti.RingTheory.TensorProduct.Compatible

/-!
# Points of affine fibre products

The evaluation topology identifies the points of `Spec (A ⊗[C] B)` over `k` with the
subspace of pairs of points of `Spec A` and `Spec B` having the same image in `Spec C`.
The comparison `relativeTensorProductHomeomorph` requires no finiteness or separation
hypotheses. When the coefficient semiring is Hausdorff (for example, any T1 topological ring),
this subspace is closed.

The forward map is restriction to each tensor factor, and its inverse multiplies the two
coordinate values on pure tensors. In particular the common point of `Spec C` is allowed
to vary; the coefficient ring is not given a fixed `C`-algebra structure.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 2.1 and its proof,
  pp. 2–3 (affine presentations and compatibility with fibre products).
-/

public section

open Topology TensorProduct

namespace TauCeti.PointTopology

variable {k C A B R : Type*} [CommSemiring k] [CommSemiring C] [Algebra k C]
  [Semiring A] [Algebra C A] [Algebra k A] [IsScalarTower k C A]
  [Semiring B] [Algebra C B] [Algebra k B] [IsScalarTower k C B]
  [CommSemiring R] [Algebra k R]

variable [TopologicalSpace R] [IsTopologicalSemiring R]

variable (k C A B R) in
/-- Points of an affine fibre product are homeomorphic to the subspace of compatible pairs
of points. The common point of the base is not fixed. -/
noncomputable def relativeTensorProductHomeomorph :
    (A ⊗[C] B →ₐ[k] R) ≃ₜ
      {p : (A →ₐ[k] R) × (B →ₐ[k] R) //
        p.1.comp (IsScalarTower.toAlgHom k C A) =
          p.2.comp (IsScalarTower.toAlgHom k C B)} where
  toEquiv := relativeTensorProductEquiv k C A B R
  continuous_toFun := continuous_induced_rng.2 (by
    simpa only [Equiv.toFun_as_coe, Function.comp_def, relativeTensorProductEquiv_apply_coe]
      using (continuous_comap (Algebra.TensorProduct.includeLeft (R := C))).prodMk
        (continuous_comap (Algebra.TensorProduct.includeRight.restrictScalars k)))
  continuous_invFun := by
    refine continuous_of_continuous_tmul _ fun a b ↦ ?_
    simpa only [Equiv.invFun_as_coe, relativeTensorProductEquiv_symm_apply,
      AlgHom.tensorProductLift_tmul, Function.comp_apply] using
      ((continuous_eval a).comp (continuous_fst.comp continuous_subtype_val)).fun_mul
        ((continuous_eval b).comp (continuous_snd.comp continuous_subtype_val))

/-- The fibre-product comparison restricts a point to the left tensor factor. -/
@[simp]
theorem relativeTensorProductHomeomorph_apply_fst (x : A ⊗[C] B →ₐ[k] R) (a : A) :
    (relativeTensorProductHomeomorph k C A B R x).1.1 a = x (a ⊗ₜ[C] 1) := by
  simp [relativeTensorProductHomeomorph]

/-- The fibre-product comparison restricts a point to the right tensor factor. -/
@[simp]
theorem relativeTensorProductHomeomorph_apply_snd (x : A ⊗[C] B →ₐ[k] R) (b : B) :
    (relativeTensorProductHomeomorph k C A B R x).1.2 b = x (1 ⊗ₜ[C] b) := by
  simp [relativeTensorProductHomeomorph]

/-- The inverse fibre-product comparison multiplies coordinate values on pure tensors. -/
@[simp]
theorem relativeTensorProductHomeomorph_symm_apply_tmul
    (p : {p : (A →ₐ[k] R) × (B →ₐ[k] R) //
      p.1.comp (IsScalarTower.toAlgHom k C A) =
        p.2.comp (IsScalarTower.toAlgHom k C B)}) (a : A) (b : B) :
    (relativeTensorProductHomeomorph k C A B R).symm p (a ⊗ₜ[C] b) =
      p.1.1 a * p.1.2 b := by
  simp [relativeTensorProductHomeomorph]

/-- Restricting to the tensor factors embeds points in the product of the two point spaces. -/
theorem isEmbedding_restrict_tensorProduct :
    IsEmbedding fun x : A ⊗[C] B →ₐ[k] R ↦
      (x.comp Algebra.TensorProduct.includeLeft,
        x.comp (Algebra.TensorProduct.includeRight.restrictScalars k)) := by
  simpa only [Function.comp_def, relativeTensorProductHomeomorph,
    Homeomorph.homeomorph_mk_coe, relativeTensorProductEquiv_apply_coe] using
    IsEmbedding.subtypeVal.comp (relativeTensorProductHomeomorph k C A B R).isEmbedding

/-- The compatible-pair comparison has closed image over a Hausdorff coefficient semiring.
In particular this applies to every T1 topological ring, which is automatically Hausdorff. -/
theorem isClosedEmbedding_restrict_tensorProduct [T2Space R] :
    IsClosedEmbedding fun x : A ⊗[C] B →ₐ[k] R ↦
      (x.comp Algebra.TensorProduct.includeLeft,
        x.comp (Algebra.TensorProduct.includeRight.restrictScalars k)) := by
  refine ⟨isEmbedding_restrict_tensorProduct, ?_⟩
  rw [range_restrict_tensorProduct]
  have := (isEmbedding_coeFn (k := k) (A := C) (R := R)).t2Space
  exact isClosed_eq ((continuous_comap _).comp continuous_fst)
    ((continuous_comap _).comp continuous_snd)

end TauCeti.PointTopology
