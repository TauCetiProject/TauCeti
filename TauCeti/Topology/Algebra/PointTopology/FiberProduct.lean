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
hypotheses. When the coefficient ring is T1, this subspace is closed.

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
  toFun x := ⟨⟨x.comp Algebra.TensorProduct.includeLeft,
    x.comp (Algebra.TensorProduct.includeRight.restrictScalars k)⟩,
    x.comp_includeLeft_eq_comp_includeRight⟩
  invFun p := p.1.1.tensorProductLift p.1.2 p.2
  left_inv x := by
    apply AlgHom.toRingHom_injective
    apply Algebra.TensorProduct.ringHom_ext <;> ext <;> simp [← Algebra.TensorProduct.one_def]
  right_inv p := by ext <;> simp
  continuous_toFun := ((continuous_comap _).prodMk (continuous_comap _)).subtype_mk _
  continuous_invFun := by
    refine continuous_iff.2 fun t ↦ ?_
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simpa only [AlgHom.tensorProductLift_tmul, Function.comp_apply] using
        ((continuous_eval a).comp (continuous_fst.comp continuous_subtype_val)).fun_mul
          ((continuous_eval b).comp (continuous_snd.comp continuous_subtype_val))
    | add t u ht hu => simpa only [map_add] using ht.fun_add hu

/-- The fibre-product comparison restricts a point to the left tensor factor. -/
@[simp]
theorem relativeTensorProductHomeomorph_apply_fst (x : A ⊗[C] B →ₐ[k] R) (a : A) :
    (relativeTensorProductHomeomorph k C A B R x).1.1 a = x (a ⊗ₜ[C] 1) :=
  (rfl)

/-- The fibre-product comparison restricts a point to the right tensor factor. -/
@[simp]
theorem relativeTensorProductHomeomorph_apply_snd (x : A ⊗[C] B →ₐ[k] R) (b : B) :
    (relativeTensorProductHomeomorph k C A B R x).1.2 b = x (1 ⊗ₜ[C] b) :=
  (rfl)

/-- The inverse fibre-product comparison multiplies coordinate values on pure tensors. -/
@[simp]
theorem relativeTensorProductHomeomorph_symm_apply_tmul
    (p : {p : (A →ₐ[k] R) × (B →ₐ[k] R) //
      p.1.comp (IsScalarTower.toAlgHom k C A) =
        p.2.comp (IsScalarTower.toAlgHom k C B)}) (a : A) (b : B) :
    (relativeTensorProductHomeomorph k C A B R).symm p (a ⊗ₜ[C] b) =
      p.1.1 a * p.1.2 b :=
  AlgHom.tensorProductLift_tmul _ _ _ _ _

/-- Restricting to the tensor factors embeds points in the product of the two point spaces. -/
theorem isEmbedding_relativeTensorProduct :
    IsEmbedding fun x : A ⊗[C] B →ₐ[k] R ↦
      (x.comp Algebra.TensorProduct.includeLeft,
        x.comp (Algebra.TensorProduct.includeRight.restrictScalars k)) :=
  IsEmbedding.subtypeVal.comp (relativeTensorProductHomeomorph k C A B R).isEmbedding

/-- The compatible-pair comparison has closed image over a Hausdorff coefficient semiring.
In particular this applies to every T1 topological ring, which is automatically Hausdorff. -/
theorem isClosedEmbedding_relativeTensorProduct [T2Space R] :
    IsClosedEmbedding fun x : A ⊗[C] B →ₐ[k] R ↦
      (x.comp Algebra.TensorProduct.includeLeft,
        x.comp (Algebra.TensorProduct.includeRight.restrictScalars k)) := by
  refine ⟨isEmbedding_relativeTensorProduct, ?_⟩
  rw [AlgHom.range_tensorProduct_restrict]
  have heq : {p : (A →ₐ[k] R) × (B →ₐ[k] R) |
      p.1.comp (IsScalarTower.toAlgHom k C A) =
        p.2.comp (IsScalarTower.toAlgHom k C B)} =
      ⋂ c : C, {p | p.1 (algebraMap C A c) = p.2 (algebraMap C B c)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, AlgHom.ext_iff, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
  rw [heq]
  exact isClosed_iInter fun c ↦ isClosed_eq
    ((continuous_eval _).comp continuous_fst) ((continuous_eval _).comp continuous_snd)

end TauCeti.PointTopology
