/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.Algebra.Hom

/-!
# Functoriality of the affine point topology

Precomposition and continuous change of coefficients are continuous for the evaluation topology.
A surjection of coordinate rings gives a closed embedding of points over a T1 ring. Change of
coefficients preserves embeddings and closed embeddings, and preserves open embeddings when the
coordinate algebra is of finite type. Tensor products give products of point spaces, and base
change does not alter the point topology.

These results allow affine presentations and changes of coefficient rings to be used in the
construction of topological groups of rational points and integral points.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 2.1 and Exercises 2.2–2.3.
* The surjective-precomposition argument follows Andrew Yang and Christian Merten's
  `CommRingCat.HomTopology.isClosedEmbedding_precomp_of_surjective` in Mathlib.
-/

public section

open Topology TensorProduct

namespace TauCeti.PointTopology

section Semiring

variable {k A B R S : Type*} [CommSemiring k]
  [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]
  [Semiring R] [Algebra k R] [Semiring S] [Algebra k S]
  [TopologicalSpace R] [TopologicalSpace S]

/-- Precomposition by a coordinate algebra map is continuous on points. -/
@[continuity, fun_prop]
theorem continuous_comap (φ : B →ₐ[k] A) :
    Continuous fun x : A →ₐ[k] R ↦ x.comp φ :=
  continuous_iff.2 fun b ↦ continuous_eval (φ b)

/-- A surjection of coordinate algebras induces an embedding of point spaces. -/
theorem isEmbedding_comap_of_surjective (φ : B →ₐ[k] A) (hφ : Function.Surjective φ) :
    IsEmbedding fun x : A →ₐ[k] R ↦ x.comp φ := by
  refine .of_comp (continuous_comap φ) isEmbedding_coeFn.continuous ?_
  exact (Function.Surjective.isEmbedding_comp φ hφ).comp isEmbedding_coeFn

/-- Continuous change of coefficients is continuous on points. -/
@[continuity, fun_prop]
theorem continuous_map_codomain (ψ : R →ₐ[k] S) (hψ : Continuous ψ) :
    Continuous fun x : A →ₐ[k] R ↦ ψ.comp x :=
  continuous_iff.2 fun a ↦ hψ.comp (continuous_eval a)

/-- An embedding of coefficient rings induces an embedding of point spaces. -/
theorem isEmbedding_map_codomain (ψ : R →ₐ[k] S) (hψ : IsEmbedding ψ) :
    IsEmbedding fun x : A →ₐ[k] R ↦ ψ.comp x := by
  refine .of_comp (continuous_map_codomain ψ hψ.continuous)
    isEmbedding_coeFn.continuous ?_
  exact (IsEmbedding.piMap (fun _ : A ↦ hψ)).comp isEmbedding_coeFn

/-- A closed embedding of coefficient rings induces a closed embedding on points, with no
finiteness or separation assumption on the coordinate algebra or the coefficient rings. -/
theorem isClosedEmbedding_map_codomain (ψ : R →ₐ[k] S) (hψ : IsClosedEmbedding ψ) :
    IsClosedEmbedding fun x : A →ₐ[k] R ↦ ψ.comp x := by
  refine ⟨isEmbedding_map_codomain ψ hψ.isEmbedding, ?_⟩
  rw [AlgHom.range_comp_left_of_injective ψ hψ.injective]
  convert isClosed_iInter (fun a : A ↦
    hψ.isClosed_range.preimage (continuous_eval (k := k) (A := A) a)) using 1
  ext x
  simp

end Semiring

section FiniteType

variable {k A R S : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
  [Semiring R] [Algebra k R] [Semiring S] [Algebra k S]
  [TopologicalSpace R] [TopologicalSpace S]

/-- An open embedding of coefficient rings induces an open embedding on points of a finite type
algebra. Finite type is needed because infinitely many coordinate conditions need not be open. -/
theorem isOpenEmbedding_map_codomain [Algebra.FiniteType k A]
    (ψ : R →ₐ[k] S) (hψ : IsOpenEmbedding ψ) :
    IsOpenEmbedding fun x : A →ₐ[k] R ↦ ψ.comp x := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  refine ⟨isEmbedding_map_codomain ψ hψ.isEmbedding, ?_⟩
  rw [AlgHom.range_comp_left_eq_of_adjoin_eq_top ψ hψ.injective
    (a := ((↑) : s → A)) (by simpa using hs)]
  convert isOpen_iInter_of_finite (fun i : s ↦
    hψ.isOpen_range.preimage (continuous_eval (k := k) (A := A) (i : A))) using 1
  ext x
  simp

end FiniteType

section Ring

variable {k A B R : Type*} [CommSemiring k] [Ring A] [Algebra k A]
  [Ring B] [Algebra k B] [Ring R] [Algebra k R] [TopologicalSpace R]

/-- A surjection of coordinate rings induces a closed embedding of points over a T1 ring. -/
theorem isClosedEmbedding_comap_of_surjective [T1Space R]
    (φ : B →ₐ[k] A) (hφ : Function.Surjective φ) :
    IsClosedEmbedding fun x : A →ₐ[k] R ↦ x.comp φ := by
  refine ⟨isEmbedding_comap_of_surjective φ hφ, ?_⟩
  rw [AlgHom.range_comp_right_of_surjective φ hφ]
  convert isClosed_biInter (fun b (_ : b ∈ RingHom.ker φ) ↦
    (isClosed_singleton (x := (0 : R))).preimage
      (continuous_eval (k := k) (A := B) (R := R) b)) using 1
  ext x
  simp

end Ring

section TensorProduct

variable {k A B R : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
  [Semiring B] [Algebra k B] [CommSemiring R] [Algebra k R]
  [TopologicalSpace R] [IsTopologicalSemiring R]

variable (k A B R) in
/-- Points of a tensor product are homeomorphic to the product of the two point spaces. -/
noncomputable def tensorProductHomeomorph :
    (A ⊗[k] B →ₐ[k] R) ≃ₜ (A →ₐ[k] R) × (B →ₐ[k] R) where
  toFun x := ⟨x.comp Algebra.TensorProduct.includeLeft,
    x.comp Algebra.TensorProduct.includeRight⟩
  invFun x := Algebra.TensorProduct.lift x.1 x.2 (fun _ _ ↦ .all _ _)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := (continuous_comap _).prodMk (continuous_comap _)
  continuous_invFun := by
    refine continuous_iff.2 fun t ↦ ?_
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simpa only [Algebra.TensorProduct.lift_tmul, Function.comp_apply] using
        ((continuous_eval a).comp continuous_fst).fun_mul
          ((continuous_eval b).comp continuous_snd)
    | add t u ht hu => simpa only [map_add] using ht.fun_add hu

/-- The tensor-product comparison restricts a point to the left factor. -/
@[simp]
theorem tensorProductHomeomorph_apply_fst (x : A ⊗[k] B →ₐ[k] R) (a : A) :
    (tensorProductHomeomorph k A B R x).1 a = x (a ⊗ₜ[k] 1) :=
  (rfl)

/-- The tensor-product comparison restricts a point to the right factor. -/
@[simp]
theorem tensorProductHomeomorph_apply_snd (x : A ⊗[k] B →ₐ[k] R) (b : B) :
    (tensorProductHomeomorph k A B R x).2 b = x (1 ⊗ₜ[k] b) :=
  (rfl)

/-- The inverse tensor-product comparison multiplies the two coordinate values. -/
@[simp]
theorem tensorProductHomeomorph_symm_apply_tmul
    (x : (A →ₐ[k] R) × (B →ₐ[k] R)) (a : A) (b : B) :
    (tensorProductHomeomorph k A B R).symm x (a ⊗ₜ[k] b) = x.1 a * x.2 b :=
  Algebra.TensorProduct.lift_tmul x.1 x.2 (fun _ _ ↦ .all _ _) a b

end TensorProduct

section BaseChange

variable {k K A R : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
  [Semiring A] [Algebra k A] [Semiring R] [Algebra k R] [Algebra K R]
  [IsScalarTower k K R] [TopologicalSpace R] [IsTopologicalSemiring R]

variable (k K A R) in
/-- The base-change adjunction is a homeomorphism for the evaluation point topologies. -/
noncomputable def baseChangeHomeomorph :
    (K ⊗[k] A →ₐ[K] R) ≃ₜ (A →ₐ[k] R) where
  toEquiv := (AlgHom.liftEquiv k K A R).symm
  continuous_toFun := continuous_iff.2 fun a ↦ by
    simpa only [Equiv.toFun_as_coe, AlgHom.liftEquiv_symm_apply] using
      (continuous_eval (k := K) (A := K ⊗[k] A) (R := R) (1 ⊗ₜ[k] a))
  continuous_invFun := by
    refine continuous_iff.2 fun t ↦ ?_
    induction t using TensorProduct.inductionOn with
    | tmul c a =>
      simpa only [Equiv.invFun_as_coe, Equiv.symm_symm, AlgHom.liftEquiv_tmul,
        Algebra.smul_def] using
        (continuous_const (y := algebraMap K R c)).fun_mul
          (continuous_eval (k := k) (A := A) a)
    | add t u ht hu => simpa only [map_add] using ht.fun_add hu

/-- Restriction along base change evaluates at `1 ⊗ a`. -/
@[simp]
theorem baseChangeHomeomorph_apply (x : K ⊗[k] A →ₐ[K] R) (a : A) :
    baseChangeHomeomorph k K A R x a = x (1 ⊗ₜ[k] a) := by
  simp only [baseChangeHomeomorph, Homeomorph.homeomorph_mk_coe,
    AlgHom.liftEquiv_symm_apply]

/-- Extending a point across base change uses the prescribed coefficient algebra structure. -/
@[simp]
theorem baseChangeHomeomorph_symm_apply_tmul (x : A →ₐ[k] R) (c : K) (a : A) :
    (baseChangeHomeomorph k K A R).symm x (c ⊗ₜ[k] a) = c • x a :=
  AlgHom.liftEquiv_tmul x c a

end BaseChange

end TauCeti.PointTopology
