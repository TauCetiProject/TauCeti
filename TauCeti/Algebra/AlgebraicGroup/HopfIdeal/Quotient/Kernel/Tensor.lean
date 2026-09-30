/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic

/-!
# The kernel pair of an affine group homomorphism in coordinates

For a coordinate morphism `f : H ⟶ K`, the kernel pair of `Spec K → Spec H` is
isomorphic to `Spec K × ker f`. On points the isomorphism sends `(g, n)` to `(g, g n)`;
its inverse sends `(g, h)` to `(g, g⁻¹ h)`. This file constructs the corresponding
`K`-algebra equivalence `K ⊗[H] K ≃ₐ[K] K ⊗[R] (K ⧸ kernelHopfIdeal f)`.

No flatness or surjectivity hypothesis is needed. The isomorphism supplies the kernel-pair
calculation used to descend properties of affine-group morphisms from their kernels.
The construction uses `kernelHopfIdeal_toIdeal_le_ker_iff` and the convolution functoriality
of `TauCeti.AlgHom.mapDomain` and `TauCeti.AlgHom.mapValue`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
* J. S. Milne, *Algebraic Groups* (2017), §5.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

noncomputable section

/-- The product of the universal source point and universal kernel point, as a map of
`H`-algebras. -/
private def kernelPairRight (f : H ⟶ K) :
    letI := f.hom.toAlgHom.toAlgebra
    K →ₐ[H] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let := f.hom.toAlgHom.toAlgebra
  let Q := K ⧸ (kernelHopfIdeal f).toIdeal
  let l : K →ₐ[R] K ⊗[R] Q := Algebra.TensorProduct.includeLeft
  let r : K →ₐ[R] K ⊗[R] Q :=
    Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ R _)
  have hr : AlgHom.mapDomain f.hom (toConv r) = 1 := by
    apply ofConv_injective
    exact (kernelHopfIdeal_toIdeal_le_ker_iff f r).mp (by
      intro x hx
      have hz : (Ideal.Quotient.mkₐ R (kernelHopfIdeal f).toIdeal) x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hx
      simp [RingHom.mem_ker, r, hz])
  have he : (ofConv (toConv l * toConv r)).comp f.hom.toAlgHom =
      l.comp f.hom.toAlgHom := by
    have he : AlgHom.mapDomain f.hom (toConv l * toConv r) =
        AlgHom.mapDomain f.hom (toConv l) := by
      rw [map_mul, hr]
      exact mul_one (AlgHom.mapDomain f.hom (toConv l))
    exact congrArg ofConv he
  exact
    { (ofConv (toConv l * toConv r)).toRingHom with
      commutes' h := AlgHom.congr_fun he h }

/-- The coordinate map of `(g,n) ↦ (g,gn)`. -/
private def kernelPairForward (f : H ⟶ K) :
    letI := f.hom.toAlgHom.toAlgebra
    K ⊗[H] K →ₐ[K] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  letI := f.hom.toAlgHom.toAlgebra
  exact Algebra.TensorProduct.lift (Algebra.ofId _ _) (kernelPairRight f)
    (fun _ _ ↦ Commute.all _ _)

/-- The ratio of the two universal points in the kernel pair factors through the kernel. -/
private def kernelPairRatio (f : H ⟶ K) :
    letI := f.hom.toAlgHom.toAlgebra
    K ⧸ (kernelHopfIdeal f).toIdeal →ₐ[R] K ⊗[H] K := by
  let := f.hom.toAlgHom.toAlgebra
  let l : K →ₐ[R] K ⊗[H] K :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[H] K).restrictScalars R
  let r : K →ₐ[R] K ⊗[H] K :=
    (Algebra.TensorProduct.includeRight : K →ₐ[H] K ⊗[H] K).restrictScalars R
  have he : AlgHom.mapDomain f.hom (toConv l) =
      AlgHom.mapDomain f.hom (toConv r) := by
    apply ofConv_injective
    ext h
    exact RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := H)
        (A := K) (B := K)) h
  have hratio : AlgHom.mapDomain f.hom ((toConv l)⁻¹ * toConv r) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  apply Ideal.Quotient.liftₐ _ (ofConv ((toConv l)⁻¹ * toConv r))
  intro x hx
  apply (kernelHopfIdeal_toIdeal_le_ker_iff f _).mpr (congrArg ofConv hratio) hx

/-- The coordinate map of `(g,h) ↦ (g,g⁻¹h)`. -/
private def kernelPairBackward (f : H ⟶ K) :
    letI := f.hom.toAlgHom.toAlgebra
    K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal) →ₐ[K] K ⊗[H] K := by
  letI := f.hom.toAlgHom.toAlgebra
  exact Algebra.TensorProduct.lift (Algebra.ofId _ _) (kernelPairRatio f)
    (fun _ _ ↦ Commute.all _ _)

private theorem kernelPairRight_apply (f : H ⟶ K) (x : K) :
    let := f.hom.toAlgHom.toAlgebra
    kernelPairRight f x =
      (ofConv (toConv (Algebra.TensorProduct.includeLeft :
        K →ₐ[R] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal)) *
        toConv (Algebra.TensorProduct.includeRight.comp
          (Ideal.Quotient.mkₐ R (kernelHopfIdeal f).toIdeal))) :
        K →ₐ[R] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal)) x := by
  -- The constructor retains the convolution's underlying ring homomorphism;
  -- only its scalar-compatibility proof changes.
  rfl

private theorem kernelPairForward_tmul (f : H ⟶ K) (x y : K) :
    let := f.hom.toAlgHom.toAlgebra
    kernelPairForward f (x ⊗ₜ[H] y) =
      (x ⊗ₜ[R] (1 : K ⧸ (kernelHopfIdeal f).toIdeal)) * kernelPairRight f y := by
  let := f.hom.toAlgHom.toAlgebra
  rw [kernelPairForward, Algebra.TensorProduct.lift_tmul]
  simp only [Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

private theorem kernelPairRatio_mk (f : H ⟶ K) (x : K) :
    let := f.hom.toAlgHom.toAlgebra
    kernelPairRatio f (Ideal.Quotient.mk (kernelHopfIdeal f).toIdeal x) =
      (ofConv ((toConv ((Algebra.TensorProduct.includeLeft :
        K →ₐ[K] K ⊗[H] K).restrictScalars R))⁻¹ *
        toConv ((Algebra.TensorProduct.includeRight :
          K →ₐ[H] K ⊗[H] K).restrictScalars R))) x := by
  -- The quotient lift evaluates to its defining homomorphism on representatives.
  -- Reduction here also unfolds the kernel-membership proof passed to the lift,
  -- whose type prevents rewriting directly with `Ideal.Quotient.liftₐ_apply`.
  rfl

private theorem kernelPairBackward_tmul (f : H ⟶ K) (x : K)
    (y : K ⧸ (kernelHopfIdeal f).toIdeal) :
    let := f.hom.toAlgHom.toAlgebra
    kernelPairBackward f (x ⊗ₜ[R] y) =
      (x ⊗ₜ[H] (1 : K)) * kernelPairRatio f y := by
  let := f.hom.toAlgHom.toAlgebra
  simp [kernelPairBackward]

/-- The two coordinate constructions compose to the identity on the kernel pair. -/
private theorem kernelPairBackward_comp_forward (f : H ⟶ K) :
    letI := f.hom.toAlgHom.toAlgebra
    (kernelPairBackward f).comp (kernelPairForward f) = AlgHom.id K (K ⊗[H] K) := by
  let := f.hom.toAlgHom.toAlgebra
  let l : K →ₐ[R] K ⊗[H] K :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[H] K).restrictScalars R
  let r : K →ₐ[R] K ⊗[H] K :=
    (Algebra.TensorProduct.includeRight : K →ₐ[H] K ⊗[H] K).restrictScalars R
  have he : AlgHom.mapValue ((kernelPairBackward f).restrictScalars R)
      (toConv (Algebra.TensorProduct.includeLeft :
        K →ₐ[R] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal)) *
       toConv (Algebra.TensorProduct.includeRight.comp
        (Ideal.Quotient.mkₐ R (kernelHopfIdeal f).toIdeal))) = toConv r := by
    rw [map_mul]
    have hl : AlgHom.mapValue ((kernelPairBackward f).restrictScalars R)
        (toConv (Algebra.TensorProduct.includeLeft :
          K →ₐ[R] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal))) = toConv l := by
      apply ofConv_injective
      ext x
      simp [AlgHom.mapValue_apply, kernelPairBackward_tmul, l]
    have hr : AlgHom.mapValue ((kernelPairBackward f).restrictScalars R)
        (toConv (Algebra.TensorProduct.includeRight.comp
          (Ideal.Quotient.mkₐ R (kernelHopfIdeal f).toIdeal))) =
        (toConv l)⁻¹ * toConv r := by
      apply ofConv_injective
      ext x
      simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
        AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
        Ideal.Quotient.mkₐ_eq_mk, kernelPairBackward_tmul, kernelPairRatio_mk,
        ← Algebra.TensorProduct.one_def, one_mul, l, r]
    rw [hl, hr, mul_inv_cancel_left]
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · ext x
    simpa only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      kernelPairForward_tmul, ← Algebra.TensorProduct.one_def, one_mul,
      kernelPairRight_apply, AlgHom.id_apply, AlgHom.mapValue_apply, ofConv_toConv,
      AlgHom.restrictScalars_apply, r] using AlgHom.congr_fun (congrArg ofConv he) x

/-- The two coordinate constructions compose to the identity on the source times the kernel. -/
private theorem kernelPairForward_comp_backward (f : H ⟶ K) :
    letI := f.hom.toAlgHom.toAlgebra
    (kernelPairForward f).comp (kernelPairBackward f) =
      AlgHom.id K (K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal)) := by
  let := f.hom.toAlgHom.toAlgebra
  let Q := K ⧸ (kernelHopfIdeal f).toIdeal
  let l : K →ₐ[R] K ⊗[R] Q := Algebra.TensorProduct.includeLeft
  let r : K →ₐ[R] K ⊗[R] Q :=
    Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ R _)
  have he : AlgHom.mapValue ((kernelPairForward f).restrictScalars R)
      ((toConv ((Algebra.TensorProduct.includeLeft :
          K →ₐ[K] K ⊗[H] K).restrictScalars R))⁻¹ *
        toConv ((Algebra.TensorProduct.includeRight :
          K →ₐ[H] K ⊗[H] K).restrictScalars R)) = toConv r := by
    rw [map_mul, map_inv]
    have hl : AlgHom.mapValue ((kernelPairForward f).restrictScalars R)
        (toConv ((Algebra.TensorProduct.includeLeft :
          K →ₐ[K] K ⊗[H] K).restrictScalars R)) = toConv l := by
      apply ofConv_injective
      ext x
      simp [AlgHom.mapValue_apply, kernelPairForward_tmul, l]
    have hr : AlgHom.mapValue ((kernelPairForward f).restrictScalars R)
        (toConv ((Algebra.TensorProduct.includeRight :
          K →ₐ[H] K ⊗[H] K).restrictScalars R)) = toConv l * toConv r := by
      apply ofConv_injective
      ext x
      simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
        AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
        kernelPairForward_tmul, ← Algebra.TensorProduct.one_def, one_mul,
        kernelPairRight_apply, l, r]
    rw [hl, hr, inv_mul_cancel_left]
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (kernelHopfIdeal f).toIdeal x
    have hx := AlgHom.congr_fun (congrArg ofConv he) x
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply] at hx
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.mkₐ_eq_mk,
      kernelPairBackward_tmul, kernelPairRatio_mk,
      ← Algebra.TensorProduct.one_def, one_mul, AlgHom.id_apply]
    exact hx

/-- The coordinate algebra of the kernel pair of an affine group homomorphism is the tensor
product of the source coordinate algebra with that of its scheme-theoretic kernel.
The map on points is `(g,n) ↦ (g,gn)`. -/
def kernelPairTensorEquiv (f : H ⟶ K) :
    letI := f.hom.toAlgHom.toAlgebra
    K ⊗[H] K ≃ₐ[K] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  letI := f.hom.toAlgHom.toAlgebra
  exact AlgEquiv.ofAlgHom (kernelPairForward f) (kernelPairBackward f)
    (kernelPairForward_comp_backward f) (kernelPairBackward_comp_forward f)

/-- On pure tensors, the kernel-pair equivalence multiplies the first factor by the
comultiplication of the second, followed by projection onto the kernel coordinates. -/
@[simp]
theorem kernelPairTensorEquiv_tmul (f : H ⟶ K) (x y : K) :
    letI := f.hom.toAlgHom.toAlgebra
    kernelPairTensorEquiv f (x ⊗ₜ[H] y) =
      (x ⊗ₜ[R] (1 : K ⧸ (kernelHopfIdeal f).toIdeal)) *
        Algebra.TensorProduct.map (AlgHom.id R K)
          (Ideal.Quotient.mkₐ R (kernelHopfIdeal f).toIdeal)
          (Coalgebra.comul (R := R) y) := by
  let := f.hom.toAlgHom.toAlgebra
  have hm : Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft :
        K →ₐ[R] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal))
      (Algebra.TensorProduct.includeRight.comp
        (Ideal.Quotient.mkₐ R (kernelHopfIdeal f).toIdeal)) (fun _ _ ↦ Commute.all _ _) =
      Algebra.TensorProduct.map (AlgHom.id R K)
        (Ideal.Quotient.mkₐ R (kernelHopfIdeal f).toIdeal) := by
    ext <;> simp
  simp only [kernelPairTensorEquiv, AlgEquiv.ofAlgHom_apply,
    kernelPairForward_tmul, kernelPairRight_apply]
  congr 1
  rw [← hm]
  exact AlgHom.convMul_apply
    (toConv (Algebra.TensorProduct.includeLeft :
      K →ₐ[R] K ⊗[R] (K ⧸ (kernelHopfIdeal f).toIdeal)))
    (toConv (Algebra.TensorProduct.includeRight.comp
      (Ideal.Quotient.mkₐ R (kernelHopfIdeal f).toIdeal))) y

/-- On a quotient representative, the inverse kernel-pair equivalence uses the antipode
in the first leg of comultiplication and then balances the tensor product over `H`. -/
@[simp]
theorem kernelPairTensorEquiv_symm_tmul_mk (f : H ⟶ K) (x y : K) :
    letI := f.hom.toAlgHom.toAlgebra
    (kernelPairTensorEquiv f).symm
        (x ⊗ₜ[R] (Ideal.Quotient.mk (kernelHopfIdeal f).toIdeal) y) =
      (x ⊗ₜ[H] (1 : K)) *
        Algebra.TensorProduct.mapOfCompatibleSMul H R K K K
          (Algebra.TensorProduct.map (_root_.HopfAlgebra.antipodeAlgHom R K) (AlgHom.id R K)
            (Coalgebra.comul (R := R) y)) := by
  let := f.hom.toAlgHom.toAlgebra
  let l : K →ₐ[R] K ⊗[H] K :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[H] K).restrictScalars R
  let r : K →ₐ[R] K ⊗[H] K :=
    (Algebra.TensorProduct.includeRight : K →ₐ[H] K ⊗[H] K).restrictScalars R
  have hm : Algebra.TensorProduct.lift (ofConv (toConv l)⁻¹) r
      (fun _ _ ↦ Commute.all _ _) =
      ((Algebra.TensorProduct.mapOfCompatibleSMul H R K K K).restrictScalars R).comp
        (Algebra.TensorProduct.map (_root_.HopfAlgebra.antipodeAlgHom R K) (AlgHom.id R K)) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [l, r, AlgHom.convInv_apply, Algebra.TensorProduct.tmul_mul_tmul]
  simp only [kernelPairTensorEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply,
    kernelPairBackward_tmul, kernelPairRatio_mk]
  congr 1
  rw [AlgHom.convMul_apply, hm]
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]

end
end TauCeti.CommHopfAlgCat
