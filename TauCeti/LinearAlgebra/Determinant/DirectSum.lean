/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Quotient.Prod
public import TauCeti.LinearAlgebra.Submodule.Prod
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# Determinant lines of direct sums

For finite-dimensional vector spaces `U` and `W`, the split short exact sequence
`0 → U → U × W → W → 0` identifies `det U ⊗ det W` with `det (U × W)`
(`TauCeti.detLineProdEquiv`): inside the exterior algebra of `U × W` it sends `a ⊗ b` to the
product of the images of `a` and `b` under the two inclusions. This is the top-degree piece of
Mathlib's `ExteriorAlgebra.prodEquivTensor`. Exchanging the factors costs the sign
`(-1) ^ (dim U * dim W)` (`TauCeti.detLineCongr_prodComm_detLineProdEquiv`).

For linear maps `f : M → N` and `g : M' → N'` with finite-dimensional kernels and cokernels, the
kernel and the cokernel of the direct sum `f.prodMap g` are the products of those of `f` and `g`.
The determinant lines `det f = det (ker f) ⊗ (det (coker f))^*` therefore satisfy

`det (f.prodMap g) ≃ det f ⊗ det g`

(`LinearMap.detLineProdMapEquiv`). Reordering `det (ker f) ⊗ det (ker g) ⊗ (det (coker f))^* ⊗
(det (coker g))^*` into `det (ker f) ⊗ (det (coker f))^* ⊗ det (ker g) ⊗ (det (coker g))^*` moves
`(det (coker f))^*` past `det (ker g)`; following the Koszul rule for lines graded by dimension,
the isomorphism carries the sign `(-1) ^ (dim (coker f) * dim (ker g))` of this move. With this
normalization, exchanging the two summands costs the sign `(-1) ^ (ind f * ind g)`, which only
depends on the parities of the Fredholm indices `ind f = dim (ker f) - dim (coker f)`
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`). This is the direct sum law of the
determinant lines of Fredholm operators, through which orientations of the determinant lines of
two operators orient that of their direct sum, as for the linearized operators of a broken
configuration before gluing.

## Main declarations

* `TauCeti.detLineProdEquiv`: the isomorphism `det U ⊗ det W ≃ det (U × W)`, with its value
  `TauCeti.coe_detLineProdEquiv_tmul`.
* `TauCeti.detLineCongr_prodCongr_detLineProdEquiv`: naturality under linear isomorphisms of the
  two factors.
* `TauCeti.detLineCongr_prodComm_detLineProdEquiv`: exchanging the factors is the sign
  `(-1) ^ (dim U * dim W)`.
* `TauCeti.detLineCongr_prodAssoc_detLineProdEquiv`: the isomorphism is associative.
* `TauCeti.dualDetLineProdEquiv`: the dual isomorphism `(det U)^* ⊗ (det W)^* ≃ (det (U × W))^*`,
  evaluated by `TauCeti.dualDetLineProdEquiv_tmul_detLineProdEquiv_tmul`.
* `LinearMap.detLineProdMapEquiv`: the isomorphism `det (f.prodMap g) ≃ det f ⊗ det g`, with its
  value `LinearMap.detLineProdMapEquiv_tmul`.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`: exchanging the summands is the sign
  `(-1) ^ ((dim (ker f) + dim (coker f)) * (dim (ker g) + dim (coker g)))`, the parity of
  `ind f * ind g`.

## References

* F. Knudsen, D. Mumford, *The projectivity of the moduli space of stable curves I:
  Preliminaries on "det" and "Div"*, Math. Scand. **39** (1976), 19–55 (graded determinant
  lines and their Koszul signs).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of Fredholm operators).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties,
  and classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

variable {K : Type*} [Field K]

section Module

variable {U W X : Type*} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X] [FiniteDimensional K U] [FiniteDimensional K W]

/-- **The determinant line of a product.** For finite-dimensional vector spaces `U` and `W`, the
isomorphism `det U ⊗ det W ≃ det (U × W)` of the split short exact sequence
`0 → U → U × W → W → 0` (`TauCeti.detLineShortExactEquiv`). Inside the exterior algebra of
`U × W` it sends `a ⊗ b` to the product of the images of `a` and `b` under the two inclusions
(`TauCeti.coe_detLineProdEquiv_tmul`). -/
def detLineProdEquiv : detLine K U ⊗[K] detLine K W ≃ₗ[K] detLine K (U × W) :=
  detLineShortExactEquiv (LinearMap.inl_injective (R := K)) Function.Exact.inl_snd
    (LinearMap.snd_surjective (R := K))

/-- `TauCeti.detLineProdEquiv` sends `a ⊗ b` to the product in the exterior algebra of `U × W`
of the images of `a` and `b` under the inclusions of `U` and `W`. -/
@[simp]
theorem coe_detLineProdEquiv_tmul (a : detLine K U) (b : detLine K W) :
    (detLineProdEquiv (a ⊗ₜ b) : ExteriorAlgebra K (U × W)) =
      ExteriorAlgebra.map (LinearMap.inl K U W) (a : ExteriorAlgebra K U) *
        ExteriorAlgebra.map (LinearMap.inr K U W) (b : ExteriorAlgebra K W) := by
  obtain ⟨c, rfl⟩ := (Module.finBasis K W).exists_smul_ιMulti_eq b
  have h := coe_detLineShortExactEquiv_tmul_eq_map_mul (LinearMap.inl_injective (R := K))
    Function.Exact.inl_snd (LinearMap.snd_surjective (R := K)) a
    (LinearMap.inr K U W ∘ Module.finBasis K W)
  rw [show (LinearMap.snd K U W : U × W → W) ∘ (LinearMap.inr K U W ∘ Module.finBasis K W) =
    Module.finBasis K W by funext; simp] at h
  rw [TensorProduct.tmul_smul, map_smul, Submodule.coe_smul, detLineProdEquiv, h,
    Submodule.coe_smul, map_smul, mul_smul_comm, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti]

/-- **Naturality of `TauCeti.detLineProdEquiv`.** For linear isomorphisms `e₁ : U ≃ U'` and
`e₂ : W ≃ W'`, the isomorphism of determinant lines induced by `e₁ × e₂` is the tensor product of
those induced by `e₁` and `e₂`. -/
theorem detLineCongr_prodCongr_detLineProdEquiv {U' W' : Type*} [AddCommGroup U'] [Module K U']
    [AddCommGroup W'] [Module K W'] [FiniteDimensional K U'] [FiniteDimensional K W']
    (e₁ : U ≃ₗ[K] U') (e₂ : W ≃ₗ[K] W') (a : detLine K U) (b : detLine K W) :
    LinearEquiv.detLineCongr (e₁.prodCongr e₂) (detLineProdEquiv (a ⊗ₜ b)) =
      detLineProdEquiv (LinearEquiv.detLineCongr e₁ a ⊗ₜ LinearEquiv.detLineCongr e₂ b) := by
  have hl : (e₁.prodCongr e₂).toLinearMap ∘ₗ LinearMap.inl K U W =
      LinearMap.inl K U' W' ∘ₗ e₁.toLinearMap := by ext <;> simp
  have hr : (e₁.prodCongr e₂).toLinearMap ∘ₗ LinearMap.inr K U W =
      LinearMap.inr K U' W' ∘ₗ e₂.toLinearMap := by ext <;> simp
  refine Subtype.ext ?_
  simp only [LinearEquiv.coe_detLineCongr, coe_detLineProdEquiv_tmul, map_mul,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hl, hr]

/-- **Exchanging the factors of `TauCeti.detLineProdEquiv`** multiplies it by
`(-1) ^ (dim U * dim W)`: under `U × W ≃ W × U`, the image of `a ⊗ b` is `(-1) ^ (dim U * dim W)`
times the image of `b ⊗ a`. -/
theorem detLineCongr_prodComm_detLineProdEquiv (a : detLine K U) (b : detLine K W) :
    LinearEquiv.detLineCongr (LinearEquiv.prodComm K U W) (detLineProdEquiv (a ⊗ₜ b)) =
      (-1 : K) ^ (finrank K U * finrank K W) • detLineProdEquiv (b ⊗ₜ a) := by
  refine Subtype.ext ?_
  have hl : (LinearEquiv.prodComm K U W).toLinearMap ∘ₗ LinearMap.inl K U W =
      LinearMap.inr K W U := by ext <;> simp
  have hr : (LinearEquiv.prodComm K U W).toLinearMap ∘ₗ LinearMap.inr K U W =
      LinearMap.inl K W U := by ext <;> simp
  rw [LinearEquiv.coe_detLineCongr, coe_detLineProdEquiv_tmul, map_mul, ← AlgHom.comp_apply,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, hl, hr,
    Submodule.coe_smul,
    coe_detLineProdEquiv_tmul, ExteriorAlgebra.map_inl_inr_anticomm K _ _ b a,
    ← Int.cast_smul_eq_zsmul K, smul_smul]
  norm_num [mul_comm (finrank K W), ← mul_pow]

/-- **Associativity of `TauCeti.detLineProdEquiv`.** Under `(U × W) × X ≃ U × (W × X)`, the image
of `(a ⊗ b) ⊗ c` is the image of `a ⊗ (b ⊗ c)`. -/
theorem detLineCongr_prodAssoc_detLineProdEquiv [FiniteDimensional K X] (a : detLine K U)
    (b : detLine K W) (c : detLine K X) :
    LinearEquiv.detLineCongr (LinearEquiv.prodAssoc K U W X)
        (detLineProdEquiv (detLineProdEquiv (a ⊗ₜ b) ⊗ₜ c)) =
      detLineProdEquiv (a ⊗ₜ detLineProdEquiv (b ⊗ₜ c)) := by
  have h₁ : (LinearEquiv.prodAssoc K U W X).toLinearMap ∘ₗ LinearMap.inl K (U × W) X ∘ₗ
      LinearMap.inl K U W = LinearMap.inl K U (W × X) := by
    ext <;> simp [LinearEquiv.prodAssoc_apply]
  have h₂ : (LinearEquiv.prodAssoc K U W X).toLinearMap ∘ₗ LinearMap.inl K (U × W) X ∘ₗ
      LinearMap.inr K U W = LinearMap.inr K U (W × X) ∘ₗ LinearMap.inl K W X := by
    ext <;> simp [LinearEquiv.prodAssoc_apply]
  have h₃ : (LinearEquiv.prodAssoc K U W X).toLinearMap ∘ₗ LinearMap.inr K (U × W) X =
      LinearMap.inr K U (W × X) ∘ₗ LinearMap.inr K W X := by
    ext <;> simp [LinearEquiv.prodAssoc_apply]
  refine Subtype.ext ?_
  simp only [LinearEquiv.coe_detLineCongr, coe_detLineProdEquiv_tmul, map_mul,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h₁, h₂, h₃, mul_assoc]

/-- **The dual of `TauCeti.detLineProdEquiv`**: the isomorphism
`(det U)^* ⊗ (det W)^* ≃ (det (U × W))^*` whose value on `φ ⊗ ψ` takes the value `φ a * ψ b` at the
image of `a ⊗ b` (`TauCeti.dualDetLineProdEquiv_tmul_detLineProdEquiv_tmul`). -/
def dualDetLineProdEquiv :
    Dual K (detLine K U) ⊗[K] Dual K (detLine K W) ≃ₗ[K] Dual K (detLine K (U × W)) :=
  dualDistribEquiv K _ _ ≪≫ₗ detLineProdEquiv.symm.dualMap

@[simp]
theorem dualDetLineProdEquiv_tmul_detLineProdEquiv_tmul (φ : Dual K (detLine K U))
    (ψ : Dual K (detLine K W)) (a : detLine K U) (b : detLine K W) :
    dualDetLineProdEquiv (φ ⊗ₜ ψ) (detLineProdEquiv (a ⊗ₜ b)) = φ a * ψ b := by
  simpa [dualDetLineProdEquiv] using mul_comm (ψ b) (φ a)

/-- **Exchanging the factors of `TauCeti.dualDetLineProdEquiv`** multiplies it by
`(-1) ^ (dim U * dim W)`, as for `TauCeti.detLineCongr_prodComm_detLineProdEquiv`. -/
theorem dualDetLineProdEquiv_tmul_comp_detLineCongr_prodComm (φ : Dual K (detLine K U))
    (ψ : Dual K (detLine K W)) :
    dualDetLineProdEquiv (φ ⊗ₜ ψ) ∘ₗ
        (LinearEquiv.detLineCongr (LinearEquiv.prodComm K W U)).toLinearMap =
      (-1 : K) ^ (finrank K U * finrank K W) • dualDetLineProdEquiv (ψ ⊗ₜ φ) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := detLineProdEquiv.surjective x
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul b a =>
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, detLineCongr_prodComm_detLineProdEquiv,
      map_smul, dualDetLineProdEquiv_tmul_detLineProdEquiv_tmul, LinearMap.smul_apply,
      dualDetLineProdEquiv_tmul_detLineProdEquiv_tmul, smul_eq_mul, smul_eq_mul, mul_comm (φ a),
      mul_comm (finrank K W)]

end Module

end TauCeti

namespace LinearMap

open TauCeti

variable {K : Type*} [Field K] {M N M' N' : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
  (f : M →ₗ[K] N) (g : M' →ₗ[K] N') [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]
  [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)]

/-- **The determinant line of a direct sum.** For linear maps `f` and `g` with finite-dimensional
kernels and cokernels, the isomorphism `det (f.prodMap g) ≃ det f ⊗ det g`. The kernel and the
cokernel of `f.prodMap g` are the products of those of `f` and `g`
(`LinearMap.kerProdMapEquiv`, `LinearMap.quotientRangeProdMapEquiv`), so their determinant lines
split by `TauCeti.detLineProdEquiv` and `TauCeti.dualDetLineProdEquiv`; the four factors are then
reordered, with the Koszul sign `(-1) ^ (dim (coker f) * dim (ker g))` of moving
`(det (coker f))^*` past `det (ker g)`. Its value is `LinearMap.detLineProdMapEquiv_tmul`. -/
def detLineProdMapEquiv : (f.prodMap g).detLine ≃ₗ[K] f.detLine ⊗[K] g.detLine :=
  TensorProduct.congr
      ((LinearEquiv.detLineCongr (kerProdMapEquiv f g)).trans detLineProdEquiv.symm)
      ((LinearEquiv.detLineCongr (quotientRangeProdMapEquiv f g)).symm.dualMap.trans
        dualDetLineProdEquiv.symm) ≪≫ₗ
    TensorProduct.tensorTensorTensorComm K _ _ _ _ ≪≫ₗ
    LinearEquiv.smulOfUnit ((-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)))

/-- **The value of `LinearMap.detLineProdMapEquiv`.** Let `a ⊗ φ ∈ det f` and `b ⊗ ψ ∈ det g`. The
element of `det (f.prodMap g)` whose kernel part is the image of `a ⊗ b` and whose cokernel part
is the functional evaluating `φ ⊗ ψ` goes to `(-1) ^ (dim (coker f) * dim (ker g))` times
`(a ⊗ φ) ⊗ (b ⊗ ψ)`. -/
theorem detLineProdMapEquiv_tmul (a : TauCeti.detLine K (ker f))
    (φ : Dual K (TauCeti.detLine K (N ⧸ range f))) (b : TauCeti.detLine K (ker g))
    (ψ : Dual K (TauCeti.detLine K (N' ⧸ range g))) :
    detLineProdMapEquiv f g
        (LinearEquiv.detLineCongr (kerProdMapEquiv f g).symm (detLineProdEquiv (a ⊗ₜ b)) ⊗ₜ
          (dualDetLineProdEquiv (φ ⊗ₜ ψ) ∘ₗ
            (LinearEquiv.detLineCongr (quotientRangeProdMapEquiv f g)).toLinearMap)) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) • ((a ⊗ₜ φ) ⊗ₜ (b ⊗ₜ ψ)) := by
  have hφψ : (LinearEquiv.detLineCongr (quotientRangeProdMapEquiv f g)).symm.dualMap
      (dualDetLineProdEquiv (φ ⊗ₜ ψ) ∘ₗ
        (LinearEquiv.detLineCongr (quotientRangeProdMapEquiv f g)).toLinearMap) =
      dualDetLineProdEquiv (φ ⊗ₜ ψ) := by
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearEquiv.dualMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  simp only [detLineProdMapEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    ← LinearEquiv.detLineCongr_symm, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
    hφψ, TensorProduct.tensorTensorTensorComm_tmul, LinearEquiv.smulOfUnit]
  simp [Units.smul_def]

/-- **The inverse of `LinearMap.detLineProdMapEquiv`** sends `(a ⊗ φ) ⊗ (b ⊗ ψ)` to
`(-1) ^ (dim (coker f) * dim (ker g))` times the element of `det (f.prodMap g)` whose kernel part
is the image of `a ⊗ b` and whose cokernel part is the functional evaluating `φ ⊗ ψ`. -/
theorem detLineProdMapEquiv_symm_tmul (a : TauCeti.detLine K (ker f))
    (φ : Dual K (TauCeti.detLine K (N ⧸ range f))) (b : TauCeti.detLine K (ker g))
    (ψ : Dual K (TauCeti.detLine K (N' ⧸ range g))) :
    (detLineProdMapEquiv f g).symm ((a ⊗ₜ φ) ⊗ₜ (b ⊗ₜ ψ)) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) •
        (LinearEquiv.detLineCongr (kerProdMapEquiv f g).symm (detLineProdEquiv (a ⊗ₜ b)) ⊗ₜ
          (dualDetLineProdEquiv (φ ⊗ₜ ψ) ∘ₗ
            (LinearEquiv.detLineCongr (quotientRangeProdMapEquiv f g)).toLinearMap)) := by
  rw [LinearEquiv.symm_apply_eq, map_smul, detLineProdMapEquiv_tmul, smul_smul, ← mul_pow,
    neg_one_mul, neg_neg, one_pow, one_smul]

omit [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)] in
/-- The kernel part of `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`: exchanging the
factors of `ker f × ker g` costs `(-1) ^ (dim (ker f) * dim (ker g))`. -/
private theorem detLineCongr_ofSubmodules_prodComm (a : TauCeti.detLine K (ker f))
    (b : TauCeti.detLine K (ker g)) (h : (ker (f.prodMap g)).map
      (LinearEquiv.prodComm K M M').toLinearMap = ker (g.prodMap f)) :
    LinearEquiv.detLineCongr ((LinearEquiv.prodComm K M M').ofSubmodules _ _ h)
        (LinearEquiv.detLineCongr (kerProdMapEquiv f g).symm (detLineProdEquiv (a ⊗ₜ b))) =
      (-1 : K) ^ (finrank K (ker f) * finrank K (ker g)) •
        LinearEquiv.detLineCongr (kerProdMapEquiv g f).symm (detLineProdEquiv (b ⊗ₜ a)) := by
  have hk : (kerProdMapEquiv f g).symm.trans ((LinearEquiv.prodComm K M M').ofSubmodules _ _ h) =
      (LinearEquiv.prodComm K (ker f) (ker g)).trans (kerProdMapEquiv g f).symm := by
    ext x <;> simp
  rw [← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans, hk,
    LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply,
    detLineCongr_prodComm_detLineProdEquiv, map_smul]

omit [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)] in
/-- The cokernel part of `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`: exchanging the
factors of `coker f × coker g` costs `(-1) ^ (dim (coker f) * dim (coker g))`. -/
private theorem comp_detLineCongr_quotientEquiv_prodComm_symm
    (φ : Dual K (TauCeti.detLine K (N ⧸ range f)))
    (ψ : Dual K (TauCeti.detLine K (N' ⧸ range g)))
    (h : (range (f.prodMap g)).map (LinearEquiv.prodComm K N N').toLinearMap =
      range (g.prodMap f)) :
    (dualDetLineProdEquiv (φ ⊗ₜ ψ) ∘ₗ
        (LinearEquiv.detLineCongr (quotientRangeProdMapEquiv f g)).toLinearMap) ∘ₗ
      (LinearEquiv.detLineCongr
        (Submodule.Quotient.equiv _ _ (LinearEquiv.prodComm K N N') h)).symm.toLinearMap =
    (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (N' ⧸ range g)) •
      (dualDetLineProdEquiv (ψ ⊗ₜ φ) ∘ₗ
        (LinearEquiv.detLineCongr (quotientRangeProdMapEquiv g f)).toLinearMap) := by
  have hc : (Submodule.Quotient.equiv _ _ (LinearEquiv.prodComm K N N') h).symm.trans
      (quotientRangeProdMapEquiv f g) =
        (quotientRangeProdMapEquiv g f).trans
          (LinearEquiv.prodComm K (N' ⧸ range g) (N ⧸ range f)) := by
    refine LinearEquiv.toLinearMap_injective (Submodule.linearMap_qext _ ?_)
    ext x <;> simp [Submodule.Quotient.equiv_symm]
  rw [LinearEquiv.detLineCongr_symm, LinearMap.comp_assoc, ← LinearEquiv.coe_trans,
    ← LinearEquiv.detLineCongr_trans, hc, LinearEquiv.detLineCongr_trans,
    LinearEquiv.coe_trans, ← LinearMap.comp_assoc,
    dualDetLineProdEquiv_tmul_comp_detLineCongr_prodComm, LinearMap.smul_comp]

/-- `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm` on the elements of
`det (f.prodMap g)` built from `a ⊗ b` and `φ ⊗ ψ`. -/
private theorem detLineProdMapEquiv_detLineCongr_prodComm_tmul (a : TauCeti.detLine K (ker f))
    (φ : Dual K (TauCeti.detLine K (N ⧸ range f))) (b : TauCeti.detLine K (ker g))
    (ψ : Dual K (TauCeti.detLine K (N' ⧸ range g))) :
    detLineProdMapEquiv g f ((f.prodMap g).detLineCongr (LinearEquiv.prodComm K M M')
        (LinearEquiv.prodComm K N N') (by ext <;> simp)
          (LinearEquiv.detLineCongr (kerProdMapEquiv f g).symm (detLineProdEquiv (a ⊗ₜ b)) ⊗ₜ
            (dualDetLineProdEquiv (φ ⊗ₜ ψ) ∘ₗ
              (LinearEquiv.detLineCongr (quotientRangeProdMapEquiv f g)).toLinearMap))) =
      (-1 : K) ^ ((finrank K (ker f) + finrank K (N ⧸ range f)) *
          (finrank K (ker g) + finrank K (N' ⧸ range g))) •
        TensorProduct.comm K _ _ (detLineProdMapEquiv f g
          (LinearEquiv.detLineCongr (kerProdMapEquiv f g).symm (detLineProdEquiv (a ⊗ₜ b)) ⊗ₜ
            (dualDetLineProdEquiv (φ ⊗ₜ ψ) ∘ₗ
              (LinearEquiv.detLineCongr (quotientRangeProdMapEquiv f g)).toLinearMap))) := by
  simp only [LinearMap.detLineCongr_tmul, detLineCongr_ofSubmodules_prodComm,
    comp_detLineCongr_quotientEquiv_prodComm_symm, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', map_smul, detLineProdMapEquiv_tmul, TensorProduct.comm_tmul,
    smul_smul]
  congr 1
  -- The exponents differ by `2 * dim (coker f) * dim (ker g)`.
  rw [← pow_add, ← pow_add, ← pow_add,
    show (finrank K (ker f) + finrank K (N ⧸ range f)) *
        (finrank K (ker g) + finrank K (N' ⧸ range g)) +
          finrank K (N ⧸ range f) * finrank K (ker g) =
        finrank K (N ⧸ range f) * finrank K (N' ⧸ range g) +
          finrank K (ker f) * finrank K (ker g) +
            finrank K (N' ⧸ range g) * finrank K (ker f) +
          2 * (finrank K (N ⧸ range f) * finrank K (ker g)) by ring,
    pow_add _ _ (2 * _), pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Exchanging the summands of `LinearMap.detLineProdMapEquiv`.** Transporting along the
exchange `M × M' ≃ M' × M`, `N × N' ≃ N' × N` of `f.prodMap g` with `g.prodMap f` turns the
isomorphism for `(f, g)` into the one for `(g, f)` up to exchanging the tensor factors and the
sign `(-1) ^ ((dim (ker f) + dim (coker f)) * (dim (ker g) + dim (coker g)))`. This is the sign
`(-1) ^ (ind f * ind g)`: it depends only on the parities of the indices. -/
theorem detLineProdMapEquiv_detLineCongr_prodComm (x : (f.prodMap g).detLine) :
    detLineProdMapEquiv g f ((f.prodMap g).detLineCongr (LinearEquiv.prodComm K M M')
        (LinearEquiv.prodComm K N N') (by ext <;> simp) x) =
      (-1 : K) ^ ((finrank K (ker f) + finrank K (N ⧸ range f)) *
          (finrank K (ker g) + finrank K (N' ⧸ range g))) •
        TensorProduct.comm K _ _ (detLineProdMapEquiv f g x) := by
  obtain ⟨y, rfl⟩ := (detLineProdMapEquiv f g).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂, smul_add]
  | tmul s t =>
  induction s using TensorProduct.inductionOn with
  | add s₁ s₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂, smul_add]
  | tmul a φ =>
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂, smul_add]
  | tmul b ψ =>
  simp only [detLineProdMapEquiv_symm_tmul, map_smul,
    detLineProdMapEquiv_detLineCongr_prodComm_tmul]
  exact smul_comm _ _ _

end LinearMap
