/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Prod
public import TauCeti.LinearAlgebra.Quotient.Prod
import TauCeti.LinearAlgebra.Contraction
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Determinant lines of direct sums

For finite-dimensional vector spaces `U` and `W`, the short exact sequence
`0 → U → U × W → W → 0` identifies `det U ⊗ det W` with `det (U × W)`
(`TauCeti.detLineProdEquiv`), sending `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to
`(u₁, 0) ∧ ⋯ ∧ (uₐ, 0) ∧ (0, w₁) ∧ ⋯ ∧ (0, w_c)`. Exchanging the factors costs the sign
`(-1) ^ (dim U * dim W)` (`TauCeti.detLineCongr_prodComm_detLineProdEquiv`).

For linear maps `f : M → N` and `g : M' → N'` with finite-dimensional kernels and cokernels, the
kernel and cokernel of the direct sum `f.prodMap g` are the products of those of `f` and `g`.
This gives the **direct sum isomorphism of determinant lines**
`det (f ⊕ g) ≃ det f ⊗ det g` (`LinearMap.detLineProdMapEquiv`), where
`det f = det (ker f) ⊗ (det (coker f))^*`. Rearranging
`(det (ker f) ⊗ det (ker g)) ⊗ ((det (coker f))^* ⊗ (det (coker g))^*)` into
`(det (ker f) ⊗ (det (coker f))^*) ⊗ (det (ker g) ⊗ (det (coker g))^*)` moves the factor
`(det (coker f))^*` past `det (ker g)`, so the isomorphism carries the Koszul sign
`(-1) ^ (dim (coker f) * dim (ker g))`. With this sign, exchanging the two summands multiplies
the isomorphism by `(-1) ^ (ind f * ind g)`, where `ind = dim ker - dim coker`
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`), while reassociating three summands
involves no sign (`LinearMap.detLineProdMapEquiv_detLineCongr_prodAssoc`): the two ways of
splitting `det ((f ⊕ g) ⊕ k)` and `det (f ⊕ (g ⊕ k))` into `det f ⊗ det g ⊗ det k` agree. This is
the direct-sum law through which orientations of the determinant lines of Fredholm operators, and
so of moduli spaces cut out by them, are compared for split operators; associativity makes the
comparison for a split into finitely many summands independent of the bracketing. The same holds
for spaces: `TauCeti.detLineProdEquiv` is the exterior product of the images of its factors
(`TauCeti.coe_detLineProdEquiv_tmul_eq_mul`), natural in both factors and associative.

## Main declarations

* `TauCeti.detLineProdEquiv`: `det U ⊗ det W ≃ det (U × W)`, with its value
  `TauCeti.coe_detLineProdEquiv_tmul`.
* `TauCeti.detLineCongr_prodComm_detLineProdEquiv`: exchanging the factors costs
  `(-1) ^ (dim U * dim W)`.
* `TauCeti.coe_detLineProdEquiv_tmul_eq_mul`: `TauCeti.detLineProdEquiv` is the exterior product
  of the images of the factors.
* `TauCeti.detLineCongr_prodCongr_detLineProdEquiv`: naturality in both factors.
* `TauCeti.detLineCongr_prodAssoc_detLineProdEquiv`: associativity, without a sign.
* `LinearMap.detLineProdMapEquiv`: `det (f.prodMap g) ≃ det f ⊗ det g`, with its value
  `LinearMap.detLineProdMapEquiv_tmul`.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`: exchanging the summands costs
  `(-1) ^ (ind f * ind g)`.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodAssoc`: reassociating three summands involves no
  sign.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, [arXiv:1304.6368](https://arxiv.org/abs/1304.6368) (the canonical
  isomorphisms of determinant lines and their sign conventions).
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

section Prod

variable (K : Type*) [Field K] (U W : Type*) [AddCommGroup U] [Module K U] [AddCommGroup W]
  [Module K W] [FiniteDimensional K U] [FiniteDimensional K W]

/-- **The determinant line of a product.** The isomorphism `det U ⊗ det W ≃ det (U × W)` of the
short exact sequence `0 → U → U × W → W → 0`. It sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to
`(u₁, 0) ∧ ⋯ ∧ (uₐ, 0) ∧ (0, w₁) ∧ ⋯ ∧ (0, w_c)` (`TauCeti.coe_detLineProdEquiv_tmul`). -/
def detLineProdEquiv : detLine K U ⊗[K] detLine K W ≃ₗ[K] detLine K (U × W) :=
  detLineShortExactEquiv LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective

variable {K U W}

/-- `TauCeti.detLineProdEquiv` sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to
`(u₁, 0) ∧ ⋯ ∧ (uₐ, 0) ∧ (0, w₁) ∧ ⋯ ∧ (0, w_c)`, as elements of the exterior algebra of
`U × W`. -/
@[simp]
theorem coe_detLineProdEquiv_tmul (u : Fin (finrank K U) → U) (w : Fin (finrank K W) → W) :
    (detLineProdEquiv K U W (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w) :
        ExteriorAlgebra K (U × W)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (LinearMap.inl K U W ∘ u) (LinearMap.inr K U W ∘ w)) := by
  have h := coe_detLineShortExactEquiv_tmul LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective u (LinearMap.inr K U W ∘ w)
  rwa [← Function.comp_assoc, ← LinearMap.coe_comp, LinearMap.snd_comp_inr, LinearMap.id_coe,
    Function.id_comp] at h

/-- **Exchanging the factors of a product** multiplies `TauCeti.detLineProdEquiv` by
`(-1) ^ (dim U * dim W)`: the isomorphism `det (U × W) ≃ det (W × U)` induced by the swap
`(u, w) ↦ (w, u)` takes `detLineProdEquiv K U W t` to `(-1) ^ (dim U * dim W)` times
`detLineProdEquiv K W U` of the exchanged tensor. -/
theorem detLineCongr_prodComm_detLineProdEquiv (t : detLine K U ⊗[K] detLine K W) :
    (LinearEquiv.prodComm K U W).detLineCongr (detLineProdEquiv K U W t) =
      (-1 : K) ^ (finrank K U * finrank K W) •
        detLineProdEquiv K W U (TensorProduct.comm K _ _ t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht, smul_add]
  | tmul a b =>
    have ha : a ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K (finrank K U))) := by
      rw [exteriorPower.ιMulti_span]; trivial
    have hb : b ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K (finrank K W))) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction ha using Submodule.span_induction with
    | zero => simp
    | add a a' _ _ h h' => simp only [add_tmul, map_add, h, h', smul_add]
    | smul r a _ h => simp only [← smul_tmul', map_smul, h, smul_comm r]
    | mem _ ha =>
      obtain ⟨u, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | zero => simp
      | add b b' _ _ h h' => simp only [tmul_add, map_add, h, h', smul_add]
      | smul r b _ h => simp only [tmul_smul, map_smul, h, smul_comm r]
      | mem _ hb =>
        obtain ⟨w, rfl⟩ := hb
        have hswap : LinearEquiv.prodComm K U W ∘
            Fin.append (LinearMap.inl K U W ∘ u) (LinearMap.inr K U W ∘ w) =
              Fin.append (LinearMap.inr K W U ∘ u) (LinearMap.inl K W U ∘ w) := by
          funext i
          induction i using Fin.addCases <;> simp
        -- Exchange the two blocks of the wedge product in the exterior algebra of `W × U`.
        refine Subtype.ext ?_
        rw [LinearEquiv.coe_detLineCongr, coe_detLineProdEquiv_tmul, comm_tmul,
          Submodule.coe_smul, coe_detLineProdEquiv_tmul, ExteriorAlgebra.map_apply_ιMulti,
          LinearEquiv.coe_toLinearMap, hswap, ← ExteriorAlgebra.ιMulti_mul_ιMulti,
          ← ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm,
          Units.smul_def, ← Int.cast_smul_eq_zsmul K]
        push_cast
        rw [mul_comm (finrank K W)]

/-- **`TauCeti.detLineProdEquiv` is the exterior product.** In the exterior algebra of `U × W`, the
image of `a ⊗ b` is the product of the images of `a` and `b` under the inclusions of `U` and
`W`. -/
theorem coe_detLineProdEquiv_tmul_eq_mul (a : detLine K U) (b : detLine K W) :
    (detLineProdEquiv K U W (a ⊗ₜ b) : ExteriorAlgebra K (U × W)) =
      ExteriorAlgebra.map (LinearMap.inl K U W) a *
        ExteriorAlgebra.map (LinearMap.inr K U W) b := by
  -- Both sides are bilinear in `(a, b)`; compare them on exterior products.
  have h : (TensorProduct.mk K _ _).compr₂
      ((Submodule.subtype _) ∘ₗ (detLineProdEquiv K U W).toLinearMap) =
      (LinearMap.mul K (ExteriorAlgebra K (U × W))).compl₁₂
        ((ExteriorAlgebra.map (LinearMap.inl K U W)).toLinearMap ∘ₗ Submodule.subtype _)
        ((ExteriorAlgebra.map (LinearMap.inr K U W)).toLinearMap ∘ₗ Submodule.subtype _) := by
    ext u w
    simp [ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti]
  exact congrArg (fun φ ↦ φ a b) h

/-- **Naturality of `TauCeti.detLineProdEquiv`.** For isomorphisms `e₁ : U ≃ U'` and
`e₂ : W ≃ W'`, the isomorphism `det (U × W) ≃ det (U' × W')` induced by `e₁ × e₂` takes
`detLineProdEquiv K U W t` to `detLineProdEquiv K U' W'` of the image of `t` under
`det e₁ ⊗ det e₂`. -/
theorem detLineCongr_prodCongr_detLineProdEquiv {U' W' : Type*} [AddCommGroup U'] [Module K U']
    [AddCommGroup W'] [Module K W'] [FiniteDimensional K U'] [FiniteDimensional K W']
    (e₁ : U ≃ₗ[K] U') (e₂ : W ≃ₗ[K] W') (t : detLine K U ⊗[K] detLine K W) :
    (e₁.prodCongr e₂).detLineCongr (detLineProdEquiv K U W t) =
      detLineProdEquiv K U' W' (TensorProduct.congr e₁.detLineCongr e₂.detLineCongr t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    refine Subtype.ext ?_
    have h₁ : (e₁.prodCongr e₂).toLinearMap ∘ₗ LinearMap.inl K U W =
        LinearMap.inl K U' W' ∘ₗ e₁.toLinearMap := by ext <;> simp
    have h₂ : (e₁.prodCongr e₂).toLinearMap ∘ₗ LinearMap.inr K U W =
        LinearMap.inr K U' W' ∘ₗ e₂.toLinearMap := by ext <;> simp
    simp only [LinearEquiv.coe_detLineCongr, coe_detLineProdEquiv_tmul_eq_mul, congr_tmul,
      map_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h₁, h₂]

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Associativity of `TauCeti.detLineProdEquiv`.** The two ways of identifying
`(det U ⊗ det V) ⊗ det W` with the determinant line of a product of three spaces agree under the
associator `(U × V) × W ≃ U × (V × W)`: both send `(a ⊗ b) ⊗ c` to the exterior product of the
images of `a`, `b` and `c`. Unlike the exchange of two factors
(`TauCeti.detLineCongr_prodComm_detLineProdEquiv`), this involves no sign. -/
theorem detLineCongr_prodAssoc_detLineProdEquiv
    (t : (detLine K U ⊗[K] detLine K V) ⊗[K] detLine K W) :
    (LinearEquiv.prodAssoc K U V W).detLineCongr
        (detLineProdEquiv K (U × V) W ((detLineProdEquiv K U V).toLinearMap.rTensor _ t)) =
      detLineProdEquiv K U (V × W)
        ((detLineProdEquiv K V W).toLinearMap.lTensor _ (TensorProduct.assoc K _ _ _ t)) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul ab c =>
    induction ab using TensorProduct.inductionOn with
    | add s t hs ht => simp only [add_tmul, map_add, hs, ht]
    | tmul a b =>
      refine Subtype.ext ?_
      have h₁ : (LinearEquiv.prodAssoc K U V W).toLinearMap ∘ₗ LinearMap.inl K (U × V) W ∘ₗ
          LinearMap.inl K U V = LinearMap.inl K U (V × W) := by ext <;> simp
      have h₂ : (LinearEquiv.prodAssoc K U V W).toLinearMap ∘ₗ LinearMap.inl K (U × V) W ∘ₗ
          LinearMap.inr K U V = LinearMap.inr K U (V × W) ∘ₗ LinearMap.inl K V W := by
        ext <;> simp
      have h₃ : (LinearEquiv.prodAssoc K U V W).toLinearMap ∘ₗ LinearMap.inr K (U × V) W =
          LinearMap.inr K U (V × W) ∘ₗ LinearMap.inr K V W := by ext <;> simp
      simp only [LinearEquiv.coe_detLineCongr, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        assoc_tmul, LinearEquiv.coe_coe, coe_detLineProdEquiv_tmul_eq_mul, map_mul,
        ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h₁, h₂, h₃, mul_assoc]

/-- Associativity of `TauCeti.detLineProdEquiv` transported along splittings `X ≃ U × V`,
`X' ≃ V × W`, `Y ≃ X × W` and `Z ≃ U × X'`, for an isomorphism `e : Y ≃ Z` compatible with
them. -/
private theorem detLineCongr_detLineProdEquiv_assoc_of_equiv {X X' Y Z : Type*} [AddCommGroup X]
    [Module K X] [AddCommGroup X'] [Module K X'] [AddCommGroup Y] [Module K Y] [AddCommGroup Z]
    [Module K Z] [FiniteDimensional K X] [FiniteDimensional K X'] (κ₁ : X ≃ₗ[K] U × V)
    (κ₂ : X' ≃ₗ[K] V × W) (κ₃ : Y ≃ₗ[K] X × W) (κ₄ : Z ≃ₗ[K] U × X') (e : Y ≃ₗ[K] Z)
    (he : ∀ u v w, e (κ₃.symm (κ₁.symm (u, v), w)) = κ₄.symm (u, κ₂.symm (v, w)))
    (t : (detLine K U ⊗[K] detLine K V) ⊗[K] detLine K W) :
    e.detLineCongr (κ₃.symm.detLineCongr (detLineProdEquiv K X W
        (((detLineProdEquiv K U V).trans κ₁.symm.detLineCongr).toLinearMap.rTensor _ t))) =
      κ₄.symm.detLineCongr (detLineProdEquiv K U X'
        (((detLineProdEquiv K V W).trans κ₂.symm.detLineCongr).toLinearMap.lTensor _
          (TensorProduct.assoc K _ _ _ t))) := by
  have h : (LinearEquiv.prodAssoc K U V W).symm.trans ((κ₁.symm.prodCongr (.refl K W)).trans
      (κ₃.symm.trans e)) = ((LinearEquiv.refl K U).prodCongr κ₂.symm).trans κ₄.symm := by
    ext ⟨u, v, w⟩ : 1
    exact he u v w
  -- Move `κ₁` and `κ₂` out of the tensor products by naturality, then reassociate.
  have hX (s : detLine K (U × V) ⊗[K] detLine K W) :
      detLineProdEquiv K X W (κ₁.symm.detLineCongr.toLinearMap.rTensor _ s) =
        (κ₁.symm.prodCongr (.refl K W)).detLineCongr (detLineProdEquiv K _ W s) := by
    rw [detLineCongr_prodCongr_detLineProdEquiv, LinearEquiv.detLineCongr_refl]
    rfl
  have hX' (s : detLine K U ⊗[K] detLine K (V × W)) :
      detLineProdEquiv K U X' (κ₂.symm.detLineCongr.toLinearMap.lTensor _ s) =
        ((LinearEquiv.refl K U).prodCongr κ₂.symm).detLineCongr (detLineProdEquiv K U _ s) := by
    rw [detLineCongr_prodCongr_detLineProdEquiv, LinearEquiv.detLineCongr_refl]
    rfl
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.rTensor_comp_apply,
    LinearMap.lTensor_comp_apply, hX, hX', ← detLineCongr_prodAssoc_detLineProdEquiv]
  simpa only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply,
    ← LinearEquiv.detLineCongr_symm, LinearEquiv.symm_apply_apply] using
    congr($(congrArg LinearEquiv.detLineCongr h)
      ((LinearEquiv.prodAssoc K U V W).detLineCongr (detLineProdEquiv K (U × V) W
        ((detLineProdEquiv K U V).toLinearMap.rTensor _ t))))

end Prod

end TauCeti

namespace LinearMap

open TauCeti

variable {K : Type*} [Field K] {M N M' N' : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
  (f : M →ₗ[K] N) (g : M' →ₗ[K] N')

variable {M'' N'' : Type*} [AddCommGroup M''] [Module K M''] [AddCommGroup N''] [Module K N'']
  (k : M'' →ₗ[K] N'')

/-- The kernel of `f.prodMap g` is `ker f × ker g`. -/
private def kerProdMapEquiv : ker (f.prodMap g) ≃ₗ[K] ker f × ker g :=
  (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv _ _)

@[simp]
private theorem coe_kerProdMapEquiv_symm_apply (x : ker f × ker g) :
    ((kerProdMapEquiv f g).symm x : M × M') = ((x.1 : M), (x.2 : M')) := (rfl)

/-- The cokernel of `f.prodMap g` is the product of the cokernels of `f` and `g`. -/
private def cokerProdMapEquiv :
    ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] (N ⧸ range f) × (N' ⧸ range g) :=
  (Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans (Submodule.quotientProdEquiv _ _)

@[simp]
private theorem cokerProdMapEquiv_mk (x : N × N') :
    cokerProdMapEquiv f g (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := by
  simp [cokerProdMapEquiv]

@[simp]
private theorem cokerProdMapEquiv_symm_mk (y : N) (y' : N') :
    (cokerProdMapEquiv f g).symm (Submodule.Quotient.mk y, Submodule.Quotient.mk y') =
      Submodule.Quotient.mk (y, y') := by
  simp [cokerProdMapEquiv, LinearEquiv.symm_apply_eq]

section Kernel

variable [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]

/-- The determinant line of the kernel of `f.prodMap g` is `det (ker f) ⊗ det (ker g)`, through
`ker (f.prodMap g) = ker f × ker g`. -/
private def detLineKerProdMap :
    TauCeti.detLine K (ker (f.prodMap g)) ≃ₗ[K]
      TauCeti.detLine K (ker f) ⊗[K] TauCeti.detLine K (ker g) :=
  (kerProdMapEquiv f g).detLineCongr.trans (detLineProdEquiv K _ _).symm

/-- `detLineKerProdMap` sends the wedge product of the vectors `(uᵢ, 0)` followed by the vectors
`(0, wⱼ)` to `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_b)`. -/
private theorem detLineKerProdMap_apply (u : Fin (finrank K (ker f)) → ker f)
    (w : Fin (finrank K (ker g)) → ker g) {β : TauCeti.detLine K (ker (f.prodMap g))}
    (hβ : (β : ExteriorAlgebra K (ker (f.prodMap g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (fun i ↦ ⟨(u i, 0), by simp⟩) fun j ↦ ⟨(0, w j), by simp⟩)) :
    detLineKerProdMap f g β = exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w := by
  rw [detLineKerProdMap, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [LinearEquiv.coe_detLineCongr, hβ, ExteriorAlgebra.map_apply_ιMulti,
    coe_detLineProdEquiv_tmul]
  congr 1
  funext i
  induction i using Fin.addCases <;> ext <;> simp [kerProdMapEquiv]

/-- Exchanging the summands of the kernel: if `e : ker (f.prodMap g) ≃ ker (g.prodMap f)` swaps the
two components, the kernel factors are exchanged with the sign `(-1) ^ (dim ker f * dim ker g)`. -/
private theorem detLineKerProdMap_detLineCongr (e : ker (f.prodMap g) ≃ₗ[K] ker (g.prodMap f))
    (he : ∀ x, (e x : M' × M) = (x : M × M').swap) (β : TauCeti.detLine K (ker (f.prodMap g))) :
    detLineKerProdMap g f (e.detLineCongr β) =
      (-1 : K) ^ (finrank K (ker f) * finrank K (ker g)) •
        TensorProduct.comm K _ _ (detLineKerProdMap f g β) := by
  obtain ⟨t, rfl⟩ := (detLineKerProdMap f g).symm.surjective β
  -- Unfold both kernel isomorphisms and cancel the inverses.
  rw [LinearEquiv.apply_symm_apply]
  simp only [detLineKerProdMap, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm, LinearEquiv.symm_apply_eq]
  -- Read through the kernel splittings, the exchange `e` is the swap of `ker f × ker g`.
  have hswap : (kerProdMapEquiv f g).symm.trans (e.trans (kerProdMapEquiv g f)) =
      LinearEquiv.prodComm K (ker f) (ker g) := by
    ext x <;> simp [kerProdMapEquiv, he]
  rw [map_smul, ← detLineCongr_prodComm_detLineProdEquiv, ← hswap]
  simp only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply]

variable [FiniteDimensional K (ker k)]

/-- Reassociating the kernel of a triple direct sum: if
`e : ker ((f.prodMap g).prodMap k) ≃ ker (f.prodMap (g.prodMap k))` is the associator, the inverses
of the kernel isomorphisms are compatible with the associator of the tensor products. -/
private theorem detLineCongr_detLineKerProdMap_symm_assoc
    (e : ker ((f.prodMap g).prodMap k) ≃ₗ[K] ker (f.prodMap (g.prodMap k)))
    (he : ∀ x, (e x : M × M' × M'') = LinearEquiv.prodAssoc K M M' M'' x)
    (s : (TauCeti.detLine K (ker f) ⊗[K] TauCeti.detLine K (ker g)) ⊗[K]
      TauCeti.detLine K (ker k)) :
    e.detLineCongr ((detLineKerProdMap (f.prodMap g) k).symm
        ((detLineKerProdMap f g).symm.toLinearMap.rTensor _ s)) =
      (detLineKerProdMap f (g.prodMap k)).symm
        ((detLineKerProdMap g k).symm.toLinearMap.lTensor _ (TensorProduct.assoc K _ _ _ s)) := by
  simp only [detLineKerProdMap, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.detLineCongr_symm, LinearEquiv.trans_apply]
  exact detLineCongr_detLineProdEquiv_assoc_of_equiv _ _ _ _ e
    (fun _ _ _ ↦ Subtype.ext (by simp [he])) s

/-- The kernel isomorphisms of a triple direct sum are compatible with the associators. -/
private theorem assoc_rTensor_detLineKerProdMap
    (e : ker ((f.prodMap g).prodMap k) ≃ₗ[K] ker (f.prodMap (g.prodMap k)))
    (he : ∀ x, (e x : M × M' × M'') = LinearEquiv.prodAssoc K M M' M'' x)
    (β : TauCeti.detLine K (ker ((f.prodMap g).prodMap k))) :
    TensorProduct.assoc K _ _ _ ((detLineKerProdMap f g).toLinearMap.rTensor _
        (detLineKerProdMap (f.prodMap g) k β)) =
      (detLineKerProdMap g k).toLinearMap.lTensor _
        (detLineKerProdMap f (g.prodMap k) (e.detLineCongr β)) := by
  have h := detLineCongr_detLineKerProdMap_symm_assoc f g k e he
    ((detLineKerProdMap f g).toLinearMap.rTensor _ (detLineKerProdMap (f.prodMap g) k β))
  rw [← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp, LinearMap.rTensor_id,
    LinearMap.id_apply, LinearEquiv.symm_apply_apply] at h
  simp only [h, LinearEquiv.apply_symm_apply, ← LinearMap.lTensor_comp_apply, LinearEquiv.comp_symm,
    LinearMap.lTensor_id, LinearMap.id_apply]

end Kernel

section Cokernel

variable [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)]

/-- The determinant line of the cokernel of `f.prodMap g` is `det (coker f) ⊗ det (coker g)`,
through `coker (f.prodMap g) = coker f × coker g`. -/
private def detLineCokerProdMap :
    TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g) ≃ₗ[K]
      TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)) :=
  (detLineProdEquiv K _ _).trans (cokerProdMapEquiv f g).detLineCongr.symm

/-- `detLineCokerProdMap` sends `[y₁] ∧ ⋯ ∧ [yₐ] ⊗ [y'₁] ∧ ⋯ ∧ [y'_b]` to the wedge product of the
classes of `(yᵢ, 0)` followed by those of `(0, y'ⱼ)`. -/
private theorem coe_detLineCokerProdMap_tmul (y : Fin (finrank K (N ⧸ range f)) → N)
    (y' : Fin (finrank K (N' ⧸ range g)) → N') :
    (detLineCokerProdMap f g (exteriorPower.ιMulti K _ ((range f).mkQ ∘ y) ⊗ₜ
        exteriorPower.ιMulti K _ ((range g).mkQ ∘ y')) :
        ExteriorAlgebra K ((N × N') ⧸ range (f.prodMap g))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (fun i ↦ (range (f.prodMap g)).mkQ (y i, 0))
        fun j ↦ (range (f.prodMap g)).mkQ (0, y' j)) := by
  rw [detLineCokerProdMap, LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm,
    LinearEquiv.coe_detLineCongr, coe_detLineProdEquiv_tmul, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext i
  induction i using Fin.addCases <;> simp [LinearEquiv.symm_apply_eq]

/-- Exchanging the summands of the cokernel: if
`e : coker (f.prodMap g) ≃ coker (g.prodMap f)` swaps the two components, the cokernel factors
are exchanged with the sign `(-1) ^ (dim coker f * dim coker g)`. -/
private theorem detLineCongr_detLineCokerProdMap
    (e : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((N' × N) ⧸ range (g.prodMap f)))
    (he : ∀ x, e ((range (f.prodMap g)).mkQ x) = (range (g.prodMap f)).mkQ x.swap)
    (t : TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g)) :
    e.detLineCongr (detLineCokerProdMap f g t) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (N' ⧸ range g)) •
        detLineCokerProdMap g f (TensorProduct.comm K _ _ t) := by
  -- Unfold both cokernel isomorphisms.
  simp only [detLineCokerProdMap, LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm]
  set κ := cokerProdMapEquiv f g
  set κ' := cokerProdMapEquiv g f
  have hκ (a : N) (b : N') : κ.symm ((range f).mkQ a, (range g).mkQ b) =
      (range (f.prodMap g)).mkQ (a, b) :=
    cokerProdMapEquiv_symm_mk f g a b
  have hκ' (a : N') (b : N) : κ'.symm ((range g).mkQ a, (range f).mkQ b) =
      (range (g.prodMap f)).mkQ (a, b) :=
    cokerProdMapEquiv_symm_mk g f a b
  -- Read through `κ` and `κ'`, the exchange `e` is the swap of `coker f × coker g`.
  have hswap : κ.symm.trans e =
      (LinearEquiv.prodComm K (N ⧸ range f) (N' ⧸ range g)).trans κ'.symm := by
    ext ⟨a, b⟩
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodComm_apply, Prod.swap_prod_mk]
    rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hκ, he, hκ', Prod.swap_prod_mk]
  rw [← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans, hswap]
  simp only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply,
    detLineCongr_prodComm_detLineProdEquiv, map_smul]

/-- The dual of `detLineCokerProdMap` under an exchange `e` of the summands of the cokernel. -/
private theorem dualDistribEquiv_symm_dualMap_detLineCokerProdMap
    (e : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((N' × N) ⧸ range (g.prodMap f)))
    (he : ∀ x, e ((range (f.prodMap g)).mkQ x) = (range (g.prodMap f)).mkQ x.swap)
    (φ : Dual K (TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)))) :
    (dualDistribEquiv K _ _).symm
        ((detLineCokerProdMap g f).dualMap (φ ∘ₗ e.detLineCongr.symm.toLinearMap)) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (N' ⧸ range g)) •
        TensorProduct.comm K _ _
          ((dualDistribEquiv K _ _).symm ((detLineCokerProdMap f g).dualMap φ)) := by
  rw [LinearEquiv.symm_apply_eq, map_smul]
  refine LinearMap.ext fun t ↦ ?_
  have h := detLineCongr_detLineCokerProdMap f g e he ((TensorProduct.comm K _ _).symm t)
  rw [LinearEquiv.apply_symm_apply, TensorProduct.comm_symm] at h
  have h' : e.detLineCongr.symm (detLineCokerProdMap g f t) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (N' ⧸ range g)) •
        detLineCokerProdMap f g (TensorProduct.comm K _ _ t) := by
    rw [LinearEquiv.symm_apply_eq, map_smul, h, smul_smul, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_smul]
  -- `dualDistribEquiv` commutes with exchanging the tensor factors (`dualDistrib_apply_comm`).
  have hdd (ψ : Dual K (TauCeti.detLine K (N ⧸ range f)) ⊗[K]
      Dual K (TauCeti.detLine K (N' ⧸ range g)))
      (s : TauCeti.detLine K (N' ⧸ range g) ⊗[K] TauCeti.detLine K (N ⧸ range f)) :
      dualDistribEquiv K _ _ (TensorProduct.comm K _ _ ψ) s =
        dualDistribEquiv K _ _ ψ (TensorProduct.comm K _ _ s) := by
    rw [← LinearEquiv.coe_coe (dualDistribEquiv K _ _),
      ← LinearEquiv.coe_coe (dualDistribEquiv K _ _), toLinearMap_dualDistribEquiv,
      toLinearMap_dualDistribEquiv, TensorProduct.dualDistrib_apply_comm]
  simp only [LinearEquiv.dualMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h', map_smul,
    LinearMap.smul_apply, hdd, LinearEquiv.apply_symm_apply]

variable [FiniteDimensional K (N'' ⧸ range k)]

/-- Reassociating the cokernel of a triple direct sum: if
`e : coker ((f.prodMap g).prodMap k) ≃ coker (f.prodMap (g.prodMap k))` is induced by the
associator, the cokernel isomorphisms are compatible with the associator of the tensor products. -/
private theorem detLineCongr_detLineCokerProdMap_assoc
    (e : (((N × N') × N'') ⧸ range ((f.prodMap g).prodMap k)) ≃ₗ[K]
      ((N × N' × N'') ⧸ range (f.prodMap (g.prodMap k))))
    (he : ∀ x, e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (LinearEquiv.prodAssoc K N N' N'' x))
    (s : (TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g)) ⊗[K]
      TauCeti.detLine K (N'' ⧸ range k)) :
    e.detLineCongr (detLineCokerProdMap (f.prodMap g) k
        ((detLineCokerProdMap f g).toLinearMap.rTensor _ s)) =
      detLineCokerProdMap f (g.prodMap k)
        ((detLineCokerProdMap g k).toLinearMap.lTensor _ (TensorProduct.assoc K _ _ _ s)) := by
  simp only [detLineCokerProdMap, LinearEquiv.detLineCongr_symm, LinearEquiv.trans_apply]
  refine detLineCongr_detLineProdEquiv_assoc_of_equiv _ _ _ _ e (fun a b c ↦ ?_) s
  induction a using Submodule.Quotient.induction_on
  induction b using Submodule.Quotient.induction_on
  induction c using Submodule.Quotient.induction_on
  simp [he]

/-- The dual cokernel isomorphisms of a triple direct sum are compatible with the associators. -/
private theorem assoc_rTensor_dualDistribEquiv_symm_dualMap_detLineCokerProdMap
    (e : (((N × N') × N'') ⧸ range ((f.prodMap g).prodMap k)) ≃ₗ[K]
      ((N × N' × N'') ⧸ range (f.prodMap (g.prodMap k))))
    (he : ∀ x, e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (LinearEquiv.prodAssoc K N N' N'' x))
    (φ : Dual K (TauCeti.detLine K (((N × N') × N'') ⧸ range ((f.prodMap g).prodMap k)))) :
    TensorProduct.assoc K _ _ _
        (((detLineCokerProdMap f g).dualMap.trans
            (dualDistribEquiv K _ _).symm).toLinearMap.rTensor _
          ((dualDistribEquiv K _ _).symm ((detLineCokerProdMap (f.prodMap g) k).dualMap φ))) =
      ((detLineCokerProdMap g k).dualMap.trans (dualDistribEquiv K _ _).symm).toLinearMap.lTensor _
        ((dualDistribEquiv K _ _).symm ((detLineCokerProdMap f (g.prodMap k)).dualMap
          (φ ∘ₗ e.detLineCongr.symm.toLinearMap))) := by
  -- Both sides are the values at `φ` of isomorphisms. Compare their inverses on pure tensors
  -- `d₁ ⊗ (d₂ ⊗ d₃)`, evaluated on the images of pure tensors of the three cokernel lines.
  have H : (((detLineCokerProdMap (f.prodMap g) k).dualMap.trans
        (dualDistribEquiv K _ _).symm).trans
        (((detLineCokerProdMap f g).dualMap.trans (dualDistribEquiv K _ _).symm).rTensor _)).trans
        (TensorProduct.assoc K _ _ _) =
      (e.detLineCongr.symm.dualMap.trans
        ((detLineCokerProdMap f (g.prodMap k)).dualMap.trans (dualDistribEquiv K _ _).symm)).trans
        (((detLineCokerProdMap g k).dualMap.trans (dualDistribEquiv K _ _).symm).lTensor _) := by
    refine LinearEquiv.symm_bijective.injective (LinearEquiv.toLinearMap_injective
      (TensorProduct.ext_threefold' fun d₁ d₂ d₃ ↦ LinearMap.ext fun x ↦ ?_))
    obtain ⟨s, rfl⟩ := (((detLineCokerProdMap f g).rTensor _).trans
      (detLineCokerProdMap (f.prodMap g) k)).surjective x
    induction s using TensorProduct.inductionOn with
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul ab c =>
      induction ab using TensorProduct.inductionOn with
      | add s t hs ht => simp only [add_tmul, map_add, hs, ht]
      | tmul a b =>
        have hx := detLineCongr_detLineCokerProdMap_assoc f g k e he ((a ⊗ₜ b) ⊗ₜ c)
        simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, assoc_tmul,
          LinearEquiv.coe_coe] at hx
        -- Both sides evaluate to the product of `d₁ a`, `d₂ b` and `d₃ c`, in different orders.
        simp only [LinearEquiv.trans_symm, LinearEquiv.symm_rTensor, LinearEquiv.symm_symm,
          LinearEquiv.dualMap_symm, LinearEquiv.coe_coe, LinearEquiv.trans_apply, assoc_symm_tmul,
          LinearEquiv.rTensor_tmul, LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply,
          dualDistribEquiv_tmul_tmul, LinearEquiv.detLineCongr_symm, LinearEquiv.symm_lTensor,
          LinearEquiv.lTensor_tmul, hx]
        ring
  have hφ : e.detLineCongr.symm.dualMap φ = φ ∘ₗ e.detLineCongr.symm.toLinearMap :=
    LinearMap.ext fun _ ↦ LinearEquiv.dualMap_apply _ _ _
  have := congr($H φ)
  simp only [LinearEquiv.trans_apply, hφ] at this
  exact this

end Cokernel

variable [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]
  [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)]

/-- **The determinant line of a direct sum.** For linear maps `f : M → N` and `g : M' → N'`
with finite-dimensional kernels and cokernels, the isomorphism
`det (f.prodMap g) ≃ det f ⊗ det g` of determinant lines
`det f = det (ker f) ⊗ (det (coker f))^*`. It is assembled from
`ker (f.prodMap g) = ker f × ker g`, `coker (f.prodMap g) = coker f × coker g` and
`TauCeti.detLineProdEquiv`, and carries the Koszul sign `(-1) ^ (dim (coker f) * dim (ker g))` of
moving `(det (coker f))^*` past `det (ker g)`. Its value is `LinearMap.detLineProdMapEquiv_tmul`,
and exchanging `f` and `g` costs `(-1) ^ (ind f * ind g)`
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`). -/
def detLineProdMapEquiv : (f.prodMap g).detLine ≃ₗ[K] f.detLine ⊗[K] g.detLine :=
  TensorProduct.congr
      ((LinearEquiv.smulOfNeZero K _ ((-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)))
          (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))).trans (detLineKerProdMap f g))
      ((detLineCokerProdMap f g).dualMap.trans (dualDistribEquiv K _ _).symm) ≪≫ₗ
    TensorProduct.tensorTensorTensorComm K _ _ _ _

/-- **The value of `LinearMap.detLineProdMapEquiv` on exterior products.** Let `u` and `w` be
families of `dim (ker f)` and `dim (ker g)` kernel vectors, and `y`, `y'` families of
`dim (coker f)` and `dim (coker g)` vectors of `N` and `N'`. Let `β` be the exterior product of the
kernel vectors `(uᵢ, 0)` followed by `(0, wⱼ)` of `f.prodMap g`, and `γ` the exterior product of
the classes of `(yᵢ, 0)` followed by `(0, y'ⱼ)` in its cokernel. Pairing the dual factors of the
image of `β ⊗ φ` with the exterior products of the classes of `y` and of `y'` gives
`(-1) ^ (dim (coker f) * dim (ker g)) * φ γ` times `(u₁ ∧ ⋯) ⊗ (w₁ ∧ ⋯)`. When the classes of `y`
and `y'` are bases of the cokernels their exterior products span the cokernel lines, so this
determines the image. -/
theorem detLineProdMapEquiv_tmul (u : Fin (finrank K (ker f)) → ker f)
    (w : Fin (finrank K (ker g)) → ker g) (y : Fin (finrank K (N ⧸ range f)) → N)
    (y' : Fin (finrank K (N' ⧸ range g)) → N') {β : TauCeti.detLine K (ker (f.prodMap g))}
    (hβ : (β : ExteriorAlgebra K (ker (f.prodMap g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (fun i ↦ ⟨(u i, 0), by simp⟩) fun j ↦ ⟨(0, w j), by simp⟩))
    {γ : TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g))}
    (hγ : (γ : ExteriorAlgebra K ((N × N') ⧸ range (f.prodMap g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (fun i ↦ (range (f.prodMap g)).mkQ (y i, 0))
        fun j ↦ (range (f.prodMap g)).mkQ (0, y' j)))
    (φ : Dual K (TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)))) :
    TensorProduct.map
        ((TensorProduct.rid K (TauCeti.detLine K (ker f))).toLinearMap ∘ₗ
          (Dual.eval K _ (exteriorPower.ιMulti K _ ((range f).mkQ ∘ y))).lTensor _)
        ((TensorProduct.rid K (TauCeti.detLine K (ker g))).toLinearMap ∘ₗ
          (Dual.eval K _ (exteriorPower.ιMulti K _ ((range g).mkQ ∘ y'))).lTensor _)
        (detLineProdMapEquiv f g (β ⊗ₜ φ)) =
      ((-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) * φ γ) •
        (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w) := by
  have hγ' : detLineCokerProdMap f g (exteriorPower.ιMulti K _ ((range f).mkQ ∘ y) ⊗ₜ
      exteriorPower.ιMulti K _ ((range g).mkQ ∘ y')) = γ :=
    Subtype.ext (by rw [coe_detLineCokerProdMap_tmul, hγ])
  simp only [detLineProdMapEquiv, LinearEquiv.trans_apply, congr_tmul,
    LinearEquiv.smulOfNeZero_apply, map_smul, detLineKerProdMap_apply f g u w hβ, smul_tmul',
    map_lTensor_eval_tensorTensorTensorComm_tmul, ← toLinearMap_dualDistribEquiv,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply, hγ', smul_smul]
  rw [mul_comm]

/-- **Exchanging the summands of a direct sum** multiplies `LinearMap.detLineProdMapEquiv` by
`(-1) ^ (ind f * ind g)`. The swaps `M × M' ≃ M' × M` and `N × N' ≃ N' × N` carry `f.prodMap g`
to `g.prodMap f`, and so induce `det (f.prodMap g) ≃ det (g.prodMap f)`
(`LinearMap.detLineCongr`); followed by `detLineProdMapEquiv g f`, this is
`detLineProdMapEquiv f g` followed by the exchange of the tensor factors, up to the sign
`(-1) ^ ((dim ker f + dim coker f) * (dim ker g + dim coker g))`, whose parity is that of
`ind f * ind g`. -/
theorem detLineProdMapEquiv_detLineCongr_prodComm (x : (f.prodMap g).detLine) :
    detLineProdMapEquiv g f ((f.prodMap g).detLineCongr (LinearEquiv.prodComm K M M')
        (LinearEquiv.prodComm K N N') (by ext <;> simp) x) =
      (-1 : K) ^ ((finrank K (ker f) + finrank K (N ⧸ range f)) *
          (finrank K (ker g) + finrank K (N' ⧸ range g))) •
        TensorProduct.comm K _ _ (detLineProdMapEquiv f g x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' h h' => simp only [map_add, h, h', smul_add]
  | tmul β φ =>
    rw [detLineCongr_tmul]
    simp only [detLineProdMapEquiv, LinearEquiv.trans_apply, congr_tmul,
      LinearEquiv.smulOfNeZero_apply, map_smul]
    have hsq : (g.prodMap f) ∘ₗ (LinearEquiv.prodComm K M M').toLinearMap =
        (LinearEquiv.prodComm K N N').toLinearMap ∘ₗ f.prodMap g := by
      ext <;> simp
    have hK := detLineKerProdMap_detLineCongr f g ((LinearEquiv.prodComm K M M').ofSubmodules _ _
      ((f.prodMap g).map_ker_eq_ker_of_comp_eq (LinearEquiv.prodComm K M M').surjective
        (LinearEquiv.prodComm K N N').injective hsq)) (fun x ↦ by simp) β
    have hC := dualDistribEquiv_symm_dualMap_detLineCokerProdMap f g
      (Submodule.Quotient.equiv _ _ (LinearEquiv.prodComm K N N')
        ((f.prodMap g).map_range_eq_range_of_comp_eq (LinearEquiv.prodComm K M M').surjective hsq))
      (fun x ↦ by simp) φ
    simp only [hK, hC, ← smul_tmul', tmul_smul, map_smul,
      tensorTensorTensorComm_comm_tmul_comm, smul_smul]
    congr 1
    -- The two signs differ by `(-1) ^ (2 * (dim coker f * dim ker g))`.
    rw [← pow_add, ← pow_add, ← pow_add, show ∀ a b c d : ℕ,
        (a + b) * (c + d) + b * c = b * d + (d * a + a * c) + 2 * (b * c) by intros; ring,
      pow_add (-1 : K) _ (2 * _), pow_mul (-1 : K) 2, neg_one_sq, one_pow, mul_one]

section Assoc

variable [FiniteDimensional K (ker k)] [FiniteDimensional K (N'' ⧸ range k)]

/-- Multiplication by a nonzero scalar `c`, as a linear map, is `c • id`. -/
private theorem toLinearMap_smulOfNeZero {V : Type*} [AddCommGroup V] [Module K V] (c : K)
    (hc : c ≠ 0) : (LinearEquiv.smulOfNeZero K V c hc).toLinearMap = c • LinearMap.id :=
  LinearMap.ext fun _ ↦ LinearEquiv.smulOfNeZero_apply _ _ _ _ _

/-- **Associativity of the direct sum isomorphism of determinant lines.** For linear maps `f`, `g`
and `k` with finite-dimensional kernels and cokernels, the two ways of splitting the determinant
line of a triple direct sum into `det f ⊗ det g ⊗ det k` agree: the associators
`(M × M') × M'' ≃ M × (M' × M'')` and `(N × N') × N'' ≃ N × (N' × N'')` carry
`(f.prodMap g).prodMap k` to `f.prodMap (g.prodMap k)` and so induce
`det ((f.prodMap g).prodMap k) ≃ det (f.prodMap (g.prodMap k))` (`LinearMap.detLineCongr`);
followed by `LinearMap.detLineProdMapEquiv` twice, this is `LinearMap.detLineProdMapEquiv` applied
twice the other way round, followed by the associator of the tensor products. There is no sign:
both sides carry the Koszul sign
`(-1) ^ (dim coker f * dim ker g + dim coker f * dim ker k + dim coker g * dim ker k)` of moving
each cokernel factor past the kernel factors to its right. -/
theorem detLineProdMapEquiv_detLineCongr_prodAssoc (x : ((f.prodMap g).prodMap k).detLine) :
    (detLineProdMapEquiv g k).toLinearMap.lTensor _ (detLineProdMapEquiv f (g.prodMap k)
        (((f.prodMap g).prodMap k).detLineCongr (g := f.prodMap (g.prodMap k))
          (LinearEquiv.prodAssoc K M M' M'') (LinearEquiv.prodAssoc K N N' N'') (by ext <;> simp)
          x)) =
      TensorProduct.assoc K _ _ _ ((detLineProdMapEquiv f g).toLinearMap.rTensor _
        (detLineProdMapEquiv (f.prodMap g) k x)) := by
  induction x using TensorProduct.inductionOn with
  | add x x' h h' => simp only [LinearEquiv.map_add, LinearMap.map_add, h, h']
  | tmul β φ =>
    have hsq : (f.prodMap (g.prodMap k)) ∘ₗ (LinearEquiv.prodAssoc K M M' M'').toLinearMap =
        (LinearEquiv.prodAssoc K N N' N'').toLinearMap ∘ₗ (f.prodMap g).prodMap k := by
      ext <;> simp
    have hK := assoc_rTensor_detLineKerProdMap f g k
      ((LinearEquiv.prodAssoc K M M' M'').ofSubmodules _ _
        (((f.prodMap g).prodMap k).map_ker_eq_ker_of_comp_eq
          (LinearEquiv.prodAssoc K M M' M'').surjective
          (LinearEquiv.prodAssoc K N N' N'').injective hsq)) (fun x ↦ by simp) β
    have hC := assoc_rTensor_dualDistribEquiv_symm_dualMap_detLineCokerProdMap f g k
      (Submodule.Quotient.equiv _ _ (LinearEquiv.prodAssoc K N N' N'')
        (((f.prodMap g).prodMap k).map_range_eq_range_of_comp_eq
          (LinearEquiv.prodAssoc K M M' M'').surjective hsq)) (fun x ↦ by simp) φ
    simp only [detLineCongr_tmul, detLineProdMapEquiv, LinearEquiv.coe_trans,
      TensorProduct.toLinearMap_congr, LinearEquiv.trans_apply, congr_tmul]
    refine (TensorProduct.assoc_rTensor_comp_map_tensorTensorTensorComm_tmul ?_ hC).symm
    -- The kernel factors: `hK` up to the Koszul signs, which agree on both sides.
    simp only [toLinearMap_smulOfNeZero, LinearMap.comp_smul, LinearMap.comp_id,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, LinearMap.smul_apply,
      LinearEquiv.smulOfNeZero_apply, map_smul, hK, smul_smul]
    rw [← pow_add, ← pow_add]
    congr 2
    rw [finrank_quotient_range_prodMap, finrank_ker_prodMap]
    ring

end Assoc

end LinearMap
