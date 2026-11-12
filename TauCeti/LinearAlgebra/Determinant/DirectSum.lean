/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Dimension.Prod
public import TauCeti.LinearAlgebra.Quotient.Prod
import TauCeti.LinearAlgebra.Contraction
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Determinant lines of direct sums

For finite-dimensional vector spaces `U` and `W`, the short exact sequence
`0 → U → U × W → W → 0` identifies `det U ⊗ det W` with `det (U × W)`
(`TauCeti.detLineProdEquiv`), sending `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to
`(u₁, 0) ∧ ⋯ ∧ (uₐ, 0) ∧ (0, w₁) ∧ ⋯ ∧ (0, w_c)`. Exchanging the factors costs the sign
`(-1) ^ (dim U * dim W)` (`TauCeti.detLineCongr_prodComm_detLineProdEquiv`), while regrouping
the factors of a triple product costs none (`TauCeti.detLineCongr_prodAssoc_detLineProdEquiv`).
Both follow from reading the isomorphism as multiplication in the exterior algebra
(`TauCeti.coe_detLineProdEquiv_tmul_eq_map_mul_map`).

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
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`); there is no sign when one of the indices
is even (`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm_of_even`). Regrouping the summands
of `(f ⊕ g) ⊕ h` into `f ⊕ (g ⊕ h)` costs no sign
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodAssoc`): the Koszul signs of the two composite
isomorphisms with `det f ⊗ det g ⊗ det h` agree. Associativity and the exchange law together
compare the determinant line of a direct sum of finitely many operators with the tensor product of
their determinant lines under every reordering of the summands; when all indices are even, as for
the complex-linear operators attached to the components of a configuration of pseudoholomorphic
curves, no reordering introduces a sign. This is the direct-sum law through which orientations of
the determinant lines of Fredholm operators, and so of moduli spaces cut out by them, are compared
for split operators.

## Main declarations

* `TauCeti.detLineProdEquiv`: `det U ⊗ det W ≃ det (U × W)`, with its value
  `TauCeti.coe_detLineProdEquiv_tmul`.
* `TauCeti.detLineCongr_prodComm_detLineProdEquiv`: exchanging the factors costs
  `(-1) ^ (dim U * dim W)`.
* `LinearMap.detLineProdMapEquiv`: `det (f.prodMap g) ≃ det f ⊗ det g`, with its value
  `LinearMap.detLineProdMapEquiv_tmul`.
* `TauCeti.coe_detLineProdEquiv_tmul_eq_map_mul_map`: `TauCeti.detLineProdEquiv` is
  multiplication in the exterior algebra.
* `TauCeti.detLineCongr_prodAssoc_detLineProdEquiv`: regrouping the factors costs no sign.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`: exchanging the summands costs
  `(-1) ^ (ind f * ind g)`, and nothing when `ind f` is even
  (`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm_of_even`).
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodAssoc`: regrouping the summands costs no sign.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, [arXiv:1304.6368](https://arxiv.org/abs/1304.6368) (the canonical
  isomorphisms of determinant lines and their sign conventions).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  **44** (1996), 818–893 (orientations of configurations of curves from the determinant lines of
  their components).
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

/-- **`TauCeti.detLineProdEquiv` is multiplication in the exterior algebra.** The image of `a ⊗ b`
is the product of the images of `a` and `b` under the algebra maps induced by the inclusions
`U → U × W` and `W → U × W`. -/
theorem coe_detLineProdEquiv_tmul_eq_map_mul_map (a : detLine K U) (b : detLine K W) :
    (detLineProdEquiv K U W (a ⊗ₜ b) : ExteriorAlgebra K (U × W)) =
      ExteriorAlgebra.map (LinearMap.inl K U W) (a : ExteriorAlgebra K U) *
        ExteriorAlgebra.map (LinearMap.inr K U W) (b : ExteriorAlgebra K W) := by
  have key : Submodule.subtype _ ∘ₗ (detLineProdEquiv K U W).toLinearMap =
      LinearMap.mul' K (ExteriorAlgebra K (U × W)) ∘ₗ TensorProduct.map
        ((ExteriorAlgebra.map (LinearMap.inl K U W)).toLinearMap ∘ₗ Submodule.subtype _)
        ((ExteriorAlgebra.map (LinearMap.inr K U W)).toLinearMap ∘ₗ Submodule.subtype _) := by
    ext u w
    simp [ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
  simpa using congr($key (a ⊗ₜ b))

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Associativity of the determinant line of a product.** The isomorphism
`det ((U × V) × W) ≃ det (U × (V × W))` induced by `(u, v, w) ↦ (u, (v, w))` takes the image of
`(a ⊗ b) ⊗ c` under the two-step product isomorphism `(det U ⊗ det V) ⊗ det W ≃ det ((U × V) × W)`
to the image of `a ⊗ (b ⊗ c)` under `det U ⊗ (det V ⊗ det W) ≃ det (U × (V × W))`. Unlike the
exchange of factors (`TauCeti.detLineCongr_prodComm_detLineProdEquiv`), regrouping costs no
sign. -/
theorem detLineCongr_prodAssoc_detLineProdEquiv
    (t : (detLine K U ⊗[K] detLine K V) ⊗[K] detLine K W) :
    (LinearEquiv.prodAssoc K U V W).detLineCongr
        (detLineProdEquiv K (U × V) W (LinearEquiv.rTensor _ (detLineProdEquiv K U V) t)) =
      detLineProdEquiv K U (V × W)
        (LinearEquiv.lTensor _ (detLineProdEquiv K V W) (TensorProduct.assoc K _ _ _ t)) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht, map_add, map_add, map_add]
  | tmul x c =>
    induction x using TensorProduct.inductionOn with
    | add s t hs ht => rw [add_tmul, map_add, map_add, map_add, hs, ht, map_add, map_add, map_add]
    | tmul a b =>
      have h₁ : (LinearEquiv.prodAssoc K U V W).toLinearMap ∘ₗ LinearMap.inl K (U × V) W ∘ₗ
          LinearMap.inl K U V = LinearMap.inl K U (V × W) := by ext <;> simp
      have h₂ : (LinearEquiv.prodAssoc K U V W).toLinearMap ∘ₗ LinearMap.inl K (U × V) W ∘ₗ
          LinearMap.inr K U V = LinearMap.inr K U (V × W) ∘ₗ LinearMap.inl K V W := by
        ext <;> simp
      have h₃ : (LinearEquiv.prodAssoc K U V W).toLinearMap ∘ₗ LinearMap.inr K (U × V) W =
          LinearMap.inr K U (V × W) ∘ₗ LinearMap.inr K V W := by ext <;> simp
      refine Subtype.ext ?_
      simp only [LinearEquiv.rTensor_tmul, LinearEquiv.coe_detLineCongr,
        coe_detLineProdEquiv_tmul_eq_map_mul_map, map_mul, assoc_tmul, LinearEquiv.lTensor_tmul,
        ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, mul_assoc, h₁, h₂, h₃]

end Prod

end TauCeti

namespace LinearMap

open TauCeti

variable {K : Type*} [Field K] {M N M' N' : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
  (f : M →ₗ[K] N) (g : M' →ₗ[K] N')

section Kernel

variable [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]

/-- The determinant line of the kernel of `f.prodMap g` is `det (ker f) ⊗ det (ker g)`, through
`ker (f.prodMap g) = ker f × ker g`. -/
private def detLineKerProdMap :
    TauCeti.detLine K (ker (f.prodMap g)) ≃ₗ[K]
      TauCeti.detLine K (ker f) ⊗[K] TauCeti.detLine K (ker g) :=
  ((LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv _ _)).detLineCongr.trans
    (detLineProdEquiv K _ _).symm

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
  induction i using Fin.addCases <;> ext <;> simp

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
  set κ := (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv (ker f) (ker g))
  set κ' := (LinearEquiv.ofEq _ _ (ker_prodMap g f)).trans (Submodule.prodEquiv (ker g) (ker f))
  -- Read through `κ` and `κ'`, the exchange `e` is the swap of `ker f × ker g`.
  have hswap : κ.symm.trans (e.trans κ') = LinearEquiv.prodComm K (ker f) (ker g) := by
    ext x <;> simp [κ, κ', he]
  rw [map_smul, ← detLineCongr_prodComm_detLineProdEquiv, ← hswap]
  simp only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply]

variable {M'' N'' : Type*} [AddCommGroup M''] [Module K M''] [AddCommGroup N''] [Module K N'']
  (h : M'' →ₗ[K] N'') [FiniteDimensional K (ker h)]

/-- Regrouping the summands of the kernel: if `e : ker ((f ⊕ g) ⊕ h) ≃ ker (f ⊕ (g ⊕ h))` is
induced by `(x, y, z) ↦ (x, (y, z))`, the kernel factors are regrouped without a sign. -/
private theorem detLineCongr_detLineKerProdMap_symm_assoc
    (e : ker ((f.prodMap g).prodMap h) ≃ₗ[K] ker (f.prodMap (g.prodMap h)))
    (he : ∀ x, (e x : M × M' × M'') = LinearEquiv.prodAssoc K M M' M'' x)
    (a : TauCeti.detLine K (ker f)) (b : TauCeti.detLine K (ker g))
    (c : TauCeti.detLine K (ker h)) :
    e.detLineCongr ((detLineKerProdMap (f.prodMap g) h).symm
        ((detLineKerProdMap f g).symm (a ⊗ₜ b) ⊗ₜ c)) =
      (detLineKerProdMap f (g.prodMap h)).symm (a ⊗ₜ (detLineKerProdMap g h).symm (b ⊗ₜ c)) := by
  set κ₁ := (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv (ker f) (ker g))
  set κ₂ := (LinearEquiv.ofEq _ _ (ker_prodMap (f.prodMap g) h)).trans
    (Submodule.prodEquiv (ker (f.prodMap g)) (ker h))
  set κ₃ := (LinearEquiv.ofEq _ _ (ker_prodMap g h)).trans (Submodule.prodEquiv (ker g) (ker h))
  set κ₄ := (LinearEquiv.ofEq _ _ (ker_prodMap f (g.prodMap h))).trans
    (Submodule.prodEquiv (ker f) (ker (g.prodMap h)))
  -- The four inclusions of the kernel factors agree after regrouping.
  have h₁ : e.toLinearMap ∘ₗ κ₂.symm.toLinearMap ∘ₗ LinearMap.inl K _ _ ∘ₗ κ₁.symm.toLinearMap ∘ₗ
      LinearMap.inl K _ _ = κ₄.symm.toLinearMap ∘ₗ LinearMap.inl K _ _ := by
    ext x
    · simp [κ₁, κ₂, κ₄, he]
    · simp [κ₁, κ₂, κ₄, he]
    · simp [κ₁, κ₂, κ₄, he]
  have h₂ : e.toLinearMap ∘ₗ κ₂.symm.toLinearMap ∘ₗ LinearMap.inl K _ _ ∘ₗ κ₁.symm.toLinearMap ∘ₗ
      LinearMap.inr K _ _ = κ₄.symm.toLinearMap ∘ₗ LinearMap.inr K _ _ ∘ₗ
        κ₃.symm.toLinearMap ∘ₗ LinearMap.inl K _ _ := by
    ext x
    · simp [κ₁, κ₂, κ₃, κ₄, he]
    · simp [κ₁, κ₂, κ₃, κ₄, he]
    · simp [κ₁, κ₂, κ₃, κ₄, he]
  have h₃ : e.toLinearMap ∘ₗ κ₂.symm.toLinearMap ∘ₗ LinearMap.inr K _ _ =
      κ₄.symm.toLinearMap ∘ₗ LinearMap.inr K _ _ ∘ₗ κ₃.symm.toLinearMap ∘ₗ
        LinearMap.inr K _ _ := by
    ext x
    · simp [κ₂, κ₃, κ₄, he]
    · simp [κ₂, κ₃, κ₄, he]
    · simp [κ₂, κ₃, κ₄, he]
  refine Subtype.ext ?_
  simp only [detLineKerProdMap, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.detLineCongr_symm, LinearEquiv.coe_detLineCongr,
    coe_detLineProdEquiv_tmul_eq_map_mul_map, map_mul, ← AlgHom.comp_apply,
    ExteriorAlgebra.map_comp_map, mul_assoc]
  simp only [← LinearMap.comp_assoc] at h₁ h₂ h₃ ⊢
  rw [h₁, h₂, h₃]

end Kernel

section Cokernel

variable [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)]

/-- The determinant line of the cokernel of `f.prodMap g` is `det (coker f) ⊗ det (coker g)`,
through `coker (f.prodMap g) = coker f × coker g`. -/
private def detLineCokerProdMap :
    TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g) ≃ₗ[K]
      TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)) :=
  (detLineProdEquiv K _ _).trans
    ((Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans
      (Submodule.quotientProdEquiv _ _)).detLineCongr.symm

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
  set κ := (Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans
    (Submodule.quotientProdEquiv (range f) (range g))
  set κ' := (Submodule.quotEquivOfEq _ _ (range_prodMap g f)).trans
    (Submodule.quotientProdEquiv (range g) (range f))
  have hκ (a : N) (b : N') : κ.symm ((range f).mkQ a, (range g).mkQ b) =
      (range (f.prodMap g)).mkQ (a, b) := by
    rw [LinearEquiv.symm_apply_eq]
    simp [κ]
  have hκ' (a : N') (b : N) : κ'.symm ((range g).mkQ a, (range f).mkQ b) =
      (range (g.prodMap f)).mkQ (a, b) := by
    rw [LinearEquiv.symm_apply_eq]
    simp [κ']
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

variable {M'' N'' : Type*} [AddCommGroup M''] [Module K M''] [AddCommGroup N''] [Module K N'']
  (h : M'' →ₗ[K] N'') [FiniteDimensional K (N'' ⧸ range h)]

/-- Regrouping the summands of the cokernel: if
`e : coker ((f ⊕ g) ⊕ h) ≃ coker (f ⊕ (g ⊕ h))` is induced by `(x, y, z) ↦ (x, (y, z))`, the
cokernel factors are regrouped without a sign. -/
private theorem detLineCongr_detLineCokerProdMap_assoc
    (e : (((N × N') × N'') ⧸ range ((f.prodMap g).prodMap h)) ≃ₗ[K]
      ((N × N' × N'') ⧸ range (f.prodMap (g.prodMap h))))
    (he : ∀ x, e ((range ((f.prodMap g).prodMap h)).mkQ x) =
      (range (f.prodMap (g.prodMap h))).mkQ (LinearEquiv.prodAssoc K N N' N'' x))
    (a : TauCeti.detLine K (N ⧸ range f)) (b : TauCeti.detLine K (N' ⧸ range g))
    (c : TauCeti.detLine K (N'' ⧸ range h)) :
    e.detLineCongr (detLineCokerProdMap (f.prodMap g) h (detLineCokerProdMap f g (a ⊗ₜ b) ⊗ₜ c)) =
      detLineCokerProdMap f (g.prodMap h) (a ⊗ₜ detLineCokerProdMap g h (b ⊗ₜ c)) := by
  set κ₁ := (Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans
    (Submodule.quotientProdEquiv (range f) (range g))
  set κ₂ := (Submodule.quotEquivOfEq _ _ (range_prodMap (f.prodMap g) h)).trans
    (Submodule.quotientProdEquiv (range (f.prodMap g)) (range h))
  set κ₃ := (Submodule.quotEquivOfEq _ _ (range_prodMap g h)).trans
    (Submodule.quotientProdEquiv (range g) (range h))
  set κ₄ := (Submodule.quotEquivOfEq _ _ (range_prodMap f (g.prodMap h))).trans
    (Submodule.quotientProdEquiv (range f) (range (g.prodMap h)))
  have hκ₁ (x : N) (y : N') : κ₁.symm ((range f).mkQ x, (range g).mkQ y) =
      (range (f.prodMap g)).mkQ (x, y) := by
    rw [LinearEquiv.symm_apply_eq]; simp [κ₁]
  have hκ₂ (x : N × N') (y : N'') : κ₂.symm ((range (f.prodMap g)).mkQ x, (range h).mkQ y) =
      (range ((f.prodMap g).prodMap h)).mkQ (x, y) := by
    rw [LinearEquiv.symm_apply_eq]; simp [κ₂]
  have hκ₃ (x : N') (y : N'') : κ₃.symm ((range g).mkQ x, (range h).mkQ y) =
      (range (g.prodMap h)).mkQ (x, y) := by
    rw [LinearEquiv.symm_apply_eq]; simp [κ₃]
  have hκ₄ (x : N) (y : N' × N'') : κ₄.symm ((range f).mkQ x, (range (g.prodMap h)).mkQ y) =
      (range (f.prodMap (g.prodMap h))).mkQ (x, y) := by
    rw [LinearEquiv.symm_apply_eq]; simp [κ₄]
  simp only [Submodule.mkQ_apply] at he
  -- The four inclusions of the cokernel factors agree after regrouping.
  have h₁ : e.toLinearMap ∘ₗ κ₂.symm.toLinearMap ∘ₗ LinearMap.inl K _ _ ∘ₗ κ₁.symm.toLinearMap ∘ₗ
      LinearMap.inl K _ _ = κ₄.symm.toLinearMap ∘ₗ LinearMap.inl K _ _ := by
    ext x
    have e₁ := hκ₁ x 0
    have e₂ := hκ₂ (x, 0) 0
    have e₄ := hκ₄ x 0
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_zero] at e₁ e₂ e₄
    simp [e₁, e₂, e₄, he, Prod.mk_zero_zero]
  have h₂ : e.toLinearMap ∘ₗ κ₂.symm.toLinearMap ∘ₗ LinearMap.inl K _ _ ∘ₗ κ₁.symm.toLinearMap ∘ₗ
      LinearMap.inr K _ _ = κ₄.symm.toLinearMap ∘ₗ LinearMap.inr K _ _ ∘ₗ
        κ₃.symm.toLinearMap ∘ₗ LinearMap.inl K _ _ := by
    ext y
    have e₁ := hκ₁ 0 y
    have e₂ := hκ₂ (0, y) 0
    have e₃ := hκ₃ y 0
    have e₄ := hκ₄ 0 (y, 0)
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_zero] at e₁ e₂ e₃ e₄
    simp [e₁, e₂, e₃, e₄, he]
  have h₃ : e.toLinearMap ∘ₗ κ₂.symm.toLinearMap ∘ₗ LinearMap.inr K _ _ =
      κ₄.symm.toLinearMap ∘ₗ LinearMap.inr K _ _ ∘ₗ κ₃.symm.toLinearMap ∘ₗ
        LinearMap.inr K _ _ := by
    ext z
    have e₂ := hκ₂ 0 z
    have e₃ := hκ₃ 0 z
    have e₄ := hκ₄ 0 (0, z)
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_zero] at e₂ e₃ e₄
    simp [e₂, e₃, e₄, he]
  simp only [detLineCokerProdMap, LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm]
  refine Subtype.ext ?_
  simp only [LinearEquiv.coe_detLineCongr, coe_detLineProdEquiv_tmul_eq_map_mul_map,
    map_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, mul_assoc]
  simp only [← LinearMap.comp_assoc] at h₁ h₂ h₃ ⊢
  rw [h₁, h₂, h₃]

/-- A functional on the cokernel line of `f.prodMap g`, read through `detLineCokerProdMap` as an
element of `(det (coker f))^* ⊗ (det (coker g))^*`, pairs with `detLineCokerProdMap f g t` as its
tensor factors pair with `t`. -/
private theorem dualMap_detLineCokerProdMap_symm_apply
    (u : Dual K (TauCeti.detLine K (N ⧸ range f)) ⊗[K] Dual K (TauCeti.detLine K (N' ⧸ range g)))
    (t : TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g)) :
    ((detLineCokerProdMap f g).dualMap.trans (dualDistribEquiv K _ _).symm).symm u
        (detLineCokerProdMap f g t) = dualDistribEquiv K _ _ u t := by
  simp [LinearEquiv.dualMap_symm]

/-- Regrouping the dual cokernel factors: the dual form of
`detLineCongr_detLineCokerProdMap_assoc`. -/
private theorem dualMap_detLineCokerProdMap_symm_assoc
    (e : (((N × N') × N'') ⧸ range ((f.prodMap g).prodMap h)) ≃ₗ[K]
      ((N × N' × N'') ⧸ range (f.prodMap (g.prodMap h))))
    (he : ∀ x, e ((range ((f.prodMap g).prodMap h)).mkQ x) =
      (range (f.prodMap (g.prodMap h))).mkQ (LinearEquiv.prodAssoc K N N' N'' x))
    (p : Dual K (TauCeti.detLine K (N ⧸ range f))) (q : Dual K (TauCeti.detLine K (N' ⧸ range g)))
    (r : Dual K (TauCeti.detLine K (N'' ⧸ range h))) :
    ((detLineCokerProdMap (f.prodMap g) h).dualMap.trans (dualDistribEquiv K _ _).symm).symm
        (((detLineCokerProdMap f g).dualMap.trans (dualDistribEquiv K _ _).symm).symm (p ⊗ₜ q) ⊗ₜ
          r) ∘ₗ e.detLineCongr.symm.toLinearMap =
      ((detLineCokerProdMap f (g.prodMap h)).dualMap.trans (dualDistribEquiv K _ _).symm).symm
        (p ⊗ₜ ((detLineCokerProdMap g h).dualMap.trans (dualDistribEquiv K _ _).symm).symm
          (q ⊗ₜ r)) := by
  rw [LinearEquiv.eq_symm_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  refine TensorProduct.ext' fun x w ↦ ?_
  obtain ⟨t, rfl⟩ := (detLineCokerProdMap g h).surjective w
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, tmul_add, ht, ht']
  | tmul y z =>
    simp only [LinearEquiv.dualMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    rw [← detLineCongr_detLineCokerProdMap_assoc f g h e he x y z]
    simp only [LinearEquiv.symm_apply_apply, dualMap_detLineCokerProdMap_symm_apply,
      dualDistribEquiv_tmul_tmul, mul_assoc]

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

/-- **Exchanging a summand of even index** costs no sign: if `ind f` is even, the swaps
`M × M' ≃ M' × M` and `N × N' ≃ N' × N` carry `LinearMap.detLineProdMapEquiv f g` to
`LinearMap.detLineProdMapEquiv g f` followed by the exchange of the tensor factors. This applies
in particular to complex-linear operators, whose real index is even. -/
theorem detLineProdMapEquiv_detLineCongr_prodComm_of_even
    (hf : Even (finrank K (ker f) + finrank K (N ⧸ range f))) (x : (f.prodMap g).detLine) :
    detLineProdMapEquiv g f ((f.prodMap g).detLineCongr (LinearEquiv.prodComm K M M')
        (LinearEquiv.prodComm K N N') (by ext <;> simp) x) =
      TensorProduct.comm K _ _ (detLineProdMapEquiv f g x) := by
  rw [detLineProdMapEquiv_detLineCongr_prodComm, (hf.mul_right _).neg_one_pow, one_smul]

/-- `LinearMap.detLineProdMapEquiv` on the elements read off from pure tensors of kernel lines and
of dual cokernel lines through `detLineKerProdMap` and `detLineCokerProdMap`. -/
private theorem detLineProdMapEquiv_symm_tmul_symm (a : TauCeti.detLine K (ker f))
    (b : TauCeti.detLine K (ker g)) (p : Dual K (TauCeti.detLine K (N ⧸ range f)))
    (q : Dual K (TauCeti.detLine K (N' ⧸ range g))) :
    detLineProdMapEquiv f g ((detLineKerProdMap f g).symm (a ⊗ₜ b) ⊗ₜ
        ((detLineCokerProdMap f g).dualMap.trans (dualDistribEquiv K _ _).symm).symm (p ⊗ₜ q)) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) • ((a ⊗ₜ p) ⊗ₜ (b ⊗ₜ q)) := by
  simp only [detLineProdMapEquiv, LinearEquiv.trans_apply, congr_tmul,
    LinearEquiv.smulOfNeZero_apply, map_smul, LinearEquiv.apply_symm_apply, smul_tmul',
    tensorTensorTensorComm_tmul]

variable {M'' N'' : Type*} [AddCommGroup M''] [Module K M''] [AddCommGroup N''] [Module K N'']
  (h : M'' →ₗ[K] N'') [FiniteDimensional K (ker h)] [FiniteDimensional K (N'' ⧸ range h)]

/-- `LinearMap.detLineProdMapEquiv_detLineCongr_prodAssoc` on the element of the determinant line
of `(f ⊕ g) ⊕ h` read off from pure tensors of the kernel and dual cokernel lines of `f`, `g`
and `h`. -/
private theorem detLineProdMapEquiv_detLineCongr_prodAssoc_tmul
    (a : TauCeti.detLine K (ker f)) (b : TauCeti.detLine K (ker g))
    (c : TauCeti.detLine K (ker h)) (p : Dual K (TauCeti.detLine K (N ⧸ range f)))
    (q : Dual K (TauCeti.detLine K (N' ⧸ range g))) (r : Dual K (TauCeti.detLine K (N'' ⧸ range h)))
    (hsq : (f.prodMap (g.prodMap h)) ∘ₗ (LinearEquiv.prodAssoc K M M' M'').toLinearMap =
      (LinearEquiv.prodAssoc K N N' N'').toLinearMap ∘ₗ (f.prodMap g).prodMap h) :
    LinearEquiv.lTensor _ (detLineProdMapEquiv g h) (detLineProdMapEquiv f (g.prodMap h)
        (((f.prodMap g).prodMap h).detLineCongr (LinearEquiv.prodAssoc K M M' M'')
          (LinearEquiv.prodAssoc K N N' N'') hsq
          ((detLineKerProdMap (f.prodMap g) h).symm ((detLineKerProdMap f g).symm (a ⊗ₜ b) ⊗ₜ c) ⊗ₜ
            ((detLineCokerProdMap (f.prodMap g) h).dualMap.trans (dualDistribEquiv K _ _).symm).symm
              (((detLineCokerProdMap f g).dualMap.trans (dualDistribEquiv K _ _).symm).symm
                (p ⊗ₜ q) ⊗ₜ r) : ((f.prodMap g).prodMap h).detLine))) =
      TensorProduct.assoc K _ _ _ (LinearEquiv.rTensor _ (detLineProdMapEquiv f g)
        (detLineProdMapEquiv (f.prodMap g) h
          ((detLineKerProdMap (f.prodMap g) h).symm ((detLineKerProdMap f g).symm (a ⊗ₜ b) ⊗ₜ c) ⊗ₜ
            ((detLineCokerProdMap (f.prodMap g) h).dualMap.trans (dualDistribEquiv K _ _).symm).symm
              (((detLineCokerProdMap f g).dualMap.trans (dualDistribEquiv K _ _).symm).symm
                (p ⊗ₜ q) ⊗ₜ r) : ((f.prodMap g).prodMap h).detLine))) := by
  have hK := detLineCongr_detLineKerProdMap_symm_assoc f g h
    ((LinearEquiv.prodAssoc K M M' M'').ofSubmodules _ _
      (((f.prodMap g).prodMap h).map_ker_eq_ker_of_comp_eq
        (LinearEquiv.prodAssoc K M M' M'').surjective (LinearEquiv.prodAssoc K N N' N'').injective
        hsq)) (fun _ ↦ rfl) a b c
  have hC := dualMap_detLineCokerProdMap_symm_assoc f g h
    (Submodule.Quotient.equiv _ _ (LinearEquiv.prodAssoc K N N' N'')
      (((f.prodMap g).prodMap h).map_range_eq_range_of_comp_eq
        (LinearEquiv.prodAssoc K M M' M'').surjective hsq)) (fun _ ↦ rfl) p q r
  simp only [detLineCongr_tmul, hK, hC, detLineProdMapEquiv_symm_tmul_symm,
    LinearEquiv.map_smul, LinearEquiv.lTensor_tmul, LinearEquiv.rTensor_tmul, tmul_smul,
    ← smul_tmul', assoc_tmul, smul_smul]
  -- Both Koszul signs are `(-1) ^ (cf * kg + cf * kh + cg * kh)`.
  have hsign : (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker (g.prodMap h))) *
      (-1) ^ (finrank K (N' ⧸ range g) * finrank K (ker h)) =
      (-1) ^ (finrank K ((N × N') ⧸ range (f.prodMap g)) * finrank K (ker h)) *
        (-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) := by
    rw [finrank_ker_prodMap, finrank_quotient_range_prodMap, ← pow_add, ← pow_add]
    ring_nf
  simp only [hsign]

/-- **Regrouping the summands of a direct sum** costs no sign. The regroupings
`(M × M') × M'' ≃ M × (M' × M'')` and `(N × N') × N'' ≃ N × (N' × N'')` carry
`(f.prodMap g).prodMap h` to `f.prodMap (g.prodMap h)`, and so induce an isomorphism of their
determinant lines (`LinearMap.detLineCongr`). Followed by the direct sum isomorphisms
`det (f ⊕ (g ⊕ h)) ≃ det f ⊗ det (g ⊕ h) ≃ det f ⊗ (det g ⊗ det h)`, it agrees with
`det ((f ⊕ g) ⊕ h) ≃ det (f ⊕ g) ⊗ det h ≃ (det f ⊗ det g) ⊗ det h` followed by the
regrouping of the tensor factors. The Koszul signs of the two composites,
`(-1) ^ ((dim coker f + dim coker g) * dim ker h + dim coker f * dim ker g)` and
`(-1) ^ (dim coker f * (dim ker g + dim ker h) + dim coker g * dim ker h)`, coincide. Together with
the exchange law `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`, this compares the
determinant line of a direct sum of finitely many operators with the tensor product of their
determinant lines under every reordering of the summands. -/
theorem detLineProdMapEquiv_detLineCongr_prodAssoc (x : ((f.prodMap g).prodMap h).detLine) :
    LinearEquiv.lTensor _ (detLineProdMapEquiv g h) (detLineProdMapEquiv f (g.prodMap h)
        (((f.prodMap g).prodMap h).detLineCongr (LinearEquiv.prodAssoc K M M' M'')
          (LinearEquiv.prodAssoc K N N' N'') (by ext <;> simp) x)) =
      TensorProduct.assoc K _ _ _ (LinearEquiv.rTensor _ (detLineProdMapEquiv f g)
        (detLineProdMapEquiv (f.prodMap g) h x)) := by
  -- Read the determinant line of `(f ⊕ g) ⊕ h` from the kernel and dual cokernel lines of `f`,
  -- `g` and `h`, through the kernel and cokernel isomorphisms of `f ⊕ g` and of `(f ⊕ g) ⊕ h`,
  -- and reduce to pure tensors there.
  let Ψ := TensorProduct.congr
    ((LinearEquiv.rTensor _ (detLineKerProdMap f g).symm).trans
      (detLineKerProdMap (f.prodMap g) h).symm)
    ((LinearEquiv.rTensor _ ((detLineCokerProdMap f g).dualMap.trans
        (dualDistribEquiv K _ _).symm).symm).trans
      ((detLineCokerProdMap (f.prodMap g) h).dualMap.trans (dualDistribEquiv K _ _).symm).symm)
  suffices key : ∀ y, LinearEquiv.lTensor _ (detLineProdMapEquiv g h)
      (detLineProdMapEquiv f (g.prodMap h) (((f.prodMap g).prodMap h).detLineCongr
        (LinearEquiv.prodAssoc K M M' M'') (LinearEquiv.prodAssoc K N N' N'')
        (by ext <;> simp) (Ψ y))) =
      TensorProduct.assoc K _ _ _ (LinearEquiv.rTensor _ (detLineProdMapEquiv f g)
        (detLineProdMapEquiv (f.prodMap g) h (Ψ y))) by
    simpa only [LinearEquiv.apply_symm_apply] using key (Ψ.symm x)
  intro y
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => simp only [LinearEquiv.map_add, hy, hy']
  | tmul s u =>
    induction s using TensorProduct.inductionOn with
    | add s s' hs hs' => simp only [add_tmul, LinearEquiv.map_add, hs, hs']
    | tmul t c =>
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' => simp only [add_tmul, LinearEquiv.map_add, ht, ht']
      | tmul a b =>
        induction u using TensorProduct.inductionOn with
        | add u u' hu hu' => simp only [tmul_add, LinearEquiv.map_add, hu, hu']
        | tmul v r =>
          induction v using TensorProduct.inductionOn with
          | add v v' hv hv' => simp only [add_tmul, tmul_add, LinearEquiv.map_add, hv, hv']
          | tmul p q => exact detLineProdMapEquiv_detLineCongr_prodAssoc_tmul f g h a b c p q r _

end LinearMap
