/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Quotient.Prod
public import TauCeti.LinearAlgebra.LinearMap.Comp
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
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`). This is the direct-sum law through which
orientations of the determinant lines of Fredholm operators, and so of moduli spaces cut out by
them, are compared for split operators.

The direct sum isomorphism is natural: for commuting squares of isomorphisms `(e₁, e₂)` from `f`
to `f'` and `(e₁', e₂')` from `g` to `g'`, transporting `det (f ⊕ g)` along `(e₁ × e₁', e₂ × e₂')`
is the tensor product of the transports of `det f` and `det g`, with no sign
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodCongr`). So a symmetry acting separately on
the summands of a split operator acts on its determinant line by the product of its actions on
the determinant lines of the summands.

## Main declarations

* `TauCeti.detLineProdEquiv`: `det U ⊗ det W ≃ det (U × W)`, with its value
  `TauCeti.coe_detLineProdEquiv_tmul`.
* `TauCeti.detLineCongr_prodComm_detLineProdEquiv`: exchanging the factors costs
  `(-1) ^ (dim U * dim W)`.
* `TauCeti.coe_detLineProdEquiv_tmul_eq_mul`: `TauCeti.detLineProdEquiv` is the exterior product
  of the images of the factors.
* `TauCeti.detLineCongr_prodCongr_detLineProdEquiv`: naturality in both factors.
* `LinearMap.detLineProdMapEquiv`: `det (f.prodMap g) ≃ det f ⊗ det g`, with its value
  `LinearMap.detLineProdMapEquiv_tmul`.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`: exchanging the summands costs
  `(-1) ^ (ind f * ind g)`.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodCongr`: naturality under products of commuting
  squares.

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
      ExteriorAlgebra.map (LinearMap.inl K U W) (a : ExteriorAlgebra K U) *
        ExteriorAlgebra.map (LinearMap.inr K U W) (b : ExteriorAlgebra K W) := by
  have hb : b ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K (finrank K W))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hb using Submodule.span_induction with
  | zero => simp
  | add b b' _ _ h h' => simp only [tmul_add, map_add, Submodule.coe_add, h, h', mul_add]
  | smul r b _ h => simp only [tmul_smul, map_smul, Submodule.coe_smul, h, mul_smul_comm]
  | mem _ hb =>
    obtain ⟨w, rfl⟩ := hb
    have hw : w = LinearMap.snd K U W ∘ (LinearMap.inr K U W ∘ w) := by
      funext i
      simp
    have h := coe_detLineShortExactEquiv_tmul_eq_map_mul LinearMap.inl_injective
      Function.Exact.inl_snd LinearMap.snd_surjective a (LinearMap.inr K U W ∘ w)
    rw [← hw] at h
    rw [detLineProdEquiv, h, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]

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

section

variable {P Q P' Q' : Type*} [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
  [AddCommGroup P'] [Module K P'] [AddCommGroup Q'] [Module K Q'] (f' : P →ₗ[K] Q)
  (g' : P' →ₗ[K] Q') [FiniteDimensional K (Q ⧸ range f')] [FiniteDimensional K (Q' ⧸ range g')]

/-- An isomorphism `e` of the cokernels of `f.prodMap g` and `f'.prodMap g'` which, read through
`coker (f.prodMap g) = coker f × coker g` and `coker (f'.prodMap g') = coker f' × coker g'`, is
an isomorphism `ε` of the products acts on `detLineCokerProdMap` as `ε` acts on the determinant
lines of the products. -/
private theorem detLineCongr_detLineCokerProdMap_of_forall
    (e : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((Q × Q') ⧸ range (f'.prodMap g')))
    (ε : ((N ⧸ range f) × (N' ⧸ range g)) ≃ₗ[K] ((Q ⧸ range f') × (Q' ⧸ range g')))
    (he : ∀ a b, e ((range (f.prodMap g)).mkQ (a, b)) =
      ((Submodule.quotEquivOfEq _ _ (range_prodMap f' g')).trans
        (Submodule.quotientProdEquiv (range f') (range g'))).symm
          (ε ((range f).mkQ a, (range g).mkQ b)))
    (t : TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g)) :
    e.detLineCongr (detLineCokerProdMap f g t) =
      detLineCokerProdMap f' g'
        ((detLineProdEquiv K _ _).symm (ε.detLineCongr (detLineProdEquiv K _ _ t))) := by
  -- Unfold both cokernel isomorphisms.
  simp only [detLineCokerProdMap, LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm,
    LinearEquiv.apply_symm_apply]
  set κ := (Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans
    (Submodule.quotientProdEquiv (range f) (range g))
  set κ' := (Submodule.quotEquivOfEq _ _ (range_prodMap f' g')).trans
    (Submodule.quotientProdEquiv (range f') (range g'))
  have hκ (a : N) (b : N') : κ.symm ((range f).mkQ a, (range g).mkQ b) =
      (range (f.prodMap g)).mkQ (a, b) := by
    rw [LinearEquiv.symm_apply_eq]
    simp [κ]
  -- Read through `κ` and `κ'`, the isomorphism `e` is `ε`.
  have hκe : κ.symm.trans e = ε.trans κ'.symm := by
    ext ⟨a, b⟩
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    simp only [LinearEquiv.trans_apply]
    rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hκ, he]
  rw [← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans, hκe,
    LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply]

/-- The dual form of `detLineCongr_detLineCokerProdMap_of_forall`: if the inverse of the
isomorphism of cokernel lines induced by `e` reads as `Ψ` on the tensor products of the cokernel
lines of the summands, and `Φ` is the transpose of `Ψ` under `dualDistribEquiv`, then
transporting a functional on the cokernel line along `e` acts on its two dual factors by `Φ`. -/
private theorem dualDistribEquiv_symm_dualMap_detLineCokerProdMap_of_forall
    (e : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((Q × Q') ⧸ range (f'.prodMap g')))
    (Ψ : TauCeti.detLine K (Q ⧸ range f') ⊗[K] TauCeti.detLine K (Q' ⧸ range g') →ₗ[K]
      TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g))
    (Φ : Dual K (TauCeti.detLine K (N ⧸ range f)) ⊗[K] Dual K (TauCeti.detLine K (N' ⧸ range g))
      →ₗ[K] Dual K (TauCeti.detLine K (Q ⧸ range f')) ⊗[K]
        Dual K (TauCeti.detLine K (Q' ⧸ range g')))
    (h : ∀ t, e.detLineCongr.symm (detLineCokerProdMap f' g' t) = detLineCokerProdMap f g (Ψ t))
    (hΦ : ∀ ψ t, dualDistribEquiv K _ _ (Φ ψ) t = dualDistribEquiv K _ _ ψ (Ψ t))
    (φ : Dual K (TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)))) :
    (dualDistribEquiv K _ _).symm
        ((detLineCokerProdMap f' g').dualMap (φ ∘ₗ e.detLineCongr.symm.toLinearMap)) =
      Φ ((dualDistribEquiv K _ _).symm ((detLineCokerProdMap f g).dualMap φ)) := by
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun t ↦ ?_
  rw [hΦ, LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.dualMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h]

end

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
  rw [detLineCongr_detLineCokerProdMap_of_forall f g g f e (LinearEquiv.prodComm K _ _)
      (fun a b ↦ by rw [he, LinearEquiv.eq_symm_apply]; simp) t,
    detLineCongr_prodComm_detLineProdEquiv, map_smul, LinearEquiv.symm_apply_apply, map_smul]

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
  rw [dualDistribEquiv_symm_dualMap_detLineCokerProdMap_of_forall f g g f e
      ((-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (N' ⧸ range g)) •
        (TensorProduct.comm K _ _).toLinearMap)
      ((-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (N' ⧸ range g)) •
        (TensorProduct.comm K _ _).toLinearMap) (fun t ↦ ?_) (fun ψ s ↦ ?_) φ,
    LinearMap.smul_apply, LinearEquiv.coe_coe]
  · have h := detLineCongr_detLineCokerProdMap f g e he ((TensorProduct.comm K _ _).symm t)
    rw [LinearEquiv.apply_symm_apply, TensorProduct.comm_symm] at h
    rw [LinearEquiv.symm_apply_eq, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, map_smul,
      h, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  -- `dualDistribEquiv` commutes with exchanging the tensor factors (`dualDistrib_apply_comm`).
  · simp only [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe]
    congr 1
    simpa only [← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
      (TensorProduct.dualDistrib_apply_comm ψ s).symm

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


/-! ### Naturality of the direct sum isomorphism -/

section Naturality

variable {P Q P' Q' : Type*} [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
  [AddCommGroup P'] [Module K P'] [AddCommGroup Q'] [Module K Q'] {f' : P →ₗ[K] Q}
  {g' : P' →ₗ[K] Q'} [FiniteDimensional K (ker f')] [FiniteDimensional K (ker g')]
  [FiniteDimensional K (Q ⧸ range f')] [FiniteDimensional K (Q' ⧸ range g')]
  (e₁ : M ≃ₗ[K] P) (e₂ : N ≃ₗ[K] Q) (e₁' : M' ≃ₗ[K] P') (e₂' : N' ≃ₗ[K] Q')
  (hf : f' ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f)
  (hg : g' ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g)

omit [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)]
  [FiniteDimensional K (Q ⧸ range f')] [FiniteDimensional K (Q' ⧸ range g')] in
/-- Naturality of `detLineKerProdMap`: an isomorphism of kernels of the direct sums acting as
`e₁ × e₁'` corresponds to the isomorphisms of the kernels of the summands. -/
private theorem detLineKerProdMap_detLineCongr_prodCongr
    (e : ker (f.prodMap g) ≃ₗ[K] ker (f'.prodMap g'))
    (he : ∀ x, (e x : P × P') = e₁.prodCongr e₁' x) (β : TauCeti.detLine K (ker (f.prodMap g))) :
    detLineKerProdMap f' g' (e.detLineCongr β) =
      TensorProduct.map
        (e₁.ofSubmodules _ _
          (f.map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective hf)).detLineCongr.toLinearMap
        (e₁'.ofSubmodules _ _
          (g.map_ker_eq_ker_of_comp_eq e₁'.surjective e₂'.injective hg)).detLineCongr.toLinearMap
        (detLineKerProdMap f g β) := by
  obtain ⟨t, rfl⟩ := (detLineKerProdMap f g).symm.surjective β
  rw [LinearEquiv.apply_symm_apply]
  simp only [detLineKerProdMap, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm, LinearEquiv.symm_apply_eq]
  set κ := (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv (ker f) (ker g))
  set κ' := (LinearEquiv.ofEq _ _ (ker_prodMap f' g')).trans
    (Submodule.prodEquiv (ker f') (ker g'))
  -- Read through `κ` and `κ'`, the isomorphism `e` is the product of the kernel isomorphisms.
  have hκ : κ.symm.trans (e.trans κ') =
      (e₁.ofSubmodules _ _ (f.map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective hf)).prodCongr
        (e₁'.ofSubmodules _ _ (g.map_ker_eq_ker_of_comp_eq e₁'.surjective e₂'.injective hg)) := by
    ext x <;> simp [κ, κ', he]
  rw [← TensorProduct.toLinearMap_congr, LinearEquiv.coe_coe,
    ← detLineCongr_prodCongr_detLineProdEquiv, ← hκ]
  simp only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply]

omit [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)] [FiniteDimensional K (ker f')]
  [FiniteDimensional K (ker g')] in
/-- Naturality of `detLineCokerProdMap`: an isomorphism of cokernels of the direct sums induced by
`e₂ × e₂'` corresponds to the isomorphisms of the cokernels of the summands. -/
private theorem detLineCongr_detLineCokerProdMap_prodCongr
    (e : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((Q × Q') ⧸ range (f'.prodMap g')))
    (he : ∀ x, e ((range (f.prodMap g)).mkQ x) = (range (f'.prodMap g')).mkQ (e₂.prodCongr e₂' x))
    (t : TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g)) :
    e.detLineCongr (detLineCokerProdMap f g t) =
      detLineCokerProdMap f' g' (TensorProduct.congr
        (Submodule.Quotient.equiv _ _ e₂
          (f.map_range_eq_range_of_comp_eq e₁.surjective hf)).detLineCongr
        (Submodule.Quotient.equiv _ _ e₂'
          (g.map_range_eq_range_of_comp_eq e₁'.surjective hg)).detLineCongr t) := by
  rw [detLineCongr_detLineCokerProdMap_of_forall f g f' g' e
      ((Submodule.Quotient.equiv _ _ e₂
          (f.map_range_eq_range_of_comp_eq e₁.surjective hf)).prodCongr
        (Submodule.Quotient.equiv _ _ e₂'
          (g.map_range_eq_range_of_comp_eq e₁'.surjective hg)))
      (fun a b ↦ by rw [he, LinearEquiv.eq_symm_apply]; simp) t,
    detLineCongr_prodCongr_detLineProdEquiv, LinearEquiv.symm_apply_apply]

/-- Pairing through `dualDistribEquiv` with dual factors transported by the inverses of `α` and
`β` is pairing after the inverses of `α` and `β`. -/
private theorem dualDistribEquiv_congr_dualMap_apply {A B A' B' : Type*} [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup A'] [Module K A'] [AddCommGroup B']
    [Module K B'] [FiniteDimensional K A] [FiniteDimensional K B] [FiniteDimensional K A']
    [FiniteDimensional K B'] (α : A ≃ₗ[K] A') (β : B ≃ₗ[K] B') (ψ : Dual K A ⊗[K] Dual K B)
    (t : A' ⊗[K] B') :
    dualDistribEquiv K _ _
        (TensorProduct.map α.symm.dualMap.toLinearMap β.symm.dualMap.toLinearMap ψ) t =
      dualDistribEquiv K _ _ ψ ((TensorProduct.congr α β).symm.toLinearMap t) := by
  induction ψ using TensorProduct.inductionOn with
  | add ψ ψ' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | tmul a b =>
    induction t using TensorProduct.inductionOn with
    | add t t' h h' => simp only [map_add, h, h']
    | tmul s u => simp

/-- `tensorTensorTensorComm` intertwines a scalar multiple of `map α β a ⊗ map γ δ d` with the
corresponding image of `(r • a) ⊗ d`. -/
private theorem tensorTensorTensorComm_smul_map_tmul_map {A B C D A' B' C' D' : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    [AddCommGroup D] [Module K D] [AddCommGroup A'] [Module K A'] [AddCommGroup B'] [Module K B']
    [AddCommGroup C'] [Module K C'] [AddCommGroup D'] [Module K D'] (r : K) (a : A ⊗[K] B)
    (d : C ⊗[K] D) (α : A →ₗ[K] A') (β : B →ₗ[K] B') (γ : C →ₗ[K] C') (δ : D →ₗ[K] D') :
    tensorTensorTensorComm K A' B' C' D'
        ((r • TensorProduct.map α β a) ⊗ₜ TensorProduct.map γ δ d) =
      TensorProduct.map (TensorProduct.map α γ) (TensorProduct.map β δ)
        (tensorTensorTensorComm K A B C D ((r • a) ⊗ₜ d)) := by
  rw [← map_smul, ← TensorProduct.map_tmul, ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
    TensorProduct.tensorTensorTensorComm_comp_map, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap]

/-- Naturality of `LinearMap.detLineProdMapEquiv` for isomorphisms `k` of the kernels and `c` of the
cokernels of the direct sums induced by `e₁ × e₁'` and `e₂ × e₂'`. -/
private theorem detLineProdMapEquiv_detLineCongrKerCoker
    (k : ker (f.prodMap g) ≃ₗ[K] ker (f'.prodMap g'))
    (hk : ∀ x, (k x : P × P') = e₁.prodCongr e₁' x)
    (c : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((Q × Q') ⧸ range (f'.prodMap g')))
    (hc : ∀ x, c ((range (f.prodMap g)).mkQ x) = (range (f'.prodMap g')).mkQ (e₂.prodCongr e₂' x))
    (x : (f.prodMap g).detLine) :
    detLineProdMapEquiv f' g' (detLineCongrKerCoker k c x) =
      TensorProduct.map (f.detLineCongr e₁ e₂ hf).toLinearMap
        (g.detLineCongr e₁' e₂' hg).toLinearMap
        (detLineProdMapEquiv f g x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' h h' => simp only [map_add, h, h']
  | tmul β φ =>
    have hC := detLineCongr_detLineCokerProdMap_prodCongr f g e₁ e₂ e₁' e₂' hf hg c hc
    have hD := dualDistribEquiv_symm_dualMap_detLineCokerProdMap_of_forall f g f' g' c _ _
      (fun t ↦ by rw [LinearEquiv.symm_apply_eq, hC, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply])
      (dualDistribEquiv_congr_dualMap_apply
        (Submodule.Quotient.equiv _ _ e₂
          (f.map_range_eq_range_of_comp_eq e₁.surjective hf)).detLineCongr
        (Submodule.Quotient.equiv _ _ e₂'
          (g.map_range_eq_range_of_comp_eq e₁'.surjective hg)).detLineCongr) φ
    rw [detLineCongrKerCoker_tmul]
    simp only [detLineProdMapEquiv, LinearEquiv.trans_apply, congr_tmul,
      LinearEquiv.smulOfNeZero_apply, map_smul]
    refine (congrArg (fun y ↦ tensorTensorTensorComm K _ _ _ _ ((_ • y) ⊗ₜ _))
      (detLineKerProdMap_detLineCongr_prodCongr f g e₁ e₂ e₁' e₂' hf hg k hk β)).trans ?_
    refine (congrArg (fun z ↦ tensorTensorTensorComm K _ _ _ _ (_ ⊗ₜ z)) hD).trans ?_
    -- The Koszul signs agree, the dimensions being preserved by the isomorphisms.
    have hs : (-1 : K) ^ (finrank K (Q ⧸ range f') * finrank K (ker g')) =
        (-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) := by
      rw [(e₁'.ofSubmodules _ _
          (g.map_ker_eq_ker_of_comp_eq e₁'.surjective e₂'.injective hg)).finrank_eq,
        (Submodule.Quotient.equiv _ _ e₂
          (f.map_range_eq_range_of_comp_eq e₁.surjective hf)).finrank_eq]
    refine (congrArg (fun r : K ↦ tensorTensorTensorComm K _ _ _ _ ((r • _) ⊗ₜ _)) hs).trans ?_
    refine (tensorTensorTensorComm_smul_map_tmul_map _ _ _ _ _ _ _).trans ?_
    exact (congrArg₂ (fun F G ↦ TensorProduct.map F G _) (toLinearMap_detLineCongr f e₁ e₂ hf)
      (toLinearMap_detLineCongr g e₁' e₂' hg)).symm

/-- **Naturality of the direct sum isomorphism of determinant lines.** Commuting squares
`(e₁, e₂)` from `f` to `f'` and `(e₁', e₂')` from `g` to `g'` give a commuting square
`(e₁ × e₁', e₂ × e₂')` from `f.prodMap g` to `f'.prodMap g'`. Under
`LinearMap.detLineProdMapEquiv`, the transport of `det (f.prodMap g)` along it is the tensor
product of the transports of `det f` and `det g`, with no sign. -/
theorem detLineProdMapEquiv_detLineCongr_prodCongr (x : (f.prodMap g).detLine) :
    detLineProdMapEquiv f' g' ((f.prodMap g).detLineCongr (e₁.prodCongr e₁') (e₂.prodCongr e₂')
        (prodMap_comp_prodCongr_eq_of_comp_eq hf hg) x) =
      TensorProduct.map (f.detLineCongr e₁ e₂ hf).toLinearMap
        (g.detLineCongr e₁' e₂' hg).toLinearMap
        (detLineProdMapEquiv f g x) := by
  -- `LinearMap.detLineCongr` is `LinearMap.detLineCongrKerCoker` of the induced isomorphisms.
  have hx : (f.prodMap g).detLineCongr (e₁.prodCongr e₁') (e₂.prodCongr e₂')
      (prodMap_comp_prodCongr_eq_of_comp_eq hf hg) x =
      detLineCongrKerCoker ((e₁.prodCongr e₁').ofSubmodules _ _
        ((f.prodMap g).map_ker_eq_ker_of_comp_eq (e₁.prodCongr e₁').surjective
          (e₂.prodCongr e₂').injective (prodMap_comp_prodCongr_eq_of_comp_eq hf hg)))
        (Submodule.Quotient.equiv _ _ (e₂.prodCongr e₂')
          ((f.prodMap g).map_range_eq_range_of_comp_eq (e₁.prodCongr e₁').surjective
            (prodMap_comp_prodCongr_eq_of_comp_eq hf hg))) x := by
    induction x using TensorProduct.inductionOn with
    | add x x' h h' => simp only [map_add, h, h']
    | tmul β φ => rw [detLineCongr_tmul, detLineCongrKerCoker_tmul]
  rw [hx]
  exact detLineProdMapEquiv_detLineCongrKerCoker f g e₁ e₂ e₁' e₂' hf hg _ (fun _ ↦ rfl) _
    (fun _ ↦ rfl) x

end Naturality

end LinearMap
