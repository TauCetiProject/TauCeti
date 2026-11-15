/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.Determinant.Exact
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
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`). Both isomorphisms are natural: transport
along isomorphisms of the factors, or along commuting squares for `f` and `g`, is the tensor
product of the transports (`TauCeti.detLineCongr_prodCongr_detLineProdEquiv`,
`LinearMap.detLineProdMapEquiv_detLineCongr_prodCongr`). This is the direct-sum law through which
orientations of the determinant lines of Fredholm operators, and so of moduli spaces cut out by
them, are compared for split operators.

## Main declarations

* `TauCeti.detLineProdEquiv`: `det U ⊗ det W ≃ det (U × W)`, with its value
  `TauCeti.coe_detLineProdEquiv_tmul`.
* `TauCeti.detLineCongr_prodComm_detLineProdEquiv`: exchanging the factors costs
  `(-1) ^ (dim U * dim W)`.
* `TauCeti.detLineCongr_prodCongr_detLineProdEquiv`: `TauCeti.detLineProdEquiv` is natural in both
  factors.
* `LinearMap.detLineProdMapEquiv`: `det (f.prodMap g) ≃ det f ⊗ det g`, with its value
  `LinearMap.detLineProdMapEquiv_tmul`.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`: exchanging the summands costs
  `(-1) ^ (ind f * ind g)`.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodCongr`: `LinearMap.detLineProdMapEquiv` is
  natural with respect to commuting squares for both summands.

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

variable {U' W' : Type*} [AddCommGroup U'] [Module K U'] [AddCommGroup W'] [Module K W']
  [FiniteDimensional K U'] [FiniteDimensional K W'] in
/-- **Naturality of the determinant line of a product.** Isomorphisms `a : U ≃ U'` and
`b : W ≃ W'` intertwine `TauCeti.detLineProdEquiv K U W` and `TauCeti.detLineProdEquiv K U' W'`
with the isomorphisms of determinant lines they induce. -/
theorem detLineCongr_prodCongr_detLineProdEquiv (a : U ≃ₗ[K] U') (b : W ≃ₗ[K] W')
    (t : detLine K U ⊗[K] detLine K W) :
    (a.prodCongr b).detLineCongr (detLineProdEquiv K U W t) =
      detLineProdEquiv K U' W' (TensorProduct.congr a.detLineCongr b.detLineCongr t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul x y =>
    obtain ⟨c, rfl⟩ := (Module.finBasis K U).exists_smul_ιMulti_eq x
    obtain ⟨d, rfl⟩ := (Module.finBasis K W).exists_smul_ιMulti_eq y
    simp only [TensorProduct.smul_tmul_smul, map_smul]
    congr 1
    refine Subtype.ext ?_
    rw [TensorProduct.congr_tmul, LinearEquiv.detLineCongr_ιMulti,
      LinearEquiv.detLineCongr_ιMulti, LinearEquiv.coe_detLineCongr, coe_detLineProdEquiv_tmul,
      coe_detLineProdEquiv_tmul, ← ExteriorAlgebra.ιMulti_mul_ιMulti,
      ← ExteriorAlgebra.ιMulti_mul_ιMulti, map_mul, ExteriorAlgebra.map_apply_ιMulti,
      ExteriorAlgebra.map_apply_ιMulti]
    simp only [← Function.comp_assoc]
    rw [ExteriorAlgebra.ιMulti_comp_cast, ExteriorAlgebra.ιMulti_comp_cast]
    congr 2 <;> funext i <;> simp

end Prod

end TauCeti

namespace LinearMap

open TauCeti

variable {K : Type*} [Field K] {M N M' N' : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
  (f : M →ₗ[K] N) (g : M' →ₗ[K] N')
  {P Q P' Q' : Type*} [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
  [AddCommGroup P'] [Module K P'] [AddCommGroup Q'] [Module K Q']

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

variable {f' : P →ₗ[K] Q} {g' : P' →ₗ[K] Q'} [FiniteDimensional K (ker f')]
  [FiniteDimensional K (ker g')] in
/-- Naturality of the kernel factor: if `e : ker (f.prodMap g) ≃ ker (f'.prodMap g')` acts as
`e₁ × e₁'`, and `a : ker f ≃ ker f'` and `b : ker g ≃ ker g'` act as `e₁` and `e₁'`, then `e`
corresponds to `a ⊗ b` on the kernel factors. -/
private theorem detLineKerProdMap_detLineCongr_prodCongr {e₁ : M →ₗ[K] P} {e₁' : M' →ₗ[K] P'}
    (e : ker (f.prodMap g) ≃ₗ[K] ker (f'.prodMap g')) (a : ker f ≃ₗ[K] ker f')
    (b : ker g ≃ₗ[K] ker g') (he : ∀ x, (e x : P × P') = Prod.map e₁ e₁' x)
    (ha : ∀ x, (a x : P) = e₁ x) (hb : ∀ y, (b y : P') = e₁' y)
    (β : TauCeti.detLine K (ker (f.prodMap g))) :
    detLineKerProdMap f' g' (e.detLineCongr β) =
      TensorProduct.congr a.detLineCongr b.detLineCongr (detLineKerProdMap f g β) := by
  obtain ⟨t, rfl⟩ := (detLineKerProdMap f g).symm.surjective β
  rw [LinearEquiv.apply_symm_apply]
  simp only [detLineKerProdMap, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm, LinearEquiv.symm_apply_eq]
  set κ := (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv (ker f) (ker g))
  set κ' := (LinearEquiv.ofEq _ _ (ker_prodMap f' g')).trans
    (Submodule.prodEquiv (ker f') (ker g'))
  -- Read through `κ` and `κ'`, the isomorphism `e` is `a × b`.
  have hprod : κ.symm.trans (e.trans κ') = a.prodCongr b := by
    ext x <;> simp [κ, κ', he, ha, hb]
  rw [← detLineCongr_prodCongr_detLineProdEquiv, ← hprod]
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

variable {f' : P →ₗ[K] Q} {g' : P' →ₗ[K] Q'} [FiniteDimensional K (Q ⧸ range f')]
  [FiniteDimensional K (Q' ⧸ range g')]

/-- Naturality of the cokernel factor: if `e : coker (f.prodMap g) ≃ coker (f'.prodMap g')` is
induced by `e₂ × e₂'`, and `a : coker f ≃ coker f'` and `b : coker g ≃ coker g'` are induced by
`e₂` and `e₂'`, then `e` corresponds to `a ⊗ b` on the cokernel factors. -/
private theorem detLineCongr_detLineCokerProdMap_prodCongr {e₂ : N →ₗ[K] Q} {e₂' : N' →ₗ[K] Q'}
    (e : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((Q × Q') ⧸ range (f'.prodMap g')))
    (a : (N ⧸ range f) ≃ₗ[K] (Q ⧸ range f')) (b : (N' ⧸ range g) ≃ₗ[K] (Q' ⧸ range g'))
    (he : ∀ x, e ((range (f.prodMap g)).mkQ x) = (range (f'.prodMap g')).mkQ (Prod.map e₂ e₂' x))
    (ha : ∀ y, a ((range f).mkQ y) = (range f').mkQ (e₂ y))
    (hb : ∀ y, b ((range g).mkQ y) = (range g').mkQ (e₂' y))
    (t : TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g)) :
    e.detLineCongr (detLineCokerProdMap f g t) =
      detLineCokerProdMap f' g' (TensorProduct.congr a.detLineCongr b.detLineCongr t) := by
  simp only [detLineCokerProdMap, LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm]
  set κ := (Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans
    (Submodule.quotientProdEquiv (range f) (range g))
  set κ' := (Submodule.quotEquivOfEq _ _ (range_prodMap f' g')).trans
    (Submodule.quotientProdEquiv (range f') (range g'))
  have hκ (y : N) (y' : N') : κ.symm ((range f).mkQ y, (range g).mkQ y') =
      (range (f.prodMap g)).mkQ (y, y') := by
    rw [LinearEquiv.symm_apply_eq]
    simp [κ]
  have hκ' (y : Q) (y' : Q') : κ'.symm ((range f').mkQ y, (range g').mkQ y') =
      (range (f'.prodMap g')).mkQ (y, y') := by
    rw [LinearEquiv.symm_apply_eq]
    simp [κ']
  -- Read through `κ` and `κ'`, the isomorphism `e` is `a × b`.
  have hprod : κ.symm.trans e = (a.prodCongr b).trans κ'.symm := by
    ext ⟨y, y'⟩
    induction y using Submodule.Quotient.induction_on
    induction y' using Submodule.Quotient.induction_on
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]
    rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hκ, he, ha, hb, hκ']
    rfl
  rw [← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans, hprod]
  simp only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply,
    detLineCongr_prodCongr_detLineProdEquiv]

/-- The dual form of `detLineCongr_detLineCokerProdMap_prodCongr`, as it enters
`LinearMap.detLineProdMapEquiv`. -/
private theorem dualDistribEquiv_symm_dualMap_detLineCokerProdMap_prodCongr
    {e₂ : N →ₗ[K] Q} {e₂' : N' →ₗ[K] Q'}
    (e : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((Q × Q') ⧸ range (f'.prodMap g')))
    (a : (N ⧸ range f) ≃ₗ[K] (Q ⧸ range f')) (b : (N' ⧸ range g) ≃ₗ[K] (Q' ⧸ range g'))
    (he : ∀ x, e ((range (f.prodMap g)).mkQ x) = (range (f'.prodMap g')).mkQ (Prod.map e₂ e₂' x))
    (ha : ∀ y, a ((range f).mkQ y) = (range f').mkQ (e₂ y))
    (hb : ∀ y, b ((range g).mkQ y) = (range g').mkQ (e₂' y))
    (φ : Dual K (TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)))) :
    (dualDistribEquiv K _ _).symm
        ((detLineCokerProdMap f' g').dualMap (φ ∘ₗ e.detLineCongr.symm.toLinearMap)) =
      TensorProduct.congr a.detLineCongr.symm.dualMap b.detLineCongr.symm.dualMap
        ((dualDistribEquiv K _ _).symm ((detLineCokerProdMap f g).dualMap φ)) := by
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun t ↦ ?_
  have h := detLineCongr_detLineCokerProdMap_prodCongr f g e a b he ha hb
    ((TensorProduct.congr a.detLineCongr b.detLineCongr).symm t)
  rw [LinearEquiv.apply_symm_apply] at h
  -- `dualDistribEquiv` turns `congr` of dual maps into precomposition with `congr`.
  have hdd (ψ : Dual K (TauCeti.detLine K (N ⧸ range f)) ⊗[K]
      Dual K (TauCeti.detLine K (N' ⧸ range g)))
      (s : TauCeti.detLine K (Q ⧸ range f') ⊗[K] TauCeti.detLine K (Q' ⧸ range g')) :
      dualDistribEquiv K _ _ (TensorProduct.congr a.detLineCongr.symm.dualMap
          b.detLineCongr.symm.dualMap ψ) s =
        dualDistribEquiv K _ _ ψ
          ((TensorProduct.congr a.detLineCongr b.detLineCongr).symm s) := by
    induction ψ using TensorProduct.inductionOn with
    | add ψ ψ' hψ hψ' => simp only [map_add, LinearMap.add_apply, hψ, hψ']
    | tmul α β =>
      induction s using TensorProduct.inductionOn with
      | add s s' hs hs' => simp only [map_add, hs, hs']
      | tmul x y => simp
  rw [hdd, LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ← h, LinearEquiv.symm_apply_apply, LinearEquiv.dualMap_apply]

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

variable {f' : P →ₗ[K] Q} {g' : P' →ₗ[K] Q'} [FiniteDimensional K (ker f')]
  [FiniteDimensional K (ker g')] [FiniteDimensional K (Q ⧸ range f')]
  [FiniteDimensional K (Q' ⧸ range g')]

/-- **Naturality of the determinant line of a direct sum.** Commuting squares
`f' ∘ e₁ = e₂ ∘ f` and `g' ∘ e₁' = e₂' ∘ g` of linear isomorphisms give the commuting square
`(f'.prodMap g') ∘ (e₁ × e₁') = (e₂ × e₂') ∘ (f.prodMap g)`. Transport along it
(`LinearMap.detLineCongr`) corresponds, under `LinearMap.detLineProdMapEquiv`, to the tensor
product of the transports along the two squares. -/
theorem detLineProdMapEquiv_detLineCongr_prodCongr (e₁ : M ≃ₗ[K] P) (e₂ : N ≃ₗ[K] Q)
    (h : f' ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) (e₁' : M' ≃ₗ[K] P') (e₂' : N' ≃ₗ[K] Q')
    (h' : g' ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g) (x : (f.prodMap g).detLine) :
    detLineProdMapEquiv f' g' ((f.prodMap g).detLineCongr (e₁.prodCongr e₁') (e₂.prodCongr e₂')
        (by rw [LinearEquiv.coe_prodCongr, LinearEquiv.coe_prodCongr, prodMap_comp, prodMap_comp, h,
          h']) x) =
      TensorProduct.congr (f.detLineCongr e₁ e₂ h) (g.detLineCongr e₁' e₂' h')
        (detLineProdMapEquiv f g x) := by
  have hsq : (f'.prodMap g') ∘ₗ (e₁.prodCongr e₁').toLinearMap =
      (e₂.prodCongr e₂').toLinearMap ∘ₗ f.prodMap g := by
    rw [LinearEquiv.coe_prodCongr, LinearEquiv.coe_prodCongr, prodMap_comp, prodMap_comp, h, h']
  -- The isomorphisms of kernels and cokernels induced by the two squares.
  let kf := e₁.ofSubmodules _ _ (f.map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)
  let kg := e₁'.ofSubmodules _ _ (g.map_ker_eq_ker_of_comp_eq e₁'.surjective e₂'.injective h')
  let cf := Submodule.Quotient.equiv _ _ e₂ (f.map_range_eq_range_of_comp_eq e₁.surjective h)
  let cg := Submodule.Quotient.equiv _ _ e₂' (g.map_range_eq_range_of_comp_eq e₁'.surjective h')
  -- After the kernel and cokernel factors are compared, the rearrangement of the four factors
  -- commutes with the four transports.
  have key (c : K) (A : TauCeti.detLine K (ker f) ⊗[K] TauCeti.detLine K (ker g))
      (B : Dual K (TauCeti.detLine K (N ⧸ range f)) ⊗[K]
        Dual K (TauCeti.detLine K (N' ⧸ range g))) :
      tensorTensorTensorComm K _ _ _ _ ((c • TensorProduct.congr kf.detLineCongr kg.detLineCongr A)
          ⊗ₜ TensorProduct.congr cf.detLineCongr.symm.dualMap cg.detLineCongr.symm.dualMap B) =
        TensorProduct.congr (f.detLineCongr e₁ e₂ h) (g.detLineCongr e₁' e₂' h')
          (tensorTensorTensorComm K _ _ _ _ ((c • A) ⊗ₜ B)) := by
    simp only [← smul_tmul', map_smul]
    congr 1
    induction A using TensorProduct.inductionOn with
    | add A A' hA hA' => simp only [map_add, add_tmul, hA, hA']
    | tmul a b =>
      induction B using TensorProduct.inductionOn with
      | add B B' hB hB' => simp only [map_add, tmul_add, hB, hB']
      | tmul c d =>
        -- The dual factors agree: `e.dualMap ψ` is `ψ ∘ₗ e` by definition.
        simp only [tensorTensorTensorComm_tmul, congr_tmul, detLineCongr_tmul]
        congr 2
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul β φ =>
    simp only [detLineCongr_tmul, detLineProdMapEquiv, LinearEquiv.trans_apply, congr_tmul,
      LinearEquiv.smulOfNeZero_apply, map_smul]
    have hK := detLineKerProdMap_detLineCongr_prodCongr f g (e₁ := e₁.toLinearMap)
      (e₁' := e₁'.toLinearMap) ((e₁.prodCongr e₁').ofSubmodules _ _
        ((f.prodMap g).map_ker_eq_ker_of_comp_eq (e₁.prodCongr e₁').surjective
          (e₂.prodCongr e₂').injective hsq)) kf kg (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ ↦ rfl) β
    have hC := dualDistribEquiv_symm_dualMap_detLineCokerProdMap_prodCongr f g
      (e₂ := e₂.toLinearMap) (e₂' := e₂'.toLinearMap) (Submodule.Quotient.equiv _ _
        (e₂.prodCongr e₂') ((f.prodMap g).map_range_eq_range_of_comp_eq
          (e₁.prodCongr e₁').surjective hsq)) cf cg (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) φ
    have hs : (-1 : K) ^ (finrank K (Q ⧸ range f') * finrank K (ker g')) =
        (-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) := by
      rw [cf.finrank_eq, kg.finrank_eq]
    simp only [hK, hC, hs]
    exact key _ _ _

end LinearMap
