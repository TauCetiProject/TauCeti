/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Exact
public import TauCeti.LinearAlgebra.LinearMap.Comp
public import TauCeti.LinearAlgebra.Prod
public import TauCeti.LinearAlgebra.Quotient.Prod
import TauCeti.Algebra.Module.Equiv.Basic
import TauCeti.LinearAlgebra.Contraction
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.TensorProduct.Dual
import TauCeti.LinearAlgebra.TensorProduct.Separation

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

The product of two four-term exact sequences `0 → Aᵢ → Bᵢ → Cᵢ → Dᵢ → 0` is exact, and its
isomorphism `det (B₁ × B₂) ⊗ (det (C₁ × C₂))^* ≃ det (A₁ × A₂) ⊗ (det (D₁ × D₂))^*`
(`TauCeti.detLineFourTermEquiv`) is the product of the isomorphisms of the two sequences, read
through the isomorphism `TauCeti.detLineTensorDualProdEquiv` which gathers the determinant lines
and the dual lines of the two sequences, up to the Koszul sign
`(-1) ^ (dim A₂ * dim (range g₁) + dim (range g₂) * dim D₁)`
(`TauCeti.detLineFourTermEquiv_prodMap`). A Fredholm operator `T` stabilized by finitely many
directions `D : Λ → F` has the exact sequence `0 → ker T → ker (T.coprod D) → Λ → coker T → 0`
through which its determinant line is computed, so this product law is the step toward comparing
the stabilized determinant line of a direct sum of operators, stabilized by the direct sum of the
stabilizers, with those of the summands; that comparison is made in
`TauCeti.Analysis.Fredholm.DeterminantLine.DirectSum`.

The direct sum isomorphism is natural: for commuting squares of isomorphisms `(e₁, e₂)` from `f`
to `f'` and `(e₁', e₂')` from `g` to `g'`, transporting `det (f ⊕ g)` along `(e₁ × e₁', e₂ × e₂')`
is the tensor product of the transports of `det f` and `det g`, with no sign
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodCongr`). So a symmetry acting separately on
the summands of a split operator acts on its determinant line by the product of its actions on
the determinant lines of the summands.

For bijective maps all kernels and cokernels vanish and the Koszul sign is `1`: the direct sum
isomorphism sends the generator of `det (f ⊕ g)` given by bijectivity
(`LinearMap.detLineEquivOfBijective`) to the tensor product of the generators of `det f` and
`det g` (`LinearMap.detLineProdMapEquiv_detLineEquivOfBijective_symm_one`), so the trivializations
given by bijectivity multiply
(`LinearMap.detLineEquivOfBijective_detLineProdMapEquiv_symm_tmul`).

## Main declarations

* `TauCeti.detLineProdEquiv`: `det U ⊗ det W ≃ det (U × W)`, with its value
  `TauCeti.coe_detLineProdEquiv_tmul`, also on arbitrary lifts of the second factor
  (`TauCeti.coe_detLineProdEquiv_tmul_snd_comp`).
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
* `LinearMap.detLineProdMapEquiv_congr_detLineTensorDualProdEquiv`,
  `LinearMap.detLineProdMapEquiv_symm_tmul`: the direct sum isomorphism undoes
  `TauCeti.detLineTensorDualProdEquiv`, read through the splittings of kernel and cokernel, up to
  `(-1) ^ (dim (coker f) * dim (ker g))`.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodAssoc`: reassociating three summands involves no
  sign.
* `TauCeti.detLineDualProdEquiv`: the isomorphism `(det V₁)^* ⊗ (det V₂)^* ≃ (det (V₁ × V₂))^*`,
  with its value `TauCeti.detLineDualProdEquiv_tmul_apply`.
* `TauCeti.detLineTensorDualProdEquiv`: the isomorphism
  `(det U₁ ⊗ (det V₁)^*) ⊗ (det U₂ ⊗ (det V₂)^*) ≃ det (U₁ × U₂) ⊗ (det (V₁ × V₂))^*`.
* `TauCeti.detLineFourTermEquiv_prodMap`: the four-term isomorphism of a product of exact
  sequences is the product of the four-term isomorphisms, up to a Koszul sign.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodCongr`: naturality under products of commuting
  squares.
* `LinearMap.detLineEquivOfBijective_detLineProdMapEquiv_symm_tmul`: for bijective maps the
  trivializations given by bijectivity multiply.

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

/-- `TauCeti.detLineProdEquiv` sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to
`(u₁, 0) ∧ ⋯ ∧ (uₐ, 0) ∧ v₁ ∧ ⋯ ∧ v_c` for any lifts `vᵢ` of the `wᵢ` to `U × W`: the components of
the `vᵢ` in `U` do not contribute, since `(u₁, 0), …, (uₐ, 0)` already span `U × 0`. -/
theorem coe_detLineProdEquiv_tmul_snd_comp (u : Fin (finrank K U) → U)
    (v : Fin (finrank K W) → U × W) :
    (detLineProdEquiv K U W (exteriorPower.ιMulti K _ u ⊗ₜ
        exteriorPower.ιMulti K _ (LinearMap.snd K U W ∘ v)) : ExteriorAlgebra K (U × W)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (LinearMap.inl K U W ∘ u) v) :=
  coe_detLineShortExactEquiv_tmul LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective u v

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
  obtain ⟨s, rfl⟩ := (Module.finBasis K U).exists_smul_ιMulti_eq a
  obtain ⟨t, rfl⟩ := (Module.finBasis K W).exists_smul_ιMulti_eq b
  simp [← smul_tmul', ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti]

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
    rw [detLineCongr_prodCongr_detLineProdEquiv, LinearEquiv.detLineCongr_refl,
      ← LinearEquiv.rTensor, ← LinearEquiv.coe_rTensor, LinearEquiv.coe_coe]
  have hX' (s : detLine K U ⊗[K] detLine K (V × W)) :
      detLineProdEquiv K U X' (κ₂.symm.detLineCongr.toLinearMap.lTensor _ s) =
        ((LinearEquiv.refl K U).prodCongr κ₂.symm).detLineCongr (detLineProdEquiv K U _ s) := by
    rw [detLineCongr_prodCongr_detLineProdEquiv, LinearEquiv.detLineCongr_refl,
      ← LinearEquiv.lTensor, ← LinearEquiv.coe_lTensor, LinearEquiv.coe_coe]
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.rTensor_comp_apply,
    LinearMap.lTensor_comp_apply, hX, hX', ← detLineCongr_prodAssoc_detLineProdEquiv]
  simpa only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply,
    ← LinearEquiv.detLineCongr_symm, LinearEquiv.symm_apply_apply] using
    congr($(congrArg LinearEquiv.detLineCongr h)
      ((LinearEquiv.prodAssoc K U V W).detLineCongr (detLineProdEquiv K (U × V) W
        ((detLineProdEquiv K U V).toLinearMap.rTensor _ t))))

end Prod

section TensorDual

variable (K : Type*) [Field K] (U₁ V₁ U₂ V₂ : Type*) [AddCommGroup U₁] [Module K U₁]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup U₂] [Module K U₂] [AddCommGroup V₂] [Module K V₂]
  [FiniteDimensional K U₁] [FiniteDimensional K V₁] [FiniteDimensional K U₂]
  [FiniteDimensional K V₂]

/-- **The dual line of a product.** The isomorphism `(det V₁)^* ⊗ (det V₂)^* ≃ (det (V₁ × V₂))^*`
dual to `TauCeti.detLineProdEquiv`: the product of the functionals `φ₁` and `φ₂` takes the value
`φ₁ c₁ * φ₂ c₂` at the image of `c₁ ⊗ c₂` (`TauCeti.detLineDualProdEquiv_tmul_apply`). -/
def detLineDualProdEquiv :
    Dual K (detLine K V₁) ⊗[K] Dual K (detLine K V₂) ≃ₗ[K] Dual K (detLine K (V₁ × V₂)) :=
  dualDistribEquiv K _ _ ≪≫ₗ (detLineProdEquiv K V₁ V₂).symm.dualMap

/-- The product of two tensors of a determinant line with a dual determinant line:
`(det U₁ ⊗ (det V₁)^*) ⊗ (det U₂ ⊗ (det V₂)^*) ≃ det (U₁ × U₂) ⊗ (det (V₁ × V₂))^*`. It gathers
the two determinant lines and the two dual lines, with no sign, and identifies them by
`TauCeti.detLineProdEquiv` and `TauCeti.detLineDualProdEquiv`. It sends `(a₁ ⊗ φ₁) ⊗ (a₂ ⊗ φ₂)` to
`a ⊗ φ`, where `a` is the image of `a₁ ⊗ a₂` and `φ` is the image of `φ₁ ⊗ φ₂`
(`TauCeti.detLineTensorDualProdEquiv_tmul`). -/
def detLineTensorDualProdEquiv :
    (detLine K U₁ ⊗[K] Dual K (detLine K V₁)) ⊗[K] (detLine K U₂ ⊗[K] Dual K (detLine K V₂)) ≃ₗ[K]
      detLine K (U₁ × U₂) ⊗[K] Dual K (detLine K (V₁ × V₂)) :=
  TensorProduct.tensorTensorTensorComm K _ _ _ _ ≪≫ₗ
    TensorProduct.congr (detLineProdEquiv K U₁ U₂) (detLineDualProdEquiv K V₁ V₂)

variable {K U₁ V₁ U₂ V₂}

/-- The product of the functionals `φ₁` and `φ₂` under `TauCeti.detLineDualProdEquiv` takes the
value `φ₁ c₁ * φ₂ c₂` at the image of `c₁ ⊗ c₂` in `det (V₁ × V₂)`. -/
@[simp]
theorem detLineDualProdEquiv_tmul_apply (φ₁ : Dual K (detLine K V₁))
    (φ₂ : Dual K (detLine K V₂)) (c₁ : detLine K V₁) (c₂ : detLine K V₂) :
    detLineDualProdEquiv K V₁ V₂ (φ₁ ⊗ₜ φ₂) (detLineProdEquiv K V₁ V₂ (c₁ ⊗ₜ c₂)) =
      φ₁ c₁ * φ₂ c₂ := by
  rw [detLineDualProdEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    LinearEquiv.symm_apply_apply, dualDistribEquiv_tmul_tmul, mul_comm]

/-- `TauCeti.detLineTensorDualProdEquiv` on pure tensors. -/
@[simp]
theorem detLineTensorDualProdEquiv_tmul (a₁ : detLine K U₁) (φ₁ : Dual K (detLine K V₁))
    (a₂ : detLine K U₂) (φ₂ : Dual K (detLine K V₂)) :
    detLineTensorDualProdEquiv K U₁ V₁ U₂ V₂ ((a₁ ⊗ₜ φ₁) ⊗ₜ (a₂ ⊗ₜ φ₂)) =
      detLineProdEquiv K U₁ U₂ (a₁ ⊗ₜ a₂) ⊗ₜ detLineDualProdEquiv K V₁ V₂ (φ₁ ⊗ₜ φ₂) := by
  simp [detLineTensorDualProdEquiv]

/-- **Naturality of `TauCeti.detLineTensorDualProdEquiv`** in the determinant-line factors. For
isomorphisms `e₁ : U₁ ≃ U₁'` and `e₂ : U₂ ≃ U₂'`, the isomorphism induced by `e₁ × e₂` on
`det (U₁ × U₂)` takes the image of `t` to the image of `t` under `det e₁` and `det e₂`, the dual
factors being unchanged. -/
theorem rTensor_detLineCongr_prodCongr_detLineTensorDualProdEquiv {U₁' U₂' : Type*}
    [AddCommGroup U₁'] [Module K U₁'] [AddCommGroup U₂'] [Module K U₂'] [FiniteDimensional K U₁']
    [FiniteDimensional K U₂'] (e₁ : U₁ ≃ₗ[K] U₁') (e₂ : U₂ ≃ₗ[K] U₂')
    (t : (detLine K U₁ ⊗[K] Dual K (detLine K V₁)) ⊗[K]
      (detLine K U₂ ⊗[K] Dual K (detLine K V₂))) :
    LinearEquiv.rTensor _ (e₁.prodCongr e₂).detLineCongr
        (detLineTensorDualProdEquiv K U₁ V₁ U₂ V₂ t) =
      detLineTensorDualProdEquiv K U₁' V₁ U₂' V₂
        (TensorProduct.congr (LinearEquiv.rTensor _ e₁.detLineCongr)
          (LinearEquiv.rTensor _ e₂.detLineCongr) t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul x y =>
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [add_tmul, map_add, hx, hx']
    | tmul a φ =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp only [tmul_add, map_add, hy, hy']
      | tmul b ψ => simp [detLineCongr_prodCongr_detLineProdEquiv]

end TensorDual

section FourTerm

/-! ### Products of four-term exact sequences -/

variable {K : Type*} [Field K]

/-- If `b₁` and `b₂` are the exterior products of the appended families `p₁, q₁` and `p₂, q₂`, then
`(-1) ^ (m₂ * n₁)` times the image of `b₁ ⊗ b₂` in `det (V₁ × V₂)` is the exterior product of the
families `p₁, p₂` followed by `q₁, q₂`: the blocks `q₁` and `p₂` are exchanged. -/
private theorem coe_smul_detLineProdEquiv_tmul {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    {m₁ n₁ m₂ n₂ M N : ℕ} {b₁ : detLine K V₁} {b₂ : detLine K V₂} {p₁ : Fin m₁ → V₁}
    {q₁ : Fin n₁ → V₁} {p₂ : Fin m₂ → V₂} {q₂ : Fin n₂ → V₂}
    (hb₁ : (b₁ : ExteriorAlgebra K V₁) = ExteriorAlgebra.ιMulti K _ (Fin.append p₁ q₁))
    (hb₂ : (b₂ : ExteriorAlgebra K V₂) = ExteriorAlgebra.ιMulti K _ (Fin.append p₂ q₂))
    (hM : M = m₁ + m₂) (hN : N = n₁ + n₂) :
    (((-1 : K) ^ (m₂ * n₁) • detLineProdEquiv K V₁ V₂ (b₁ ⊗ₜ b₂) : detLine K (V₁ × V₂)) :
        ExteriorAlgebra K (V₁ × V₂)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append
        (Fin.append (LinearMap.inl K V₁ V₂ ∘ p₁) (LinearMap.inr K V₁ V₂ ∘ p₂) ∘ Fin.cast hM)
        (Fin.append (LinearMap.inl K V₁ V₂ ∘ q₁) (LinearMap.inr K V₁ V₂ ∘ q₂) ∘ Fin.cast hN)) := by
  rw [Submodule.coe_smul, coe_detLineProdEquiv_tmul_eq_mul, hb₁, hb₂]
  simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.ιMulti_comp_cast, map_mul,
    ExteriorAlgebra.map_apply_ιMulti, mul_assoc]
  -- Exchange the middle blocks `p₂` and `q₁` on the right.
  rw [← mul_assoc (ExteriorAlgebra.ιMulti K m₂ _),
    ExteriorAlgebra.ιMulti_mul_ιMulti_eq_neg_one_pow_smul (LinearMap.inr K V₁ V₂ ∘ p₂)
      (LinearMap.inl K V₁ V₂ ∘ q₁)]
  simp [mul_assoc, mul_comm n₁ m₂]

variable {A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Type*} [AddCommGroup A₁] [Module K A₁] [AddCommGroup B₁]
  [Module K B₁] [AddCommGroup C₁] [Module K C₁] [AddCommGroup D₁] [Module K D₁] [AddCommGroup A₂]
  [Module K A₂] [AddCommGroup B₂] [Module K B₂] [AddCommGroup C₂] [Module K C₂] [AddCommGroup D₂]
  [Module K D₂] [FiniteDimensional K A₁] [FiniteDimensional K B₁] [FiniteDimensional K C₁]
  [FiniteDimensional K D₁] [FiniteDimensional K A₂] [FiniteDimensional K B₂]
  [FiniteDimensional K C₂] [FiniteDimensional K D₂] {f₁ : A₁ →ₗ[K] B₁} {g₁ : B₁ →ₗ[K] C₁}
  {h₁ : C₁ →ₗ[K] D₁} {f₂ : A₂ →ₗ[K] B₂} {g₂ : B₂ →ₗ[K] C₂} {h₂ : C₂ →ₗ[K] D₂}
  (hf₁ : Function.Injective f₁) (hfg₁ : Function.Exact f₁ g₁) (hgh₁ : Function.Exact g₁ h₁)
  (hh₁ : Function.Surjective h₁) (hf₂ : Function.Injective f₂) (hfg₂ : Function.Exact f₂ g₂)
  (hgh₂ : Function.Exact g₂ h₂) (hh₂ : Function.Surjective h₂)

include hf₁ hfg₁ hgh₁ hh₁ hf₂ hfg₂ hgh₂ hh₂ in
/-- `TauCeti.detLineFourTermEquiv_prodMap` on the exterior products of
`TauCeti.detLineFourTermEquiv_tmul`. -/
private theorem detLineFourTermEquiv_prodMap_tmul (u₁ : Fin (finrank K A₁) → A₁)
    (v₁ : Fin (finrank K (LinearMap.range g₁)) → B₁) (z₁ : Fin (finrank K D₁) → C₁)
    (u₂ : Fin (finrank K A₂) → A₂) (v₂ : Fin (finrank K (LinearMap.range g₂)) → B₂)
    (z₂ : Fin (finrank K D₂) → C₂) {β₁ : detLine K B₁} {β₂ : detLine K B₂} {γ₁ : detLine K C₁}
    {γ₂ : detLine K C₂}
    (hβ₁ : (β₁ : ExteriorAlgebra K B₁) = ExteriorAlgebra.ιMulti K _ (Fin.append (f₁ ∘ u₁) v₁))
    (hβ₂ : (β₂ : ExteriorAlgebra K B₂) = ExteriorAlgebra.ιMulti K _ (Fin.append (f₂ ∘ u₂) v₂))
    (hγ₁ : (γ₁ : ExteriorAlgebra K C₁) = ExteriorAlgebra.ιMulti K _ (Fin.append (g₁ ∘ v₁) z₁))
    (hγ₂ : (γ₂ : ExteriorAlgebra K C₂) = ExteriorAlgebra.ιMulti K _ (Fin.append (g₂ ∘ v₂) z₂))
    {ξ₁ : Dual K (detLine K D₁)} {ξ₂ : Dual K (detLine K D₂)}
    (hξ₁ : ξ₁ (exteriorPower.ιMulti K _ (h₁ ∘ z₁)) = 1)
    (hξ₂ : ξ₂ (exteriorPower.ιMulti K _ (h₂ ∘ z₂)) = 1) (φ₁ : Dual K (detLine K C₁))
    (φ₂ : Dual K (detLine K C₂)) :
    detLineFourTermEquiv (f := f₁.prodMap f₂) (g := g₁.prodMap g₂) (h := h₁.prodMap h₂)
        (hf₁.prodMap hf₂) (Function.Exact.prodMap hfg₁ hfg₂) (Function.Exact.prodMap hgh₁ hgh₂)
        (hh₁.prodMap hh₂)
        (detLineTensorDualProdEquiv K B₁ C₁ B₂ C₂ ((β₁ ⊗ₜ φ₁) ⊗ₜ (β₂ ⊗ₜ φ₂))) =
      (-1 : K) ^ (finrank K A₂ * finrank K (LinearMap.range g₁) +
          finrank K (LinearMap.range g₂) * finrank K D₁) •
        detLineTensorDualProdEquiv K A₁ D₁ A₂ D₂
          (detLineFourTermEquiv hf₁ hfg₁ hgh₁ hh₁ (β₁ ⊗ₜ φ₁) ⊗ₜ
            detLineFourTermEquiv hf₂ hfg₂ hgh₂ hh₂ (β₂ ⊗ₜ φ₂)) := by
  -- Plan: evaluate both sides with `TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul`, for the
  -- product sequence with the interleaved families `u`, `v`, `z` below and for each factor.
  -- The exterior products of the interleaved families are `± β₁ β₂` and `± γ₁ γ₂`
  -- (`coe_smul_detLineProdEquiv_tmul`), and these two signs give the stated one.
  -- The families of the product sequence.
  have hA : finrank K (A₁ × A₂) = finrank K A₁ + finrank K A₂ := Module.finrank_prod
  have hR : finrank K (LinearMap.range (g₁.prodMap g₂)) =
      finrank K (LinearMap.range g₁) + finrank K (LinearMap.range g₂) := by
    rw [LinearMap.range_prodMap, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]
  have hD : finrank K (D₁ × D₂) = finrank K D₁ + finrank K D₂ := Module.finrank_prod
  set u := Fin.append (LinearMap.inl K A₁ A₂ ∘ u₁) (LinearMap.inr K A₁ A₂ ∘ u₂) ∘ Fin.cast hA
  set v := Fin.append (LinearMap.inl K B₁ B₂ ∘ v₁) (LinearMap.inr K B₁ B₂ ∘ v₂) ∘ Fin.cast hR
  set z := Fin.append (LinearMap.inl K C₁ C₂ ∘ z₁) (LinearMap.inr K C₁ C₂ ∘ z₂) ∘ Fin.cast hD
  set s := finrank K A₂ * finrank K (LinearMap.range g₁)
  set s' := finrank K (LinearMap.range g₂) * finrank K D₁
  -- The exterior products of the product sequence. They are introduced as opaque variables:
  -- unification would otherwise unfold their definitions, which is too slow.
  obtain ⟨β, hβdef⟩ : ∃ β : detLine K (B₁ × B₂),
      β = (-1 : K) ^ s • detLineProdEquiv K B₁ B₂ (β₁ ⊗ₜ β₂) := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : detLine K (C₁ × C₂),
      γ = (-1 : K) ^ s' • detLineProdEquiv K C₁ C₂ (γ₁ ⊗ₜ γ₂) := ⟨_, rfl⟩
  obtain ⟨Ξ, hΞdef⟩ : ∃ Ξ : Dual K (detLine K (D₁ × D₂)),
      Ξ = detLineDualProdEquiv K D₁ D₂ (ξ₁ ⊗ₜ ξ₂) := ⟨_, rfl⟩
  have hβ : (β : ExteriorAlgebra K (B₁ × B₂)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (⇑(f₁.prodMap f₂) ∘ u) v) := by
    rw [hβdef, ← Function.comp_assoc, LinearMap.prodMap_comp_append]
    exact coe_smul_detLineProdEquiv_tmul hβ₁ hβ₂ hA hR
  have hγ : (γ : ExteriorAlgebra K (C₁ × C₂)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (⇑(g₁.prodMap g₂) ∘ v) z) := by
    rw [hγdef, ← Function.comp_assoc, LinearMap.prodMap_comp_append]
    exact coe_smul_detLineProdEquiv_tmul hγ₁ hγ₂ hR hD
  have hu : exteriorPower.ιMulti K _ u =
      detLineProdEquiv K A₁ A₂ (exteriorPower.ιMulti K _ u₁ ⊗ₜ exteriorPower.ιMulti K _ u₂) :=
    Subtype.ext (by rw [coe_detLineProdEquiv_tmul, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_comp_cast])
  have hξ : Ξ (exteriorPower.ιMulti K _ (⇑(h₁.prodMap h₂) ∘ z)) = 1 := by
    have hz : exteriorPower.ιMulti K _ (⇑(h₁.prodMap h₂) ∘ z) =
        detLineProdEquiv K D₁ D₂
          (exteriorPower.ιMulti K _ (h₁ ∘ z₁) ⊗ₜ exteriorPower.ιMulti K _ (h₂ ∘ z₂)) :=
      Subtype.ext (by rw [coe_detLineProdEquiv_tmul, exteriorPower.ιMulti_apply_coe,
        ← Function.comp_assoc, LinearMap.prodMap_comp_append, ExteriorAlgebra.ιMulti_comp_cast])
    rw [hΞdef, hz, detLineDualProdEquiv_tmul_apply, hξ₁, hξ₂, mul_one]
  have hsq (n : ℕ) : (-1 : K) ^ n * (-1) ^ n = 1 := by simp [← mul_pow]
  have hββ : detLineProdEquiv K B₁ B₂ (β₁ ⊗ₜ β₂) = (-1 : K) ^ s • β := by
    rw [hβdef, smul_smul, hsq, one_smul]
  have hγγ : detLineProdEquiv K C₁ C₂ (γ₁ ⊗ₜ γ₂) = (-1 : K) ^ s' • γ := by
    rw [hγdef, smul_smul, hsq, one_smul]
  have e := detLineFourTermEquiv_tmul_eq_smul_tmul (f := f₁.prodMap f₂) (g := g₁.prodMap g₂)
      (h := h₁.prodMap h₂) (hf₁.prodMap hf₂) (Function.Exact.prodMap hfg₁ hfg₂)
      (Function.Exact.prodMap hgh₁ hgh₂) (hh₁.prodMap hh₂) u v z hβ hγ
      (detLineDualProdEquiv K C₁ C₂ (φ₁ ⊗ₜ φ₂)) hξ
  have e₁ := detLineFourTermEquiv_tmul_eq_smul_tmul hf₁ hfg₁ hgh₁ hh₁ u₁ v₁ z₁ hβ₁ hγ₁ φ₁ hξ₁
  have e₂ := detLineFourTermEquiv_tmul_eq_smul_tmul hf₂ hfg₂ hgh₂ hh₂ u₂ v₂ z₂ hβ₂ hγ₂ φ₂ hξ₂
  have hφ : detLineDualProdEquiv K C₁ C₂ (φ₁ ⊗ₜ φ₂) γ = (-1 : K) ^ s' * (φ₁ γ₁ * φ₂ γ₂) := by
    rw [← detLineDualProdEquiv_tmul_apply, hγγ, LinearMap.map_smul, smul_eq_mul,
      ← mul_assoc, hsq, one_mul]
  rw [detLineTensorDualProdEquiv_tmul, hββ, ← smul_tmul', LinearEquiv.map_smul, e]
  simp only [e₁, e₂, TensorProduct.smul_tmul_smul, LinearEquiv.map_smul,
    detLineTensorDualProdEquiv_tmul, ← hu]
  rw [hφ, smul_smul, smul_smul, pow_add, hΞdef, mul_assoc]

include hf₁ hfg₁ hgh₁ hh₁ hf₂ hfg₂ hgh₂ hh₂ in
/-- **The four-term isomorphism of a product of exact sequences.** The product of two four-term
exact sequences `0 → Aᵢ → Bᵢ → Cᵢ → Dᵢ → 0` is exact, and its isomorphism
`det (B₁ × B₂) ⊗ (det (C₁ × C₂))^* ≃ det (A₁ × A₂) ⊗ (det (D₁ × D₂))^*`
(`TauCeti.detLineFourTermEquiv`) is the product of the isomorphisms of the two sequences, read
through `TauCeti.detLineTensorDualProdEquiv`, up to the sign
`(-1) ^ (dim A₂ * dim (range g₁) + dim (range g₂) * dim D₁)`. The isomorphism of a sequence puts
the directions of `A` before those spanning the range of `g` in `det B`, and those spanning the
range of `g` before the lifts of `D` in `det C`; the sign comes from interleaving the blocks of the
two sequences. -/
theorem detLineFourTermEquiv_prodMap (x₁ : detLine K B₁ ⊗[K] Dual K (detLine K C₁))
    (x₂ : detLine K B₂ ⊗[K] Dual K (detLine K C₂)) :
    detLineFourTermEquiv (f := f₁.prodMap f₂) (g := g₁.prodMap g₂) (h := h₁.prodMap h₂)
        (hf₁.prodMap hf₂) (Function.Exact.prodMap hfg₁ hfg₂) (Function.Exact.prodMap hgh₁ hgh₂)
        (hh₁.prodMap hh₂)
        (detLineTensorDualProdEquiv K B₁ C₁ B₂ C₂ (x₁ ⊗ₜ x₂)) =
      (-1 : K) ^ (finrank K A₂ * finrank K (LinearMap.range g₁) +
          finrank K (LinearMap.range g₂) * finrank K D₁) •
        detLineTensorDualProdEquiv K A₁ D₁ A₂ D₂
          (detLineFourTermEquiv hf₁ hfg₁ hgh₁ hh₁ x₁ ⊗ₜ
            detLineFourTermEquiv hf₂ hfg₂ hgh₂ hh₂ x₂) := by
  -- Exterior products of each sequence, the first spanning `det Bᵢ`, evaluating both sides.
  obtain ⟨v₁, z₁, β₁, γ₁, ξ₁, hβ₁, hγ₁, hξ₁, hspan₁⟩ :=
    exists_spanning_ιMulti_append hf₁ hfg₁ hgh₁ hh₁
  obtain ⟨v₂, z₂, β₂, γ₂, ξ₂, hβ₂, hγ₂, hξ₂, hspan₂⟩ :=
    exists_spanning_ιMulti_append hf₂ hfg₂ hgh₂ hh₂
  -- Both sides are linear in `x₁` and `x₂`.
  induction x₁ using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [TensorProduct.add_tmul, map_add, hx, hx', smul_add]
  | tmul y₁ φ₁ =>
    induction x₂ using TensorProduct.inductionOn with
    | add x x' hx hx' =>
      simp only [TensorProduct.tmul_add, map_add, hx, hx', smul_add]
    | tmul y₂ φ₂ =>
      obtain ⟨r₁, rfl⟩ := hspan₁ y₁
      obtain ⟨r₂, rfl⟩ := hspan₂ y₂
      simp only [← smul_tmul', TensorProduct.tmul_smul, LinearEquiv.map_smul, smul_smul,
        detLineFourTermEquiv_prodMap_tmul hf₁ hfg₁ hgh₁ hh₁ hf₂ hfg₂ hgh₂ hh₂ _ v₁ z₁ _ v₂ z₂
          hβ₁ hβ₂ hγ₁ hγ₂ hξ₁ hξ₂]
      congr 1
      ring

end FourTerm

end TauCeti

namespace LinearMap

open TauCeti

variable {K : Type*} [Field K] {M N M' N' : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
  (f : M →ₗ[K] N) (g : M' →ₗ[K] N')

variable {M'' N'' : Type*} [AddCommGroup M''] [Module K M''] [AddCommGroup N''] [Module K N'']
  (k : M'' →ₗ[K] N'')

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
  rw [LinearEquiv.coe_detLineCongr_of_coe_eq_ιMulti _ hβ, coe_detLineProdEquiv_tmul]
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
  -- Read through the kernel splittings, the exchange `e` is the swap of `ker f × ker g`.
  have hswap : (kerProdMapEquiv f g).symm.trans (e.trans (kerProdMapEquiv g f)) =
      LinearEquiv.prodComm K (ker f) (ker g) := by
    ext x <;> simp [he]
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
      (cokerProdMapEquiv f' g').symm (ε ((range f).mkQ a, (range g).mkQ b)))
    (t : TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g)) :
    e.detLineCongr (detLineCokerProdMap f g t) =
      detLineCokerProdMap f' g'
        ((detLineProdEquiv K _ _).symm (ε.detLineCongr (detLineProdEquiv K _ _ t))) := by
  -- Unfold both cokernel isomorphisms.
  simp only [detLineCokerProdMap, LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm,
    LinearEquiv.apply_symm_apply]
  set κ := cokerProdMapEquiv f g
  set κ' := cokerProdMapEquiv f' g'
  have hκ (a : N) (b : N') : κ.symm ((range f).mkQ a, (range g).mkQ b) =
      (range (f.prodMap g)).mkQ (a, b) :=
    cokerProdMapEquiv_symm_mk f g a b
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

/-- **The direct sum isomorphism through the splittings of kernel and cokernel.** Let `eA`
identify `ker f × ker g` with the kernel of `f.prodMap g` and `eD` identify
`coker f × coker g` with its cokernel, both componentwise. Gathering
`(det (ker f) ⊗ (det (coker f))^*) ⊗ (det (ker g) ⊗ (det (coker g))^*)` into
`det (ker f × ker g) ⊗ (det (coker f × coker g))^*` by `TauCeti.detLineTensorDualProdEquiv`,
which carries no sign, and transporting along `eA` and `eD` gives an element of the determinant
line of `f.prodMap g`; `LinearMap.detLineProdMapEquiv` sends it back to the original tensor times
the Koszul sign `(-1) ^ (dim (coker f) * dim (ker g))` of moving `(det (coker f))^*` past
`det (ker g)`. -/
theorem detLineProdMapEquiv_congr_detLineTensorDualProdEquiv
    (eA : (ker f × ker g) ≃ₗ[K] ker (f.prodMap g))
    (heA : ∀ x, (eA x : M × M') = ((x.1 : M), (x.2 : M')))
    (eD : ((N ⧸ range f) × (N' ⧸ range g)) ≃ₗ[K] (N × N') ⧸ range (f.prodMap g))
    (heD : ∀ y y', eD ((range f).mkQ y, (range g).mkQ y') = (range (f.prodMap g)).mkQ (y, y'))
    (y₁ : f.detLine) (y₂ : g.detLine) :
    detLineProdMapEquiv f g (TensorProduct.congr eA.detLineCongr eD.detLineCongr.symm.dualMap
        (detLineTensorDualProdEquiv K _ _ _ _ (y₁ ⊗ₜ y₂))) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) • (y₁ ⊗ₜ y₂) := by
  -- Read through the splittings used by `detLineProdMapEquiv`, `eA` and `eD` are identities.
  have hA : eA.trans (kerProdMapEquiv f g) = LinearEquiv.refl K _ := by
    ext x <;> simp [heA]
  have hD : (cokerProdMapEquiv f g).symm.trans eD.symm = LinearEquiv.refl K _ := by
    simp only [Submodule.mkQ_apply] at heD
    refine LinearEquiv.ext fun ⟨a, b⟩ ↦ ?_
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    simp [LinearEquiv.symm_apply_eq, heD]
  induction y₁ using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx', smul_add]
  | tmul a₁ φ₁ =>
    induction y₂ using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [TensorProduct.tmul_add, map_add, hx, hx', smul_add]
    | tmul a₂ φ₂ =>
      simp only [detLineTensorDualProdEquiv_tmul, TensorProduct.congr_tmul, detLineProdMapEquiv,
        LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, map_smul, detLineKerProdMap,
        detLineCokerProdMap]
      have hA' := LinearEquiv.congr_fun (congrArg LinearEquiv.detLineCongr hA)
        (detLineProdEquiv K _ _ (a₁ ⊗ₜ a₂))
      have hD' (t : TauCeti.detLine K (N ⧸ range f) ⊗[K] TauCeti.detLine K (N' ⧸ range g)) :=
        LinearEquiv.congr_fun (congrArg LinearEquiv.detLineCongr hD) (detLineProdEquiv K _ _ t)
      simp only [LinearEquiv.detLineCongr_trans, LinearEquiv.detLineCongr_refl,
        LinearEquiv.trans_apply, LinearEquiv.refl_apply] at hA' hD'
      have hφ : ((detLineProdEquiv K (N ⧸ range f) (N' ⧸ range g)).trans
            (cokerProdMapEquiv f g).detLineCongr.symm).dualMap
          (eD.detLineCongr.symm.dualMap (detLineDualProdEquiv K _ _ (φ₁ ⊗ₜ φ₂))) =
          dualDistribEquiv K _ _ (φ₁ ⊗ₜ φ₂) := by
        refine LinearMap.ext fun t ↦ ?_
        simp only [LinearEquiv.dualMap_apply, LinearEquiv.trans_apply,
          LinearEquiv.detLineCongr_symm, hD', detLineDualProdEquiv, LinearEquiv.symm_apply_apply]
      rw [hφ, LinearEquiv.symm_apply_apply]
      simp only [hA', LinearEquiv.symm_apply_apply, ← smul_tmul', map_smul,
        tensorTensorTensorComm_tmul]

/-- The inverse form of `LinearMap.detLineProdMapEquiv_congr_detLineTensorDualProdEquiv`: the
inverse of the direct sum isomorphism is `TauCeti.detLineTensorDualProdEquiv` read through
componentwise splittings `eA` and `eD` of the kernel and cokernel of `f.prodMap g`, up to the sign
`(-1) ^ (dim (coker f) * dim (ker g))`. -/
theorem detLineProdMapEquiv_symm_tmul
    (eA : (ker f × ker g) ≃ₗ[K] ker (f.prodMap g))
    (heA : ∀ x, (eA x : M × M') = ((x.1 : M), (x.2 : M')))
    (eD : ((N ⧸ range f) × (N' ⧸ range g)) ≃ₗ[K] (N × N') ⧸ range (f.prodMap g))
    (heD : ∀ y y', eD ((range f).mkQ y, (range g).mkQ y') = (range (f.prodMap g)).mkQ (y, y'))
    (y₁ : f.detLine) (y₂ : g.detLine) :
    (detLineProdMapEquiv f g).symm (y₁ ⊗ₜ y₂) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) •
        TensorProduct.congr eA.detLineCongr eD.detLineCongr.symm.dualMap
          (detLineTensorDualProdEquiv K _ _ _ _ (y₁ ⊗ₜ y₂)) := by
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.map_smul,
    detLineProdMapEquiv_congr_detLineTensorDualProdEquiv f g eA heA eD heD, smul_smul,
    ← pow_add, ← two_mul, (even_two_mul _).neg_one_pow, one_smul]

/-- The direct sum of nonzero elements of determinant lines is nonzero. -/
theorem detLineProdMapEquiv_symm_tmul_ne_zero {y₁ : f.detLine} {y₂ : g.detLine} (hy₁ : y₁ ≠ 0)
    (hy₂ : y₂ ≠ 0) : (detLineProdMapEquiv f g).symm (y₁ ⊗ₜ y₂) ≠ 0 :=
  (LinearEquiv.map_ne_zero_iff _).2 (TauCeti.tmul_ne_zero hy₁ hy₂)

/-- The direct sum of nonzero elements of determinant lines, multiplied by a sign `(-1) ^ n`, is
nonzero. -/
theorem neg_one_pow_smul_detLineProdMapEquiv_symm_tmul_ne_zero (n : ℕ) {y₁ : f.detLine}
    {y₂ : g.detLine} (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    (-1 : K) ^ n • (detLineProdMapEquiv f g).symm (y₁ ⊗ₜ y₂) ≠ 0 :=
  smul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (detLineProdMapEquiv_symm_tmul_ne_zero f g hy₁ hy₂)

/-- **The direct sum of the generators of bijective maps.** For bijective maps `f` and `g`, the
direct sum isomorphism sends the generator of `det (f.prodMap g)` given by bijectivity
(`LinearMap.detLineEquivOfBijective`) to the tensor product of the generators of `det f` and
`det g`. All kernels and cokernels vanish, so the Koszul sign is `1`. -/
theorem detLineProdMapEquiv_detLineEquivOfBijective_symm_one (hf : Function.Bijective f)
    (hg : Function.Bijective g) :
    detLineProdMapEquiv f g ((detLineEquivOfBijective (hf.prodMap hg)).symm 1) =
      (detLineEquivOfBijective hf).symm 1 ⊗ₜ (detLineEquivOfBijective hg).symm 1 := by
  have hkf := finrank_ker_eq_zero_of_injective hf.1
  have hkg := finrank_ker_eq_zero_of_injective hg.1
  have hcf := finrank_quotient_range_eq_zero_of_surjective hf.2
  have hcg := finrank_quotient_range_eq_zero_of_surjective hg.2
  have hfg : Function.Bijective (f.prodMap g) := hf.prodMap hg
  have hk := finrank_ker_eq_zero_of_injective hfg.1
  have hc := finrank_quotient_range_eq_zero_of_surjective hfg.2
  rw [← LinearEquiv.eq_symm_apply, LinearEquiv.symm_apply_eq,
    detLineEquivOfBijective_symm_one_eq_ιMulti_tmul hf,
    detLineEquivOfBijective_symm_one_eq_ιMulti_tmul hg,
    detLineProdMapEquiv_symm_tmul f g (kerProdMapEquiv f g).symm
      (coe_kerProdMapEquiv_symm_apply f g) (cokerProdMapEquiv f g).symm
      (cokerProdMapEquiv_symm_mk f g),
    show (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) = 1 by simp [hcf],
    one_smul, TauCeti.detLineTensorDualProdEquiv_tmul, congr_tmul]
  -- The kernel factor is the empty exterior product of the zero kernel of `f.prodMap g`.
  have hA : (kerProdMapEquiv f g).symm.detLineCongr (TauCeti.detLineProdEquiv K _ _
      (exteriorPower.ιMulti K _ 0 ⊗ₜ exteriorPower.ιMulti K _ 0)) =
        exteriorPower.ιMulti K _ (Fin.elim0 ∘ Fin.cast hk) := by
    refine Subtype.ext ?_
    rw [LinearEquiv.coe_detLineCongr_of_coe_eq_ιMulti _ (TauCeti.coe_detLineProdEquiv_tmul _ _),
      exteriorPower.ιMulti_apply_coe,
      ← TauCeti.ExteriorAlgebra.ιMulti_comp_cast
        (show 0 = finrank K (ker f) + finrank K (ker g) by omega),
      ExteriorAlgebra.ιMulti_zero_apply, ← TauCeti.ExteriorAlgebra.ιMulti_comp_cast hk.symm,
      ExteriorAlgebra.ιMulti_zero_apply]
  -- The cokernel factor is evaluated at the empty exterior product of the zero cokernel.
  have hγ : (cokerProdMapEquiv f g).symm.detLineCongr.symm
      (exteriorPower.ιMulti K _ (Fin.elim0 ∘ Fin.cast hc)) =
        TauCeti.detLineProdEquiv K _ _ ((TauCeti.detLineEquivOfFinrankEqZero hcf).symm 1 ⊗ₜ
          (TauCeti.detLineEquivOfFinrankEqZero hcg).symm 1) := by
    refine Subtype.ext ?_
    rw [LinearEquiv.detLineCongr_symm, LinearEquiv.coe_detLineCongr_of_coe_eq_ιMulti _
        (exteriorPower.ιMulti_apply_coe _ _ _), TauCeti.detLineEquivOfFinrankEqZero_symm_one,
      TauCeti.detLineEquivOfFinrankEqZero_symm_one, TauCeti.coe_detLineProdEquiv_tmul,
      ← TauCeti.ExteriorAlgebra.ιMulti_comp_cast hc.symm, ExteriorAlgebra.ιMulti_zero_apply,
      ← TauCeti.ExteriorAlgebra.ιMulti_comp_cast
        (show 0 = finrank K (N ⧸ range f) + finrank K (N' ⧸ range g) by omega),
      ExteriorAlgebra.ιMulti_zero_apply]
  rw [hA, detLineEquivOfBijective_tmul_ιMulti hfg _ _ (Fin.elim0 ∘ Fin.cast hc),
    LinearEquiv.dualMap_apply, hγ, TauCeti.detLineDualProdEquiv_tmul_apply]
  simp

/-- **Bijective trivializations multiply.** For bijective maps `f` and `g`, reading the direct sum
of `x ∈ det f` and `y ∈ det g` in the trivialization of `det (f.prodMap g)` given by bijectivity
gives the product of the readings of `x` and `y` (`LinearMap.detLineEquivOfBijective`). So the
direct sum isomorphism carries the orientations given by bijectivity to the orientation given by
bijectivity. -/
theorem detLineEquivOfBijective_detLineProdMapEquiv_symm_tmul (hf : Function.Bijective f)
    (hg : Function.Bijective g) (x : f.detLine) (y : g.detLine) :
    detLineEquivOfBijective (hf.prodMap hg) ((detLineProdMapEquiv f g).symm (x ⊗ₜ y)) =
      detLineEquivOfBijective hf x * detLineEquivOfBijective hg y := by
  -- Every element of the determinant line of a bijective map is a multiple of its generator.
  have hx : x = detLineEquivOfBijective hf x • (detLineEquivOfBijective hf).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hy : y = detLineEquivOfBijective hg y • (detLineEquivOfBijective hg).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  rw [hx, hy, smul_tmul_smul, map_smul,
    ← detLineProdMapEquiv_detLineEquivOfBijective_symm_one f g hf hg]
  simp

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
  -- Read through the kernel splittings, the isomorphism `e` is the product of the kernel
  -- isomorphisms.
  have hκ : (kerProdMapEquiv f g).symm.trans (e.trans (kerProdMapEquiv f' g')) =
      (e₁.ofSubmodules _ _ (f.map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective hf)).prodCongr
        (e₁'.ofSubmodules _ _ (g.map_ker_eq_ker_of_comp_eq e₁'.surjective e₂'.injective hg)) := by
    ext x <;> simp [he]
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
      (dualDistribEquiv_map_symm_dualMap_apply
        (Submodule.Quotient.equiv _ _ e₂
          (f.map_range_eq_range_of_comp_eq e₁.surjective hf)).detLineCongr
        (Submodule.Quotient.equiv _ _ e₂'
          (g.map_range_eq_range_of_comp_eq e₁'.surjective hg)).detLineCongr) φ
    rw [detLineCongrKerCoker_tmul]
    simp only [detLineProdMapEquiv, LinearEquiv.trans_apply, congr_tmul,
      LinearEquiv.smulOfNeZero_apply, map_smul]
    -- The Koszul signs agree, the dimensions being preserved by the isomorphisms.
    have hs : (-1 : K) ^ (finrank K (Q ⧸ range f') * finrank K (ker g')) =
        (-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) := by
      rw [(e₁'.ofSubmodules _ _
          (g.map_ker_eq_ker_of_comp_eq e₁'.surjective e₂'.injective hg)).finrank_eq,
        (Submodule.Quotient.equiv _ _ e₂
          (f.map_range_eq_range_of_comp_eq e₁.surjective hf)).finrank_eq]
    -- Compare the kernel factors, the signs and the dual cokernel factors, then regroup.
    exact (congrArg (tensorTensorTensorComm K _ _ _ _) (congrArg₂ (· ⊗ₜ ·) (congrArg₂ (· • ·) hs
      (detLineKerProdMap_detLineCongr_prodCongr f g e₁ e₂ e₁' e₂' hf hg k hk β)) hD)).trans
      ((tensorTensorTensorComm_smul_map_tmul_map _ _ _ _ _ _ _).trans
        (congrArg₂ (fun F G ↦ TensorProduct.map F G _) (toLinearMap_detLineCongr f e₁ e₂ hf)
          (toLinearMap_detLineCongr g e₁' e₂' hg)).symm)

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
  rw [detLineCongr_eq_detLineCongrKerCoker]
  exact detLineProdMapEquiv_detLineCongrKerCoker f g e₁ e₂ e₁' e₂' hf hg _
    (fun _ ↦ by simp) _ (fun _ ↦ by simp) x

end Naturality

section Assoc

variable [FiniteDimensional K (ker k)] [FiniteDimensional K (N'' ⧸ range k)]

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
    simp only [LinearEquiv.toLinearMap_smulOfNeZero, LinearMap.comp_smul, LinearMap.comp_id,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, LinearMap.smul_apply,
      LinearEquiv.smulOfNeZero_apply, map_smul, hK, smul_smul]
    rw [← pow_add, ← pow_add]
    congr 2
    rw [finrank_quotient_range_prodMap, finrank_ker_prodMap]
    ring

end Assoc

end LinearMap
