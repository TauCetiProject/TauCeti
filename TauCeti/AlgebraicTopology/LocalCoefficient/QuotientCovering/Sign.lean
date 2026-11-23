/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Exact
public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Permutation

/-!
# The local system associated to the sign representation of `ℤˣ`

Let `p : E ⟶ B` be the quotient covering map of an action of `ℤˣ = {1, -1}` on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`, and let `σ` be the action of `-1`. Then `p` is a double cover:
`σ` has no fixed point (`IsQuotientCoveringMap.apply_ne_self_of_forall_eq_neg_one_smul`) and the
fibre through `e` is `{e, σ e}` (`IsQuotientCoveringMap.eq_or_eq_of_apply_eq`). For a commutative
ring `k`, the sign representation of `ℤˣ` on `k`, in which `-1` acts by `-1`, is
`Rep.of (Representation.ofDistribMulAction k ℤˣ k)`. This file identifies the local system on `B`
associated to it (`IsQuotientCoveringMap.associatedLocalSystem`), whose fibre over `x` is the module
of coinvariants `(k ⊗ k[p⁻¹ x])_{ℤˣ}`, with the sign local system of `σ`
(`IsCoveringMap.signLocalSystem`), whose fibre over `x` is the module of functions on `p⁻¹ x`
changing sign under `σ`:

`L_sign ≅ sign(σ)`

(`IsQuotientCoveringMap.associatedLocalSystemSignIso`). The isomorphism sends the class of `a ⊗ f`,
for a formal sum `f` of sheets over `x`, to `a` times the antisymmetrization `e ↦ f e - f (σ e)` of
`f` (`IsCoveringMap.permutationLocalSystemToSign`). This is well defined because `a ⊗ f` and
`(-a) ⊗ σ f` have the same class and antisymmetrization changes sign under `σ`. It is natural
because antisymmetrization commutes with monodromy, and bijective because the class of `a ⊗ e`
goes to the function with value `a` at `e`, while both fibres are copies of `k` through the sheet
`e` (`IsQuotientCoveringMap.associatedLocalSystemFiberIso` and `TauCeti.signFiberEquiv`).

For the orientation double cover of a real vector bundle, the sign local system of the deck
involution is the orientation local system `o(E)`, and the isomorphism specializes to
`L_sign ≅ o(E)` (`TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`). Combined with
`TopPair.coinvariantsTensorSingularChainsRepIsoTwisted`, this identifies chains twisted by `o(E)`
with the coinvariants of chains on the cover tensored with the sign representation, which is the
form in which an equivariant chain map on the cover computes homology twisted by `o(E)`.

## Main definitions

* `IsQuotientCoveringMap.associatedLocalSystemSignHom`: the morphism from the local system
  associated to the sign representation to the sign local system of the action of `-1`, with its
  value `IsQuotientCoveringMap.associatedLocalSystemSignHom_app_coinvariantsTensorMk` on a tensor
  class.
* `IsQuotientCoveringMap.associatedLocalSystemSignIso`: this morphism as an isomorphism.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H (local
  coefficient systems of a covering space and the orientation local system).
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section III.1.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TauCeti

namespace IsQuotientCoveringMap

variable {E B : TopCat.{0}} {p : E ⟶ B} [MulAction ℤˣ E] (hG : IsQuotientCoveringMap p ℤˣ)
  (k : Type) [CommRing k] {σ : C(E, E)} (hσ : ∀ e, σ e = (-1 : ℤˣ) • e)

include hG hσ in
/-- The action of `-1` is a map over the base of the quotient covering. -/
theorem comp_eq_of_forall_eq_neg_one_smul : ⇑p ∘ ⇑σ = ⇑p :=
  funext fun e ↦ (congrArg p (hσ e)).trans (hG.map_smul (-1))

include hσ in
/-- The action of `-1` is an involution. -/
theorem involutive_of_forall_eq_neg_one_smul : Function.Involutive σ := fun e ↦ by
  rw [hσ, hσ, smul_smul, neg_one_mul, neg_neg, one_smul]

include hG hσ in
/-- The action of `-1` has no fixed point. -/
theorem apply_ne_self_of_forall_eq_neg_one_smul (e : E) : σ e ≠ e := fun h ↦ by
  have := hG.isCancelSMul
  exact absurd (IsCancelSMul.eq_one_of_smul ((hσ e).symm.trans h)) (by decide)

include hG hσ in
/-- The fibre of the quotient covering through `e` is `{e, σ e}`. -/
theorem eq_or_eq_of_apply_eq {e e' : E} (h : p e' = p e) : e' = e ∨ e' = σ e := by
  obtain ⟨g, rfl⟩ := hG.apply_eq_iff_mem_orbit.1 h
  rcases Int.units_eq_one_or g with rfl | rfl
  · exact .inl (one_smul _ _)
  · exact .inr (hσ e).symm

/-- In the permutation representation on a fibre, `-1` moves the sheets by `σ`. -/
private theorem fiberRepresentation_neg_one_apply (x : FundamentalGroupoid B)
    (v : p ⁻¹' {x.as} →₀ k) :
    hG.fiberRepresentation k x.as (-1) v =
      Finsupp.mapDomain (Function.fiberMap σ (comp_eq_of_forall_eq_neg_one_smul hG hσ) x.as) v := by
  let := hG.mulActionFiber x.as
  refine LinearMap.congr_fun (f := hG.fiberRepresentation k x.as (-1))
    (g := Finsupp.lmapDomain k k
      (Function.fiberMap σ (comp_eq_of_forall_eq_neg_one_smul hG hσ) x.as))
    (Finsupp.lhom_ext fun e r ↦ ?_) v
  rw [fiberRepresentation_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  congr 1
  exact Subtype.ext (by rw [Function.fiberMap_apply_coe, hσ, coe_mulActionFiber_smul])

/-- Antisymmetrizing a formal sum of sheets moved by `-1` negates it. -/
private theorem permutationLocalSystemToSignApp_fiberRepresentation_neg_one
    (x : FundamentalGroupoid B) (v : p ⁻¹' {x.as} →₀ k) :
    hG.isCoveringMap.permutationLocalSystemToSignApp k (comp_eq_of_forall_eq_neg_one_smul hG hσ)
        (involutive_of_forall_eq_neg_one_smul hσ) x (hG.fiberRepresentation k x.as (-1) v) =
      -hG.isCoveringMap.permutationLocalSystemToSignApp k (comp_eq_of_forall_eq_neg_one_smul hG hσ)
        (involutive_of_forall_eq_neg_one_smul hσ) x v := by
  have hσp := comp_eq_of_forall_eq_neg_one_smul hG hσ
  have hσσ := involutive_of_forall_eq_neg_one_smul hσ
  refine (hG.isCoveringMap.signLocalSystemObjEquiv σ hσp x).injective
    (Subtype.ext (funext fun e ↦ ?_))
  rw [map_neg, Submodule.coe_neg, Pi.neg_apply, fiberRepresentation_neg_one_apply hG k hσ,
    IsCoveringMap.signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply,
    IsCoveringMap.signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply,
    Function.mapDomain_fiberMap_apply_of_involutive hσσ hσp,
    Function.mapDomain_fiberMap_apply_of_involutive hσσ hσp,
    Function.fiberMap_fiberMap_of_involutive hσσ hσp, neg_sub]

/-- Over `x`, the morphism of representations `a ⊗ f ↦ a • T f` from the sign representation
tensored with the permutation representation on the fibre to the trivial representation on the
fibre of the sign local system, where `T` is antisymmetrization. -/
private def signTensorToSign (x : FundamentalGroupoid B) :
    Rep.of (Representation.ofDistribMulAction k ℤˣ k) ⊗ (hG.permutationRepFunctor k).obj x ⟶
      Rep.trivial k ℤˣ ((hG.isCoveringMap.signLocalSystem k σ
        (comp_eq_of_forall_eq_neg_one_smul hG hσ)).obj x) :=
  let T := hG.isCoveringMap.permutationLocalSystemToSignApp k
    (comp_eq_of_forall_eq_neg_one_smul hG hσ) (involutive_of_forall_eq_neg_one_smul hσ) x
  have h (g : ℤˣ) : TensorProduct.lift ((LinearMap.lsmul k _).compl₂ T) ∘ₗ
      TensorProduct.map (Representation.ofDistribMulAction k ℤˣ k g)
        (hG.fiberRepresentation k x.as g) =
        TensorProduct.lift ((LinearMap.lsmul k _).compl₂ T) := TensorProduct.ext' fun a f ↦ by
    rcases Int.units_eq_one_or g with rfl | rfl
    · simp
    · -- `-1` negates `a` and, through antisymmetrization, the formal sum `f`.
      simp [T, permutationLocalSystemToSignApp_fiberRepresentation_neg_one hG k hσ]
  Rep.ofHom
    { toLinearMap := TensorProduct.lift ((LinearMap.lsmul k _).compl₂ T)
      -- The tensor product of representations acts by `TensorProduct.map` on the tensor product
      -- of the underlying modules.
      isIntertwining' g := (h g).trans (LinearMap.id_comp _).symm }

/-- The map out of the coinvariants induced by `signTensorToSign` sends the class of `a ⊗ f` to
`a • T f`. -/
private theorem coinvariantsHomLinearEquiv_symm_signTensorToSign_mk (x : FundamentalGroupoid B)
    (a : k) (f : p ⁻¹' {x.as} →₀ k) :
    ((Rep.coinvariantsHomLinearEquiv _ _).symm (signTensorToSign hG k hσ x)).hom
        (Rep.coinvariantsTensorMk (Rep.of (Representation.ofDistribMulAction k ℤˣ k))
          (Rep.of (hG.fiberRepresentation k x.as)) a f) =
      a • hG.isCoveringMap.permutationLocalSystemToSignApp k
        (comp_eq_of_forall_eq_neg_one_smul hG hσ) (involutive_of_forall_eq_neg_one_smul hσ) x f :=
  Rep.coinvariantsHomLinearEquiv_symm_apply_mk _ (signTensorToSign hG k hσ x) (a ⊗ₜ f)

/-- **The local system associated to the sign representation maps to the sign local system.** For
the quotient covering map `p` of a free action of `ℤˣ`, with `σ` the action of `-1`, this is the
morphism from the local system associated to the sign representation of `ℤˣ` on `k` to the sign
local system of `σ` sending the class of `a ⊗ f`, for a formal sum `f` of sheets over `x`, to `a`
times the function `e ↦ f e - f (σ e)` on the fibre
(`IsQuotientCoveringMap.associatedLocalSystemSignHom_app_coinvariantsTensorMk`). It is an
isomorphism (`IsQuotientCoveringMap.associatedLocalSystemSignIso`). -/
def associatedLocalSystemSignHom :
    hG.associatedLocalSystem k (Rep.of (Representation.ofDistribMulAction k ℤˣ k)) ⟶
      hG.isCoveringMap.signLocalSystem k σ (comp_eq_of_forall_eq_neg_one_smul hG hσ) where
  app x := (Rep.coinvariantsHomLinearEquiv _ _).symm (signTensorToSign hG k hσ x)
  naturality x y γ := by
    refine Rep.coinvariantsTensor_hom_ext
      (LinearMap.ext₂ fun (a : k) (f : p ⁻¹' {x.as} →₀ k) ↦ ?_)
    have hn := NatTrans.naturality_apply (hG.isCoveringMap.permutationLocalSystemToSign k
      (comp_eq_of_forall_eq_neg_one_smul hG hσ) (involutive_of_forall_eq_neg_one_smul hσ)) γ f
    simp only [IsCoveringMap.permutationLocalSystem_map_apply,
      IsCoveringMap.permutationLocalSystemToSign_app_hom] at hn
    -- Both sides evaluate the composites on the class of `a ⊗ f`.
    calc ((Rep.coinvariantsHomLinearEquiv _ _).symm (signTensorToSign hG k hσ y)).hom
          (((hG.associatedLocalSystem k
              (Rep.of (Representation.ofDistribMulAction k ℤˣ k))).map γ).hom
            (Rep.coinvariantsTensorMk (Rep.of (Representation.ofDistribMulAction k ℤˣ k))
              (Rep.of (hG.fiberRepresentation k x.as)) a f))
        _ = a • hG.isCoveringMap.permutationLocalSystemToSignApp k
              (comp_eq_of_forall_eq_neg_one_smul hG hσ)
                (involutive_of_forall_eq_neg_one_smul hσ) y
                  (Finsupp.lmapDomain k k (hG.isCoveringMap.monodromy γ) f) := by
          rw [associatedLocalSystem_map_coinvariantsTensorMk,
            coinvariantsHomLinearEquiv_symm_signTensorToSign_mk]
        _ = ((hG.isCoveringMap.signLocalSystem k σ
              (comp_eq_of_forall_eq_neg_one_smul hG hσ)).map γ).hom
              (((Rep.coinvariantsHomLinearEquiv _ _).symm (signTensorToSign hG k hσ x)).hom
                (Rep.coinvariantsTensorMk (Rep.of (Representation.ofDistribMulAction k ℤˣ k))
                  (Rep.of (hG.fiberRepresentation k x.as)) a f)) := by
          rw [coinvariantsHomLinearEquiv_symm_signTensorToSign_mk, map_smul]
          exact congrArg (a • ·) hn

/-- The morphism `associatedLocalSystemSignHom` sends the class of `a ⊗ f` over `x` to `a` times
the antisymmetrization `e ↦ f e - f (σ e)` of `f`. -/
-- Match before simplification unfolds `Rep.coinvariantsTensorMk` on the left-hand side.
@[simp↓]
theorem associatedLocalSystemSignHom_app_coinvariantsTensorMk (x : FundamentalGroupoid B)
    (a : k) (f : p ⁻¹' {x.as} →₀ k) :
    ((hG.associatedLocalSystemSignHom k hσ).app x).hom
        (Rep.coinvariantsTensorMk (Rep.of (Representation.ofDistribMulAction k ℤˣ k))
          (Rep.of (hG.fiberRepresentation k x.as)) a f) =
      a • hG.isCoveringMap.permutationLocalSystemToSignApp k
        (comp_eq_of_forall_eq_neg_one_smul hG hσ) (involutive_of_forall_eq_neg_one_smul hσ) x f :=
  coinvariantsHomLinearEquiv_symm_signTensorToSign_mk hG k hσ x a f

/-- Over each point, `associatedLocalSystemSignHom` is the identification of the fibre of the
associated local system with `k` given by a sheet `e`, followed by the inverse of evaluation at
`e` on the functions changing sign under `σ`. -/
private theorem associatedLocalSystemSignHom_app_associatedLocalSystemFiberIso_inv
    {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) (c : k) :
    hG.isCoveringMap.signLocalSystemObjEquiv σ (comp_eq_of_forall_eq_neg_one_smul hG hσ) x
        (((hG.associatedLocalSystemSignHom k hσ).app x).hom
          ((hG.associatedLocalSystemFiberIso k _ e).inv.hom c)) =
      (signFiberEquiv (apply_ne_self_of_forall_eq_neg_one_smul hG hσ)
        (fun _ _ ↦ eq_or_eq_of_apply_eq hG hσ) e).symm c := by
  refine (signFiberEquiv (apply_ne_self_of_forall_eq_neg_one_smul hG hσ)
    (fun _ _ ↦ eq_or_eq_of_apply_eq hG hσ) e).injective ?_
  rw [LinearEquiv.apply_symm_apply, signFiberEquiv_apply, associatedLocalSystemFiberIso_inv_apply,
    associatedLocalSystemSignHom_app_coinvariantsTensorMk, map_smul, Submodule.coe_smul,
    Pi.smul_apply, IsCoveringMap.signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne, sub_zero, smul_eq_mul, mul_one]
  exact fun h ↦ apply_ne_self_of_forall_eq_neg_one_smul hG hσ e
    ((Function.fiberMap_apply_coe σ _ x.as e).symm.trans (congrArg Subtype.val h))

/-- Over each point, `associatedLocalSystemSignHom` is bijective. -/
theorem bijective_associatedLocalSystemSignHom_app (x : FundamentalGroupoid B) :
    Function.Bijective ((hG.associatedLocalSystemSignHom k hσ).app x).hom := by
  obtain ⟨e, he⟩ := hG.surjective x.as
  let i := hG.associatedLocalSystemFiberIso k (Rep.of (Representation.ofDistribMulAction k ℤˣ k))
    (x := x) ⟨e, he⟩
  -- Through the sheet `e`, the morphism is the composite of three linear equivalences.
  have h : ⇑((hG.associatedLocalSystemSignHom k hσ).app x).hom =
      ⇑(i.toLinearEquiv ≪≫ₗ (signFiberEquiv (apply_ne_self_of_forall_eq_neg_one_smul hG hσ)
        (fun _ _ ↦ eq_or_eq_of_apply_eq hG hσ) ⟨e, he⟩).symm ≪≫ₗ
          (hG.isCoveringMap.signLocalSystemObjEquiv σ
            (comp_eq_of_forall_eq_neg_one_smul hG hσ) x).symm) := funext fun v ↦ by
    obtain ⟨c, rfl⟩ : ∃ c, i.inv.hom c = v := ⟨i.hom.hom v, by simp⟩
    refine (hG.isCoveringMap.signLocalSystemObjEquiv σ
      (comp_eq_of_forall_eq_neg_one_smul hG hσ) x).injective ?_
    rw [associatedLocalSystemSignHom_app_associatedLocalSystemFiberIso_inv]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    -- `i.inv` is the inverse of the linear equivalence of `i`.
    exact congrArg _ (i.toLinearEquiv.apply_symm_apply c).symm
  rw [h]
  exact LinearEquiv.bijective _

/-- The morphism `associatedLocalSystemSignHom` is an isomorphism, being bijective over each
point. -/
instance isIso_associatedLocalSystemSignHom : IsIso (hG.associatedLocalSystemSignHom k hσ) :=
  haveI (x : FundamentalGroupoid B) : IsIso ((hG.associatedLocalSystemSignHom k hσ).app x) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (hG.bijective_associatedLocalSystemSignHom_app k hσ x)
  NatIso.isIso_of_isIso_app _

/-- **The local system associated to the sign representation is the sign local system.** For the
quotient covering map `p` of a free action of `ℤˣ`, with `σ` the action of `-1`, the local system on
the base associated to the sign representation of `ℤˣ` on `k`, with fibre `(k ⊗ k[p⁻¹ x])_{ℤˣ}` over
`x`, is isomorphic to the sign local system of `σ`, with fibre the functions on `p⁻¹ x` changing
sign under `σ`. The class of `a ⊗ f` goes to `a` times `e ↦ f e - f (σ e)`
(`IsQuotientCoveringMap.associatedLocalSystemSignHom_app_coinvariantsTensorMk`). -/
def associatedLocalSystemSignIso :
    hG.associatedLocalSystem k (Rep.of (Representation.ofDistribMulAction k ℤˣ k)) ≅
      hG.isCoveringMap.signLocalSystem k σ (comp_eq_of_forall_eq_neg_one_smul hG hσ) :=
  asIso (hG.associatedLocalSystemSignHom k hσ)

/-- The isomorphism `associatedLocalSystemSignIso` is `associatedLocalSystemSignHom`. -/
@[simp]
theorem associatedLocalSystemSignIso_hom :
    (hG.associatedLocalSystemSignIso k hσ).hom = hG.associatedLocalSystemSignHom k hσ :=
  (rfl)

end IsQuotientCoveringMap
