/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
import TauCeti.Algebra.Coalgebra.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Finite
import TauCeti.Algebra.HopfAlgebra.Antipode
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Existence of cointegrals

Every finite projective Hopf algebra `H` over a nontrivial commutative semiring has a nonzero left
cointegral, `TauCeti.exists_isLeftCointegral_ne_zero`. This is the existence half of the
Larson–Sweedler theorem in the generality of finite projective Hopf algebras; over a field, the
consequences (one-dimensionality of integrals and cointegrals, Frobenius functionals, bijectivity
of the antipode) are in `TauCeti.Algebra.HopfAlgebra.Frobenius`.

The proof is the Hopf-module argument. The dual `H*` is a right `H`-comodule through left
convolution multiplication, `∑ φ(f₁) f₀ = φ * f`, and a right `H`-module through
`(f ↼ h)(x) = f(x S(h))`; together they satisfy the Hopf-module law
`ρ(f ↼ h) = ∑ f₀ ↼ h₁ ⊗ f₁ h₂`. The projection `P f = ∑ f₀ ↼ S(f₁)` lands in the coinvariants,
which are the left cointegrals, and every `f` is recovered as `∑ P(f₀) ↼ f₁`. Since `H*` contains
the counit, `P` is not zero. These Hopf-module structures on `H*` are used only for this argument
and stay private.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS 82, AMS, 1993, Section 1.9
  (Hopf modules) and Section 2.1 (integrals of finite-dimensional Hopf algebras).
-/

public section

open scoped TensorProduct
open TensorProduct WithConv Coalgebra HopfAlgebra

namespace TauCeti

variable {R H : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

namespace ConvolutionDual

/-- Right translation of a functional by the antipode of `h`: `(f ↼ h)(x) = f (x * S h)`.
This is the right `H`-action on the dual used by the Hopf-module argument. -/
private noncomputable def act : ConvolutionDual R H ⊗[R] H →ₗ[R] ConvolutionDual R H :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun f h ↦ toConv (f.ofConv ∘ₗ LinearMap.mulRight R (antipode R h)))
    (fun f g h ↦ by ext; simp)
    (fun c f h ↦ by ext; simp)
    (fun f h h' ↦ by ext; simp [mul_add])
    (fun c f h ↦ by ext; simp)

private theorem act_tmul_apply (f : ConvolutionDual R H) (h x : H) :
    act (f ⊗ₜ[R] h) x = f (x * antipode R h) := by
  simp [act]

private theorem act_act (f : ConvolutionDual R H) (a b : H) :
    act (act (f ⊗ₜ[R] a) ⊗ₜ[R] b) = act (f ⊗ₜ[R] (a * b)) := by
  ext x
  simp [act_tmul_apply, antipode_mul_antidistrib, mul_assoc]

private theorem act_one (f : ConvolutionDual R H) : act (f ⊗ₜ[R] (1 : H)) = f := by
  ext x
  simp [act_tmul_apply]

section Comodule

variable [Module.Finite R H] [Module.Projective R H]

/-- The right `H`-coaction on the dual corresponding to left convolution multiplication,
`∑ φ(f₁) f₀ = φ * f`. -/
@[implicit_reducible]
private noncomputable def leftMulComodule : Comodule R H (ConvolutionDual R H) :=
  Comodule.ofConvolutionAction (Algebra.lmul R (ConvolutionDual R H))

attribute [local instance] leftMulComodule

private theorem tensorComponent_coact (φ : Module.Dual R H) (f : ConvolutionDual R H) :
    LinearMap.tensorComponent φ (Comodule.coact (R := R) (C := H) f) = toConv φ * f := by
  simp

end Comodule

/-- Applying the action and the multiplication after interchanging the middle factors, against a
fixed pure tensor `a ⊗ b`. -/
private theorem map_act_mul'_tensorTensorTensorComm (t : ConvolutionDual R H ⊗[R] H) (a b : H) :
    TensorProduct.map act (LinearMap.mul' R H)
        (tensorTensorTensorComm R (ConvolutionDual R H) H H H (t ⊗ₜ[R] (a ⊗ₜ[R] b))) =
      TensorProduct.map (act ∘ₗ (TensorProduct.mk R (ConvolutionDual R H) H).flip a)
        (LinearMap.mulRight R b) t := by
  induction t using TensorProduct.inductionOn with
  | tmul f c => simp
  | add t u ht hu => simp [add_tmul, ht, hu]

/-- The scalar identity `∑ φ(p S(h₂) h₃) n(q S(h₁)) = φ(p) n(q S(h))` behind the Hopf-module
law, written with nested coproduct representations. -/
private theorem sum_coassoc_eval (φ : Module.Dual R H) (n : ConvolutionDual R H) (p q h : H) :
    ∑ j ∈ (ℛ R h).index, ∑ k ∈ (ℛ R ((ℛ R h).left j)).index,
        φ (p * (antipode R ((ℛ R ((ℛ R h).left j)).right k) * (ℛ R h).right j)) *
          n (q * antipode R ((ℛ R ((ℛ R h).left j)).left k)) =
      φ p * n (q * antipode R h) := by
  let Θ : H ⊗[R] (H ⊗[R] H) →ₗ[R] R := TensorProduct.lift <|
    (LinearMap.mul R R).compl₁₂ (n.ofConv ∘ₗ LinearMap.mulLeft R q ∘ₗ antipode R)
      (φ ∘ₗ LinearMap.mulLeft R p ∘ₗ LinearMap.mul' R H ∘ₗ (antipode R).rTensor H)
  have hΘ := congrArg Θ (Coalgebra.sum_tmul_tmul_eq (ℛ R h) (fun j ↦ ℛ R ((ℛ R h).left j))
    (fun j ↦ ℛ R ((ℛ R h).right j)))
  simp only [map_sum, Θ, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.rTensor_tmul,
    LinearMap.mul'_apply] at hΘ
  have key (j : _) : ∑ l ∈ (ℛ R ((ℛ R h).right j)).index,
      n.ofConv (q * antipode R ((ℛ R h).left j)) *
        φ (p * (antipode R ((ℛ R ((ℛ R h).right j)).left l) * (ℛ R ((ℛ R h).right j)).right l)) =
      counit (R := R) ((ℛ R h).right j) • (φ p * n (q * antipode R ((ℛ R h).left j))) := by
    rw [← Finset.mul_sum, ← map_sum, ← Finset.mul_sum, sum_antipode_mul_eq_smul]
    simp only [mul_smul_comm, mul_one, map_smul, smul_eq_mul]
    ring
  -- Swap the factors so the summand is `Θ` applied to `(h₁)₁ ⊗ (h₁)₂ ⊗ h₂`.
  calc _ = ∑ j ∈ (ℛ R h).index, ∑ k ∈ (ℛ R ((ℛ R h).left j)).index,
          n.ofConv (q * antipode R ((ℛ R ((ℛ R h).left j)).left k)) *
            φ (p * (antipode R ((ℛ R ((ℛ R h).left j)).right k) * (ℛ R h).right j)) :=
        Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
    -- Coassociativity: rewrite `(h₁)₁ ⊗ (h₁)₂ ⊗ h₂` as `h₁ ⊗ (h₂)₁ ⊗ (h₂)₂` under `Θ`.
    _ = ∑ j ∈ (ℛ R h).index, ∑ l ∈ (ℛ R ((ℛ R h).right j)).index,
          n.ofConv (q * antipode R ((ℛ R h).left j)) *
            φ (p * (antipode R ((ℛ R ((ℛ R h).right j)).left l) *
              (ℛ R ((ℛ R h).right j)).right l)) := hΘ
    -- The antipode law `∑ S((h₂)₁) (h₂)₂ = ε(h₂) 1` collapses the inner sum.
    _ = ∑ j ∈ (ℛ R h).index,
          counit (R := R) ((ℛ R h).right j) • (φ p * n (q * antipode R ((ℛ R h).left j))) :=
        Finset.sum_congr rfl fun j _ ↦ key j
    -- Pull the scalars inside `n ∘ (q * S ·)` by linearity.
    _ = φ p * n (q * antipode R (∑ j ∈ (ℛ R h).index,
          counit (R := R) ((ℛ R h).right j) • (ℛ R h).left j)) := by
      simp [Finset.mul_sum, map_sum, mul_left_comm]
    -- The counit law `∑ ε(h₂) h₁ = h`.
    _ = _ := by rw [Coalgebra.sum_smul_counit]

/-- The identity `∑ u ↼ S(h₃) ⊗ h₁ S(h₂) = (u ↼ S h) ⊗ 1` behind coinvariance of the projection. -/
private theorem sum_act_antipode_tmul_mul_antipode (u : ConvolutionDual R H) (h : H) :
    ∑ j ∈ (ℛ R h).index, ∑ k ∈ (ℛ R ((ℛ R h).right j)).index,
        act (u ⊗ₜ[R] antipode R ((ℛ R ((ℛ R h).right j)).right k)) ⊗ₜ[R]
          ((ℛ R h).left j * antipode R ((ℛ R ((ℛ R h).right j)).left k)) =
      act (u ⊗ₜ[R] antipode R h) ⊗ₜ[R] (1 : H) := by
  let Ψ : H ⊗[R] (H ⊗[R] H) →ₗ[R] ConvolutionDual R H ⊗[R] H :=
    TensorProduct.map (act ∘ₗ TensorProduct.mk R _ H u ∘ₗ antipode R)
        (LinearMap.mul' R H ∘ₗ (antipode R).lTensor H) ∘ₗ
      (TensorProduct.comm R (H ⊗[R] H) H).toLinearMap ∘ₗ (TensorProduct.assoc R H H H).symm
  have hΨ := congrArg Ψ (Coalgebra.sum_tmul_tmul_eq (ℛ R h) (fun j ↦ ℛ R ((ℛ R h).left j))
    (fun j ↦ ℛ R ((ℛ R h).right j)))
  simp only [map_sum, Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul, TensorProduct.comm_tmul, TensorProduct.map_tmul,
    TensorProduct.mk_apply, LinearMap.lTensor_tmul, LinearMap.mul'_apply] at hΨ
  rw [← hΨ]
  simp only [← TensorProduct.tmul_sum, sum_mul_antipode_eq_smul, TensorProduct.tmul_smul]
  conv_rhs => rw [← Coalgebra.sum_counit_smul (ℛ R h)]
  simp only [map_sum, map_smul, TensorProduct.tmul_sum, TensorProduct.sum_tmul,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← map_smul, TensorProduct.smul_tmul']

variable [Module.Finite R H] [Module.Projective R H]

attribute [local instance] leftMulComodule

/-- The dual is a right Hopf module: `ρ(f ↼ h) = ∑ f₀ ↼ h₁ ⊗ f₁ h₂`. -/
private theorem coact_comp_act :
    Comodule.coact (R := R) (C := H) ∘ₗ act =
      TensorProduct.map act (LinearMap.mul' R H) ∘ₗ
        (tensorTensorTensorComm R (ConvolutionDual R H) H H H).toLinearMap ∘ₗ
          TensorProduct.map (Comodule.coact (R := R) (C := H)) comul := by
  refine TensorProduct.ext' fun n h ↦ TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    fun φ ↦ ?_
  -- Pair both sides with `φ` in the `H` factor: the left side becomes `φ * (n ↼ h)` and,
  -- after expanding `Δ h = ∑ h₁ ⊗ h₂`, the right side becomes `∑ (φ ∘ (· * h₂) * n) ↼ h₁`.
  rw [LinearMap.comp_apply, tensorComponent_coact]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul]
  rw [← (ℛ R h).eq, TensorProduct.tmul_sum, map_sum, map_sum, map_sum]
  simp only [map_act_mul'_tensorTensorTensorComm, LinearMap.tensorComponent_map,
    tensorComponent_coact]
  -- Evaluate at `x`, expanding the convolution on the left through `Δ x`.
  ext x
  rw [(ℛ R x).convMul_apply]
  simp only [ofConv_sum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, act_tmul_apply]
  -- On the right, expand each convolution through the product representation of
  -- `Δ (x S(h₁)) = ∑ x₁ S((h₁)₂) ⊗ x₂ S((h₁)₁)`, then sum over the `Δ x` index first.
  rw [Finset.sum_congr rfl fun j _ ↦
    ((ℛ R x).mul (ℛ R ((ℛ R h).left j)).antipode).convMul_apply _ _]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left, Coalgebra.Repr.mul_right,
    Coalgebra.Repr.antipode_index, Coalgebra.Repr.antipode_left, Coalgebra.Repr.antipode_right,
    Finset.sum_product, LinearMap.comp_apply, LinearMap.mulRight_apply]
  rw [Finset.sum_comm]
  -- For each summand `x₁ ⊗ x₂` of `Δ x`, the law reduces to the scalar identity
  -- `sum_coassoc_eval` with `p = x₁` and `q = x₂`.
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa only [mul_assoc] using (sum_coassoc_eval φ n _ _ h).symm

/-- The projection `f ↦ ∑ f₀ ↼ S(f₁)` of the Hopf module onto its coinvariants. -/
private noncomputable def coinvariantProj : ConvolutionDual R H →ₗ[R] ConvolutionDual R H :=
  act ∘ₗ (antipode R).lTensor _ ∘ₗ Comodule.coact (R := R) (C := H)

/-- The projection lands in the coinvariants: `ρ (P f) = P f ⊗ 1`. -/
private theorem coact_coinvariantProj (f : ConvolutionDual R H) :
    Comodule.coact (R := R) (C := H) (coinvariantProj f) = coinvariantProj f ⊗ₜ[R] (1 : H) := by
  have hc (x : H) : comul (R := R) x = ∑ i ∈ (ℛ R x).index, (ℛ R x).left i ⊗ₜ[R] (ℛ R x).right i :=
    (ℛ R x).eq.symm
  have hmap (t : ConvolutionDual R H ⊗[R] H) :
      TensorProduct.map (Comodule.coact (R := R) (C := H)) comul ((antipode R).lTensor _ t) =
        (comul ∘ₗ antipode R).lTensor _ ((Comodule.coact (R := R) (C := H)).rTensor H t) := by
    induction t using TensorProduct.inductionOn with
    | tmul u h => simp
    | add t u ht hu => simp only [map_add, ht, hu]
  have hG (t : ConvolutionDual R H ⊗[R] H) :
      TensorProduct.map act (LinearMap.mul' R H) (tensorTensorTensorComm R _ H H H
        ((comul ∘ₗ antipode R).lTensor _
          ((TensorProduct.assoc R _ H H).symm (comul.lTensor _ t)))) =
        act ((antipode R).lTensor _ t) ⊗ₜ[R] (1 : H) := by
    induction t using TensorProduct.inductionOn with
    | tmul u h =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, ← sum_act_antipode_tmul_mul_antipode u h]
      rw [hc h]
      simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.assoc_symm_tmul,
        LinearMap.lTensor_tmul, LinearMap.comp_apply,
        TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply]
      simp only [hc, map_sum, TensorProduct.comm_tmul, TensorProduct.map_tmul,
        TensorProduct.tmul_sum, tensorTensorTensorComm_tmul, LinearMap.mul'_apply]
    | add t u ht hu => simp only [map_add, ht, hu, TensorProduct.add_tmul]
  have hcomp := LinearMap.congr_fun coact_comp_act ((antipode R).lTensor _ (Comodule.coact f))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcomp
  rw [coinvariantProj, LinearMap.comp_apply, LinearMap.comp_apply, hcomp, hmap,
    ← Comodule.coassoc_symm_apply, hG]

/-- Every element is recovered from the coinvariants: `f = ∑ P(f₀) ↼ f₁`. -/
private theorem act_rTensor_coinvariantProj_coact (f : ConvolutionDual R H) :
    act (coinvariantProj.rTensor H (Comodule.coact (R := R) (C := H) f)) = f := by
  have h1 (t : ConvolutionDual R H ⊗[R] H) :
      act (coinvariantProj.rTensor H t) =
        act ((LinearMap.mul' R H ∘ₗ (antipode R).rTensor H).lTensor _
          (TensorProduct.assoc R _ H H ((Comodule.coact (R := R) (C := H)).rTensor H t))) := by
    induction t using TensorProduct.inductionOn with
    | tmul u b =>
      simp only [LinearMap.rTensor_tmul, coinvariantProj, LinearMap.comp_apply]
      induction Comodule.coact (R := R) (C := H) u using TensorProduct.inductionOn with
      | tmul g a => simp [act_act]
      | add t t' ht ht' => simp only [map_add, TensorProduct.add_tmul, ht, ht']
    | add t u ht hu => simp only [map_add, ht, hu]
  have h2 (t : ConvolutionDual R H ⊗[R] H) :
      act ((Algebra.linearMap R H ∘ₗ counit).lTensor _ t) =
        TensorProduct.rid R _ (counit.lTensor _ t) := by
    induction t using TensorProduct.inductionOn with
    | tmul g a =>
      simp [Algebra.algebraMap_eq_smul_one, act_one]
    | add t u ht hu => simp only [map_add, ht, hu]
  rw [h1, Comodule.coassoc_apply, ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc,
    HopfAlgebra.mul_antipode_rTensor_comul, h2, Comodule.rid_lTensor_counit_coact]

/-- Over a nontrivial base the projection onto the coinvariants is nonzero. -/
private theorem exists_coinvariantProj_ne_zero [Nontrivial R] :
    ∃ f : ConvolutionDual R H, coinvariantProj f ≠ 0 := by
  by_contra! h
  have h0 : (coinvariantProj : ConvolutionDual R H →ₗ[R] _) = 0 := LinearMap.ext h
  have hf := act_rTensor_coinvariantProj_coact (toConv (counit (R := R) (A := H)))
  rw [h0, LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero] at hf
  simpa using congrArg (fun f : ConvolutionDual R H ↦ f.ofConv 1) hf

end ConvolutionDual

variable (R H) in
open ConvolutionDual in
/-- **Existence of left cointegrals.** A finite projective Hopf algebra over a nontrivial
commutative semiring has a nonzero left cointegral. -/
theorem exists_isLeftCointegral_ne_zero [Nontrivial R] [Module.Finite R H]
    [Module.Projective R H] : ∃ φ : Module.Dual R H, IsLeftCointegral φ ∧ φ ≠ 0 := by
  let := leftMulComodule (R := R) (H := H)
  obtain ⟨f, hf⟩ := exists_coinvariantProj_ne_zero (R := R) (H := H)
  refine ⟨(coinvariantProj f).ofConv, ?_, by simpa using hf⟩
  rw [isLeftCointegral_iff_convMul]
  intro ψ
  have := congrArg (LinearMap.tensorComponent ψ.ofConv) (coact_coinvariantProj f)
  rw [tensorComponent_coact, LinearMap.tensorComponent_tmul] at this
  simpa using this

end TauCeti
