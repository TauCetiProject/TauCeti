/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Basic

/-!
# The tensor square of a sign local system

The tensor square of the sign local system of a double cover is canonically constant.
On each fibre the pairing sends `f ⊗ g` to `f(e) * g(e)`. Changing the point `e` to the
other sheet negates both factors, so this pairing needs no choice of a sheet. It is a
linear equivalence and commutes with path transport. In particular, an orientation
local system has a canonical perfect pairing with itself, even on a nonorientable bundle.

The coefficient ring is commutative, with no restriction on its characteristic. The
cover must be surjective, with exactly two points in each fibre exchanged by its deck map.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (the orientation local system).
* J. Milnor and J. Stasheff, *Characteristic Classes*, §12 (twisted coefficients).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u v

namespace TauCeti

variable {R : Type*} [CommRing R] {E X : Type*} {p : E → X}
  {σ : E → E} {hσ : p ∘ σ = p}
  (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

/-- The tensor square of a sign fibre is identified with the coefficient ring by multiplying
values at one point. The result is independent of that point. -/
def signFiberTensorEquiv {x : X} (e : p ⁻¹' {x}) :
    signFiber R σ hσ x ⊗[R] signFiber R σ hσ x ≃ₗ[R] R :=
  TensorProduct.congr (signFiberEquiv hfix hfib e) (signFiberEquiv hfix hfib e) ≪≫ₗ
    TensorProduct.lid R R

/-- The sign pairing multiplies the two sheet coordinates. -/
@[simp]
theorem signFiberTensorEquiv_tmul {x : X} (e : p ⁻¹' {x})
    (f g : signFiber R σ hσ x) :
    signFiberTensorEquiv hfix hfib e (f ⊗ₜ[R] g) =
      (f : p ⁻¹' {x} → R) e * (g : p ⁻¹' {x} → R) e := by
  simp [signFiberTensorEquiv]

/-- The sign pairing can be evaluated at either point of the fibre. -/
theorem signFiberTensorEquiv_tmul_eq {x : X} (e e' : p ⁻¹' {x})
    (f g : signFiber R σ hσ x) :
    signFiberTensorEquiv hfix hfib e (f ⊗ₜ[R] g) =
      (f : p ⁻¹' {x} → R) e' * (g : p ⁻¹' {x} → R) e' := by
  have he := signFiberTensorEquiv_tmul hfix hfib e f g
  rcases hfib e e' (e'.2.trans e.2.symm) with h | h
  · simpa only [Subtype.ext h] using he
  · have h' : e' = Function.fiberMap σ hσ x e :=
      Subtype.ext (h.trans (Function.fiberMap_apply_coe σ hσ x e).symm)
    rw [h', mem_signFiber_iff.1 f.2, mem_signFiber_iff.1 g.2, neg_mul_neg]
    exact he

/-- The tensor-square identification does not depend on a choice of sheet. -/
theorem signFiberTensorEquiv_eq {x : X} (e e' : p ⁻¹' {x}) :
    signFiberTensorEquiv (R := R) (hσ := hσ) hfix hfib e =
      signFiberTensorEquiv hfix hfib e' := by
  apply LinearEquiv.toLinearMap_injective
  ext f g
  exact (signFiberTensorEquiv_tmul_eq hfix hfib e e' f g).trans
    (signFiberTensorEquiv_tmul hfix hfib e' f g).symm

/-- In coordinates on either sheet, the inverse pairing sends `a * b` to the tensor of the
sign functions with values `a` and `b`. In particular, the inverse image of `1` is the
square of either orientation generator. -/
theorem signFiberTensorEquiv_symm_mul {x : X} (e e' : p ⁻¹' {x}) (a b : R) :
    (signFiberTensorEquiv (hσ := hσ) hfix hfib e).symm (a * b) =
      (signFiberEquiv hfix hfib e').symm a ⊗ₜ[R]
        (signFiberEquiv hfix hfib e').symm b := by
  apply (signFiberTensorEquiv hfix hfib e).injective
  rw [LinearEquiv.apply_symm_apply, signFiberTensorEquiv_tmul_eq hfix hfib e e']
  simp

end TauCeti

namespace IsCoveringMap

variable {R E : Type u} [CommRing R] [TopologicalSpace E] {X : TopCat.{v}} {p : E → X}
  (hp : IsCoveringMap p) {σ : C(E, E)} {hσ : p ∘ σ = p}
  (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)
  (hsurj : Function.Surjective p)

private def tensorSquareEquiv (x : FundamentalGroupoid X) :
    (hp.signLocalSystem R σ hσ).obj x ⊗[R] (hp.signLocalSystem R σ hσ).obj x ≃ₗ[R]
      ULift.{u} R :=
  TensorProduct.congr (hp.signLocalSystemObjEquiv σ hσ x)
      (hp.signLocalSystemObjEquiv σ hσ x) ≪≫ₗ
    TauCeti.signFiberTensorEquiv hfix hfib ⟨(hsurj x.as).choose, (hsurj x.as).choose_spec⟩ ≪≫ₗ
      ULift.moduleEquiv.symm

private theorem tensorSquareEquiv_tmul (x : FundamentalGroupoid X) (e : p ⁻¹' {x.as})
    (f g : (hp.signLocalSystem R σ hσ).obj x) :
    tensorSquareEquiv hp hfix hfib hsurj x (f ⊗ₜ[R] g) = ULift.up
      ((hp.signLocalSystemObjEquiv σ hσ x f : p ⁻¹' {x.as} → R) e *
        (hp.signLocalSystemObjEquiv σ hσ x g : p ⁻¹' {x.as} → R) e) := by
  simp only [tensorSquareEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul]
  rw [TauCeti.signFiberTensorEquiv_tmul_eq hfix hfib _ e]
  rfl

/-- The tensor square of the sign local system of a surjective double cover is canonically
constant. Its components multiply evaluations at either sheet; thus no continuous section
or orientation of the cover is required. -/
def signLocalSystemTensorIso :
    hp.signLocalSystem R σ hσ ⊗ hp.signLocalSystem R σ hσ ≅
      (TauCeti.LocalCoefficientSystem.constantFunctor X).obj (ModuleCat.of R (ULift.{u} R)) :=
  NatIso.ofComponents (fun x ↦ (tensorSquareEquiv hp hfix hfib hsurj x).toModuleIso) (by
    intro x y γ
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext f g
    have e : p ⁻¹' {y.as} := ⟨(hsurj y.as).choose, (hsurj y.as).choose_spec⟩
    -- The functor-category tensor and `ModuleCat` composition hide the pure tensor from
    -- rewriting. Read this component equation as an equality in the underlying modules.
    change tensorSquareEquiv hp hfix hfib hsurj y
      (((hp.signLocalSystem R σ hσ).map γ).hom f ⊗ₜ[R]
        ((hp.signLocalSystem R σ hσ).map γ).hom g) =
      tensorSquareEquiv hp hfix hfib hsurj x (f ⊗ₜ[R] g)
    -- Compute using matching sheets: the target point and its inverse monodromy lift.
    rw [tensorSquareEquiv_tmul hp hfix hfib hsurj y e,
      tensorSquareEquiv_tmul hp hfix hfib hsurj x (hp.monodromy (inv γ) e)]
    simp)

/-- The canonical trivialization multiplies values on either sheet. -/
theorem signLocalSystemTensorIso_hom_app_tmul (x : FundamentalGroupoid X)
    (e : p ⁻¹' {x.as}) (f g : (hp.signLocalSystem R σ hσ).obj x) :
    ((hp.signLocalSystemTensorIso hfix hfib hsurj).hom.app x).hom (f ⊗ₜ[R] g) = ULift.up
      ((hp.signLocalSystemObjEquiv σ hσ x f : p ⁻¹' {x.as} → R) e *
        (hp.signLocalSystemObjEquiv σ hσ x g : p ⁻¹' {x.as} → R) e) :=
  tensorSquareEquiv_tmul hp hfix hfib hsurj x e f g

/-- The inverse trivialization sends a product of scalars to the corresponding tensor in
any chosen sheet coordinates. -/
theorem signLocalSystemTensorIso_inv_app_mul (x : FundamentalGroupoid X)
    (e : p ⁻¹' {x.as}) (a b : R) :
    ((hp.signLocalSystemTensorIso hfix hfib hsurj).inv.app x).hom (ULift.up (a * b)) =
      (hp.signLocalSystemObjEquiv σ hσ x).symm
        ((TauCeti.signFiberEquiv hfix hfib e).symm a) ⊗ₜ[R]
      (hp.signLocalSystemObjEquiv σ hσ x).symm
        ((TauCeti.signFiberEquiv hfix hfib e).symm b) := by
  apply (tensorSquareEquiv hp hfix hfib hsurj x).injective
  -- The functor-category and `ModuleCat` wrappers prevent rewriting the inverse
  -- component. Its underlying function is the inverse of the displayed fibre equivalence.
  change tensorSquareEquiv hp hfix hfib hsurj x
      ((tensorSquareEquiv hp hfix hfib hsurj x).symm (ULift.up (a * b))) = _
  rw [LinearEquiv.apply_symm_apply, tensorSquareEquiv_tmul hp hfix hfib hsurj x e]
  simp

end IsCoveringMap
