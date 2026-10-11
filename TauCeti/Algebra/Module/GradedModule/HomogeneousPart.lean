/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Homogeneous parts of polynomial-linear maps

For internally integer-graded coefficient modules on which `X` has the same degree `δ`,
each degree component of a polynomial-linear map is again polynomial-linear. The component
of degree `r` sends a homogeneous input of degree `p` to the degree-`(p + r)` projection of
its image. Neither injectivity of `X` nor a sign condition on `δ` is required.

The construction uses Mathlib's `DirectSum.decomposeLinearEquiv`, `DirectSum.component`, and
`DirectSum.toModule` to sum the selected projections over the finite input decomposition.
Its degree-zero part can turn an ungraded retraction onto a homogeneous submodule into a
homogeneous retraction.

## Main definitions and results

* `InternalGrading.homogeneousPart`: the polynomial-linear component of degree `r`.
* `InternalGrading.homogeneousPart_apply_of_mem`: its value on homogeneous inputs.
* `InternalGrading.homogeneousPart_zero` and `InternalGrading.homogeneousPart_add`: components
  preserve zero and addition of maps.
* `InternalGrading.homogeneousPart_eq_self`: taking the component of a homogeneous map at its
  degree recovers the map.
* `InternalGrading.isHomogeneous_homogeneousPart`: the component has degree `r`.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti.InternalGrading

variable {k M N : Type*} [CommSemiring k] [AddCommMonoid M] [AddCommMonoid N]
  [Module k M] [Module k N] [Module k[X] M] [Module k[X] N]
  [IsScalarTower k k[X] M] [IsScalarTower k k[X] N]
  (G : InternalGrading k M) (H : InternalGrading k N)

-- This coefficient-linear assembly is private: the public construction bundles the additional
-- polynomial linearity, and its characteristic lemma avoids exposing this implementation.
private def componentMap (f : M →ₗ[k[X]] N) (r : ℤ) : M →ₗ[k] N :=
  DirectSum.toModule k ℤ N
    (fun p ↦ (H.piece (p + r)).subtype ∘ₗ
      DirectSum.component k ℤ (fun q ↦ H.piece q) (p + r) ∘ₗ
      (DirectSum.decomposeLinearEquiv H.piece).toLinearMap ∘ₗ
      f.restrictScalars k ∘ₗ (G.piece p).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

private theorem componentMap_apply_of_mem (f : M →ₗ[k[X]] N) (r : ℤ)
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    componentMap G H f r x = (DirectSum.decompose H.piece (f x) (p + r) : N) := by
  have heq := DirectSum.decomposeLinearEquiv_apply_coe G.piece p ⟨x, hx⟩
  simp only [componentMap, _root_.LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [heq, DirectSum.toModule_lof]
  simp only [_root_.LinearMap.comp_apply, Submodule.subtype_apply,
    _root_.LinearMap.restrictScalars_apply,
    ← DirectSum.apply_eq_component]
  exact congrArg (fun z ↦ (z (p + r) : N))
    (DirectSum.decomposeLinearEquiv_apply H.piece (f x))

variable {δ : ℤ}
  (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p + δ))
  (hY : ∀ ⦃p : ℤ⦄ ⦃y : N⦄, y ∈ H.piece p → (X : k[X]) • y ∈ H.piece (p + δ))

include hX hY in
private theorem componentMap_X_smul (f : M →ₗ[k[X]] N) (r : ℤ) (x : M) :
    componentMap G H f r ((X : k[X]) • x) = (X : k[X]) • componentMap G H f r x := by
  have hhom : TauCeti.LinearMap.IsHomogeneous (_root_.LinearMap.lsmul k[X] N X)
      H.piece H.piece δ := TauCeti.LinearMap.isHomogeneous_def.mpr hY
  have heq : componentMap G H f r ∘ₗ
      (_root_.LinearMap.lsmul k[X] M X).restrictScalars k =
      (_root_.LinearMap.lsmul k[X] N X).restrictScalars k ∘ₗ componentMap G H f r := by
    apply G.linearMap_ext
    intro p y hy
    simp only [_root_.LinearMap.comp_apply, _root_.LinearMap.restrictScalars_apply,
      _root_.LinearMap.lsmul_apply]
    rw [componentMap_apply_of_mem G H f r (hX hy), map_smul,
      componentMap_apply_of_mem G H f r hy]
    have hindex : (p + δ) + r = (p + r) + δ := by omega
    rw [hindex]
    exact (hhom.map_decompose (p + r) (f y)).symm
  exact _root_.LinearMap.congr_fun heq x

include hX hY in
private theorem componentMap_smul (f : M →ₗ[k[X]] N) (r : ℤ) (a : k[X]) (x : M) :
    componentMap G H f r (a • x) = a • componentMap G H f r x := by
  have hpow (n : ℕ) (y : M) : componentMap G H f r ((X ^ n : k[X]) • y) =
      (X ^ n : k[X]) • componentMap G H f r y := by
    induction n generalizing y with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_smul, ih, componentMap_X_smul G H hX hY, mul_smul]
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, mul_smul, ← algebraMap_eq, algebraMap_smul,
      map_smul, hpow, mul_smul, algebraMap_smul]

/-- The degree-`r` part of a polynomial-linear map between internally graded modules on which
`X` shifts degree by the same integer `δ`. It selects the degree-`(p + r)` component of the
image of each degree-`p` input component and sums these finitely many values. -/
def homogeneousPart (f : M →ₗ[k[X]] N) (r : ℤ) : M →ₗ[k[X]] N where
  toFun := componentMap G H f r
  map_add' := (componentMap G H f r).map_add
  map_smul' a x := componentMap_smul G H hX hY f r a x

/-- On a degree-`p` input, the degree-`r` part of a map is the degree-`(p + r)` projection
of its image. -/
theorem homogeneousPart_apply_of_mem (f : M →ₗ[k[X]] N) (r : ℤ)
    {p : ℤ} {x : M} (hx : x ∈ G.piece p) :
    G.homogeneousPart H hX hY f r x =
      (DirectSum.decompose H.piece (f x) (p + r) : N) :=
  componentMap_apply_of_mem G H f r hx

/-- Every homogeneous part of the zero map is zero. This case is also simplified by
`homogeneousPart_eq_self`. -/
theorem homogeneousPart_zero (r : ℤ) :
    G.homogeneousPart H hX hY 0 r = 0 := by
  apply _root_.LinearMap.restrictScalars_injective k
  apply G.linearMap_ext
  intro p x hx
  simp [G.homogeneousPart_apply_of_mem H hX hY 0 r hx]

/-- Taking a homogeneous part preserves addition of polynomial-linear maps. -/
@[simp]
theorem homogeneousPart_add (f g : M →ₗ[k[X]] N) (r : ℤ) :
    G.homogeneousPart H hX hY (f + g) r =
      G.homogeneousPart H hX hY f r + G.homogeneousPart H hX hY g r := by
  apply _root_.LinearMap.restrictScalars_injective k
  apply G.linearMap_ext
  intro p x hx
  simp only [_root_.LinearMap.restrictScalars_apply, _root_.LinearMap.add_apply,
    G.homogeneousPart_apply_of_mem H hX hY (f + g) r hx,
    G.homogeneousPart_apply_of_mem H hX hY f r hx,
    G.homogeneousPart_apply_of_mem H hX hY g r hx, DirectSum.decompose_add,
    DirectSum.add_apply, Submodule.coe_add]

/-- Taking the degree-`r` part of a map already homogeneous of degree `r` recovers the map. -/
@[simp]
theorem homogeneousPart_eq_self (f : M →ₗ[k[X]] N) (r : ℤ)
    (hf : TauCeti.LinearMap.IsHomogeneous f G.piece H.piece r) :
    G.homogeneousPart H hX hY f r = f := by
  apply _root_.LinearMap.restrictScalars_injective k
  apply G.linearMap_ext
  intro p x hx
  rw [_root_.LinearMap.restrictScalars_apply, _root_.LinearMap.restrictScalars_apply,
    G.homogeneousPart_apply_of_mem H hX hY f r hx]
  exact DirectSum.decompose_of_mem_same H.piece (hf.map_mem hx)

/-- The degree-`r` component of a polynomial-linear map is homogeneous of degree `r`. -/
theorem isHomogeneous_homogeneousPart (f : M →ₗ[k[X]] N) (r : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (G.homogeneousPart H hX hY f r) G.piece H.piece r := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro p x hx
  rw [G.homogeneousPart_apply_of_mem H hX hY f r hx]
  exact (DirectSum.decompose H.piece (f x) (p + r)).property

end TauCeti.InternalGrading
