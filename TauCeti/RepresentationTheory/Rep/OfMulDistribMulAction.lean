/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.RepresentationTheory.Invariants

/-!
# Additive representations from multiplicative distributive actions

Given a multiplicative distributive action of a monoid `G` on a commutative group `M`, Mathlib's
`Rep.ofMulDistribMulAction G M` views `Additive M` as a `ℤ`-linear representation of `G`. This file
supplies evaluation, kernel, norm, and coefficient-transport lemmas for
`Rep.ofMulDistribMulAction`:

* `Rep.toAdditive_ofMulDistribMulAction_ρ_apply` and `Rep.toAdditive_ofMulDistribMulAction_norm`:
  pointwise action and norm in `Rep.toAdditive` coordinates;
* `Rep.norm_ofMulDistribMulAction_apply` and `Rep.mem_range_norm_ofMulDistribMulAction_iff`:
  explicit evaluation and range membership of the norm in multiplicative coordinates;
* `Rep.ofMulDistribMulAction_ρ_eq_neg_of_smul_eq_inv`: an element acting by inversion on `M` acts
  by negation on `Rep.ofMulDistribMulAction G M`;
* `Rep.mem_ker_applyAsHom_sub_of_smul_eq_self`: fixed points of `g : G` in `M` lie in the kernel
  of `ρ(g) - 𝟙`;
* `Rep.ofMulDistribMulActionLinearEquiv`, `Rep.ofMulDistribMulActionResHom`, and
  `Rep.ofMulDistribMulActionResHom_hom_toLinearMap`: the `ℤ`-linear equivalence, intertwining
  morphism, and underlying linear map induced by action-intertwining equivalences `eM : M' ≃* M`
  and `eG : G ≃* G'`.
-/

public section

open CategoryTheory

namespace Rep

section NormAndAction

variable {G M : Type*}

/-- Evaluating the action on `Rep.ofMulDistribMulAction G M` in `Rep.toAdditive` coordinates. -/
theorem toAdditive_ofMulDistribMulAction_ρ_apply [Monoid G] [CommGroup M]
    [MulDistribMulAction G M] (g : G) (x : Rep.ofMulDistribMulAction G M) :
    Rep.toAdditive (M := G) (G := M) ((Rep.ofMulDistribMulAction G M).ρ g x) =
      Additive.ofMul (g • Additive.toMul (Rep.toAdditive (M := G) (G := M) x)) :=
  Rep.ofMulDistribMulAction_ρ_apply_apply g (Rep.toAdditive (M := G) (G := M) x)

/-- Evaluating the norm on `Rep.ofMulDistribMulAction G M` in `Rep.toAdditive` coordinates. -/
theorem toAdditive_ofMulDistribMulAction_norm [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (x : Rep.ofMulDistribMulAction G M) :
    Rep.toAdditive (M := G) (G := M) ((Rep.ofMulDistribMulAction G M).ρ.norm x) =
      Additive.ofMul (∏ g : G, g • Additive.toMul (Rep.toAdditive (M := G) (G := M) x)) := by
  rw [Representation.norm, LinearMap.sum_apply, map_sum, ofMul_prod]
  simp only [toAdditive_ofMulDistribMulAction_ρ_apply]

/-- On `Rep.ofMulDistribMulAction G M`, the norm sends `Additive.ofMul m` to
`Additive.ofMul (∏ x : G, x • m)`. -/
theorem norm_ofMulDistribMulAction_apply [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (m : M) :
    (Rep.ofMulDistribMulAction G M).norm.asHom.hom.toLinearMap
        ((Rep.toAdditive (M := G) (G := M)).symm (Additive.ofMul m)) =
      (Rep.toAdditive (M := G) (G := M)).symm (Additive.ofMul (∏ x : G, x • m)) := by
  apply (Rep.toAdditive (M := G) (G := M)).injective
  rw [Representation.IntertwiningMap.toLinearMap_apply, Rep.norm_apply,
    toAdditive_ofMulDistribMulAction_norm, AddEquiv.apply_symm_apply, toMul_ofMul,
    AddEquiv.apply_symm_apply]

/-- An element `Additive.ofMul a` lies in the range of the norm on
`Rep.ofMulDistribMulAction G M` if and only if `a` is a norm `∏ x : G, x • m` in `M`. -/
theorem mem_range_norm_ofMulDistribMulAction_iff [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (a : M) :
    (Rep.toAdditive (M := G) (G := M)).symm (Additive.ofMul a) ∈
        LinearMap.range (Rep.ofMulDistribMulAction G M).norm.asHom.hom.toLinearMap ↔
      ∃ m : M, ∏ x : G, x • m = a := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    let m' : M := Additive.toMul (Rep.toAdditive (M := G) (G := M) m)
    refine ⟨m', Additive.ofMul.injective ((Rep.toAdditive (M := G) (G := M)).symm.injective ?_)⟩
    rw [← norm_ofMulDistribMulAction_apply (G := G) m']
    simpa only [m', ofMul_toMul, AddEquiv.symm_apply_apply] using hm
  · rintro ⟨m, rfl⟩
    exact ⟨(Rep.toAdditive (M := G) (G := M)).symm (Additive.ofMul m),
      norm_ofMulDistribMulAction_apply (G := G) m⟩

/-- If `g : G` acts on `M` by inversion, then `g` acts by negation on the additive representation
`Rep.ofMulDistribMulAction G M`. -/
theorem ofMulDistribMulAction_ρ_eq_neg_of_smul_eq_inv [Monoid G] [CommGroup M]
    [MulDistribMulAction G M] {g : G} (hinv : ∀ m : M, g • m = m⁻¹)
    (x : Rep.ofMulDistribMulAction G M) :
    (Rep.ofMulDistribMulAction G M).ρ g x = -x := by
  apply (Rep.toAdditive (M := G) (G := M)).injective
  rw [toAdditive_ofMulDistribMulAction_ρ_apply, map_neg,
    hinv (Additive.toMul (Rep.toAdditive (M := G) (G := M) x)), ofMul_inv, ofMul_toMul]

/-- An element `a : M` fixed by `g : G` defines an element in the kernel of `ρ(g) - 𝟙` on
`Rep.ofMulDistribMulAction G M`. -/
theorem mem_ker_applyAsHom_sub_of_smul_eq_self [CommMonoid G] [CommGroup M]
    [MulDistribMulAction G M] {g : G} {a : M} (ha : g • a = a) :
    (Rep.toAdditive (M := G) (G := M)).symm (Additive.ofMul a) ∈ LinearMap.ker
      (Rep.applyAsHom (Rep.ofMulDistribMulAction G M) g - 𝟙 _).hom.toLinearMap := by
  rw [LinearMap.mem_ker, Rep.applyAsHom_sub_id_apply]
  apply (Rep.toAdditive (M := G) (G := M)).injective
  rw [map_sub, map_zero, toAdditive_ofMulDistribMulAction_ρ_apply, AddEquiv.apply_symm_apply,
    toMul_ofMul, ha, sub_self]

end NormAndAction

section CoefficientTransport

/-- The `ℤ`-linear equivalence between the underlying modules of `Rep.ofMulDistribMulAction G M`
and `Rep.ofMulDistribMulAction G' M'` induced by `eM : M' ≃* M`. -/
def ofMulDistribMulActionLinearEquiv (G : Type*) {M : Type*} (G' : Type*) {M' : Type*}
    [Monoid G] [CommGroup M] [MulDistribMulAction G M]
    [Monoid G'] [CommGroup M'] [MulDistribMulAction G' M']
    (eM : M' ≃* M) :
    (Rep.ofMulDistribMulAction G M).V ≃ₗ[ℤ] (Rep.ofMulDistribMulAction G' M').V :=
  ((Rep.toAdditive (M := G) (G := M)).trans
    ((MulEquiv.toAdditive eM.symm).trans
      (Rep.toAdditive (M := G') (G := M')).symm)).toIntLinearEquiv

/-- Pointwise action of `Rep.ofMulDistribMulActionLinearEquiv` in additive coordinates. -/
theorem toAdditive_ofMulDistribMulActionLinearEquiv {G M G' M' : Type*}
    [Monoid G] [CommGroup M] [MulDistribMulAction G M]
    [Monoid G'] [CommGroup M'] [MulDistribMulAction G' M']
    (eM : M' ≃* M) (a : Rep.ofMulDistribMulAction G M) :
    Rep.toAdditive (M := G') (G := M') (ofMulDistribMulActionLinearEquiv G G' eM a) =
      Additive.ofMul (eM.symm (Additive.toMul (Rep.toAdditive (M := G) (G := M) a))) :=
  (rfl)

/-- The inverse of `ofMulDistribMulActionLinearEquiv` is induced by `eM.symm`. -/
@[simp]
theorem ofMulDistribMulActionLinearEquiv_symm {G M G' M' : Type*}
    [Monoid G] [CommGroup M] [MulDistribMulAction G M]
    [Monoid G'] [CommGroup M'] [MulDistribMulAction G' M']
    (eM : M' ≃* M) :
    (ofMulDistribMulActionLinearEquiv G G' eM).symm =
      ofMulDistribMulActionLinearEquiv G' G eM.symm := by
  refine LinearEquiv.ext fun a ↦ (ofMulDistribMulActionLinearEquiv G G' eM).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  apply (Rep.toAdditive (M := G') (G := M')).injective
  rw [toAdditive_ofMulDistribMulActionLinearEquiv, toAdditive_ofMulDistribMulActionLinearEquiv,
    toMul_ofMul, MulEquiv.symm_symm, MulEquiv.symm_apply_apply, ofMul_toMul]

/-- `ofMulDistribMulActionLinearEquiv` intertwines the actions of `G` and `G'` when `eM` and `eG`
intertwine the underlying `MulDistribMulAction`s. -/
theorem ofMulDistribMulActionLinearEquiv_isIntertwining {G M G' M' : Type*}
    [Monoid G] [CommGroup M] [MulDistribMulAction G M]
    [Monoid G'] [CommGroup M'] [MulDistribMulAction G' M']
    (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) (g : G) :
    (ofMulDistribMulActionLinearEquiv G G' eM : _ →ₗ[ℤ] _) ∘ₗ
        (Rep.ofMulDistribMulAction G M).ρ g =
      (Rep.ofMulDistribMulAction G' M').ρ (eG g) ∘ₗ
        (ofMulDistribMulActionLinearEquiv G G' eM : _ →ₗ[ℤ] _) :=
  LinearMap.ext fun a ↦ (Rep.toAdditive (M := G') (G := M')).injective <| by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      toAdditive_ofMulDistribMulActionLinearEquiv, toAdditive_ofMulDistribMulAction_ρ_apply,
      toAdditive_ofMulDistribMulAction_ρ_apply, toAdditive_ofMulDistribMulActionLinearEquiv,
      toMul_ofMul, toMul_ofMul]
    exact congrArg Additive.ofMul (eM.injective (by simp [hsmul]))

/-- The intertwining morphism `Rep.res eG.symm (Rep.ofMulDistribMulAction G M) ⟶
Rep.ofMulDistribMulAction G' M'` induced by action-intertwining equivalences `eM` and `eG`. -/
def ofMulDistribMulActionResHom {G G' : Type*} {M M' : Type _}
    [Group G] [CommGroup M] [MulDistribMulAction G M]
    [Group G'] [CommGroup M'] [MulDistribMulAction G' M']
    (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) :
    Rep.res eG.symm.toMonoidHom (Rep.ofMulDistribMulAction G M) ⟶
      Rep.ofMulDistribMulAction G' M' :=
  Rep.ofHom
    { toLinearMap := (ofMulDistribMulActionLinearEquiv G G' eM :
        (Rep.ofMulDistribMulAction G M).V →ₗ[ℤ] (Rep.ofMulDistribMulAction G' M').V)
      isIntertwining' := fun g' ↦ by
        rw [Rep.coe_res_obj_ρ', MulEquiv.coe_toMonoidHom]
        have h := ofMulDistribMulActionLinearEquiv_isIntertwining eM eG hsmul (eG.symm g')
        rwa [MulEquiv.apply_symm_apply] at h }

/-- The underlying linear map of `Rep.ofMulDistribMulActionResHom` is
`Rep.ofMulDistribMulActionLinearEquiv`. -/
theorem ofMulDistribMulActionResHom_hom_toLinearMap {G G' : Type*} {M M' : Type _}
    [Group G] [CommGroup M] [MulDistribMulAction G M]
    [Group G'] [CommGroup M'] [MulDistribMulAction G' M']
    (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) :
    (ofMulDistribMulActionResHom eM eG hsmul).hom.toLinearMap =
      (ofMulDistribMulActionLinearEquiv G G' eM :
        (Rep.ofMulDistribMulAction G M).V →ₗ[ℤ] (Rep.ofMulDistribMulAction G' M').V) :=
  (rfl)

/-- Pointwise evaluation of `Rep.ofMulDistribMulActionResHom` in additive coordinates. -/
theorem toAdditive_ofMulDistribMulActionResHom_hom {G G' : Type*} {M M' : Type _}
    [Group G] [CommGroup M] [MulDistribMulAction G M]
    [Group G'] [CommGroup M'] [MulDistribMulAction G' M']
    (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m)
    (a : Rep.ofMulDistribMulAction G M) :
    Rep.toAdditive (M := G') (G := M')
        ((ofMulDistribMulActionResHom eM eG hsmul).hom a) =
      Additive.ofMul (eM.symm (Additive.toMul (Rep.toAdditive (M := G) (G := M) a))) :=
  toAdditive_ofMulDistribMulActionLinearEquiv eM a

end CoefficientTransport

end Rep
