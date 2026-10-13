/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import TauCeti.Algebra.Regular.SMul

/-!
# Nonzerodivisors of the structure sheaf and flat morphisms

A flat ring map sends nonzerodivisors to nonzerodivisors, so along a flat morphism of schemes
`f : X ⟶ Y` the image under `f.appLE` of a nonzerodivisor on an affine open of `Y` is a
nonzerodivisor on every affine open of `X` above it (`Scheme.Hom.isSMulRegular_appLE`).

A section that is a nonzerodivisor on every affine open inside `U` is one on every open subset of
`U`, affine or not (`Scheme.isSMulRegular_map_of_forall_affineOpens`). Since restriction between
affine opens is flat, a nonzerodivisor on an affine open `U` therefore remains a nonzerodivisor on
every open subset of `U` (`IsAffineOpen.isSMulRegular_map`). Likewise, the pullback of a
nonzerodivisor along a flat morphism to an affine scheme is a nonzerodivisor on every affine open
of the source (`Scheme.Hom.isSMulRegular_map_appTop`); a nonzerodivisor of a ring `R` is one on
`Spec R` by `Scheme.isSMulRegular_ΓSpecIso_inv`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

variable {X : Scheme.{u}}

/-- A section over `U` whose restriction to every affine open inside `U` is a nonzerodivisor
restricts to a nonzerodivisor on every open subset `V ⊆ U`, affine or not. -/
theorem _root_.AlgebraicGeometry.Scheme.isSMulRegular_map_of_forall_affineOpens {U V : X.Opens}
    (hVU : V ≤ U) {a : Γ(X, U)} (ha : ∀ (W : X.affineOpens) (hWU : W.1 ≤ U),
      IsSMulRegular Γ(X, W) (X.presheaf.map (homOfLE hWU).op a)) :
    IsSMulRegular Γ(X, V) (X.presheaf.map (homOfLE hVU).op a) := by
  intro t₁ t₂ h
  refine X.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  replace hWV : W ≤ V := hWV
  refine ⟨W, hWV, hxW, ha ⟨W, hW⟩ (hWV.trans hVU) ?_⟩
  have hres := congrArg (X.presheaf.map (homOfLE hWV).op) h
  simp only [smul_eq_mul, map_mul] at hres
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] at hres
  simpa only [smul_eq_mul] using hres

/-- Along a flat morphism `f`, the image under `f.appLE` of a nonzerodivisor on an affine open `U`
of the target is a nonzerodivisor on every affine open `V ⊆ f ⁻¹ᵁ U` of the source. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isSMulRegular_appLE {Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) {b : Γ(Y, U)} (hb : IsSMulRegular Γ(Y, U) b) :
    IsSMulRegular Γ(X, V) (f.appLE U V e b) := by
  let := (f.appLE U V e).hom.toAlgebra
  have : Module.Flat Γ(Y, U) Γ(X, V) := f.flat_appLE hU hV e
  simpa only [RingHom.algebraMap_toAlgebra] using hb.of_flat (S := Γ(X, V))

/-- A nonzerodivisor on an affine open `U` restricts to a nonzerodivisor on every open subset
`V ⊆ U`, affine or not. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.isSMulRegular_map {U V : X.Opens}
    (hU : IsAffineOpen U) (hVU : V ≤ U) {a : Γ(X, U)} (ha : IsSMulRegular Γ(X, U) a) :
    IsSMulRegular Γ(X, V) (X.presheaf.map (homOfLE hVU).op a) :=
  Scheme.isSMulRegular_map_of_forall_affineOpens hVU fun W hWU ↦ by
    -- The restriction `Γ(X, U) ⟶ Γ(X, W)` between affine opens is flat, so `a` stays regular on
    -- `W`.
    have hWU' : W.1 ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U := hWU
    have hres : (𝟙 X : X ⟶ X).appLE U W hWU' a = X.presheaf.map (homOfLE hWU).op a := by
      -- `appLE` of the identity is the restriction along `W ≤ 𝟙 X ⁻¹ᵁ U`, and `𝟙 X ⁻¹ᵁ U = U`
      -- holds by definition.
      rfl
    simpa only [hres] using (𝟙 X : X ⟶ X).isSMulRegular_appLE hU W.2 hWU' ha

/-- Along a flat morphism to an affine scheme, the pullback of a nonzerodivisor restricts to a
nonzerodivisor on every affine open of the source. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isSMulRegular_map_appTop {Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [Flat f] {b : Γ(Y, ⊤)} (hb : IsSMulRegular Γ(Y, ⊤) b) (U : X.affineOpens) :
    IsSMulRegular Γ(X, U) (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (f.appTop b)) := by
  have hres : f.appLE ⊤ U.1 le_top b =
      X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (f.appTop b) := by
    -- `appLE` is `app` followed by restriction, `appTop` is `app ⊤`, and `f ⁻¹ᵁ ⊤ = ⊤` holds by
    -- definition.
    rfl
  simpa only [hres] using f.isSMulRegular_appLE (isAffineOpen_top Y) U.2 le_top hb

/-- A nonzerodivisor `π` of a ring `R` is a nonzerodivisor among the global functions on
`Spec R`. -/
theorem _root_.AlgebraicGeometry.Scheme.isSMulRegular_ΓSpecIso_inv {R : Type u} [CommRing R]
    {π : R} (hπ : IsSMulRegular R π) :
    IsSMulRegular Γ(Spec (.of R), ⊤) ((Scheme.ΓSpecIso (.of R)).inv π) :=
  (TauCeti.isSMulRegular_map_iff (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv π).mpr hπ

end TauCeti
