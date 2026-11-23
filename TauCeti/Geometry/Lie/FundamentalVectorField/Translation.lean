/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import TauCeti.Geometry.Manifold.Algebra.TypeTags

/-!
# The fundamental vector fields of translations

A normed space `V` acts on itself by translations. As a Lie group action, this is the action of
`Multiplicative V`, the Lie group with the charts of `V`, by `g • x = toAdd g + x`
(`Multiplicative.contMDiffSMulSelf`). Its Lie algebra is the tangent space of `V` at the origin,
which Mathlib identifies with `V` itself by `tangentSpaceCastModel`.

Every translation has derivative the identity, so the fundamental vector field of `ξ` is the
constant vector field `ξ` (`TauCeti.fundamentalVectorField_multiplicative`). For a
finite-dimensional real space, the infinitesimal action by fundamental vector fields is therefore
the action of the abelian Lie algebra `V` by infinitesimal translations
(`TauCeti.InfinitesimalAction.fundamental_multiplicative`). These are the generators of the
phase-space translations of a symplectic vector space, whose moment maps are not equivariant.

## Main results

* `TauCeti.fundamentalVectorField_multiplicative`: the fundamental vector fields of translations
  are constant.
* `TauCeti.InfinitesimalAction.fundamental_multiplicative`: the fundamental vector fields of the
  translation action form the infinitesimal translation action.
-/

public section

open scoped Manifold

namespace TauCeti

/-- **The fundamental vector fields of translations are constant.** For the action of
`Multiplicative V` on a normed space `V` by translations, the fundamental vector field of `ξ` is
the constant vector field `ξ`. -/
theorem fundamentalVectorField_multiplicative {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (ξ : GroupLieAlgebra 𝓘(𝕜, V) (Multiplicative V)) (x : V) :
    fundamentalVectorField 𝓘(𝕜, V) ξ x =
      tangentSpaceCastModel 𝓘(𝕜, V) (1 : Multiplicative V) ξ := by
  rw [fundamentalVectorField_apply]
  -- `Multiplicative V` carries the charts of `V`, so its orbit map is the translation `v ↦ v + x`.
  have h : mfderiv 𝓘(𝕜, V) 𝓘(𝕜, V) (fun g : Multiplicative V ↦ g • x) 1 =
      fderiv 𝕜 (fun v : V ↦ v + x) 0 := mfderiv_eq_fderiv
  rw [h, fderiv_add_const, fderiv_fun_id]
  -- Both sides are `ξ`, read in the model space `V`.
  rfl

/-- **The infinitesimal action of the translation group.** On a finite-dimensional real normed
space `V`, the fundamental vector fields of the action of `Multiplicative V` by translations are
the infinitesimal translations `x ↦ ξ` of its abelian Lie algebra. -/
theorem InfinitesimalAction.fundamental_multiplicative {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    InfinitesimalAction.fundamental 𝓘(ℝ, V) (Multiplicative V) 𝓘(ℝ, V) V =
      InfinitesimalAction.translation
        (tangentSpaceCastModel 𝓘(ℝ, V) (1 : Multiplicative V)).toLinearMap := by
  ext ξ x
  rw [InfinitesimalAction.fundamental_apply, fundamentalVectorField_multiplicative,
    InfinitesimalAction.translation_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]

end TauCeti
