/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Nil.LieAlgebra
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit

/-!
# The Kirillov–Kostant–Souriau form on the coadjoint orbits of Nil

For a functional `μ` on the Lie algebra `𝔫` of the real Heisenberg group `Nil`, the coset space
`Nil ⧸ Nil_μ` of its coadjoint stabilizer is the coadjoint orbit of `μ` with its intrinsic smooth
structure, carrying the Kirillov–Kostant–Souriau form `ω_μ` of
`TauCeti.Geometry.Symplectic.Coadjoint.Orbit`. This file evaluates `ω_μ` and the orbit map on the
generators `ξ_O` of the action of `Nil`, in the coordinates of
`TauCeti.Geometry.Manifold.Riemannian.Nil.LieAlgebra`.

Write `(p, q, r) = (μ'(∂_x), μ'(∂_y), μ'(∂_z))` for the coordinates of a point `μ'` of the orbit,
and `(s, t, u)` for the coordinates of `ξ ∈ 𝔫`. The orbit map `[g] ↦ Ad*_g μ` moves along `ξ_O`
with velocity `(t r, -s r, 0)`
(`TauCeti.Nil.mvfderiv_orbitMap_apply_lieAlgebraLieEquiv_symm_heisenbergX` and its companions), and
the form is

`ω_μ(ξ_O, η_O) = r (s t' - t s')`

(`TauCeti.Nil.eval₂_coadjointOrbitForm_fundamentalVectorField`). On the orbit of a functional with
`r ≠ 0`, the plane `{μ' | μ'(∂_z) = r}`, the generator `ξ_O` has `dp(ξ_O) = t r` and
`dq(ξ_O) = -s r`, so these formulas say that `ω_μ = dp ∧ dq / r` there.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2 and Chapter 2 (the Heisenberg group).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.Nil

local notation "J" => 𝓘(ℝ, ℝ × ℝ × ℝ)

local notation "𝔫" => GroupLieAlgebra J Nil

/-- The coordinates of an element of the Lie algebra of `Nil`. -/
local notation "𝔠" => tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (1 : Nil)

/-- The central generator `∂_z` of the Lie algebra of `Nil`. -/
local notation "ζ" => lieAlgebraLieEquiv.symm (heisenbergZ ℝ)

variable {μ : Dual ℝ 𝔫} (x : Nil ⧸ (Lie.coadjointRepresentation ℝ J Nil).stabilizer μ) (ξ : 𝔫)

/-- The central coordinate `r = μ'(∂_z)` is constant along the coadjoint orbit of `μ`. -/
@[simp]
theorem orbitMap_coadjointRepresentation_apply_lieAlgebraLieEquiv_symm_heisenbergZ :
    (Lie.coadjointRepresentation ℝ J Nil).orbitMap μ x ζ = μ ζ := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [Representation.orbitMap_mk,
      coadjointRepresentation_apply_lieAlgebraLieEquiv_symm_heisenbergZ]

/-- **The KKS form of a coadjoint orbit of `Nil` on its generators.** At every point of the orbit
`Nil ⧸ Nil_μ`, `ω_μ(ξ_O, η_O) = r (s t' - t s')`, where `r = μ(∂_z)` and `(s, t, u)`,
`(s', t', u')` are the coordinates of `ξ` and `η`. -/
theorem eval₂_coadjointOrbitForm_fundamentalVectorField (η : 𝔫) :
    SmoothBundleForm.eval₂ μ.coadjointOrbitForm x (fundamentalVectorField _ ξ x)
        (fundamentalVectorField _ η x) =
      μ ζ * ((𝔠 ξ).1 * (𝔠 η).2.1 - (𝔠 ξ).2.1 * (𝔠 η).1) := by
  rw [Dual.eval₂_coadjointOrbitForm_fundamentalVectorField,
    lie_eq_smul_lieAlgebraLieEquiv_symm_heisenbergZ, map_smul, smul_eq_mul, mul_comm,
    orbitMap_coadjointRepresentation_apply_lieAlgebraLieEquiv_symm_heisenbergZ]

/-- **The generators of a coadjoint orbit of `Nil`, first coordinate**: along `ξ_O`, the coordinate
`p = μ'(∂_x)` of the orbit map changes at the rate `t r`. -/
theorem mvfderiv_orbitMap_apply_lieAlgebraLieEquiv_symm_heisenbergX :
    mvfderiv
        𝓘(ℝ, Subgroup.QuotientModelSpace J ((Lie.coadjointRepresentation ℝ J Nil).stabilizer μ))
        (fun y ↦ (Lie.coadjointRepresentation ℝ J Nil).orbitMap μ y
        (lieAlgebraLieEquiv.symm (heisenbergX ℝ))) x (fundamentalVectorField _ ξ x) =
      (𝔠 ξ).2.1 * μ ζ := by
  rw [Dual.mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField,
    lie_eq_smul_lieAlgebraLieEquiv_symm_heisenbergZ, map_smul, smul_eq_mul,
    orbitMap_coadjointRepresentation_apply_lieAlgebraLieEquiv_symm_heisenbergZ]
  simp

/-- **The generators of a coadjoint orbit of `Nil`, second coordinate**: along `ξ_O`, the
coordinate `q = μ'(∂_y)` of the orbit map changes at the rate `-s r`. -/
theorem mvfderiv_orbitMap_apply_lieAlgebraLieEquiv_symm_heisenbergY :
    mvfderiv
        𝓘(ℝ, Subgroup.QuotientModelSpace J ((Lie.coadjointRepresentation ℝ J Nil).stabilizer μ))
        (fun y ↦ (Lie.coadjointRepresentation ℝ J Nil).orbitMap μ y
        (lieAlgebraLieEquiv.symm (heisenbergY ℝ))) x (fundamentalVectorField _ ξ x) =
      -((𝔠 ξ).1 * μ ζ) := by
  rw [Dual.mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField,
    lie_eq_smul_lieAlgebraLieEquiv_symm_heisenbergZ, map_smul, smul_eq_mul,
    orbitMap_coadjointRepresentation_apply_lieAlgebraLieEquiv_symm_heisenbergZ]
  simp

/-- **The generators of a coadjoint orbit of `Nil`, third coordinate**: the coordinate
`r = μ'(∂_z)` of the orbit map is stationary along every `ξ_O`. -/
theorem mvfderiv_orbitMap_apply_lieAlgebraLieEquiv_symm_heisenbergZ :
    mvfderiv
        𝓘(ℝ, Subgroup.QuotientModelSpace J ((Lie.coadjointRepresentation ℝ J Nil).stabilizer μ))
        (fun y ↦ (Lie.coadjointRepresentation ℝ J Nil).orbitMap μ y ζ) x
        (fundamentalVectorField _ ξ x) = 0 := by
  rw [Dual.mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField,
    lie_eq_smul_lieAlgebraLieEquiv_symm_heisenbergZ, map_smul, smul_eq_mul]
  simp

end TauCeti.Nil
