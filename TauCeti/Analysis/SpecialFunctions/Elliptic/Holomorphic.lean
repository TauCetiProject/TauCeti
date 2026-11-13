/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.ComplexManifold
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Topology
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Complex.Chart
public import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Complex uniformization is biholomorphic

For a period lattice `Λ`, the Weierstrass point map `z ↦ (℘(z), ℘'(z) / 2)`, extended by the point
at infinity on `Λ`, is holomorphic from `ℂ` to the points of the Weierstrass curve
`E_Λ : y² = x³ - (g₂ / 4) x - g₃ / 4`, with their complex manifold structure as a smooth plane
cubic (`WeierstrassCurve.Projective.Point.instIsManifold`). Near every point it is given by
holomorphic nonsingular homogeneous coordinates: `[℘ : ℘' / 2 : 1]` off the lattice and
`[2 ℘ / ℘' : 1 : 2 / ℘']` near the lattice.

The point map descends to the isomorphism of topological groups `ℂ / Λ ≃ₜ+ E_Λ(ℂ)`
(`PeriodPair.weierstrassPointContinuousAddEquiv`). The torus `ℂ / Λ` is a complex manifold whose
projection from `ℂ` is a local biholomorphism, so this isomorphism is holomorphic, and its inverse,
the inverse of a holomorphic homeomorphism of Riemann surfaces, is holomorphic as well. Hence the
complex uniformization `ℂ / Λ ≃ E_Λ(ℂ)` is a biholomorphic group isomorphism.

## Main results

* `PeriodPair.contMDiff_weierstrassPoint_toProjective`: the Weierstrass point map `ℂ → E_Λ(ℂ)` is
  holomorphic.
* `PeriodPair.weierstrassPointDiffeomorph`: the biholomorphism `ℂ / Λ ≃ E_Λ(ℂ)`, whose underlying
  map is the group isomorphism `PeriodPair.weierstrassPointContinuousAddEquiv`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, Proposition VI.3.6.
-/

public section

open WeierstrassCurve
open scoped Manifold ContDiff

namespace PeriodPair

variable (L : PeriodPair)

/-- **The Weierstrass point map is holomorphic.** The map `z ↦ (℘(z), ℘'(z) / 2)` from `ℂ` to the
points of the Weierstrass curve of `Λ`, sending `Λ` to the point at infinity, is analytic, and so
`C^r` for every `r`. -/
theorem contMDiff_weierstrassPoint_toProjective (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) r (fun z ↦ (L.weierstrassPoint z).toProjective) := fun z₀ ↦ by
  obtain ⟨P, hP, h⟩ := L.exists_analyticAt_mk_eq_weierstrassPoint_toProjective z₀
  exact Projective.Point.contMDiffAt_of_eventually_eq_mk
    (hP.contDiffAt.contMDiffAt.of_le le_top) h

/-- The isomorphism `ℂ / Λ ≃ₜ+ E_Λ(ℂ)` induced by the Weierstrass point map is holomorphic. -/
private theorem contMDiff_weierstrassPointContinuousAddEquiv (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) r L.weierstrassPointContinuousAddEquiv := by
  rw [L.lattice.toAddSubgroup.contMDiff_quotient_iff (n := ω) le_top]
  simpa only [Function.comp_def, weierstrassPointContinuousAddEquiv_mk] using
    L.contMDiff_weierstrassPoint_toProjective r

/-- **Complex uniformization is biholomorphic.** The isomorphism of complex Lie groups
`ℂ / Λ ≃ E_Λ(ℂ)` induced by the Weierstrass point map, as a `C^r` diffeomorphism for every `r`;
for `r = ω` it is a biholomorphism. Its underlying map is the group isomorphism
`PeriodPair.weierstrassPointContinuousAddEquiv`
(`PeriodPair.coe_weierstrassPointDiffeomorph`). -/
noncomputable def weierstrassPointDiffeomorph (r : ℕ∞ω) :
    (ℂ ⧸ L.lattice.toAddSubgroup) ≃ₘ^r⟮𝓘(ℂ), 𝓘(ℂ)⟯ L.weierstrassCurve.toProjective.Point where
  toEquiv := L.weierstrassPointContinuousAddEquiv.toEquiv
  contMDiff_toFun := L.contMDiff_weierstrassPointContinuousAddEquiv r
  contMDiff_invFun := by
    -- The inverse of a holomorphic homeomorphism of Riemann surfaces is holomorphic.
    let e := L.weierstrassPointContinuousAddEquiv.toHomeomorph
    have he : e.isHomeomorph.homeomorph e = e := Homeomorph.ext fun _ ↦ rfl
    have h := e.isHomeomorph.mdifferentiable_symm
      ((L.contMDiff_weierstrassPointContinuousAddEquiv 1).mdifferentiable one_ne_zero)
    rw [he] at h
    exact h.contMDiff

/-- The biholomorphism `ℂ / Λ ≃ E_Λ(ℂ)` is the group isomorphism
`PeriodPair.weierstrassPointContinuousAddEquiv`. -/
@[simp]
theorem coe_weierstrassPointDiffeomorph (r : ℕ∞ω) :
    ⇑(L.weierstrassPointDiffeomorph r) = L.weierstrassPointContinuousAddEquiv :=
  (rfl)

/-- The inverse of the biholomorphism `ℂ / Λ ≃ E_Λ(ℂ)` is the inverse of the group isomorphism
`PeriodPair.weierstrassPointContinuousAddEquiv`. -/
@[simp]
theorem coe_weierstrassPointDiffeomorph_symm (r : ℕ∞ω) :
    ⇑(L.weierstrassPointDiffeomorph r).symm = L.weierstrassPointContinuousAddEquiv.symm :=
  (rfl)

end PeriodPair
