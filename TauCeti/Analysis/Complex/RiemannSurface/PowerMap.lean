/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Polynomial

/-!
# The power maps of the Riemann sphere

For `n ≠ 0`, the power map `z ↦ z ^ n` of `ℂ` extends to the Riemann sphere `OnePoint ℂ` by
sending `∞` to `∞`; this extension is Mathlib's `OnePoint.map`. In the affine chart it is
`z ↦ z ^ n`, and in the inverted chart at `∞` it is again `w ↦ w ^ n`, because
`(w⁻¹ ^ n)⁻¹ = w ^ n`. So it is holomorphic, it has local multiplicity `n` at `0` and at `∞`, and
local multiplicity `1` everywhere else, where its derivative `n z ^ (n - 1)` does not vanish.

Its fibre over `0` is the single point `0`, so its degree is `n`, and its only possible branch
values are `0` and `∞`. Together with the identity (`n = 1`), these are the simplest finite
holomorphic maps of the sphere, and the basic examples of branched covers of the sphere with
few branch values: `z ↦ z ^ n` is the local model of every branched cover near a ramification
point of index `n`.

The power map is the polynomial map of `X ^ n`, so holomorphy, the local multiplicities away from
`0`, the degree and the branch values are read off from the general polynomial maps of the sphere,
using that `0` is the only critical point of `X ^ n` when `n ≥ 2`, while `X` has no critical
points.

## Main declarations

* `TauCeti.RiemannSurface.mdifferentiable_onePointMap_pow`: the extension of `z ↦ z ^ n` to the
  Riemann sphere is holomorphic.
* `TauCeti.RiemannSurface.localMultiplicity_onePointMap_pow_zero`,
  `TauCeti.RiemannSurface.localMultiplicity_onePointMap_pow_infty`,
  `TauCeti.RiemannSurface.localMultiplicity_onePointMap_pow_coe_of_ne_zero`: its local
  multiplicities are `n` at `0` and `∞`, and `1` elsewhere.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.spherePow`: the power map as a finite holomorphic
  map of the Riemann sphere.
* `TauCeti.RiemannSurface.degree_onePointMap_pow`: it has degree `n`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.branchValues_spherePow_subset`: its branch values
  lie in `{0, ∞}`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §1.5 (c) (the charts of the Riemann sphere) and §2 (the local behaviour of
  holomorphic maps, `z ↦ z ^ k`).
-/

public noncomputable section

open Filter Function OnePoint Polynomial Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {n : ℕ}

/-- The extension of `X ^ n` to the Riemann sphere is the extension of `z ↦ z ^ n`. -/
private theorem onePointMap_eval_X_pow :
    (OnePoint.map fun z : ℂ ↦ (X ^ n : ℂ[X]).eval z) = OnePoint.map fun z : ℂ ↦ z ^ n := by
  simp

/-- **The power maps of the Riemann sphere are holomorphic.** For `n ≠ 0`, the extension of
`z ↦ z ^ n` to `OnePoint ℂ`, sending `∞` to `∞`, is holomorphic. -/
theorem mdifferentiable_onePointMap_pow (hn : n ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (OnePoint.map fun z : ℂ ↦ z ^ n) := by
  rw [← onePointMap_eval_X_pow]
  exact mdifferentiable_onePointMap_eval (by simp [Nat.pos_iff_ne_zero, hn])

/-- At a finite point `z`, the local multiplicity of the extension of `z ↦ z ^ n` to the Riemann
sphere is the order of vanishing of `w ↦ w ^ n - z ^ n` at `z`: both charts are the affine
chart. -/
private theorem localMultiplicity_onePointMap_pow_coe (z : ℂ) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) (z : OnePoint ℂ) =
      analyticOrderNatAt (fun w ↦ w ^ n - z ^ n) z := by
  simp [localMultiplicity_def]

/-- The extension of `z ↦ z ^ n` to the Riemann sphere has local multiplicity `n` at `0`. -/
@[simp]
theorem localMultiplicity_onePointMap_pow_zero :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) ((0 : ℂ) : OnePoint ℂ) = n := by
  simpa [localMultiplicity_onePointMap_pow_coe] using localMultiplicity_pow_zero n

/-- The extension of `z ↦ z ^ n` to the Riemann sphere has local multiplicity `n` at `∞`, where
it is `w ↦ w ^ n` in the inverted chart. -/
@[simp]
theorem localMultiplicity_onePointMap_pow_infty (hn : n ≠ 0) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) (∞ : OnePoint ℂ) = n := by
  rw [← onePointMap_eval_X_pow,
    localMultiplicity_onePointMap_eval_infty (by simp [Nat.pos_iff_ne_zero, hn]), natDegree_X_pow]

/-- Away from `0` and `∞`, the extension of `z ↦ z ^ n` to the Riemann sphere has local
multiplicity `1`: there the derivative `n z ^ (n - 1)` does not vanish. -/
theorem localMultiplicity_onePointMap_pow_coe_of_ne_zero (hn : n ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) (z : OnePoint ℂ) = 1 := by
  rw [← onePointMap_eval_X_pow]
  exact localMultiplicity_onePointMap_eval_coe_of_not_isRoot (by simp [Nat.pos_iff_ne_zero, hn])
    (by simp [derivative_X_pow, hn, hz])

namespace FiniteHolomorphicMap

/-- The **power map** `z ↦ z ^ n` of the Riemann sphere, for `n ≠ 0`, sending `∞` to `∞`, as a
finite holomorphic map: the polynomial map of `X ^ n`. -/
def spherePow (hn : n ≠ 0) : FiniteHolomorphicMap (OnePoint ℂ) (OnePoint ℂ) :=
  spherePolynomial (p := X ^ n) (by simp [Nat.pos_iff_ne_zero, hn])

@[simp]
theorem coe_spherePow (hn : n ≠ 0) :
    ⇑(spherePow hn) = OnePoint.map fun z : ℂ ↦ z ^ n :=
  (coe_spherePolynomial _).trans onePointMap_eval_X_pow

/-- The branch values of the power map `z ↦ z ^ n` of the Riemann sphere lie in `{0, ∞}`. -/
theorem branchValues_spherePow_subset (hn : n ≠ 0) :
    (spherePow hn).branchValues ⊆ {((0 : ℂ) : OnePoint ℂ), ∞} := by
  refine (branchValues_spherePolynomial_subset _).trans (insert_subset_iff.2 ⟨by simp, ?_⟩)
  rintro _ ⟨_, hy, rfl⟩
  obtain ⟨z, hz, rfl⟩ := mem_criticalValues.mp hy
  rw [mem_rootSet_of_ne (by simp [derivative_X_pow, hn])] at hz
  simp [derivative_X_pow, hn] at hz
  simp [hz, zero_pow hn]

end FiniteHolomorphicMap

/-- The power map `z ↦ z ^ n` of the Riemann sphere has degree `n`, the degree of `X ^ n`. -/
@[simp]
theorem degree_onePointMap_pow (hn : n ≠ 0) :
    degree (OnePoint.map fun z : ℂ ↦ z ^ n) = n := by
  rw [← onePointMap_eval_X_pow, degree_onePointMap_eval (by simp [Nat.pos_iff_ne_zero, hn]),
    natDegree_X_pow]

end TauCeti.RiemannSurface
