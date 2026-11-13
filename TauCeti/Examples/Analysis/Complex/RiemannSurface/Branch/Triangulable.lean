/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.Analysis.Complex.RiemannSurface.Branch.Triangulable
import TauCeti.Geometry.Manifold.Instances.OnePoint.Triangulation
import TauCeti.Analysis.Complex.RiemannSurface.PowerMap
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Checks of the branched-cover formula on the squaring map of the Riemann sphere

These examples check the topological branched-cover formula `χ(X) = deg f · χ(Y) - R(f)`
(`FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree` in
`TauCeti.RiemannSurface`) on the squaring map `f = (z ↦ z²)` of the Riemann sphere
`OnePoint ℂ`, the power map `TauCeti.RiemannSurface.FiniteHolomorphicMap.spherePow` with
exponent `2`.

* The Riemann sphere is triangulated by the boundary of a tetrahedron, so it keeps finite CW
  type after deleting finitely many points. Deleting `0` and `∞` leaves a cylinder, of Euler
  characteristic `2 - 2 = 0`, each puncture lowering `χ` by one.
* The preimage of `{0, ∞}` under `f` is again `{0, ∞}`, so the punctured formula
  `χ(X \ f⁻¹(S)) = deg f · χ(Y \ S)` reads `0 = 2 · 0`. A model in which a puncture left `χ`
  unchanged would turn it into the false `2 = 2 · 2`.
* `f` has degree `2` and is ramified of index `2` at `0` and at `∞`, so `R(f) = 2`, and the
  branched-cover formula on the whole sphere reads `2 = 2 · 2 - 2`. The sign error
  `χ(X) = deg f · χ(Y) + R(f)` would read `2 = 2 · 2 + 2`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17 (the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4 (the Hurwitz formula and its examples).
-/

open OnePoint Set TauCeti TauCeti.RiemannSurface TauCeti.RiemannSurface.FiniteHolomorphicMap

-- The Riemann sphere is triangulated by the boundary of a tetrahedron.
example : IsTriangulable.{0} (OnePoint ℂ) := isTriangulable_onePoint

-- Deleting `0` and `∞` from the Riemann sphere leaves a cylinder, of Euler characteristic `0`,
-- so a puncture changes the Euler characteristic of the Riemann sphere.
example : eulerChar ↥({((0 : ℂ) : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) = 0 ∧
    eulerChar ↥({((0 : ℂ) : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) ≠ eulerChar (OnePoint ℂ) := by
  have h : eulerChar ↥({((0 : ℂ) : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) = 0 := by
    rw [eulerChar_compl_of_finite (E := ℂ) (toFinite _), eulerChar_onePoint,
      Complex.finrank_real_complex, ncard_pair (coe_ne_infty 0)]
    norm_num
  exact ⟨h, by simp [h, eulerChar_onePoint, Complex.finrank_real_complex]⟩

-- The squaring map of the Riemann sphere has degree `2`.
example : degree (spherePow two_ne_zero) = 2 := by
  simp

-- The squaring map of the Riemann sphere is ramified of index `2` at `0` and at `∞`.
example : localMultiplicity (spherePow two_ne_zero) ((0 : ℂ) : OnePoint ℂ) = 2 ∧
    localMultiplicity (spherePow two_ne_zero) (∞ : OnePoint ℂ) = 2 := by
  simp

-- The squaring map of the Riemann sphere has ramification degree `2`.
example : ramificationDegree (spherePow two_ne_zero) = 2 := by
  simp

-- The preimage of `{0, ∞}` under the squaring map of the Riemann sphere is `{0, ∞}`, so the
-- punctured branched-cover formula, puncturing the target at the branch values `0` and `∞` and
-- the source at their preimage, reads `0 = 2 · 0`.
example : spherePow two_ne_zero ⁻¹' {((0 : ℂ) : OnePoint ℂ), ∞} = {((0 : ℂ) : OnePoint ℂ), ∞} ∧
    eulerChar ↥({((0 : ℂ) : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) =
      degree (spherePow two_ne_zero) *
        eulerChar ↥({((0 : ℂ) : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) := by
  have hpre : spherePow two_ne_zero ⁻¹' {((0 : ℂ) : OnePoint ℂ), ∞} =
      {((0 : ℂ) : OnePoint ℂ), ∞} := by
    ext x
    induction x using OnePoint.rec <;> simp
  have := (spherePow two_ne_zero).finiteCWType_compl_preimage
    (branchValues_spherePow_subset two_ne_zero)
  exact ⟨hpre, (Homeomorph.setCongr (congrArg compl hpre.symm)).eulerChar_eq.trans
    ((spherePow two_ne_zero).eulerChar_compl_preimage (branchValues_spherePow_subset two_ne_zero))⟩

-- Without the punctures, `χ = deg f · χ` fails for the squaring map: it would read `2 = 2 · 2`.
example : eulerChar (OnePoint ℂ) ≠ degree (spherePow two_ne_zero) * eulerChar (OnePoint ℂ) := by
  simp [eulerChar_onePoint, Complex.finrank_real_complex]

-- The branched-cover formula `2 = 2 · 2 - 2` for the squaring map of the triangulated sphere.
example : eulerChar (OnePoint ℂ) =
    degree (spherePow two_ne_zero) * eulerChar (OnePoint ℂ) -
      ramificationDegree (spherePow two_ne_zero) :=
  (spherePow two_ne_zero).eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_isTriangulable
    (isTriangulable_onePoint.{0, 0}) (isTriangulable_onePoint.{0, 0})

-- The sign error `χ(X) = deg f · χ(Y) + R(f)` fails for the squaring map: `2 ≠ 2 · 2 + 2`.
example : eulerChar (OnePoint ℂ) ≠
    degree (spherePow two_ne_zero) * eulerChar (OnePoint ℂ) +
      ramificationDegree (spherePow two_ne_zero) := by
  simp [eulerChar_onePoint, Complex.finrank_real_complex]
