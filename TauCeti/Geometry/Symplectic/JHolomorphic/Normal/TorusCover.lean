/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.GenusOne
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Curves near a square-zero torus are unbranched torus covers

Let `C` be an embedded pseudoholomorphic torus in a symplectic four-manifold, with class `A`
satisfying `A · A = 0` and `κ · A = 0`, where `κ` is the canonical class. In Taubes's analysis of
Seiberg–Witten solutions concentrating along `C` with multiplicity, the rescaled limit is a
holomorphic cycle in the normal bundle of `C`, and its components that are not contained in a
single fibre project onto `C` with positive degree. Such a component is the image of a compact
connected Riemann surface `X`, its normalization, and its projection to `C` is a finite
holomorphic map `f : X → C` of some degree `d`. Its class is `d A`, so its square and its pairing
with `κ` vanish.

Two formulas then pin the component down. The adjunction formula for a simple curve with
normalization of genus `g` and singularity number `δ ≥ 0` gives
`2 g - 2 + 2 δ = (d A) · (d A) + κ · (d A) = 0`, so `g ≤ 1`. Since `C` has Euler characteristic
zero, the Riemann–Hurwitz formula gives `R(f) = 2 g - 2 ≥ 0`
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.eulerChar_eq_neg_ramificationDegree`), so
`g ≥ 1`. Hence `g = 1`, `δ = 0` and `R(f) = 0`: the component is an embedded torus and its
projection is an unbranched covering map of `C`
(`FiniteHolomorphicMap.isCoveringMap_and_genus_eq_one_and_singularity_eq_zero`). Only the
inequality `2 g - 2 + 2 δ ≤ 0` matters for this conclusion
(`FiniteHolomorphicMap.isCoveringMap_and_genus_eq_one_and_singularity_eq_zero_of_le_zero`).

The adjunction formula, the computation of the class and the Euler characteristics are inputs
here; the intersection form `B` and the canonical class `κ` are an arbitrary integral bilinear
form and linear functional on an abelian group `H`, as in
`TauCeti.Geometry.Symplectic.JHolomorphic.GoodCycle`.

## Main results

* `FiniteHolomorphicMap.isCoveringMap_and_genus_eq_one_and_singularity_eq_zero_of_le_zero`:
  if `2 genus X - 2 + 2 δ ≤ 0` over a target of Euler characteristic zero, then `f` is a
  covering map, `X` has genus one and `δ = 0`.
* `FiniteHolomorphicMap.isCoveringMap_and_genus_eq_one_and_singularity_eq_zero`:
  a component over a square-zero torus orthogonal to `κ` satisfying the adjunction formula is an
  embedded torus covering `C` without branching.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Section 2.6 (the adjunction formula).
-/

public section

open scoped Manifold

universe u

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]
  [FiniteCWType X] [FiniteCWType Y]
  (f : FiniteHolomorphicMap X Y)

/-- Let `f : X → Y` be a finite holomorphic map from a compact Riemann surface with
`χ(X) = 2 - 2 · genus X` to a surface `Y` with `χ(Y) = 0`. If `2 genus X - 2 + 2 δ ≤ 0`, then `f`
is a covering map, `X` has genus one and `δ = 0`. -/
theorem isCoveringMap_and_genus_eq_one_and_singularity_eq_zero_of_le_zero
    (hX : eulerChar X = 2 - 2 * genus X) (hY : eulerChar Y = 0) {δ : ℕ}
    (hadj : 2 * (genus X : ℤ) - 2 + 2 * δ ≤ 0) :
    IsCoveringMap f ∧ genus X = 1 ∧ δ = 0 := by
  have hR := f.eulerChar_eq_neg_ramificationDegree hY
  rw [f.isCoveringMap_iff_ramificationDegree_eq_zero]
  omega

/-- **Curves over a square-zero torus.** Let `f : X → Y` be a finite holomorphic map from a
compact Riemann surface with `χ(X) = 2 - 2 · genus X` to a surface `Y` with `χ(Y) = 0`, and let
`A` be a class with `B A A = 0` and `κ A = 0`. If `δ` satisfies the adjunction formula
`2 genus X - 2 + 2 δ = B c c + κ c` for a class `c = n • A`, such as `c = deg f • A`, then `f` is
a covering map, `X` has genus one and `δ = 0`. -/
theorem isCoveringMap_and_genus_eq_one_and_singularity_eq_zero {H : Type*} [AddCommGroup H]
    {B : LinearMap.BilinForm ℤ H} {κ : H →ₗ[ℤ] ℤ} {A : H} (hA : B A A = 0) (hκA : κ A = 0)
    (hX : eulerChar X = 2 - 2 * genus X) (hY : eulerChar Y = 0) {n δ : ℕ}
    (hadj : 2 * (genus X : ℤ) - 2 + 2 * δ = B (n • A) (n • A) + κ (n • A)) :
    IsCoveringMap f ∧ genus X = 1 ∧ δ = 0 := by
  simp only [map_nsmul, LinearMap.smul_apply, hA, hκA, smul_zero, add_zero] at hadj
  exact f.isCoveringMap_and_genus_eq_one_and_singularity_eq_zero_of_le_zero hX hY hadj.le

end TauCeti.RiemannSurface.FiniteHolomorphicMap

end
