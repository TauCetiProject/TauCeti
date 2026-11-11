/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Pullback
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sphere

/-!
# The canonical-divisor form of Riemann–Hurwitz

Let `f : X → Y` be a finite holomorphic map of compact Riemann surfaces and `ω` a `1`-form on
`Y` which is meromorphic and of finite order everywhere. Its pullback `f*ω` is again meromorphic
and of finite order everywhere, and `div(f*ω) = f*(div ω) + R_f`
(`TauCeti.RiemannSurface.OneForm.divisor_pullback`). Taking degrees,

`deg div(f*ω) = deg f · deg div ω + deg R_f`

(`TauCeti.RiemannSurface.OneForm.degree_divisor_pullback`). Hence `f*K + R_f` is a canonical
divisor of `X` for every canonical divisor `K` of `Y`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.divisorPullback_add_ramificationDivisor`).

For a map to the Riemann sphere, pulling back the canonical divisor `-2[∞]` of `dz` gives a
canonical divisor of `X` of degree `-2 deg f + deg R_f`
(`exists_isCanonicalDivisor_degree_eq_neg_two_mul_degree_add_ramificationDegree` in the namespace
`TauCeti.RiemannSurface.FiniteHolomorphicMap`). Once all canonical divisors are known to have the
same degree `2g - 2`, this is the analytic Riemann–Hurwitz formula `2g - 2 = -2 deg f + deg R_f`;
that comparison is not made here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the canonical divisor and the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter IV §2 (the pullback of a canonical divisor) and
  Chapter V §1.
-/

public noncomputable section

open Filter Function OnePoint
open scoped Manifold Topology

namespace TauCeti.RiemannSurface

open AlgebraicGeometry

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]

namespace OneForm

variable [CompactSpace X]

/-- The divisor of the pullback of a `1`-form meromorphic and of finite order everywhere by a
holomorphic map which is nowhere locally constant is canonical. -/
theorem isCanonicalDivisor_divisor_pullback (ω : OneForm Y) {f : X → Y}
    (hω : ∀ y, ω.MeromorphicAt y) (hω₀ : ∀ y, ω.order y ≠ ⊤)
    (hf : ∀ x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x) (hnc : ∀ x, ¬ EventuallyConst f (𝓝 x)) :
    IsCanonicalDivisor (ω.pullback f).divisor :=
  isCanonicalDivisor_divisor (fun x ↦ (hω (f x)).pullback (Eventually.of_forall hf))
    fun x ↦ order_pullback_ne_top (hω (f x)) (hω₀ (f x)) (Eventually.of_forall hf) (hnc x)

end OneForm

variable [CompactSpace X] [CompactSpace Y]

/-- **Pullback of a canonical divisor.** If `K` is a canonical divisor of `Y` and `f : X → Y`
is a finite holomorphic map of compact Riemann surfaces, then `f*K + R_f` is a canonical divisor
of `X`, where `R_f` is the ramification divisor. -/
theorem IsCanonicalDivisor.divisorPullback_add_ramificationDivisor {K : WeilDivisor Y}
    (hK : IsCanonicalDivisor K) (f : FiniteHolomorphicMap X Y) :
    IsCanonicalDivisor (divisorPullback f K + ramificationDivisor f) := by
  obtain ⟨ω, hω, hω₀, rfl⟩ := hK.exists_divisor_eq
  rw [← OneForm.divisor_pullback ω f hω hω₀]
  exact OneForm.isCanonicalDivisor_divisor_pullback ω hω hω₀ f.holomorphic f.not_eventuallyConst

variable [T2Space X]

namespace FiniteHolomorphicMap

/-- **Riemann–Hurwitz for a canonical divisor.** A finite holomorphic map `f` from a compact
Riemann surface to the Riemann sphere gives the canonical divisor `f*(-2[∞]) + R_f` of degree
`-2 deg f + deg R_f`. -/
theorem exists_isCanonicalDivisor_degree_eq_neg_two_mul_degree_add_ramificationDegree
    (f : FiniteHolomorphicMap X (OnePoint ℂ)) :
    ∃ K : WeilDivisor X, IsCanonicalDivisor K ∧
      WeilDivisor.degree K = -2 * (degree f : ℤ) + ramificationDegree f := by
  refine ⟨_, isCanonicalDivisor_neg_two_infty.divisorPullback_add_ramificationDivisor f, ?_⟩
  rw [map_add, degree_divisorPullback, degree_ramificationDivisor, map_zsmul,
    WeilDivisor.degree_ofPoint]
  ring

end FiniteHolomorphicMap

end TauCeti.RiemannSurface
