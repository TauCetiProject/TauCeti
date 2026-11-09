/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Pullback
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sphere
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Basic

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
(`TauCeti.RiemannSurface.exists_isCanonicalDivisor_degree_eq`). Once all canonical divisors are
known to have the same degree `2g - 2`, this is the analytic Riemann–Hurwitz formula
`2g - 2 = -2 deg f + deg R_f`; that comparison is not made here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the canonical divisor and the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter IV §2 (the pullback of a canonical divisor) and
  Chapter V §1.
-/

public noncomputable section

open Filter Function OnePoint
open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]

namespace OneForm

/-- The pullback of a `1`-form meromorphic and of finite order at `f x` by a finite holomorphic
map has finite order at `x`. -/
theorem order_pullback_ne_top {ω : OneForm Y} (f : FiniteHolomorphicMap X Y) {x : X}
    (hω : ω.MeromorphicAt (f x)) (hω₀ : ω.order (f x) ≠ ⊤) : (ω.pullback f).order x ≠ ⊤ := by
  rw [order_pullback hω (Eventually.of_forall fun y ↦ f.holomorphic y) (f.not_eventuallyConst x)]
  lift ω.order (f x) to ℤ using hω₀ with k
  exact WithTop.add_ne_top.2 ⟨WithTop.mul_ne_top (WithTop.coe_ne_top) (WithTop.natCast_ne_top _),
    WithTop.coe_ne_top⟩

variable [CompactSpace X] [CompactSpace Y]

/-- **Degree of the divisor of a pulled-back differential.** For a finite holomorphic map `f`
of compact Riemann surfaces and a `1`-form `ω` meromorphic and of finite order everywhere,
`deg div(f*ω) = deg f · deg div ω + deg R_f`. -/
theorem degree_divisor_pullback [T2Space X] [T2Space Y] [PreconnectedSpace Y] (ω : OneForm Y)
    (f : FiniteHolomorphicMap X Y) (hω : ∀ y, ω.MeromorphicAt y) (hω₀ : ∀ y, ω.order y ≠ ⊤) :
    WeilDivisor.degree (ω.pullback f).divisor =
      (degree f : ℤ) * WeilDivisor.degree ω.divisor + ramificationDegree f := by
  rw [divisor_pullback ω f hω hω₀, map_add, degree_divisorPullback, degree_ramificationDivisor]

omit [CompactSpace Y] in
/-- The divisor of the pullback of a `1`-form meromorphic and of finite order everywhere by a
finite holomorphic map is canonical. -/
theorem isCanonicalDivisor_divisor_pullback (ω : OneForm Y) (f : FiniteHolomorphicMap X Y)
    (hω : ∀ y, ω.MeromorphicAt y) (hω₀ : ∀ y, ω.order y ≠ ⊤) :
    IsCanonicalDivisor (ω.pullback f).divisor :=
  isCanonicalDivisor_divisor
    (fun x ↦ (hω (f x)).pullback (Eventually.of_forall fun y ↦ f.holomorphic y))
    fun x ↦ order_pullback_ne_top f (hω (f x)) (hω₀ (f x))

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
  exact OneForm.isCanonicalDivisor_divisor_pullback ω f hω hω₀

variable [T2Space X]

/-- **Riemann–Hurwitz for a canonical divisor.** A finite holomorphic map `f` from a compact
Riemann surface to the Riemann sphere gives the canonical divisor `f*(-2[∞]) + R_f` of degree
`-2 deg f + deg R_f`. -/
theorem exists_isCanonicalDivisor_degree_eq (f : FiniteHolomorphicMap X (OnePoint ℂ)) :
    ∃ K : WeilDivisor X, IsCanonicalDivisor K ∧
      WeilDivisor.degree K = -2 * (degree f : ℤ) + ramificationDegree f := by
  refine ⟨_, isCanonicalDivisor_neg_two_infty.divisorPullback_add_ramificationDivisor f, ?_⟩
  rw [map_add, degree_divisorPullback, degree_ramificationDivisor, map_zsmul,
    WeilDivisor.degree_ofPoint]
  ring

end TauCeti.RiemannSurface
