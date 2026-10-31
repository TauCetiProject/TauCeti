/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.Ray

/-!
# Rays and translates of Weyl orbits of weights

Two facts about the Weyl orbit `W λ` of a weight `λ` of a root pairing over a linearly ordered
field. When the Weyl group is finite, no two distinct weights of `W λ` lie in the same ray, so a
vector in `W λ` is determined by its direction. Adding a weight `χ` fixed by the Weyl group maps
`W λ` into `W (λ + χ)`, since `w λ + χ = w (λ + χ)`.

These are the hypotheses under which a path with velocities in `W λ` has a unique distinguished
presentation, and its central shift by `χ` has velocities in `W (λ + χ)`; see
`TauCeti/RepresentationTheory/LSPath/Distinguished.lean`.

## Main results

* `RootPairing.pairwise_not_sameRay_orbit_weylGroup`: when the Weyl group is finite, no two
  distinct weights of a Weyl orbit lie in the same ray.
* `RootPairing.mapsTo_add_orbit_weylGroup`: adding a Weyl-invariant weight `χ` maps `W λ` into
  `W (λ + χ)`.
-/

public section

namespace RootPairing

variable {ι 𝕜 V N : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V] [AddCommGroup N] [Module 𝕜 N] (P : RootPairing ι 𝕜 V N)

/-- When the Weyl group is finite, no two distinct weights of a Weyl orbit lie in the same ray.
So a path with velocities in `W λ` has at most one distinguished presentation for `W λ`. -/
theorem pairwise_not_sameRay_orbit_weylGroup [Finite P.weylGroup] (lam : V) :
    (MulAction.orbit P.weylGroup lam).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v :=
  fun _ hu _ hv huv h ↦ huv (h.eq_of_mem_orbit hu hv (Set.finite_range _))

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Adding a weight `χ` fixed by the Weyl group maps the Weyl orbit `W λ` to `W (λ + χ)`, since
`w λ + χ = w (λ + χ)`. So the central shift by `χ` transports paths with velocities in `W λ` to
paths with velocities in `W (λ + χ)`. -/
theorem mapsTo_add_orbit_weylGroup {χ : V} (hχ : ∀ w : P.weylGroup, w • χ = χ) (lam : V) :
    Set.MapsTo (· + χ) (MulAction.orbit P.weylGroup lam)
      (MulAction.orbit P.weylGroup (lam + χ)) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨w, by simp only [smul_add, hχ]⟩

end RootPairing
