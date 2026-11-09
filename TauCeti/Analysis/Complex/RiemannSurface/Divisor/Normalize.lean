/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sheaf
public import TauCeti.Analysis.Complex.RiemannSurface.SphereMap

/-!
# Normalized representatives of divisor sections

A section of the divisor sheaf `𝒪_E` is represented by a function whose values are pinned at every
point (`TauCeti.RiemannSurface.IsDivisorSectionAt`): it is holomorphic where `E x ≤ 0` and `0`
where `E x > 0`. A meromorphic function `g` has no value at its poles, and its values at removable
singularities are arbitrary. `TauCeti.RiemannSurface.toDivisorSection E g` fills the removable
singularities of `g` and sets its values at the poles allowed by `E` to `0`.

Off a closed discrete set it agrees with `g`
(`TauCeti.RiemannSurface.toDivisorSection_eventuallyEq`), and if `g` is meromorphic at `x` with
order at least `-E x`, it is a local section of `𝒪_E` at `x`
(`TauCeti.RiemannSurface.isDivisorSectionAt_toDivisorSection`). This normalizes products by
meromorphic functions in the local trivializations of divisor sheaves, and quotients of
meromorphic `1`-forms in the identification of differential sheaves with divisor sheaves.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §16 (the sheaves `𝒪_D`).
-/

public noncomputable section

open Filter OnePoint Set Topology
open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {E : WeilDivisor X} {g : X → ℂ} {x : X}

/-- The function `g` normalized as a section of `𝒪_E`: removable singularities are filled, and
the values at the poles allowed by `E` are `0`. -/
def toDivisorSection (E : WeilDivisor X) (g : X → ℂ) : X → ℂ :=
  {y | E y ≤ 0}.indicator fun y ↦ affineChart (sphereMap g y)

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] in
/-- The value of `toDivisorSection E g` at `y` is the filled value of `g` if `E y ≤ 0`, and `0`
otherwise. -/
theorem toDivisorSection_apply (E : WeilDivisor X) (g : X → ℂ) (y : X) :
    toDivisorSection E g y = if E y ≤ 0 then affineChart (sphereMap g y) else 0 := by
  simp [toDivisorSection, Set.indicator]

/-- Normalizing a function meromorphic at `x` does not change it on a punctured neighbourhood
of `x`. -/
theorem toDivisorSection_eventuallyEq (E : WeilDivisor X) (hg : MeromorphicAt g x) :
    toDivisorSection E g =ᶠ[𝓝[≠] x] g := by
  have := ChartedSpace.t1Space ℂ X
  filter_upwards [E.eventually_eq_zero_nhdsNE x, affineChart_sphereMap_eventuallyEq hg]
    with y hy heq
  simp [toDivisorSection, hy, heq]

/-- A function meromorphic at `x` with order at least `-E x` becomes a local section of `𝒪_E` at
`x` once normalized. -/
theorem isDivisorSectionAt_toDivisorSection (hg : MeromorphicAt g x)
    (ho : ((-E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g x) :
    IsDivisorSectionAt E (toDivisorSection E g) x := by
  have heq := toDivisorSection_eventuallyEq E hg
  refine ⟨hg.congr heq.symm, by rwa [meromorphicOrderAt_congr heq], fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have := ChartedSpace.t1Space ℂ X
    have h0 : (0 : WithTop ℤ) ≤ ((-E x : ℤ) : WithTop ℤ) := by exact_mod_cast neg_nonneg.2 hx
    apply (contMDiffAt_affineChart_sphereMap hg (h0.trans ho)).congr_of_eventuallyEq
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · filter_upwards [E.eventually_eq_zero_nhdsNE x] with y hy
      simp [toDivisorSection, hy]
    · simp [toDivisorSection, hx]
  · simp [toDivisorSection, not_le.2 hx]

end TauCeti.RiemannSurface
