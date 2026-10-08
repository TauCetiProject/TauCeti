/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.LocalDegree

/-!
# The open mapping theorem for Riemann surfaces

A holomorphic map `f : X → Y` between Riemann surfaces which is constant near no point of `X` is
an open map: this is the open mapping theorem for Riemann surfaces. It follows from the local
fibre count `TauCeti.RiemannSurface.exists_nhds_localMultiplicity_fiber_sum`, which produces, for
every neighbourhood `U` of a point `x`, a neighbourhood `V` of `f x` all of whose points have a
preimage in `U`. As a consequence, if `f` is holomorphic and nonconstant near `x` and `g` is
nonconstant near `f x`, then `g ∘ f` is nonconstant near `x`, which is how nonconstancy of a
composite of holomorphic maps is established.

Nonconstancy is spelled pointwise, as `¬ EventuallyConst f (𝓝 x)`, exactly as in the local fibre
count; on a connected `X` this is equivalent to `f` being nonconstant by the identity theorem,
which is not part of this file.

## Main declarations

* `TauCeti.RiemannSurface.nhds_le_map_nhds_of_not_eventuallyConst`: the open mapping theorem at
  a point.
* `TauCeti.RiemannSurface.isOpenMap_of_forall_not_eventuallyConst`: the open mapping theorem.
* `TauCeti.RiemannSurface.not_eventuallyConst_comp`: a composite of maps nonconstant near a point
  is nonconstant near it.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §2, Theorem 2.7.
-/

public section

open Filter Function Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] {f : X → Y} {g : Y → Z}

/-- **The open mapping theorem, at a point.** A map holomorphic and nonconstant near `x` sends
every neighbourhood of `x` onto a neighbourhood of `f x`. -/
theorem nhds_le_map_nhds_of_not_eventuallyConst {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (hne : ¬ EventuallyConst f (𝓝 x)) :
    𝓝 (f x) ≤ map f (𝓝 x) := by
  intro s hs
  obtain ⟨U, -, hUs, V, hV, -, hfib⟩ :=
    exists_nhds_localMultiplicity_fiber_sum hf hne (mem_map.1 hs)
  refine mem_of_superset hV fun y' hy' ↦ ?_
  obtain ⟨x', hx'⟩ := nonempty_iff_ne_empty.2 (hfib y' hy').1
  have hfx' : f x' = y' := hx'.1
  exact hfx' ▸ hUs hx'.2

/-- **The open mapping theorem.** A holomorphic map between Riemann surfaces which is constant
near no point is an open map. -/
theorem isOpenMap_of_forall_not_eventuallyConst (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x ↦
    nhds_le_map_nhds_of_not_eventuallyConst (.of_forall fun y ↦ hf y) (hne x)

/-- If `f` is holomorphic and nonconstant near `x` and `g` is not constant near `f x`, then
`g ∘ f` is not constant near `x`: by the open mapping theorem, constancy of `g ∘ f` near `x`
would force constancy of `g` on the neighbourhood `f '' U` of `f x`. -/
theorem not_eventuallyConst_comp {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (hne : ¬ EventuallyConst f (𝓝 x))
    (hg : ¬ EventuallyConst g (𝓝 (f x))) : ¬ EventuallyConst (g ∘ f) (𝓝 x) := fun h ↦ by
  have : Nonempty Z := ⟨g (f x)⟩
  obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 h
  refine hg (eventuallyConst_iff_exists_eventuallyEq.2 ⟨c, ?_⟩)
  exact Eventually.filter_mono (nhds_le_map_nhds_of_not_eventuallyConst hf hne)
    (eventually_map.2 hc)

end TauCeti.RiemannSurface

end
