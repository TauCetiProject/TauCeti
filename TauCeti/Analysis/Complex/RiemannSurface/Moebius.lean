/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Degree
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius

/-!
# Möbius transformations as finite holomorphic maps

A Möbius transformation `z ↦ g • z`, `g ∈ PSL(2, ℂ)`, is a holomorphic bijection of the Riemann
sphere `OnePoint ℂ`, so it is a finite holomorphic map of the sphere to itself, and as it is
injective it has degree one.

## Main declarations

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.ofPSL`: a Möbius transformation as a finite
  holomorphic map of the Riemann sphere.
* `TauCeti.RiemannSurface.degree_psl_smul`: a Möbius transformation has degree one.
-/

public section

open Filter OnePoint Set
open scoped ContDiff Manifold MatrixGroups

namespace TauCeti.RiemannSurface

namespace FiniteHolomorphicMap

/-- The Möbius transformation `z ↦ g • z` of `g ∈ PSL(2, ℂ)`, as a finite holomorphic map of the
Riemann sphere. -/
noncomputable def ofPSL (g : PSL(2, ℂ)) : FiniteHolomorphicMap (OnePoint ℂ) (OnePoint ℂ) :=
  ofMDifferentiable ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ω) g).mdifferentiable (by simp))
    ⟨(0 : ℂ), (∞ : OnePoint ℂ), (MulAction.injective g).ne (coe_ne_infty 0)⟩

@[simp]
theorem coe_ofPSL (g : PSL(2, ℂ)) : ⇑(ofPSL g) = (g • ·) :=
  coe_ofMDifferentiable _ _

end FiniteHolomorphicMap

/-- A Möbius transformation of the Riemann sphere has degree one. -/
@[simp]
theorem degree_psl_smul (g : PSL(2, ℂ)) :
    degree (g • · : OnePoint ℂ → OnePoint ℂ) = 1 := by
  have hinj := MulAction.injective (β := OnePoint ℂ) g
  have := degree_eq_one_of_injOn (FiniteHolomorphicMap.ofPSL g) (x := ∞) univ_mem
    (by simpa using hinj) fun _ h ↦ hinj (by simpa using h)
  simpa using this

end TauCeti.RiemannSurface
