/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Geometry.Manifold.Complex.EulerClass
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass

/-!
# The Chern number of the tangent bundle of the Riemann sphere

The holomorphic tangent bundle of the Riemann sphere `OnePoint ℂ` has first Chern number
`c₁(TS²)[S²] = 2` (`TauCeti.evalFundamentalClass_lineFirstChernClass_tangentSpace_onePoint`). The
first Chern class of a complex line bundle is the Euler class of its underlying real plane bundle
(`TauCeti.lineFirstChernClass_def`), on a compact Riemann surface its value on the fundamental
class of the complex orientation is the Euler characteristic
(`TauCeti.evalFundamentalClass_complexEulerClass_tangentSpace_eq_eulerChar`), and the Riemann
sphere has Euler characteristic `1 + (-1) ^ 2 = 2` (`TauCeti.eulerChar_onePoint`).

The same number, as a clutching number of the tangent bundle on the standard sphere, is
`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_apply_mk_riemannSphereSquare`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (the Riemann–Roch formula, which gives the index `2 + 2 · 2 = 6` of the
  Cauchy–Riemann operator on `TS²`).
-/

public section

open scoped Manifold

namespace TauCeti

/-- **The first Chern number of the tangent bundle of the Riemann sphere is `2`.** The first Chern
class of the holomorphic tangent bundle of `OnePoint ℂ`, evaluated on the fundamental class of the
complex orientation, is `c₁(TS²)[S²] = χ(S²) = 2`. -/
theorem evalFundamentalClass_lineFirstChernClass_tangentSpace_onePoint :
    ((complexHomologicalOrientation (OnePoint ℂ)).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id (OnePoint ℂ))
        (lineFirstChernClass ℂ (TangentSpace 𝓘(ℂ, ℂ) : OnePoint ℂ → Type)
          (Module.finrank_self ℂ))).down = 2 := by
  rw [lineFirstChernClass_def, evalFundamentalClass_complexEulerClass_tangentSpace_eq_eulerChar,
    eulerChar_onePoint, Complex.finrank_real_complex]
  norm_num

end TauCeti
