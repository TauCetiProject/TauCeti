/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.Matrix.Frobenius
public import TauCeti.Geometry.Lie.Subgroup.Unitary.TangentSpace
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Calculus.TangentCone.InnerProductSpace

/-!
# Nearest points and retractions onto a closed subgroup of the unitary group

Let `G` be a closed subgroup of `U(n) = Matrix.unitaryGroup n 𝕜`, a compact submanifold of the
real inner product space of `n × n` matrices over `𝕜` (`ℝ` or `ℂ`) with the Frobenius inner
product `⟪A, B⟫ = Re tr (Aᴴ B)`, with tangent space `g 𝔤` at `g ∈ G`
(`ClosedSubgroup.tangentConeAt_eq_matrixTangentSpace`). This file specialises the first-order
facts about nearest points of a set and retractions onto it, from
`TauCeti.Analysis.Calculus.TangentCone.InnerProductSpace`, to `G`. They identify the derivative of
the nearest-point retraction `π_G` at points of `G`:

* if `g ∈ G` is, locally, a nearest point of `G` to a matrix `M`, the residual `M - g` is
  orthogonal to `g 𝔤` (`ClosedSubgroup.inner_sub_eq_zero_of_isLocalMinOn`);
* a map `r` from matrices to matrices that is the identity on `G` has derivative the identity on
  `g 𝔤` (`ClosedSubgroup.fderiv_apply_eq_self_of_mem_matrixTangentSpace`);
* if moreover `r (g + t v) = g` for every normal vector `v` and small `t`, as for the nearest-point
  retraction along short normal segments, its derivative at `g` is the orthogonal projection onto
  `g 𝔤` (`ClosedSubgroup.fderiv_eq_starProjection_matrixTangentSpace`).

These statements are about maps of matrices and the subset `G`, so they apply to any differentiable
retraction onto `G`, in particular to the smooth nearest-point retraction that the tubular
neighbourhood theorem provides on a neighbourhood of `G`.

The Frobenius inner product is a scoped instance; this file opens `Matrix.Norms.Frobenius`.

## References

* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Section 3 (the derivative
  of the nearest-point projection onto `G`).
-/

public section

noncomputable section

open Set
open scoped Matrix Topology InnerProductSpace

namespace ClosedSubgroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
  {G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)}

open scoped Matrix.Norms.Frobenius

/-- **First variation of the distance to `G`.** If `g ∈ G` is, locally in `G`, a nearest point of
`G` to `M`, the residual `M - g` is orthogonal (for the Frobenius inner product) to the tangent
space `g 𝔤` of `G` at `g`. -/
theorem inner_sub_eq_zero_of_isLocalMinOn {M : Matrix n n 𝕜} {g : G}
    (hmin : IsLocalMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
      (g : Matrix n n 𝕜))
    {V : Matrix n n 𝕜} (hV : V ∈ G.matrixTangentSpace g) :
    ⟪M - g, V⟫_ℝ = 0 :=
  TauCeti.real_inner_sub_eq_zero_of_isLocalMinOn_dist hmin
    (mem_posTangentConeAt_of_mem_matrixTangentSpace hV)
    (mem_posTangentConeAt_of_mem_matrixTangentSpace (neg_mem hV))

/-- **A retraction onto `G` is the identity on tangent vectors.** If `r` is differentiable at
`g ∈ G` and fixes every point of `G`, its derivative at `g` is the identity on `g 𝔤`. -/
theorem fderiv_apply_eq_self_of_mem_matrixTangentSpace {r : Matrix n n 𝕜 → Matrix n n 𝕜} {g : G}
    (hr : DifferentiableAt ℝ r g) (hrG : ∀ h ∈ G, r h = h) {V : Matrix n n 𝕜}
    (hV : V ∈ G.matrixTangentSpace g) :
    fderiv ℝ r g V = V :=
  TauCeti.fderiv_apply_eq_self_of_mem_tangentConeAt
    (s := ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) hr
    (fun _ ⟨h, hh, hA⟩ ↦ hA ▸ hrG h hh) ⟨g, g.property, rfl⟩
    ((tangentConeAt_eq_matrixTangentSpace g).ge hV)

/-- **The derivative of a retraction onto `G` that is constant along normal segments.** If `r` is
differentiable at `g ∈ G`, fixes every point of `G`, and satisfies `r (g + t v) = g` for every
vector `v` orthogonal to `g 𝔤` and every small `t`, then its derivative at `g` is the orthogonal
projection onto `g 𝔤`. The nearest-point retraction onto `G` has these properties. -/
theorem fderiv_eq_starProjection_matrixTangentSpace {r : Matrix n n 𝕜 → Matrix n n 𝕜} {g : G}
    (hr : DifferentiableAt ℝ r g) (hrG : ∀ h ∈ G, r h = h)
    (hnormal : ∀ v ∈ (G.matrixTangentSpace g)ᗮ,
      ∀ᶠ t in 𝓝 (0 : ℝ), r ((g : Matrix n n 𝕜) + t • v) = g) :
    fderiv ℝ r g = (G.matrixTangentSpace g).starProjection :=
  TauCeti.fderiv_eq_starProjection_of_eventually_add_smul _
    (tangentConeAt_eq_matrixTangentSpace g).ge hr (fun _ ⟨h, hh, hA⟩ ↦ hA ▸ hrG h hh)
    ⟨g, g.property, rfl⟩ hnormal

end ClosedSubgroup
