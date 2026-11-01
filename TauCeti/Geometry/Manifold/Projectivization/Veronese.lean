/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.Atlas
public import TauCeti.Topology.Algebra.Projectivization.Veronese

/-!
# The Veronese map is analytic

The degree-`d` Veronese map `Projectivization.veronese 𝕜 d` sends the point `[v]` of
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` to the point of `ℙ 𝕜 (Fin (veroneseDim (n + 1) d) → 𝕜)` whose homogeneous
coordinates are the degree-`d` monomials of `v`. These monomials are polynomial functions of `v`
that vanish simultaneously only at `v = 0`, so the Veronese map is `C^r` for every `r`, including
the analytic order `ω`; over `ℂ` it is holomorphic.

The source carries the standard atlas `Projectivization.instChartedSpace`. The number of monomials
`veroneseDim (n + 1) d` is positive but not syntactically a successor, so the target carries the
atlas `Projectivization.finChartedSpace`, the standard atlas pulled back along the canonical
reindexing of the homogeneous coordinates by `Fin (veroneseDim (n + 1) d - 1 + 1)`.

Together with `Projectivization.isClosedEmbedding_veronese`, this shows that over `ℂ` the Veronese
map of positive degree is a holomorphic map which is a closed topological embedding.

## Main declarations

* `Projectivization.contDiff_veroneseMonomials`: the vector of monomials is `C^r`.
* `Projectivization.contMDiff_veronese`: the Veronese map is `C^r` for every `r`.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Graduate Texts in Mathematics 133, Springer,
  1992, Lecture 2, Example 2.4.
-/

public section

open TauCeti
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The vector of degree-`d` monomials is a `C^r` function of the vector, for every `r`. -/
theorem contDiff_veroneseMonomials {N : ℕ} (d : ℕ) (r : ℕ∞ω) :
    ContDiff 𝕜 r (veroneseMonomials (N := N) (K := 𝕜) d) :=
  contDiff_pi.2 fun k ↦ by simp_rw [veroneseMonomials_apply]; fun_prop

/-- The Veronese map of degree `d` is `C^r` for every `r`, from `ℙ 𝕜 (Fin (n + 1) → 𝕜)` with its
standard atlas to `ℙ 𝕜 (Fin (veroneseDim (n + 1) d) → 𝕜)` with the atlas `finChartedSpace`. For
`r = ω` it is analytic; over `ℂ` it is holomorphic. -/
theorem contMDiff_veronese {n : ℕ} (d : ℕ) (r : ℕ∞ω) :
    letI := finChartedSpace 𝕜 (veroneseDim (n + 1) d)
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin (veroneseDim (n + 1) d - 1) → 𝕜) r
      (veronese (N := n + 1) 𝕜 d) := by
  let := finChartedSpace 𝕜 (veroneseDim (n + 1) d)
  set e := finSubOneAddOneLinearEquiv 𝕜 (veroneseDim (n + 1) d)
  -- After reindexing, the homogeneous coordinates of the Veronese map are `e` of the monomials.
  refine contMDiff_finChartedSpace_iff.2 ⟨continuous_veronese d,
    contMDiff_of_contDiffOn (F := fun v ↦ e (veroneseMonomials d v)) ?_
      (fun v hv ↦ (LinearEquiv.map_ne_zero_iff _).2 (veroneseMonomials_ne_zero d hv))
      fun v hv ↦ by simp [e]⟩
  exact (⟨e.toLinearMap, LinearMap.continuous_on_pi _⟩ :
    (Fin (veroneseDim (n + 1) d) → 𝕜) →L[𝕜] _).contDiff.comp (contDiff_veroneseMonomials d r)
    |>.contDiffOn

end Projectivization
