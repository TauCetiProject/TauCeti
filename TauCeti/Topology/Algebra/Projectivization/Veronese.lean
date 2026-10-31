/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Projectivization.Veronese
public import TauCeti.Topology.Algebra.Projectivization

/-!
# The Veronese map is a closed embedding

The Veronese map `Projectivization.veronese K d`, sending `[v]` to the point whose homogeneous
coordinates are the monomials of degree `d` in `v`, is continuous for the quotient topologies on
projective spaces over any topological field, since its homogeneous coordinates are polynomial.
Over `ℝ` or `ℂ` projective space is compact and Hausdorff, so the Veronese map of positive degree,
being injective, is a closed embedding: it identifies `ℙ 𝕜 (Fin N → 𝕜)` with its image, a closed
subset of the target projective space.

## Main results

* `TauCeti.continuous_veroneseMonomials`: the vector of monomials of degree `d` depends
  continuously on the vector.
* `Projectivization.continuous_veronese`: the Veronese map is continuous.
* `Projectivization.isClosedEmbedding_veronese`: over `ℝ` or `ℂ`, the Veronese map of positive
  degree is a closed embedding.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Graduate Texts in Mathematics 133, Springer,
  1992, Lecture 2, Example 2.4.
-/

public section

open scoped LinearAlgebra.Projectivization

variable {N : ℕ}

namespace TauCeti

/-- The vector of monomials of degree `d` of `v` depends continuously on `v`. -/
@[fun_prop]
theorem continuous_veroneseMonomials {K : Type*} [CommSemiring K] [TopologicalSpace K]
    [ContinuousMul K] (d : ℕ) : Continuous (veroneseMonomials (N := N) (K := K) d) :=
  continuous_pi fun k ↦ by
    simp only [veroneseMonomials_apply]
    exact continuous_finsetProd _ fun i _ ↦ (continuous_apply i).pow _

end TauCeti

namespace Projectivization

open TauCeti

/-- The Veronese map is continuous for the quotient topologies on projective spaces. -/
theorem continuous_veronese {K : Type*} [Field K] [TopologicalSpace K] [ContinuousMul K]
    (d : ℕ) : Continuous (veronese (N := N) K d) :=
  continuous_iff.2 <| (continuous_mk (K := K)
    (f := fun v : {v : Fin N → K // v ≠ 0} ↦ veroneseMonomials d v.1)
    ((continuous_veroneseMonomials d).comp continuous_subtype_val)
    fun v ↦ veroneseMonomials_ne_zero d v.2).congr fun v ↦ by simp [mk'_eq_mk]

/-- **The Veronese map is a closed embedding.** Over `ℝ` or `ℂ`, the Veronese map of positive
degree is a homeomorphism of projective space onto its image, which is closed. -/
theorem isClosedEmbedding_veronese {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} (hd : d ≠ 0) :
    Topology.IsClosedEmbedding (veronese (N := N) 𝕜 d) :=
  (continuous_veronese d).isClosedEmbedding (veronese_injective hd)

end Projectivization
