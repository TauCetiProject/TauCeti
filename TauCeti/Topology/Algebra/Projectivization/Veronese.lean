/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Projectivization.Veronese
public import TauCeti.Topology.Algebra.Projectivization

/-!
# The Veronese map is a closed embedding

The degree-`d` Veronese map `Projectivization.veronese K d`, sending `[v]` to the point whose
homogeneous coordinates are the degree-`d` monomials of `v`, is continuous over any topological
field, since the monomials are. Over `ℝ` or `ℂ`, projective space is compact and Hausdorff, so for
`d ≠ 0`, when the Veronese map is injective, it is a closed embedding, hence proper
(`Topology.IsClosedEmbedding.isProperMap`).

Over `ℂ` its image is the common zero locus of the quadratic binomials `y_α y_β - y_γ y_δ` with
`α + β = γ + δ` (`Projectivization.range_veronese`). The Veronese map is therefore a homeomorphism
`Projectivization.veroneseHomeomorph` from `ℙ ℂ (Fin N → ℂ)` onto this zero locus with its
subspace topology. Through it, statements about the linear sections of the zero locus transport
to statements about the degree-`d` hypersurfaces of `ℙ ℂ (Fin N → ℂ)`
(`Projectivization.preimage_veronese_complexProjectiveZeroLocus_veroneseLinearForm`).

## Main declarations

* `Projectivization.continuous_veroneseMonomials`, `Projectivization.continuous_veronese`: the
  vector of monomials and the Veronese map are continuous.
* `Projectivization.isClosedEmbedding_veronese`: over `ℝ` or `ℂ`, the Veronese map of positive
  degree is a closed embedding.
* `Projectivization.veroneseHomeomorph`: over `ℂ`, the Veronese map of positive degree as a
  homeomorphism onto the common zero locus of the quadratic binomials.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Graduate Texts in Mathematics 133, Springer,
  1992, Lecture 2, Example 2.4.
-/

public section

open TauCeti Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {N : ℕ}

/-- The vector of degree-`d` monomials depends continuously on the vector. -/
theorem continuous_veroneseMonomials {K : Type*} [CommSemiring K] [TopologicalSpace K]
    [ContinuousMul K] (d : ℕ) : Continuous (veroneseMonomials (N := N) (K := K) d) :=
  continuous_pi fun k ↦ by simp_rw [veroneseMonomials_apply]; fun_prop

/-- The Veronese map is continuous: its homogeneous coordinates are monomials. -/
theorem continuous_veronese {K : Type*} [Field K] [TopologicalSpace K] [ContinuousMul K]
    (d : ℕ) : Continuous (veronese (N := N) K d) :=
  continuous_of_continuousOn (continuous_veroneseMonomials d).continuousOn
    (fun _ ↦ veroneseMonomials_ne_zero d) (veronese_mk K d)

/-- Over `ℝ` or `ℂ`, the Veronese map of positive degree is a closed embedding: it is a continuous
injection from a compact space to a Hausdorff space. -/
theorem isClosedEmbedding_veronese {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} (hd : d ≠ 0) :
    IsClosedEmbedding (veronese (N := N) 𝕜 d) :=
  (continuous_veronese d).isClosedEmbedding (veronese_injective hd)

/-- Over `ℂ`, the Veronese map of positive degree is a homeomorphism from `ℙ ℂ (Fin N → ℂ)` onto
the common zero locus of the quadratic binomials `y_α y_β - y_γ y_δ` with `α + β = γ + δ`. -/
noncomputable def veroneseHomeomorph {d : ℕ} (hd : d ≠ 0) :
    ℙ ℂ (Fin N → ℂ) ≃ₜ complexProjectiveZeroLocus (veroneseRelation ℂ N d) :=
  (isClosedEmbedding_veronese hd).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_veronese hd))

@[simp]
theorem coe_veroneseHomeomorph_apply {d : ℕ} (hd : d ≠ 0) (x : ℙ ℂ (Fin N → ℂ)) :
    (veroneseHomeomorph hd x : ℙ ℂ (Fin (veroneseDim N d) → ℂ)) = veronese ℂ d x :=
  (rfl)

end Projectivization
