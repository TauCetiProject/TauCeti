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

The Veronese map `Projectivization.veronese K d`, sending `[v]` to the point whose homogeneous
coordinates are the monomials of degree `d` in `v`, is continuous for the quotient topologies on
projective spaces over any topological field, since its homogeneous coordinates are polynomial.
Over `ℝ` or `ℂ` projective space is compact and Hausdorff, so the Veronese map of positive degree,
being injective, is a closed embedding: it identifies `ℙ 𝕜 (Fin N → 𝕜)` with its image, a closed
subset of the target projective space.

Over `ℂ` its image is the common zero locus of the quadratic binomials `y_α y_β - y_γ y_δ` with
`α + β = γ + δ` (`Projectivization.range_veronese`). The Veronese map is therefore a homeomorphism
`Projectivization.veroneseHomeomorph` from `ℙ ℂ (Fin N → ℂ)` onto this zero locus with its
subspace topology. Through it, statements about the linear sections of the zero locus transport
to statements about the degree-`d` hypersurfaces of `ℙ ℂ (Fin N → ℂ)`
(`Projectivization.preimage_veronese_complexProjectiveZeroLocus_veroneseLinearForm`).

## Main results

* `TauCeti.continuous_veroneseMonomials`: the vector of monomials of degree `d` depends
  continuously on the vector.
* `Projectivization.continuous_veronese`: the Veronese map is continuous.
* `Projectivization.isClosedEmbedding_veronese`: over `ℝ` or `ℂ`, the Veronese map of positive
  degree is a closed embedding.
* `Projectivization.isClosedEmbedding_map_comp_veronese`: the same holds for the Veronese map read
  through an injective linear map into another space of homogeneous coordinates.
* `Projectivization.veroneseHomeomorph`: over `ℂ`, the Veronese map of positive degree as a
  homeomorphism onto the common zero locus of the quadratic binomials.

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

/-- For positive degree, the Veronese map read through an injective linear map is a closed
embedding: projective space is compact and the map is continuous and injective. -/
theorem isClosedEmbedding_map_comp_veronese {𝕜 : Type*} [RCLike 𝕜] {M d : ℕ} (hd : d ≠ 0)
    (f : (Fin (veroneseDim N d) → 𝕜) →ₗ[𝕜] Fin M → 𝕜) (hf : Function.Injective f) :
    Topology.IsClosedEmbedding (map f hf ∘ veronese 𝕜 d) :=
  ((continuous_map hf (LinearMap.continuous_on_pi f)).comp
    (continuous_veronese d)).isClosedEmbedding ((map_injective f hf).comp (veronese_injective hd))

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

/-- The Veronese map undoes the inverse of `veroneseHomeomorph`. -/
@[simp]
theorem veronese_veroneseHomeomorph_symm_apply {d : ℕ} (hd : d ≠ 0)
    (y : complexProjectiveZeroLocus (veroneseRelation ℂ N d)) :
    veronese ℂ d ((veroneseHomeomorph hd).symm y) = y := by
  rw [← coe_veroneseHomeomorph_apply hd, Homeomorph.apply_symm_apply]

/-- The inverse of `veroneseHomeomorph` recovers a point from its image under the Veronese map. -/
@[simp]
theorem veroneseHomeomorph_symm_apply_veronese {d : ℕ} (hd : d ≠ 0) (x : ℙ ℂ (Fin N → ℂ))
    (hx : veronese ℂ d x ∈ complexProjectiveZeroLocus (veroneseRelation ℂ N d)) :
    (veroneseHomeomorph hd).symm ⟨veronese ℂ d x, hx⟩ = x :=
  (veroneseHomeomorph hd).symm_apply_eq.2 rfl

end Projectivization
