/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Projectivization.Atlas
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Topology.Algebra.Projectivization.Veronese

/-!
# The Veronese map is a closed analytic embedding

The Veronese map `Projectivization.veronese 𝕜 d` sends `[v]` to the point of
`ℙ 𝕜 (Fin (veroneseDim (m + 1) d) → 𝕜)` whose homogeneous coordinates are the monomials of degree
`d` in `v`. The manifold structure of projective space is defined on `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, so
the Veronese map is read through an injective linear map `f` from its space of homogeneous
coordinates to `Fin (n + 1) → 𝕜`, such as a reindexing of the monomials by a linear equivalence
when `veroneseDim (m + 1) d = n + 1`, or its composite with a linear inclusion into a larger
projective space. The resulting map `Projectivization.map f hf ∘ Projectivization.veronese 𝕜 d`
is given in homogeneous coordinates by the polynomial map `f ∘ veroneseMonomials d`, so it is
analytic (`Projectivization.contMDiff_map_comp_veronese`); over `ℂ` it is holomorphic.

The target `ℙ 𝕜 (Fin (veroneseDim (m + 1) d) → 𝕜)` can also carry its own atlas
`Projectivization.finChartedSpace`, the standard atlas pulled back along the canonical reindexing
of the homogeneous coordinates by `Fin (veroneseDim (m + 1) d - 1 + 1)`. For it, the Veronese map
itself is analytic (`Projectivization.contMDiff_veronese`).

For positive degree `e + 1` it is moreover an immersion. On the affine open where the `i`-th
homogeneous coordinate is nonzero, the coordinates `y_(e e_i + e_j)` of the image of `[v]` are the
coordinates of `v i ^ e • v` (`TauCeti.veroneseLocalInverse_veroneseMonomials`). Composed with a
linear left inverse `g` of `f`, they induce the map
`Projectivization.linearProjection (veroneseLocalInverse 𝕜 e i ∘ₗ g)`, analytic on an open
neighbourhood of the image (`Projectivization.contMDiffOn_linearProjection`), which is a left
inverse of the Veronese map near `[v]`
(`Projectivization.leftInvOn_linearProjection_veroneseLocalInverse`), so its differential is
injective (`Projectivization.isImmersion_map_comp_veronese`). Since projective space is compact
and the Veronese map of positive degree is injective, it is a closed embedding
(`Projectivization.isClosedEmbedding_map_comp_veronese`), and hence a closed analytic embedding
(`Projectivization.isSmoothEmbedding_map_comp_veronese`).

## Main results

* `TauCeti.contDiff_veroneseMonomials`: the vector of monomials of degree `d` is a `C^r` function
  of the vector, for every `r`.
* `Projectivization.contMDiff_map_comp_veronese`: the Veronese map, read through an injective
  linear map, is `C^r` for every `r`, including the analytic order `ω`.
* `Projectivization.contMDiff_veronese`: the Veronese map is `C^r` for every `r`, for the atlas
  `Projectivization.finChartedSpace` on its target.
* `Projectivization.isImmersion_map_comp_veronese`: for positive degree it is an immersion.
* `Projectivization.isSmoothEmbedding_map_comp_veronese`: for positive degree it is a `C^r`
  embedding over `ℝ` or `ℂ`, with closed image by
  `Projectivization.isClosedEmbedding_map_comp_veronese`.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Graduate Texts in Mathematics 133, Springer,
  1992, Lecture 2, Example 2.4.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
-/

public section

open Set Function Topology Manifold
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {N : ℕ}

/-- The vector of monomials of degree `d` of `v` is a `C^r` function of `v`, for every `r`. -/
@[fun_prop]
theorem contDiff_veroneseMonomials (d : ℕ) {r : ℕ∞ω} :
    ContDiff 𝕜 r (veroneseMonomials (N := N) (K := 𝕜) d) :=
  contDiff_pi.2 fun k ↦ by
    simp only [veroneseMonomials_apply]
    exact contDiff_prod fun i _ ↦ (contDiff_pi.1 contDiff_id i).pow _

end TauCeti

namespace Projectivization

open TauCeti

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n d : ℕ}

/-- The Veronese map, read through an injective linear map `f` from its space of homogeneous
coordinates to `Fin (n + 1) → 𝕜`, is `C^r` for every `r`; for `r = ω` it is analytic. Over `ℂ`
it is holomorphic. -/
theorem contMDiff_map_comp_veronese
    (f : (Fin (veroneseDim (m + 1) d) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f)
    (r : ℕ∞ω) : ContMDiff 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf ∘ veronese 𝕜 d) :=
  contMDiff_of_contDiffOn (F := f ∘ veroneseMonomials d)
    ((⟨f, LinearMap.continuous_on_pi f⟩ : (Fin (veroneseDim (m + 1) d) → 𝕜) →L[𝕜]
      Fin (n + 1) → 𝕜).contDiff.comp (contDiff_veroneseMonomials d)).contDiffOn
    (fun _ hv ↦ (map_ne_zero_iff f hf).2 (veroneseMonomials_ne_zero d hv))
    fun _ _ ↦ by simp [map_mk]

/-- The Veronese map of degree `d` is `C^r` for every `r`, from `ℙ 𝕜 (Fin (m + 1) → 𝕜)` with its
standard atlas to `ℙ 𝕜 (Fin (veroneseDim (m + 1) d) → 𝕜)` with the atlas `finChartedSpace`. For
`r = ω` it is analytic; over `ℂ` it is holomorphic. -/
theorem contMDiff_veronese (d : ℕ) (r : ℕ∞ω) :
    letI := finChartedSpace 𝕜 (veroneseDim (m + 1) d)
    ContMDiff 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin (veroneseDim (m + 1) d - 1) → 𝕜) r
      (veronese (N := m + 1) 𝕜 d) :=
  -- After reindexing, the Veronese map is read through the reindexing linear equivalence.
  contMDiff_finChartedSpace_iff.2 ⟨continuous_veronese d, by
    rw [coe_finSubOneAddOneHomeomorph]
    exact contMDiff_map_comp_veronese _ (LinearEquiv.injective _) r⟩

end NontriviallyNormedField

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {m n d : ℕ}

/-- **The Veronese map is an immersion.** For positive degree, the Veronese map read through an
injective linear map `f` is a `C^r` immersion for every `r ≥ 1`. Near a point where the `i`-th
homogeneous coordinate is nonzero, it has the analytic left inverse
`[w] ↦ [veroneseLocalInverse 𝕜 (d - 1) i (g w)]` for a linear left inverse `g` of `f`. -/
theorem isImmersion_map_comp_veronese (hd : d ≠ 0)
    (f : (Fin (veroneseDim (m + 1) d) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f)
    {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsImmersion 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf ∘ veronese 𝕜 d) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hd
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  rw [isImmersion_iff_forall_isImmersionAt]
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  have hx := mapsTo_map_comp_veronese_linearProjectionDomain hf hg i hi
  have hs := isOpen_linearProjectionDomain
    (LinearMap.continuous_on_pi (veroneseLocalInverse 𝕜 e i ∘ₗ g))
  exact ((contMDiff_map_comp_veronese f hf r).contMDiffOn (s := univ))
    |>.isImmersionAt_of_comp_eventuallyEq_id isOpen_univ (mem_univ x) hr
    (((contMDiffOn_linearProjection (veroneseLocalInverse 𝕜 e i ∘ₗ g) r _ hx).contMDiffAt
      (hs.mem_nhds hx)).mdifferentiableAt hr0)
    (Filter.eventuallyEq_of_mem ((isOpen_affineOpen i).mem_nhds hi)
      (leftInvOn_linearProjection_veroneseLocalInverse hf hg i))

/-- **The Veronese map is a closed analytic embedding.** For positive degree, the Veronese map read
through an injective linear map is a `C^r` embedding for every `r ≥ 1`, including the analytic
order `ω`; its image is closed by `Projectivization.isClosedEmbedding_map_comp_veronese`. Over `ℂ`
it is a holomorphic embedding. -/
theorem isSmoothEmbedding_map_comp_veronese (hd : d ≠ 0)
    (f : (Fin (veroneseDim (m + 1) d) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f)
    {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsSmoothEmbedding 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf ∘ veronese 𝕜 d) :=
  ⟨isImmersion_map_comp_veronese hd f hf hr,
    (isClosedEmbedding_map_comp_veronese hd f hf).isEmbedding⟩

end RCLike

end Projectivization
