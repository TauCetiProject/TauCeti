/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Completing a surjection to an isomorphism

A surjective continuous linear map `A : E → G` out of a finite-dimensional normed space is the
second component of an isomorphism `E ≃ F × G` onto the product with any space `F` of the
complementary dimension `dim E - dim G`: some continuous linear map `c : E → F` makes `(c, A)`
invertible (`ContinuousLinearMap.exists_isInvertible_prod_of_surjective`). The map `c` is a
projection onto the kernel of `A` followed by an isomorphism of that kernel with `F`.

In the gluing of broken trajectories in Morse theory, `A` is the expanding coordinate of a disc in
an unstable manifold, read in a Morse chart, and `c` parametrizes the family of trajectories
through the disc; the invertibility of `(c, A)` is the hypothesis of the gluing of families of
transverse discs.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Completing a surjection to an isomorphism.** A surjective continuous linear map
`A : E → G` out of a finite-dimensional normed space extends, for every finite-dimensional `F`
with `dim F + dim G = dim E`, to an invertible map `(c, A) : E → F × G`. -/
theorem exists_isInvertible_prod_of_surjective [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A : E →L[𝕜] G} (hA : Function.Surjective A)
    (hdim : Module.finrank 𝕜 F + Module.finrank 𝕜 G = Module.finrank 𝕜 E) :
    ∃ c : E →L[𝕜] F, (c.prod A).IsInvertible := by
  have : FiniteDimensional 𝕜 G := Module.Finite.of_surjective (A : E →ₗ[𝕜] G) hA
  -- By rank–nullity the kernel `K` of `A` has the dimension of `F`.
  have h := LinearMap.finrank_range_add_finrank_ker (A : E →ₗ[𝕜] G)
  rw [LinearMap.range_eq_top_of_surjective _ hA, finrank_top] at h
  set K := LinearMap.ker (A : E →ₗ[𝕜] G)
  have hK : Module.finrank 𝕜 K = Module.finrank 𝕜 F := by omega
  -- A projection of `E` onto the kernel, followed by an isomorphism of the kernel with `F`.
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective K.subtype K.ker_subtype
  set e : K ≃ₗ[𝕜] F := LinearEquiv.ofFinrankEq K F hK
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ π),
    (isInvertible_iff_injective_of_finrank_eq (by rw [Module.finrank_prod, hdim])).2 ?_⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨hcz, hAz⟩ := Prod.mk.inj hz
  -- `z` lies in the kernel of `A`, on which the projection is the identity.
  have hzK : z ∈ K := hAz
  have hπz : π z = ⟨z, hzK⟩ := LinearMap.congr_fun hπ ⟨z, hzK⟩
  have h0 : e (π z) = 0 := hcz
  rw [hπz, LinearEquiv.map_eq_zero_iff] at h0
  exact congrArg Subtype.val h0

end ContinuousLinearMap
