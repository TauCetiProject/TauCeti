/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Identity neighbourhoods under translation

Continuous left translations transport identity-neighbourhood descriptions to every point of a
group. In particular, a group homomorphism is inducing exactly when it induces the neighbourhood
filter at the identity. A local parametrisation of a subgroup likewise transports to every point
of the subgroup, for use both in exponential charts and in subgroup atlases.

## Main results

* `TauCeti.isInducing_iff_nhds_one` characterises inducing group homomorphisms by the neighbourhood
  filters at the identity, assuming only continuous left translations on both groups.
* `TauCeti.isInducing_iff_nhds_zero` is the additive counterpart.
* `Subgroup.eventually_mem_iff_exists_mul_eq_of_mem` transports an eventual identity-neighbourhood
  characterisation `f y = x` to the translated form `g * f y = x` near `g ∈ K`.
* `AddSubgroup.eventually_mem_iff_exists_add_eq_of_mem` is the additive counterpart.

The only regularity required is continuity of the constant action: inversion is used algebraically
to identify the translated neighbourhood, while Mathlib's action homeomorphism
`Homeomorph.smul` (and its additive `Homeomorph.vadd` analogue) supplies the topological transport.
-/

public section

open Filter
open scoped Topology

variable {G : Type*} [TopologicalSpace G] [Group G] [ContinuousConstSMul G G]

namespace TauCeti

/-- A homomorphism between groups with continuous left translations is inducing exactly when it
induces the neighbourhood filter at the identity.

This generalises Mathlib's `IsTopologicalGroup.isInducing_iff_nhds_one`. -/
@[to_additive
  /-- A homomorphism between additive groups with continuous left translations is inducing exactly
  when it induces the neighbourhood filter at zero.

  This generalises Mathlib's `IsTopologicalAddGroup.isInducing_iff_nhds_zero`. -/]
theorem isInducing_iff_nhds_one {H : Type*} [Group H] [TopologicalSpace H]
    [ContinuousConstSMul H H] {F : Type*} [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    Topology.IsInducing f ↔ 𝓝 (1 : G) = (𝓝 (1 : H)).comap f := by
  rw [Topology.isInducing_iff_nhds]
  refine ⟨(map_one f ▸ · 1), fun hf x ↦ ?_⟩
  -- Left-translation homeomorphisms identify the neighbourhoods of `x` and `f x` with those of `1`.
  have hG : 𝓝 x = comap (x⁻¹ * ·) (𝓝 (1 : G)) := by
    simpa only [smul_eq_mul, inv_mul_cancel] using
      (isHomeomorph_smul (α := G) x⁻¹).isInducing.nhds_eq_comap x
  have hH : 𝓝 (f x) = comap ((f x)⁻¹ * ·) (𝓝 (1 : H)) := by
    simpa only [smul_eq_mul, inv_mul_cancel] using
      (isHomeomorph_smul (α := H) (f x)⁻¹).isInducing.nhds_eq_comap (f x)
  rw [hG, hH, comap_comap, hf, comap_comap]
  congr 1
  ext y
  simp

end TauCeti

namespace Subgroup

/-- A local parametrisation of a subgroup at the identity translates to every point of the
subgroup. The parameter set and map are arbitrary, so the statement applies directly to local
exponential charts. -/
@[to_additive
  /-- A local parametrisation of an additive subgroup at zero translates to every point of the
  subgroup. -/]
theorem eventually_mem_iff_exists_mul_eq_of_mem
    (K : Subgroup G) {ι : Type*} {s : Set ι} {f : ι → G} {g : G} (hg : g ∈ K)
    (h : ∀ᶠ x in 𝓝 (1 : G), x ∈ K ↔ ∃ y ∈ s, f y = x) :
    ∀ᶠ x in 𝓝 g, x ∈ K ↔ ∃ y ∈ s, g * f y = x := by
  have hmap : Tendsto (fun x : G => g⁻¹ * x) (𝓝 g) (𝓝 (1 : G)) := by
    have hcont : ContinuousAt (fun x : G => g⁻¹ • x) g := by
      -- Expose the bundled homeomorphism's action coercion before applying its continuity.
      convert ((Homeomorph.smul (α := G) g⁻¹).continuous.continuousAt :
        ContinuousAt (Homeomorph.smul (α := G) g⁻¹) g) using 1
      rfl
    simpa only [ContinuousAt, smul_eq_mul, inv_mul_cancel] using hcont
  filter_upwards [hmap.eventually h] with x hx
  constructor
  · intro hKx
    obtain ⟨y, hy, hfy⟩ := hx.mp ((K.mul_mem_cancel_left (K.inv_mem hg)).mpr hKx)
    refine ⟨y, hy, ?_⟩
    exact (eq_inv_mul_iff_mul_eq.mp hfy)
  · rintro ⟨y, hy, hfy⟩
    apply (K.mul_mem_cancel_left (K.inv_mem hg)).mp
    exact hx.mpr ⟨y, hy, eq_inv_mul_iff_mul_eq.mpr hfy⟩

end Subgroup

end
