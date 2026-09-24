/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Subgroup neighbourhoods under translation

An identity-neighbourhood description of a subgroup transports to every point of the subgroup by
left multiplication. The result is stated for an arbitrary local parametrisation, so it can be
used both for exponential charts and for later subgroup atlases.

## Main results

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
    simpa only [ContinuousAt, smul_eq_mul, inv_mul_cancel] using
      ((continuous_const_smul (T := G) g⁻¹).continuousAt :
        ContinuousAt (fun x : G => g⁻¹ • x) g)
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
