/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Geometry.Manifold.SMulGroupoid

/-!
# The translation groupoid

The translation groupoid of the complex plane is
`TauCeti.smulGroupoid (Multiplicative ℂ) ℂ`, using the additive action of `ℂ` on itself.
Its members are exactly the open partial homeomorphisms whose complex derivative is `1`
on their source. Equivalently, they are translations on each connected component of the
source; a connected source admits a single translation vector. These characterisations
also hold over `ℝ`.

These criteria let one recognise translation atlases by their derivatives, without choosing
translation vectors on chart overlaps.

The groupoid is the locally generated pseudogroup, not just the restrictions of global
translations: different connected components may have different translation vectors.

## References

* H. Masur and S. Tabachnikov, *Rational billiards and flat structures*, Handbook of Dynamical
  Systems, Vol. 1A (2002), Section 1, for translation atlases on flat surfaces.
-/

public section

open Set Filter Topology

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [RCLike 𝕜] (e : OpenPartialHomeomorph 𝕜 𝕜)

/-- An open partial homeomorphism is locally a translation exactly when its derivative is `1`
at every point of its source. The `HasDerivAt` form also records differentiability. -/
theorem mem_smulGroupoid_iff_hasDerivAt :
    e ∈ TauCeti.smulGroupoid (Multiplicative 𝕜) 𝕜 ↔
      ∀ x ∈ e.source, HasDerivAt e 1 x := by
  constructor
  · intro he x hx
    obtain ⟨c, hc⟩ := TauCeti.mem_smulGroupoid_iff.mp he x hx
    simpa using ((hasDerivAt_id x).const_add c.toAdd).congr_of_eventuallyEq hc
  · intro he
    apply TauCeti.mem_smulGroupoid_iff.mpr
    intro x hx
    let U := connectedComponentIn e.source x
    have hU : IsOpen U := e.open_source.connectedComponentIn
    have hUs : U ⊆ e.source := connectedComponentIn_subset _ _
    obtain ⟨c, hc⟩ := hU.exists_eq_add_of_deriv_eq isPreconnected_connectedComponentIn
      (fun z hz ↦ (he z (hUs hz)).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn (fun z hz ↦ by simp [(he z (hUs hz)).deriv])
    refine ⟨Multiplicative.ofAdd c, ?_⟩
    filter_upwards [hU.mem_nhds (mem_connectedComponentIn hx)] with z hz
    simpa [add_comm] using hc hz

/-- The translation groupoid is characterised by the total derivative being `1` on the source.
No separate differentiability hypothesis is required, since `1` is nonzero. -/
theorem mem_smulGroupoid_iff_deriv_eq_one :
    e ∈ TauCeti.smulGroupoid (Multiplicative 𝕜) 𝕜 ↔
      ∀ x ∈ e.source, deriv e x = 1 := by
  rw [e.mem_smulGroupoid_iff_hasDerivAt]
  refine ⟨fun h x hx ↦ (h x hx).deriv, fun h x hx ↦ ?_⟩
  have hd : DifferentiableAt 𝕜 e x :=
    differentiableAt_of_deriv_ne_zero (by rw [h x hx]; exact one_ne_zero)
  simpa [h x hx] using hd.hasDerivAt

/-- A member of the translation groupoid is a translation on each connected component of its
source, and this componentwise condition suffices for membership. -/
theorem mem_smulGroupoid_iff_eqOn_connectedComponentIn :
    e ∈ TauCeti.smulGroupoid (Multiplicative 𝕜) 𝕜 ↔
      ∀ x ∈ e.source, ∃ c : 𝕜,
        EqOn e (fun z ↦ c + z) (connectedComponentIn e.source x) := by
  constructor
  · intro he x _
    have hd := e.mem_smulGroupoid_iff_hasDerivAt.mp he
    obtain ⟨c, hc⟩ := (e.open_source.connectedComponentIn (x := x)).exists_eq_add_of_deriv_eq
      isPreconnected_connectedComponentIn
      (fun z hz ↦
        (hd z (connectedComponentIn_subset _ _ hz)).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn
      (fun z hz ↦ by simp [(hd z (connectedComponentIn_subset _ _ hz)).deriv])
    exact ⟨c, fun z hz ↦ by simpa [add_comm] using hc hz⟩
  · intro he
    apply TauCeti.mem_smulGroupoid_iff.mpr
    intro x hx
    obtain ⟨c, hc⟩ := he x hx
    refine ⟨Multiplicative.ofAdd c, ?_⟩
    filter_upwards [e.open_source.connectedComponentIn.mem_nhds
      (mem_connectedComponentIn hx)] with z hz
    simpa using hc hz

/-- On a connected source, the members of the translation groupoid are exactly the restrictions
of translations. The empty source is allowed. -/
theorem mem_smulGroupoid_iff_eqOn_add (hs : IsPreconnected e.source) :
    e ∈ TauCeti.smulGroupoid (Multiplicative 𝕜) 𝕜 ↔
      ∃ c : 𝕜, EqOn e (fun z ↦ c + z) e.source := by
  constructor
  · intro he
    have hd := e.mem_smulGroupoid_iff_hasDerivAt.mp he
    obtain ⟨c, hc⟩ := e.open_source.exists_eq_add_of_deriv_eq hs
      (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn (fun z hz ↦ by simp [(hd z hz).deriv])
    exact ⟨c, fun z hz ↦ by simpa [add_comm] using hc hz⟩
  · rintro ⟨c, hc⟩
    apply TauCeti.mem_smulGroupoid_iff.mpr
    intro x hx
    refine ⟨Multiplicative.ofAdd c, ?_⟩
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    simpa using hc hz

end OpenPartialHomeomorph
