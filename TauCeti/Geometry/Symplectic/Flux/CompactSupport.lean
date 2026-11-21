/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Symplectic.Flux

/-!
# The compactly supported flux of a diffeotopy

Let `σ` be a closed two-form on a manifold `M` and let `φ_t`, `t ∈ [0, 1]`, be a smooth
diffeotopy of `M` whose final diffeomorphism preserves `σ`. Its flux form
`∫₀¹ φ_t^* (ι_{X_t} σ) dt` (`TauCeti.Diffeotopy.fluxForm`) is closed, with de Rham class the flux
`Flux(φ) ∈ H¹_dR(M)` (`TauCeti.Diffeotopy.flux`).

The flux form vanishes at every point near which the whole motion is stationary, since there the
velocity of the motion is zero (`TauCeti.Diffeotopy.fluxForm_apply_eq_zero_of_eventually`). So if
every map `φ_t` is the identity outside one common closed set `K`, the flux form is supported in
`K` (`TauCeti.Diffeotopy.tsupport_fluxForm_subset`), and when `K` is compact the flux form is a
compactly supported closed form (`TauCeti.Diffeotopy.fluxForm_mem_compactlySupportedClosedForms`).
Its class in compactly supported de Rham cohomology is the **compactly supported flux**

`Flux_c(φ) ∈ H¹_c(M)` (`TauCeti.Diffeotopy.compactFlux`).

Forgetting supports, along the comparison map `H¹_c(M) → H¹_dR(M)`, carries it to the ordinary
flux (`TauCeti.Diffeotopy.toDeRhamCohomology_compactFlux`). The comparison map need not be
injective on noncompact manifolds, so the compactly supported flux can retain more information
than the ordinary one: on the cylinder `ℝ × AddCircle p` a shear supported in a compact band has
zero flux but nonzero compactly supported flux (`TauCeti.Geometry.Symplectic.Flux.Cylinder`).
On a compact manifold every form is compactly supported and the two fluxes determine each other.

## Main definitions

* `TauCeti.Diffeotopy.compactFlux`: the class in `H¹_c(M)` of a compactly supported flux form.

## Main results

* `TauCeti.Diffeotopy.fluxForm_apply_eq_zero_of_eventually`: the flux form vanishes where the
  motion is stationary nearby.
* `TauCeti.Diffeotopy.tsupport_fluxForm_subset`: a diffeotopy which is the identity outside a
  closed set `K` has flux form supported in `K`.
* `TauCeti.Diffeotopy.fluxForm_mem_compactlySupportedClosedForms`: for compact `K`, its flux form
  is compactly supported and closed.
* `TauCeti.Diffeotopy.toDeRhamCohomology_compactFlux`: forgetting supports sends the compactly
  supported flux to the flux.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism, including its compactly supported
  version on open manifolds).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 4.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (Φ : Diffeotopy J ∞ M)

variable [IsManifold J ∞ M]

/-! ### Support of the flux form -/

/-- **The flux form vanishes where the motion is stationary.** If every map of the diffeotopy
fixes every point near `x`, the flux form vanishes at `x`: near `(x, t)` the motion is the
projection to `M`, which has no time derivative. -/
theorem fluxForm_apply_eq_zero_of_eventually (σ : SmoothForm J M ℝ 2) {x : M}
    (hx : ∀ᶠ y in 𝓝 x, ∀ t, Φ (t, y) = y) : (Φ.fluxForm σ).val x = 0 := by
  rw [fluxForm_apply]
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : E [⋀^Fin 1]→L[ℝ] ℝ))
    fun t _ ↦ ?_).trans intervalIntegral.integral_zero
  have hcyl : Φ.cylinderMap =ᶠ[𝓝 (x, projIcc 0 1 zero_le_one t)] Prod.fst :=
    ((continuous_fst.tendsto _).eventually hx).mono fun p hp ↦
      (Φ.cylinderMap_apply p).trans (hp p.2)
  -- The time vector `(0, 1)` is killed by the derivative of the projection.
  have h0 : mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, projIcc 0 1 zero_le_one t)
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t))) = 0 :=
    -- The derivative of the projection sends `(0, 1)` to its first component `0`, up to the
    -- identification of the tangent spaces at `x` and at `φ_t x = x`.
    DFunLike.congr_fun ((hasMFDerivAt_fst _).congr_of_eventuallyEq hcyl).mfderiv _
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [curryLeft_mfderiv_cylinderMap_apply]
  exact (σ.val _).map_coord_zero 0 h0

/-- **Flux forms of supported diffeotopies are supported.** If every map of the diffeotopy is the
identity outside a closed set `K`, the flux form is supported in `K`. -/
theorem tsupport_fluxForm_subset (σ : SmoothForm J M ℝ 2) {K : Set M} (hK : IsClosed K)
    (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    _root_.tsupport (α := E [⋀^Fin 1]→L[ℝ] ℝ) (Φ.fluxForm σ).val ⊆ K := by
  refine closure_minimal (fun x hx ↦ ?_) hK
  by_contra hxK
  exact hx (Φ.fluxForm_apply_eq_zero_of_eventually σ
    (eventually_of_mem (hK.isOpen_compl.mem_nhds hxK) fun y hy t ↦ hΦK t hy))

/-- If every map of the diffeotopy is the identity outside a compact set, its flux form is
compactly supported. -/
theorem fluxForm_mem_compactlySupportedForms [T2Space M] (σ : SmoothForm J M ℝ 2) {K : Set M}
    (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    Φ.fluxForm σ ∈ compactlySupportedForms J M 1 :=
  (mem_compactlySupportedForms J).mpr <| hK.of_isClosed_subset (_root_.isClosed_tsupport _)
    (Φ.tsupport_fluxForm_subset σ hK.isClosed hΦK)

/-- If every map of the diffeotopy is the identity outside a compact set and the final
diffeomorphism preserves a closed two-form `σ`, the flux form is a compactly supported closed
form. -/
theorem fluxForm_mem_compactlySupportedClosedForms [T2Space M] {σ : SmoothForm J M ℝ 2}
    (hσ : SmoothForm.IsClosed σ) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ)
    {K : Set M} (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    Φ.fluxForm σ ∈ compactlySupportedClosedForms J M 1 :=
  (mem_compactlySupportedClosedForms J).mpr
    ⟨Φ.fluxForm_mem_compactlySupportedForms σ hK hΦK, Φ.fluxForm_mem_closedForms hσ hΦ⟩

/-! ### The compactly supported flux -/

/-- The **compactly supported flux** of a diffeotopy `φ` with respect to a closed two-form `σ`
preserved by its final diffeomorphism, when the flux form `∫₀¹ φ_t^* (ι_{X_t} σ) dt` is compactly
supported: the class of the flux form in `H¹_c(M)`. This is the case when every map `φ_t` is the
identity outside one common compact set
(`TauCeti.Diffeotopy.fluxForm_mem_compactlySupportedForms`). -/
def compactFlux (σ : closedForms J M 2) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hc : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1) :
    compactlySupportedDeRhamCohomology J M 1 :=
  compactlySupportedDeRhamCohomology.mk J 1
    ⟨Φ.fluxForm σ.val, (mem_compactlySupportedClosedForms J).mpr ⟨hc, Φ.fluxForm_mem_closedForms
      ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property)) hΦ⟩⟩

/-- The compactly supported flux is the compactly supported class of the flux form. -/
theorem compactFlux_def (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hc : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1) :
    Φ.compactFlux σ hΦ hc = compactlySupportedDeRhamCohomology.mk J 1
      ⟨Φ.fluxForm σ.val, (mem_compactlySupportedClosedForms J).mpr ⟨hc, Φ.fluxForm_mem_closedForms
        ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property)) hΦ⟩⟩ :=
  (rfl)

/-- **Forgetting supports gives the flux.** The comparison map `H¹_c(M) → H¹_dR(M)` sends the
compactly supported flux of a diffeotopy to its flux. -/
@[simp]
theorem toDeRhamCohomology_compactFlux (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hc : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1) :
    compactlySupportedDeRhamCohomology.toDeRhamCohomology J M 1 (Φ.compactFlux σ hΦ hc) =
      Φ.flux σ hΦ := by
  rw [compactFlux_def, compactlySupportedDeRhamCohomology.toDeRhamCohomology_mk, flux_def]

/-- The constant diffeotopy has zero compactly supported flux. -/
@[simp]
theorem compactFlux_refl (σ : closedForms J M 2)
    (hΦ : (refl J ∞ M).final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hc : (refl J ∞ M).fluxForm σ.val ∈ compactlySupportedForms J M 1) :
    (refl J ∞ M).compactFlux σ hΦ hc = 0 := by
  rw [compactFlux_def, compactlySupportedDeRhamCohomology.mk_eq_zero_iff]
  simp only [fluxForm_refl, zero_mem]

end Diffeotopy

end TauCeti
