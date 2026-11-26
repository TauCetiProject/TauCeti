/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian

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

The compactly supported flux is a homomorphism on compactly supported diffeotopies: it is additive
on pointwise composites and changes sign under pointwise inversion
(`TauCeti.Diffeotopy.compactFlux_trans`, `TauCeti.Diffeotopy.compactFlux_symm`). The ordinary laws
hold modulo exact forms; here the correction is the differential of a function vanishing at every
point which the first diffeotopy never moves
(`TauCeti.Diffeotopy.exists_fluxForm_trans_sub_sub_eq_mextDerivₗ`), so it is compactly supported.
Conjugating by a diffeomorphism `f` preserving `σ` transports the compactly supported flux by the
pullback along `f⁻¹`
(`TauCeti.Diffeotopy.compactFlux_transDiffeomorph_of_mem_diffeomorphStabilizer`).

For an exact two-form `σ = dθ` the primitive `θ` need not be compactly supported, but the flux
form is still `φ₁^* θ - θ` up to the exterior derivative of a function vanishing outside `K`
(`TauCeti.Diffeotopy.fluxForm_mextDerivₗ_sub_mem_exactCompactlySupportedForms`). Hence the
compactly supported flux is the class of the compactly supported closed form `φ₁^* θ - θ`
(`TauCeti.Diffeotopy.compactFlux_mextDerivₗ`), and it depends only on `φ₁`
(`TauCeti.Diffeotopy.compactFlux_eq_of_final_eq`). In particular a compactly supported diffeotopy
ending at the identity has zero compactly supported flux
(`TauCeti.Diffeotopy.compactFlux_eq_zero_of_final_eq_refl`): on an exact symplectic manifold, the
compactly supported fluxes of loops of compactly supported symplectomorphisms all vanish.

Similarly, a diffeotopy with a Hamiltonian `F`, read along the motion, has flux form `d g` for
a smooth function `g` vanishing wherever `F (x, ·) = 0`. If `F` vanishes outside a compact set
at every time, so does `g`, and the compactly supported flux is zero
(`TauCeti.Diffeotopy.HasHamiltonian.compactFlux_eq_zero`).

On a Hausdorff boundaryless finite-dimensional manifold with a closed nondegenerate two-form `σ`,
compact or not, every class `[α] ∈ H¹_c(M)` is a compactly supported flux
(`TauCeti.Diffeotopy.exists_compactFlux_eq`): the vector field `(σ♭)⁻¹ α` vanishes outside the
support of `α`, so its flow is complete and is the identity outside that compact set, and its
time-one flow has compactly supported flux `[α]`.

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
* `TauCeti.Diffeotopy.compactFlux_transDiffeomorph_of_mem_diffeomorphStabilizer`: conjugating by
  a diffeomorphism `f` preserving `σ` transports the compactly supported flux by `(f⁻¹)^*`.
* `TauCeti.Diffeotopy.compactFlux_trans`, `TauCeti.Diffeotopy.compactFlux_symm`,
  `TauCeti.Diffeotopy.compactFlux_symm_trans`: the compactly supported flux of pointwise
  composites, inverses and quotients of compactly supported diffeotopies.
* `TauCeti.Diffeotopy.fluxForm_mextDerivₗ_sub_mem_exactCompactlySupportedForms`,
  `TauCeti.Diffeotopy.compactFlux_mextDerivₗ`: for `σ = dθ`, the compactly supported flux is the
  class of `φ₁^* θ - θ` in `H¹_c(M)`.
* `TauCeti.Diffeotopy.compactFlux_eq_of_final_eq`,
  `TauCeti.Diffeotopy.compactFlux_eq_zero_of_final_eq_refl`: for exact `σ`, the compactly
  supported flux depends only on the final diffeomorphism, and vanishes on loops.
* `TauCeti.Diffeotopy.exists_compactFlux_eq`: for a closed nondegenerate two-form, every class of
  `H¹_c(M)` is the compactly supported flux of a compactly supported symplectic flow.
* `TauCeti.Diffeotopy.HasHamiltonian.fluxForm_mem_exactCompactlySupportedForms`,
  `TauCeti.Diffeotopy.HasHamiltonian.compactFlux_eq_zero`: a diffeotopy with a compactly
  supported Hamiltonian has compactly supported exact flux form and zero compactly supported flux.

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

/-- **Naturality of the compactly supported flux under diffeomorphisms preserving `σ`.**
Conjugating a diffeotopy by a diffeomorphism `f` preserving `σ` transports its compactly
supported flux by the pullback along `f⁻¹`. -/
theorem compactFlux_transDiffeomorph_of_mem_diffeomorphStabilizer {σ : closedForms J M 2}
    {f : M ≃ₘ⟮J, J⟯ M} (hf : f ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : (Φ.transDiffeomorph f).final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hcΦ : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1)
    (hc : (Φ.transDiffeomorph f).fluxForm σ.val ∈ compactlySupportedForms J M 1) :
    (Φ.transDiffeomorph f).compactFlux σ h hc =
      compactlySupportedDeRhamCohomology.equivOfDiffeomorph f.symm 1
        (Φ.compactFlux σ hΦ hcΦ) := by
  rw [compactFlux_def, compactFlux_def]
  -- `rw` would fail its motive check from here on: the proof `f.symm.toHomeomorph.isProperMap`
  -- has type `IsProperMap ⇑f.symm` only after unfolding the coercion of `f.symm.toHomeomorph`.
  refine Eq.trans ?_ (compactlySupportedDeRhamCohomology.equivOfDiffeomorph_mk f.symm 1 _).symm
  congr 1
  apply Subtype.ext
  exact ((Φ.fluxForm_transDiffeomorph f σ.val).trans (congrArg
    (fun τ ↦ SmoothForm.mpullback f.symm f.symm.contMDiff (Φ.fluxForm τ))
    (SmoothForm.mem_diffeomorphStabilizer.1 hf))).trans
    (compactlySupportedClosedForms.coe_mpullback f.symm f.symm.contMDiff
      f.symm.toHomeomorph.isProperMap 1 ⟨Φ.fluxForm σ.val, _⟩).symm

/-! ### The compactly supported flux homomorphism -/

section Trans

variable (Ψ : Diffeotopy J ∞ M)

/-- **The compactly supported flux homomorphism.** For a closed two-form `σ` preserved by the
final diffeomorphisms `φ₁` and `ψ₁`, where `φ_t` is the identity outside a compact set at every
time, the compactly supported flux of the pointwise composite `ψ_t ∘ φ_t` is the sum of the
compactly supported fluxes of `φ` and `ψ`. -/
theorem compactFlux_trans [R1Space M] (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : (Φ.trans Ψ).final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hcΦ : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1)
    (hcΨ : Ψ.fluxForm σ.val ∈ compactlySupportedForms J M 1)
    (hc : (Φ.trans Ψ).fluxForm σ.val ∈ compactlySupportedForms J M 1) {K : Set M}
    (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    (Φ.trans Ψ).compactFlux σ h hc = Ψ.compactFlux σ hΨ hcΨ + Φ.compactFlux σ hΦ hcΦ := by
  obtain ⟨g, hg0, hg⟩ := Φ.exists_fluxForm_trans_sub_sub_eq_mextDerivₗ Ψ
    ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property))
  rw [SmoothForm.mem_diffeomorphStabilizer.mp hΨ] at hg
  -- The primitive `g` vanishes outside `K`, so it is compactly supported.
  have hgc : g ∈ compactlySupportedForms J M 0 :=
    (mem_compactlySupportedForms J).mpr
      (HasCompactSupport.intro hK fun x hx ↦ hg0 x fun t ↦ hΦK t hx)
  rw [compactFlux_def, compactFlux_def, compactFlux_def, ← map_add,
    compactlySupportedDeRhamCohomology.mk_eq_mk_iff, Submodule.coe_add, ← sub_sub, hg,
    exactCompactlySupportedForms_succ]
  exact Submodule.mem_map_of_mem hgc

/-- **The compactly supported flux of the reversed diffeotopy.** For a closed two-form `σ`
preserved by `φ₁`, where `φ_t` is the identity outside a compact set at every time, the
diffeotopy `φ_t⁻¹` has the negated compactly supported flux of `φ`. -/
theorem compactFlux_symm [T2Space M] (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : Φ.symm.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hcΦ : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1)
    (hc : Φ.symm.fluxForm σ.val ∈ compactlySupportedForms J M 1) {K : Set M}
    (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    Φ.symm.compactFlux σ h hc = -Φ.compactFlux σ hΦ hcΦ := by
  have hzero : ∀ (h' : (Φ.trans Φ.symm).final ∈ SmoothForm.diffeomorphStabilizer σ.val)
      (hc' : (Φ.trans Φ.symm).fluxForm σ.val ∈ compactlySupportedForms J M 1),
      (Φ.trans Φ.symm).compactFlux σ h' hc' = 0 := by
    rw [self_trans_symm]
    exact compactFlux_refl σ
  have h' : (Φ.trans Φ.symm).final ∈ SmoothForm.diffeomorphStabilizer σ.val := by
    rw [self_trans_symm, final_refl]
    exact (SmoothForm.diffeomorphStabilizer σ.val).one_mem
  rw [eq_neg_iff_add_eq_zero, ← hzero h' ((Φ.trans Φ.symm).fluxForm_mem_compactlySupportedForms
    σ.val (hK.union hK) (eqOn_id_trans hΦK (eqOn_id_symm hΦK))),
    compactFlux_trans Φ Φ.symm σ hΦ h h' hcΦ hc _ hK hΦK]

/-- **The compactly supported flux of a quotient of diffeotopies.** For a closed two-form `σ`
preserved by `φ₁` and `ψ₁`, where `ψ_t` is the identity outside a compact set at every time, the
diffeotopy `φ_t ∘ ψ_t⁻¹` has the compactly supported flux of `φ` minus that of `ψ`. -/
theorem compactFlux_symm_trans [T2Space M] (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : (Ψ.symm.trans Φ).final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hcΦ : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1)
    (hcΨ : Ψ.fluxForm σ.val ∈ compactlySupportedForms J M 1)
    (hc : (Ψ.symm.trans Φ).fluxForm σ.val ∈ compactlySupportedForms J M 1) {L : Set M}
    (hL : IsCompact L) (hΨL : ∀ t, EqOn (fun x ↦ Ψ (t, x)) id Lᶜ) :
    (Ψ.symm.trans Φ).compactFlux σ h hc = Φ.compactFlux σ hΦ hcΦ - Ψ.compactFlux σ hΨ hcΨ := by
  have hΨs : Ψ.symm.final ∈ SmoothForm.diffeomorphStabilizer σ.val := by
    rw [final_symm, ← Diffeomorph.inv_def]
    exact (SmoothForm.diffeomorphStabilizer σ.val).inv_mem hΨ
  have hcΨs : Ψ.symm.fluxForm σ.val ∈ compactlySupportedForms J M 1 :=
    Ψ.symm.fluxForm_mem_compactlySupportedForms σ.val hL (eqOn_id_symm hΨL)
  rw [compactFlux_trans Ψ.symm Φ σ hΨs hΦ h hcΨs hcΦ hc hL (eqOn_id_symm hΨL),
    compactFlux_symm Ψ σ hΨ hΨs hcΨ hcΨs hL hΨL, sub_eq_add_neg]

end Trans

/-! ### Exact forms -/

/-- **The compactly supported flux form of an exact form.** For an exact two-form `dθ` and a
diffeotopy which is the identity outside a compact set `K`, the flux form differs from
`φ₁^* θ - θ` by the exterior derivative of a function vanishing outside `K`, namely of `-g` for
the function `g` of `TauCeti.Diffeotopy.exists_fluxForm_mextDerivₗ_eq`. -/
theorem fluxForm_mextDerivₗ_sub_mem_exactCompactlySupportedForms [R1Space M]
    (θ : SmoothForm J M ℝ 1) {K : Set M} (hK : IsCompact K)
    (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    Φ.fluxForm (mextDerivₗ J 1 θ) - (SmoothForm.mpullback Φ.final Φ.final.contMDiff θ - θ) ∈
      exactCompactlySupportedForms J M 1 := by
  obtain ⟨g, hg0, hg⟩ := Φ.exists_fluxForm_mextDerivₗ_eq θ
  have hgc : g ∈ compactlySupportedForms J M 0 :=
    (mem_compactlySupportedForms J).mpr
      (HasCompactSupport.intro hK fun x hx ↦ hg0 x fun t ↦ hΦK t hx)
  rw [exactCompactlySupportedForms_succ]
  exact Submodule.mem_map.mpr ⟨-g, neg_mem hgc, by rw [map_neg, hg, sub_sub_cancel_left]⟩

/-- For an exact two-form `dθ` and a diffeotopy which is the identity outside a compact set and
whose final diffeomorphism `φ₁` preserves `dθ`, the closed one-form `φ₁^* θ - θ` is compactly
supported. -/
theorem mpullback_final_sub_mem_compactlySupportedClosedForms [T2Space M]
    (θ : SmoothForm J M ℝ 1)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (mextDerivₗ J 1 θ)) {K : Set M}
    (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    SmoothForm.mpullback Φ.final Φ.final.contMDiff θ - θ ∈ compactlySupportedClosedForms J M 1 := by
  have h := sub_mem
    (Φ.fluxForm_mem_compactlySupportedClosedForms (SmoothForm.isClosed_mextDerivₗ θ) hΦ hK hΦK)
    (exactCompactlySupportedForms_le_compactlySupportedClosedForms J 1
      (Φ.fluxForm_mextDerivₗ_sub_mem_exactCompactlySupportedForms θ hK hΦK))
  rwa [sub_sub_cancel] at h

/-- **The compactly supported flux of an exact form.** For `σ = dθ` and a diffeotopy which is
the identity outside a compact set and whose final diffeomorphism `φ₁` preserves `σ`, the
compactly supported flux is the class in `H¹_c(M)` of the compactly supported closed form
`φ₁^* θ - θ`. In particular it depends only on `φ₁`, although `θ` need not be compactly
supported. -/
theorem compactFlux_mextDerivₗ [T2Space M] (θ : SmoothForm J M ℝ 1)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (mextDerivₗ J 1 θ))
    (hc : Φ.fluxForm (mextDerivₗ J 1 θ) ∈ compactlySupportedForms J M 1) {K : Set M}
    (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    Φ.compactFlux ⟨mextDerivₗ J 1 θ, mextDerivₗ_mem_closedForms J 1 θ⟩ hΦ hc =
      compactlySupportedDeRhamCohomology.mk J 1
        ⟨_, Φ.mpullback_final_sub_mem_compactlySupportedClosedForms θ hΦ hK hΦK⟩ := by
  rw [compactFlux_def, compactlySupportedDeRhamCohomology.mk_eq_mk_iff]
  exact Φ.fluxForm_mextDerivₗ_sub_mem_exactCompactlySupportedForms θ hK hΦK

/-- For an exact two-form, two diffeotopies which are the identity outside compact sets and have
the same final diffeomorphism have the same compactly supported flux. -/
theorem compactFlux_eq_of_final_eq [T2Space M] {Ψ : Diffeotopy J ∞ M} (σ : closedForms J M 2)
    (hσ : σ.val ∈ exactForms J M 2) (h : Φ.final = Ψ.final)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hcΦ : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1)
    (hcΨ : Ψ.fluxForm σ.val ∈ compactlySupportedForms J M 1) {K L : Set M} (hK : IsCompact K)
    (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) (hL : IsCompact L)
    (hΨL : ∀ t, EqOn (fun x ↦ Ψ (t, x)) id Lᶜ) :
    Φ.compactFlux σ hΦ hcΦ = Ψ.compactFlux σ hΨ hcΨ := by
  obtain ⟨σ, hσc⟩ := σ
  rw [exactForms_succ] at hσ
  obtain ⟨θ, rfl⟩ := hσ
  rw [Φ.compactFlux_mextDerivₗ θ hΦ hcΦ hK hΦK, Ψ.compactFlux_mextDerivₗ θ hΨ hcΨ hL hΨL]
  congr 2
  rw [h]

/-- **Compactly supported loops have zero compactly supported flux for an exact form.** For an
exact two-form, a diffeotopy which is the identity outside a compact set and whose final
diffeomorphism is the identity has zero compactly supported flux. So the compactly supported
fluxes of loops in the group of compactly supported symplectomorphisms of an exact symplectic
manifold all vanish. -/
theorem compactFlux_eq_zero_of_final_eq_refl [T2Space M] (σ : closedForms J M 2)
    (hσ : σ.val ∈ exactForms J M 2) (h : Φ.final = Diffeomorph.refl J M ∞)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hc : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1) {K : Set M} (hK : IsCompact K)
    (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) : Φ.compactFlux σ hΦ hc = 0 := by
  have h' : Φ.final = (refl J ∞ M).final := h.trans final_refl.symm
  rw [Φ.compactFlux_eq_of_final_eq σ hσ h' hΦ (h' ▸ hΦ) hc (by simp) hK hΦK isCompact_empty
    fun t x _ ↦ by simp, compactFlux_refl]

/-! ### Compactly supported Hamiltonians -/

section Hamiltonian

variable {Φ}

/-- **The flux form of a compactly supported Hamiltonian diffeotopy is compactly supported
exact.** If `φ_t` has a Hamiltonian `F` for `σ`, read along the motion, which vanishes at every
time outside a compact set `K`, then the flux form of `φ_t` is the exterior derivative of a
function supported in `K`. -/
theorem HasHamiltonian.fluxForm_mem_exactCompactlySupportedForms [R1Space M]
    {σ : SmoothForm J M ℝ 2} {F : M × unitInterval → ℝ} (h : Φ.HasHamiltonian σ F) {K : Set M}
    (hK : IsCompact K) (hFK : ∀ x ∉ K, ∀ t, F (x, t) = 0) :
    Φ.fluxForm σ ∈ exactCompactlySupportedForms J M 1 := by
  obtain ⟨g, hg0, hg⟩ := h.exists_fluxForm_eq_mextDerivₗ
  rw [exactCompactlySupportedForms_succ, hg]
  exact Submodule.mem_map_of_mem ((mem_compactlySupportedForms J).mpr
    (HasCompactSupport.intro hK fun x hx ↦ hg0 x (hFK x hx)))

/-- **Compactly supported Hamiltonian diffeotopies have zero compactly supported flux.** If `φ_t`
has a Hamiltonian, read along the motion, which vanishes at every time outside a compact set,
then its compactly supported flux vanishes. -/
theorem HasHamiltonian.compactFlux_eq_zero [R1Space M] {σ : closedForms J M 2}
    {F : M × unitInterval → ℝ} (h : Φ.HasHamiltonian σ.val F) {K : Set M} (hK : IsCompact K)
    (hFK : ∀ x ∉ K, ∀ t, F (x, t) = 0)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hc : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1) : Φ.compactFlux σ hΦ hc = 0 := by
  rw [compactFlux_def, compactlySupportedDeRhamCohomology.mk_eq_zero_iff]
  exact h.fluxForm_mem_exactCompactlySupportedForms hK hFK

end Hamiltonian

/-! ### Every compactly supported class is a compactly supported flux -/

section Flow

variable [FiniteDimensional ℝ E] [J.Boundaryless] [T2Space M]

/-- **Every compactly supported first de Rham class is a compactly supported flux.** On a
Hausdorff boundaryless finite-dimensional manifold with a closed nondegenerate two-form `σ`, every
class in `H¹_c(M)` is the compactly supported flux of a diffeotopy all of whose maps preserve `σ`
and which is the identity outside a compact set: the time-one flow of the symplectic vector field
`(σ♭)⁻¹ α`, for a compactly supported closed representative `α` of the class, which vanishes
outside the support of `α`. -/
theorem exists_compactFlux_eq (σ : closedForms J M 2)
    (hσ : SmoothTwoForm.IsNondegenerate σ.val) (c : compactlySupportedDeRhamCohomology J M 1) :
    ∃ (Φ : Diffeotopy J ∞ M) (K : Set M) (hK : IsCompact K)
      (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ)
      (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val),
      Φ.compactFlux σ (SmoothForm.final_mem_diffeomorphStabilizer hΦ)
        (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK) = c := by
  obtain ⟨α, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective J 1 c
  obtain ⟨hαc, hαcl⟩ := (mem_compactlySupportedClosedForms J).mp α.property
  set K := _root_.tsupport (α := E [⋀^Fin 1]→L[ℝ] ℝ) α.val.val
  have hK : IsCompact K := (mem_compactlySupportedForms J).mp hαc
  -- The vector field `X = (σ♭)⁻¹ α` contracts to `α` and vanishes outside the support of `α`.
  set X := hσ.interiorEquiv.symm α.val
  have hX : X ∈ SmoothTwoForm.symplecticVectorFields σ.val := by
    rw [SmoothTwoForm.mem_symplecticVectorFields_iff, hσ.interior_interiorEquiv_symm]
    exact (mem_closedForms J _).mp hαcl
  have hXK (x : M) (hx : x ∉ K) : X x = 0 :=
    (hσ.interiorEquiv_symm_apply_eq_zero_iff α.val x).2 (image_eq_zero_of_notMem_tsupport hx)
  have hc : IsCompleteVectorField X :=
    isCompleteVectorField_of_isCompact_of_eq_zero_off (X.contMDiff.of_le (by simp)) hK hXK
  have hσc : SmoothForm.IsClosed σ.val :=
    (SmoothForm.isClosed_def _).2 ((mem_closedForms J σ.val).1 σ.property)
  have hΦ := compactlySupportedFlowDiffeotopy_eq_globalFlowDiffeotopy le_top X.contMDiff hK hXK hc 1
  refine ⟨compactlySupportedFlowDiffeotopy le_top X.contMDiff hK hXK 1, K, hK,
    compactlySupportedFlowDiffeotopy_eqOn_compl le_top X.contMDiff hK hXK 1,
    hΦ ▸ timeSlice_globalFlowDiffeotopy_mem_diffeomorphStabilizer hσc hX hc 1, ?_⟩
  rw [compactFlux_def]
  congr 1
  exact Subtype.ext ((hΦ ▸ fluxForm_globalFlowDiffeotopy hX hc 1).trans
    ((one_smul ℝ _).trans (hσ.interiorₗ_interiorEquiv_symm α.val)))

end Flow

end Diffeotopy

end TauCeti
