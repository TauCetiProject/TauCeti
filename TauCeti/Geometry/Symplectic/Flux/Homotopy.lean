/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Flux
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator.Homotopy

/-!
# Homotopy invariance of the flux

Let `σ` be a closed two-form on a manifold `M` and let `φ_t` and `ψ_t`, `t ∈ [0, 1]`, be smooth
diffeotopies of `M`. Suppose they are joined by a smooth homotopy fixing both time ends: a smooth
map `G : (M × [0, 1]) × [0, 1] → M` with

* `G ((x, t), 0) = φ_t x` and `G ((x, t), 1) = ψ_t x`,
* `G ((x, 0), s) = x` and `G ((x, 1), s) = φ₁ x` for every `s`.

In particular `φ₁ = ψ₁`. The intermediate maps `G (·, s)` need not be diffeomorphisms, and none
of the maps involved needs to preserve `σ`. Then the flux forms of `φ` and `ψ` differ by an exact
form (`TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`), so when `φ₁` preserves `σ` the
two diffeotopies have the same flux (`TauCeti.Diffeotopy.flux_eq_of_homotopy`):

`Flux(φ) = Flux(ψ)` in `H¹_dR(M)`.

Thus the flux of a symplectic isotopy only depends on its class modulo smooth homotopies fixing
both time ends. In particular a loop of diffeomorphisms based at the identity which is
homotopic, with both time ends fixed, to the constant loop has zero flux
(`TauCeti.Diffeotopy.flux_eq_zero_of_homotopy`).

Both flux forms are homotopy operators of pullbacks of `σ` to the cylinder `M × [0, 1]`, so this
is the homotopy invariance of the homotopy operator along homotopies of cylinder maps that are
stationary at both time ends (`TauCeti.mextDeriv_homotopyOperator_homotopyOperator_mpullback`),
which moreover names the primitive `h (h (G^* σ))` of the difference.

## Main results

* `TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`: diffeotopies joined by a smooth
  homotopy fixing both time ends have flux forms differing by an exact form.
* `TauCeti.Diffeotopy.flux_eq_of_homotopy`: such diffeotopies have the same flux.
* `TauCeti.Diffeotopy.flux_eq_zero_of_homotopy`: a diffeotopy homotopic, with both time ends
  fixed, to the constant diffeotopy has zero flux.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism on the universal cover of the
  identity component of the symplectomorphism group).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] (Φ Ψ : Diffeotopy J ∞ M)

/-- **Homotopy invariance of the flux form.** Let `G` be a smooth homotopy from the motion of a
diffeotopy `φ` to the motion of a diffeotopy `ψ` which fixes both time ends: `G ((x, 0), s) = x`
and `G ((x, 1), s) = φ₁ x` for every `s`. For a closed two-form `σ`, the flux forms of `φ` and
`ψ` differ by an exact form. Neither the maps `G (·, s)` nor the diffeomorphisms of `φ` and `ψ`
need to preserve `σ`. -/
theorem fluxForm_sub_fluxForm_mem_exactForms {σ : SmoothForm J M ℝ 2} (hσ : σ.IsClosed)
    {G : (M × unitInterval) × unitInterval → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hGΦ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hGΨ : ∀ p, G (p, 1) = Ψ.cylinderMap p)
    (hG₀ : ∀ x s, G ((x, 0), s) = x) (hG₁ : ∀ x s, G ((x, 1), s) = Φ.final x) :
    Φ.fluxForm σ - Ψ.fluxForm σ ∈ exactForms J M 1 := by
  have : IsManifold (J.prod (𝓡∂ 1)) ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) (M × unitInterval) :=
    IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold J 2 M := IsManifold.of_le (n := ∞) (by simp)
  have key := mextDeriv_homotopyOperator_homotopyOperator_mpullback
    (σ.isSmoothForm.of_le (by simp)) ((SmoothForm.isClosed_def _).mp hσ) (hG.of_le (by simp))
    (fun x s ↦ (hG₀ x s).trans (hG₀ x 0).symm) (fun x s ↦ (hG₁ x s).trans (hG₁ x 0).symm)
  rw [show (fun p ↦ G (p, 0)) = Φ.cylinderMap from funext hGΦ,
    show (fun p ↦ G (p, 1)) = Ψ.cylinderMap from funext hGΨ, ← SmoothForm.coe_mpullback G hG,
    ← SmoothForm.coe_mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap,
    ← SmoothForm.coe_mpullback Ψ.cylinderMap Ψ.contMDiff_cylinderMap, ← coe_fluxForm,
    ← coe_fluxForm, ← Submodule.coe_sub] at key
  -- The primitive is the iterated homotopy operator `h_t (h_s (G^* σ))`.
  rw [exactForms_succ]
  refine ⟨⟨homotopyOperator (homotopyOperator (SmoothForm.mpullback G hG σ).1),
    (IsSmoothForm.homotopyOperator (IsSmoothForm.homotopyOperator
      (SmoothForm.mpullback G hG σ).isSmoothForm)).mem_smoothBundleForms⟩, Subtype.ext ?_⟩
  rw [mextDerivₗ_apply]
  exact key

/-- **Homotopy invariance of the flux.** Two diffeotopies joined by a smooth homotopy of their
motions fixing both time ends have the same flux, for a closed two-form `σ` preserved by their
common final diffeomorphism. -/
theorem flux_eq_of_homotopy (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    {G : (M × unitInterval) × unitInterval → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hGΦ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hGΨ : ∀ p, G (p, 1) = Ψ.cylinderMap p)
    (hG₀ : ∀ x s, G ((x, 0), s) = x) (hG₁ : ∀ x s, G ((x, 1), s) = Φ.final x) :
    Φ.flux σ hΦ = Ψ.flux σ hΨ := by
  rw [flux_def, flux_def, ← sub_eq_zero, ← map_sub, deRhamCohomology.mk_eq_zero_iff]
  exact Φ.fluxForm_sub_fluxForm_mem_exactForms Ψ
    ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.1).mp σ.2)) hG hGΦ hGΨ hG₀ hG₁

/-- **Contractible loops have zero flux.** A diffeotopy whose motion is joined to the constant
motion by a smooth homotopy fixing both time ends has zero flux, for a closed two-form `σ`. Its
final diffeomorphism is then the identity. -/
theorem flux_eq_zero_of_homotopy (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    {G : (M × unitInterval) × unitInterval → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hGΦ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hGrefl : ∀ p, G (p, 1) = p.1)
    (hG₀ : ∀ x s, G ((x, 0), s) = x) (hG₁ : ∀ x s, G ((x, 1), s) = x) :
    Φ.flux σ hΦ = 0 := by
  have hfinal : Φ.final = (refl J ∞ M).final := by
    ext x
    rw [final_refl, Diffeomorph.coe_refl, id_eq, final_apply, ← cylinderMap_apply (p := (x, 1)),
      ← hGΦ, hG₁]
  have hrefl : (refl J ∞ M).final ∈ SmoothForm.diffeomorphStabilizer σ.1 := hfinal ▸ hΦ
  rw [Φ.flux_eq_of_homotopy (refl J ∞ M) σ hΦ hrefl hG hGΦ (fun p ↦ by simp [hGrefl]) hG₀
    (fun x s ↦ by rw [hG₁, hfinal, final_refl, Diffeomorph.coe_refl, id_eq]), flux_refl]

end Diffeotopy

end TauCeti
