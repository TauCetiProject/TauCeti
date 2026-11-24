/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Reparam
public import TauCeti.Geometry.Symplectic.Flux.Trans

/-!
# The flux of concatenated and reversed diffeotopies

Let `σ` be a closed two-form on a manifold `M`. The flux `Flux(φ) ∈ H¹_dR(M)` of a smooth
diffeotopy `φ_t` whose final diffeomorphism preserves `σ` (`TauCeti.Diffeotopy.flux`) depends
only on the homotopy class of `φ` relative to both time ends
(`TauCeti.Diffeotopy.Homotopic.flux_eq`). Combined with the path-class laws of the temporal
operations of `TauCeti.Geometry.Diffeomorphism.Diffeotopy.Reparam`, this gives their flux laws:

* a reparametrization fixing both ends of the interval has the same flux
  (`TauCeti.Diffeotopy.flux_reparam`);
* the concatenation of `φ` and `ψ` has flux `Flux(φ) + Flux(ψ)`
  (`TauCeti.Diffeotopy.flux_concat`), because it is homotopic to the pointwise composite
  `ψ_t ∘ φ_t`, whose flux is the sum by `TauCeti.Diffeotopy.flux_trans`;
* the time reversal `φ_{1 - t} ∘ φ₁⁻¹` has flux `-Flux(φ)` (`TauCeti.Diffeotopy.flux_reverse`),
  because it is homotopic to the pointwise inverse `φ_t⁻¹`, whose flux is the negative by
  `TauCeti.Diffeotopy.flux_symm`.

As for `TauCeti.Diffeotopy.flux_trans`, only the final diffeomorphisms are required to preserve
`σ`, and `σ` need not be nondegenerate.

## Main results

* `TauCeti.Diffeotopy.flux_reparam`: the flux is invariant under reparametrizations fixing both
  ends.
* `TauCeti.Diffeotopy.flux_concat`: the flux is additive on concatenations.
* `TauCeti.Diffeotopy.flux_reverse`: time reversal negates the flux.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] (Φ Ψ : Diffeotopy J ∞ M) (σ : closedForms J M 2)

/-- **Reparametrization invariance of the flux.** Reparametrizing a diffeotopy by a smooth map of
the unit interval fixing both of its ends does not change the flux. -/
theorem flux_reparam {ρ : C^∞⟮𝓡∂ 1, unitInterval; 𝓡∂ 1, unitInterval⟯} (h₀ : ρ 0 = 0)
    (h₁ : ρ 1 = 1) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : (Φ.reparam ρ).final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    (Φ.reparam ρ).flux σ h = Φ.flux σ hΦ :=
  (Φ.reparam_homotopic h₀ h₁).flux_eq σ h hΦ

/-- **The flux of a concatenation** is the sum of the fluxes: running through `φ` and then through
`ψ` after `φ₁` has flux `Flux(φ) + Flux(ψ)`. -/
theorem flux_concat (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : (Φ.concat Ψ le_rfl).final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    (Φ.concat Ψ le_rfl).flux σ h = Φ.flux σ hΦ + Ψ.flux σ hΨ := by
  have hhom := Φ.concat_homotopic_trans Ψ le_rfl
  have htrans : (Φ.trans Ψ).final ∈ SmoothForm.diffeomorphStabilizer σ.val := hhom.final_eq ▸ h
  rw [hhom.flux_eq σ h htrans, flux_trans Φ Ψ σ hΦ hΨ htrans, add_comm]

/-- **The flux of a time reversal** is the negated flux: `φ_{1 - t} ∘ φ₁⁻¹` has flux
`-Flux(φ)`. -/
theorem flux_reverse (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : Φ.reverse.final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    Φ.reverse.flux σ h = -Φ.flux σ hΦ := by
  have hhom := Φ.reverse_homotopic_symm
  have hsymm : Φ.symm.final ∈ SmoothForm.diffeomorphStabilizer σ.val := hhom.final_eq ▸ h
  rw [hhom.flux_eq σ h hsymm, flux_symm Φ σ hΦ hsymm]

end Diffeotopy

end TauCeti
