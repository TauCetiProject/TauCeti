/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Prod
public import TauCeti.Geometry.Symplectic.Flux.Endpoint
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
public import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# The flux of a product of diffeotopies

Let `φ_t` be a diffeotopy of `M` and `ψ_t` a diffeotopy of `N`, and give `M × N` the product form
`σ ⊞ τ = pr₁^* σ + pr₂^* τ` of two-forms `σ` on `M` and `τ` on `N`
(`TauCeti.SmoothTwoForm.prod`). The product diffeotopy `(φ × ψ)_t = φ_t × ψ_t`
(`TauCeti.Diffeotopy.prodCongr`) has flux form

`Flux(φ × ψ) = pr₁^* Flux(φ) + pr₂^* Flux(ψ)`

(`TauCeti.Diffeotopy.fluxForm_prodCongr`), and hence, when the final diffeomorphisms preserve
`σ` and `τ`, flux `pr₁^* Flux(φ) + pr₂^* Flux(ψ)` in `H¹_dR(M × N)`
(`TauCeti.Diffeotopy.flux_prodCongr`). Both follow from the naturality of the flux under the
projections, which intertwine the product diffeotopy with its factors
(`TauCeti.Diffeotopy.flux_mpullback_of_semiconj`), and from additivity of the flux form in the
two-form.

The same argument applies to Hamiltonians: if `F` and `G` are Hamiltonians of `φ_t` and `ψ_t`,
read along their motions, then `((x, y), t) ↦ F (x, t) + G (y, t)` is a Hamiltonian of
`φ_t × ψ_t` (`TauCeti.Diffeotopy.HasHamiltonian.prodCongr`). Consequently products of Hamiltonian
diffeotopies are Hamiltonian, the product of Hamiltonian diffeomorphisms is Hamiltonian
(`TauCeti.SmoothForm.prodCongr_mem_hamiltonianGroup`), and the flux groups satisfy
`pr₁^* Γ_σ + pr₂^* Γ_τ ⊆ Γ_(σ ⊞ τ)` (`TauCeti.map_fst_add_map_snd_mem_fluxGroup`).

## Main results

* `TauCeti.Diffeotopy.fluxForm_prodCongr`: the flux form of a product diffeotopy.
* `TauCeti.Diffeotopy.flux_prodCongr`: the flux of a product diffeotopy.
* `TauCeti.Diffeotopy.HasHamiltonian.prodCongr`, `TauCeti.Diffeotopy.IsHamiltonian.prodCongr`:
  Hamiltonians of product diffeotopies.
* `TauCeti.map_fst_add_map_snd_mem_fluxGroup`: the flux groups of the factors pull back into the
  flux group of the product.
* `TauCeti.SmoothForm.prodCongr_mem_hamiltonianGroup`: products of Hamiltonian diffeomorphisms are
  Hamiltonian.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E H} {J' : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J' ∞ N]

namespace Diffeotopy

variable (Φ : Diffeotopy J ∞ M) (Ψ : Diffeotopy J' ∞ N)

/-! ### The flux of a product -/

/-- **The flux form of a product diffeotopy.** The flux form of `φ_t × ψ_t` for the product form
`σ ⊞ τ` is `pr₁^* Flux(φ) + pr₂^* Flux(ψ)`. -/
theorem fluxForm_prodCongr (σ : SmoothForm J M ℝ 2) (τ : SmoothForm J' N ℝ 2) :
    (Φ.prodCongr Ψ).fluxForm (SmoothTwoForm.prod σ τ) =
      SmoothForm.mpullback Prod.fst contMDiff_fst (Φ.fluxForm σ) +
        SmoothForm.mpullback Prod.snd contMDiff_snd (Ψ.fluxForm τ) := by
  rw [SmoothTwoForm.prod_def, fluxForm_add,
    Φ.fluxForm_mpullback_of_semiconj contMDiff_fst (Φ.semiconj_fst_timeSlice_prodCongr Ψ),
    Ψ.fluxForm_mpullback_of_semiconj contMDiff_snd (Φ.semiconj_snd_timeSlice_prodCongr Ψ)]

variable {Φ Ψ}

/-- **The flux of a product diffeotopy.** If the final diffeomorphisms of `φ_t` and `ψ_t` preserve
the closed forms `σ` and `τ`, the flux of `φ_t × ψ_t` for `σ ⊞ τ = pr₁^* σ + pr₂^* τ` is
`pr₁^* Flux(φ) + pr₂^* Flux(ψ)`. -/
theorem flux_prodCongr (σ : closedForms J M 2) (τ : closedForms J' N 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer τ.val)
    (h : (Φ.prodCongr Ψ).final ∈ SmoothForm.diffeomorphStabilizer
      (closedForms.mpullback Prod.fst contMDiff_fst 2 σ +
        closedForms.mpullback Prod.snd contMDiff_snd 2 τ).val) :
    (Φ.prodCongr Ψ).flux (closedForms.mpullback Prod.fst contMDiff_fst 2 σ +
        closedForms.mpullback Prod.snd contMDiff_snd 2 τ) h =
      deRhamCohomology.map Prod.fst contMDiff_fst 1 (Φ.flux σ hΦ) +
        deRhamCohomology.map Prod.snd contMDiff_snd 1 (Ψ.flux τ hΨ) := by
  rw [flux_def, flux_def, flux_def, deRhamCohomology.map_mk, deRhamCohomology.map_mk, ← map_add]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_add, closedForms.coe_mpullback]
  rw [← SmoothTwoForm.prod_def, fluxForm_prodCongr]

/-! ### Hamiltonians of a product -/

variable {σ : SmoothForm J M ℝ 2} {τ : SmoothForm J' N ℝ 2}
  {F : M × unitInterval → ℝ} {G : N × unitInterval → ℝ}

/-- **Hamiltonians of a product diffeotopy.** If `F` and `G` are Hamiltonians of `φ_t` and `ψ_t`
for `σ` and `τ`, read along their motions, then `((x, y), t) ↦ F (x, t) + G (y, t)` is a
Hamiltonian of `φ_t × ψ_t` for `σ ⊞ τ`. -/
theorem HasHamiltonian.prodCongr (hF : Φ.HasHamiltonian σ F) (hG : Ψ.HasHamiltonian τ G) :
    (Φ.prodCongr Ψ).HasHamiltonian (SmoothTwoForm.prod σ τ)
      (fun p ↦ F (p.1.1, p.2) + G (p.1.2, p.2)) := by
  rw [SmoothTwoForm.prod_def]
  exact (hF.mpullback_of_semiconj contMDiff_fst (Φ.semiconj_fst_timeSlice_prodCongr Ψ)).add
    (hG.mpullback_of_semiconj contMDiff_snd (Φ.semiconj_snd_timeSlice_prodCongr Ψ))

/-- The product of Hamiltonian diffeotopies of `σ` and `τ` is a Hamiltonian diffeotopy of
`σ ⊞ τ`. -/
theorem IsHamiltonian.prodCongr (hΦ : Φ.IsHamiltonian σ) (hΨ : Ψ.IsHamiltonian τ) :
    (Φ.prodCongr Ψ).IsHamiltonian (SmoothTwoForm.prod σ τ) := by
  obtain ⟨hΦσ, F, hF⟩ := isHamiltonian_iff.1 hΦ
  obtain ⟨hΨτ, G, hG⟩ := isHamiltonian_iff.1 hΨ
  refine isHamiltonian_iff.2 ⟨?_, _, hF.prodCongr hG⟩
  rw [SmoothTwoForm.prod_def]
  exact SmoothForm.timeSlice_prodCongr_mem_diffeomorphStabilizer hΦσ hΨτ

end Diffeotopy

/-- **Flux groups of products.** If `c` is the flux of a loop of `σ`-preserving diffeomorphisms of
`M` and `d` the flux of a loop of `τ`-preserving diffeomorphisms of `N`, then
`pr₁^* c + pr₂^* d` is the flux of a loop of `σ ⊞ τ`-preserving diffeomorphisms of `M × N`: the
product of the two loops. -/
theorem map_fst_add_map_snd_mem_fluxGroup {σ : closedForms J M 2} {τ : closedForms J' N 2}
    {c : deRhamCohomology J M 1} {d : deRhamCohomology J' N 1} (hc : c ∈ fluxGroup σ)
    (hd : d ∈ fluxGroup τ) :
    deRhamCohomology.map Prod.fst contMDiff_fst 1 c +
        deRhamCohomology.map Prod.snd contMDiff_snd 1 d ∈
      fluxGroup (closedForms.mpullback Prod.fst contMDiff_fst 2 σ +
        closedForms.mpullback Prod.snd contMDiff_snd 2 τ) := by
  obtain ⟨Φ, hΦ, hΦ₁, rfl⟩ := mem_fluxGroup.1 hc
  obtain ⟨Ψ, hΨ, hΨ₁, rfl⟩ := mem_fluxGroup.1 hd
  refine mem_fluxGroup.2 ⟨Φ.prodCongr Ψ, fun t ↦ ?_, ?_, Diffeotopy.flux_prodCongr σ τ _ _ _⟩
  · rw [Submodule.coe_add, closedForms.coe_mpullback, closedForms.coe_mpullback]
    exact SmoothForm.timeSlice_prodCongr_mem_diffeomorphStabilizer hΦ hΨ t
  · rw [Diffeotopy.final_prodCongr, hΦ₁, hΨ₁]
    exact Diffeomorph.ext fun _ ↦ by
      simp only [Diffeomorph.coe_prodCongr, Diffeomorph.coe_one, Prod.map_id, id_eq]

namespace SmoothForm

variable {σ : SmoothForm J M ℝ 2} {τ : SmoothForm J' N ℝ 2}

/-- **Products of Hamiltonian diffeomorphisms are Hamiltonian.** The product `f × f'` of a
Hamiltonian diffeomorphism `f` of `(M, σ)` and a Hamiltonian diffeomorphism `f'` of `(N, τ)` is a
Hamiltonian diffeomorphism of `(M × N, σ ⊞ τ)`. -/
theorem prodCongr_mem_hamiltonianGroup {f : M ≃ₘ⟮J, J⟯ M} {f' : N ≃ₘ⟮J', J'⟯ N}
    (hf : f ∈ hamiltonianGroup σ) (hf' : f' ∈ hamiltonianGroup τ) :
    f.prodCongr f' ∈ hamiltonianGroup (SmoothTwoForm.prod σ τ) := by
  obtain ⟨Φ, hΦ, rfl⟩ := mem_hamiltonianGroup.1 hf
  obtain ⟨Ψ, hΨ, rfl⟩ := mem_hamiltonianGroup.1 hf'
  exact mem_hamiltonianGroup.2 ⟨Φ.prodCongr Ψ, hΦ.prodCongr hΨ, Diffeotopy.final_prodCongr Φ Ψ⟩

end SmoothForm

end TauCeti
