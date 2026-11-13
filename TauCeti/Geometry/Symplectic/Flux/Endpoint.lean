/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer
public import TauCeti.Geometry.Symplectic.Flux.Flow
public import TauCeti.Geometry.Symplectic.Flux.Trans

/-!
# The flux group and the endpoint flux homomorphism

Let `σ` be a closed two-form on a manifold `M`, for instance a symplectic form, and let
`G_σ = TauCeti.SmoothForm.isotopyStabilizer σ` be the group of final diffeomorphisms `φ₁` of the
smooth diffeotopies `φ_t` all of whose time slices preserve `σ`. The flux `Flux(φ) ∈ H¹_dR(M)` of
such a diffeotopy (`TauCeti.Diffeotopy.flux`) depends on the whole path `φ_t` and not only on its
endpoint. This file measures that dependence and removes it.

The **flux group** `Γ_σ ⊆ H¹_dR(M)` (`TauCeti.fluxGroup σ`) is the set of fluxes of `σ`-preserving
loops, the diffeotopies preserving `σ` at every time whose final diffeomorphism is the identity. It
is an additive subgroup because the flux is additive on pointwise composites and changes sign under
pointwise inversion (`TauCeti.Diffeotopy.flux_trans`, `TauCeti.Diffeotopy.flux_symm`). Two
`σ`-preserving diffeotopies `φ_t` and `ψ_t` with the same endpoint differ by the loop
`φ_t ∘ ψ_t⁻¹`, so their fluxes differ by an element of `Γ_σ`
(`TauCeti.flux_sub_flux_mem_fluxGroup`). Hence the flux of a path descends to a group homomorphism

`TauCeti.endpointFlux σ : G_σ → H¹_dR(M) / Γ_σ`,

written multiplicatively, which sends `φ₁` to the class of the flux of any `σ`-preserving
diffeotopy ending at `φ₁` (`TauCeti.endpointFlux_apply`). Its kernel consists of the endpoints of
the `σ`-preserving diffeotopies with zero flux (`TauCeti.mem_ker_endpointFlux_iff`). On a compact
Hausdorff boundaryless finite-dimensional manifold with a symplectic form it is surjective
(`TauCeti.endpointFlux_surjective`): every class of `H¹_dR(M)` is the flux of the time-one flow of
a symplectic vector field.

Both constructions are natural under the diffeomorphisms `f` preserving `σ`. Conjugating a
`σ`-preserving diffeotopy by such an `f` transports its flux by `(f⁻¹)^*`, so `Γ_σ` is invariant
under `(f⁻¹)^*` (`TauCeti.map_symm_mem_fluxGroup`). Hence `(f⁻¹)^*` descends to
`H¹_dR(M) / Γ_σ`, and the endpoint flux of `f φ f⁻¹` is the image of the endpoint flux of `φ`
(`TauCeti.endpointFlux_mul_mul_inv`). For an exact form the flux depends only on the endpoint, so
`Γ_σ = 0` (`TauCeti.fluxGroup_eq_bot_of_mem_exactForms`).

The diffeotopies here are those of `TauCeti.Diffeotopy`. They are not required to be constant near
the ends of the time interval, and `G_σ` is defined by smooth isotopies, without reference to a
topology on the diffeomorphism group.

## Main definitions

* `TauCeti.fluxGroup σ`: the fluxes of `σ`-preserving loops, an additive subgroup of
  `H¹_dR(M)`.
* `TauCeti.endpointFlux σ`: the homomorphism `G_σ → H¹_dR(M) / Γ_σ` induced by the flux.

## Main results

* `TauCeti.flux_sub_flux_mem_fluxGroup`: the fluxes of two `σ`-preserving diffeotopies with the
  same endpoint differ by an element of the flux group.
* `TauCeti.endpointFlux_apply`: the endpoint flux of `φ₁` is the class of the flux of any
  `σ`-preserving diffeotopy ending at `φ₁`.
* `TauCeti.mem_ker_endpointFlux_iff`: its kernel consists of the endpoints of `σ`-preserving
  diffeotopies with zero flux.
* `TauCeti.endpointFlux_surjective`: on a compact Hausdorff boundaryless finite-dimensional
  symplectic manifold it is surjective.
* `TauCeti.map_symm_mem_fluxGroup`, `TauCeti.endpointFlux_mul_mul_inv`: naturality under
  diffeomorphisms preserving `σ`.
* `TauCeti.fluxGroup_eq_bot_of_mem_exactForms`: the flux group of an exact form is trivial.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux group and the flux homomorphism).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

open SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]

variable (σ : closedForms J M 2)

/-! ### The flux group -/

/-- The **flux group** `Γ_σ ⊆ H¹_dR(M)` of a closed two-form `σ`: the fluxes of the diffeotopies
preserving `σ` at every time whose final diffeomorphism is the identity. -/
def fluxGroup : AddSubgroup (deRhamCohomology J M 1) where
  carrier := {c | ∃ (Φ : Diffeotopy J ∞ M) (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.1),
    Φ.final = 1 ∧ Φ.flux σ (final_mem_diffeomorphStabilizer hΦ) = c}
  zero_mem' := ⟨Diffeotopy.refl J ∞ M, timeSlice_refl_mem_diffeomorphStabilizer,
    Diffeotopy.final_refl, Diffeotopy.flux_refl σ _⟩
  add_mem' := by
    rintro _ _ ⟨Φ, hΦ, hΦ₁, rfl⟩ ⟨Ψ, hΨ, hΨ₁, rfl⟩
    refine ⟨Φ.trans Ψ, timeSlice_trans_mem_diffeomorphStabilizer hΦ hΨ, ?_, ?_⟩
    · rw [Diffeotopy.final_trans, hΦ₁, hΨ₁, ← Diffeomorph.mul_def, mul_one]
    · rw [Diffeotopy.flux_trans Φ Ψ σ (final_mem_diffeomorphStabilizer hΦ)
        (final_mem_diffeomorphStabilizer hΨ), add_comm]
  neg_mem' := by
    rintro _ ⟨Φ, hΦ, hΦ₁, rfl⟩
    refine ⟨Φ.symm, timeSlice_symm_mem_diffeomorphStabilizer hΦ, ?_, ?_⟩
    · rw [Diffeotopy.final_symm, hΦ₁, ← Diffeomorph.inv_def, inv_one]
    · exact Diffeotopy.flux_symm Φ σ (final_mem_diffeomorphStabilizer hΦ) _

variable {σ}

/-- A class lies in the flux group exactly when it is the flux of a diffeotopy preserving `σ` at
every time whose final diffeomorphism is the identity. -/
theorem mem_fluxGroup {c : deRhamCohomology J M 1} :
    c ∈ fluxGroup σ ↔
      ∃ (Φ : Diffeotopy J ∞ M) (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.1),
        Φ.final = 1 ∧ Φ.flux σ (final_mem_diffeomorphStabilizer hΦ) = c :=
  Iff.rfl

/-- The flux of a loop preserving `σ` at every time lies in the flux group. -/
theorem flux_mem_fluxGroup {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.1) (h : Φ.final = 1) :
    Φ.flux σ (final_mem_diffeomorphStabilizer hΦ) ∈ fluxGroup σ :=
  ⟨Φ, hΦ, h, rfl⟩

/-- **Independence of the path up to the flux group.** Two diffeotopies preserving `σ` at every
time and having the same final diffeomorphism have fluxes differing by an element of the flux
group: their difference is the flux of the loop `φ_t ∘ ψ_t⁻¹`. -/
theorem flux_sub_flux_mem_fluxGroup {Φ Ψ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.1)
    (hΨ : ∀ t, Ψ.timeSlice t ∈ diffeomorphStabilizer σ.1) (h : Φ.final = Ψ.final) :
    Φ.flux σ (final_mem_diffeomorphStabilizer hΦ) - Ψ.flux σ (final_mem_diffeomorphStabilizer hΨ) ∈
      fluxGroup σ := by
  refine ⟨Ψ.symm.trans Φ, timeSlice_trans_mem_diffeomorphStabilizer
    (timeSlice_symm_mem_diffeomorphStabilizer hΨ) hΦ, ?_, ?_⟩
  · rw [Diffeotopy.final_symm_trans, h, mul_inv_cancel]
  · exact Φ.flux_symm_trans Ψ σ _ _ _

/-- **Naturality of the flux group.** For a diffeomorphism `f` preserving `σ`, the pullback along
`f⁻¹` maps the flux group into itself: it transports the flux of a loop `φ_t` to the flux of the
loop `f ∘ φ_t ∘ f⁻¹`. -/
theorem map_symm_mem_fluxGroup {f : M ≃ₘ⟮J, J⟯ M} (hf : f ∈ diffeomorphStabilizer σ.1)
    {c : deRhamCohomology J M 1} (hc : c ∈ fluxGroup σ) :
    deRhamCohomology.map f.symm f.symm.contMDiff 1 c ∈ fluxGroup σ := by
  obtain ⟨Φ, hΦ, hΦ₁, rfl⟩ := hc
  refine ⟨Φ.transDiffeomorph f, timeSlice_transDiffeomorph_mem_diffeomorphStabilizer hf hΦ, ?_,
    ?_⟩
  · rw [Diffeotopy.final_transDiffeomorph_eq_mul_mul_inv, hΦ₁, mul_one, mul_inv_cancel]
  · exact Φ.flux_transDiffeomorph_of_mem_diffeomorphStabilizer hf _ _

/-- **The flux group of an exact form is trivial.** For `σ = dθ` the flux of a diffeotopy is the
class of `φ₁^* θ - θ`, which vanishes for a loop. -/
theorem fluxGroup_eq_bot_of_mem_exactForms (hσ : σ.1 ∈ exactForms J M 2) : fluxGroup σ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 ?_
  rintro _ ⟨Φ, hΦ, hΦ₁, rfl⟩
  exact Φ.flux_eq_zero_of_final_eq_refl σ hσ hΦ₁ _

/-! ### The endpoint flux -/

variable (σ) in
/-- The class of the flux of the chosen `σ`-preserving diffeotopy ending at `φ`. It does not depend
on the choice (`endpointFluxFun_eq`). -/
private def endpointFluxFun (φ : isotopyStabilizer σ.1) : deRhamCohomology J M 1 ⧸ fluxGroup σ :=
  (mem_isotopyStabilizer.1 φ.2).choose.flux σ
    (final_mem_diffeomorphStabilizer (mem_isotopyStabilizer.1 φ.2).choose_spec.1)

/-- The class of the flux of any `σ`-preserving diffeotopy ending at `φ` is the class of the flux
of the chosen one. -/
private theorem endpointFluxFun_eq (φ : isotopyStabilizer σ.1) {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.1) (h : Φ.final = φ) :
    endpointFluxFun σ φ = (Φ.flux σ (final_mem_diffeomorphStabilizer hΦ) :
      deRhamCohomology J M 1 ⧸ fluxGroup σ) := by
  have hφ := (mem_isotopyStabilizer.1 φ.2).choose_spec
  exact QuotientAddGroup.eq_iff_sub_mem.2 (flux_sub_flux_mem_fluxGroup hφ.1 hΦ (hφ.2.trans h.symm))

variable (σ) in
/-- The **endpoint flux** of a closed two-form `σ`: the homomorphism from the group of final
diffeomorphisms of diffeotopies preserving `σ` at every time to `H¹_dR(M) / Γ_σ`, written
multiplicatively, which sends `φ₁` to the class of the flux of any `σ`-preserving diffeotopy
ending at `φ₁` (`TauCeti.endpointFlux_apply`). -/
def endpointFlux :
    isotopyStabilizer σ.1 →* Multiplicative (deRhamCohomology J M 1 ⧸ fluxGroup σ) where
  toFun φ := Multiplicative.ofAdd (endpointFluxFun σ φ)
  map_one' := by
    rw [endpointFluxFun_eq 1 timeSlice_refl_mem_diffeomorphStabilizer (by
      rw [Diffeotopy.final_refl, OneMemClass.coe_one, Diffeomorph.one_def]),
      Diffeotopy.flux_refl, QuotientAddGroup.mk_zero, ofAdd_zero]
  map_mul' φ ψ := by
    obtain ⟨Φ, hΦ, hΦ₁⟩ := mem_isotopyStabilizer.1 φ.2
    obtain ⟨Ψ, hΨ, hΨ₁⟩ := mem_isotopyStabilizer.1 ψ.2
    rw [endpointFluxFun_eq (φ * ψ) (timeSlice_trans_mem_diffeomorphStabilizer hΨ hΦ) (by
      rw [Diffeotopy.final_trans, hΦ₁, hΨ₁, ← Diffeomorph.mul_def, MulMemClass.coe_mul]),
      endpointFluxFun_eq φ hΦ hΦ₁, endpointFluxFun_eq ψ hΨ hΨ₁, Diffeotopy.flux_trans Ψ Φ σ
      (final_mem_diffeomorphStabilizer hΨ) (final_mem_diffeomorphStabilizer hΦ),
      QuotientAddGroup.mk_add, ofAdd_add, mul_comm]

/-- **The endpoint flux is the flux of any path.** For a diffeotopy `φ_t` preserving `σ` at every
time and ending at `φ`, the endpoint flux of `φ` is the class of the flux of `φ_t` modulo the
flux group. -/
theorem endpointFlux_apply (φ : isotopyStabilizer σ.1) {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.1) (h : Φ.final = φ) :
    endpointFlux σ φ =
      Multiplicative.ofAdd (Φ.flux σ (final_mem_diffeomorphStabilizer hΦ) :
        deRhamCohomology J M 1 ⧸ fluxGroup σ) :=
  congrArg Multiplicative.ofAdd (endpointFluxFun_eq φ hΦ h)

/-- **The kernel of the endpoint flux.** An element of the isotopy stabilizer of `σ` has trivial
endpoint flux exactly when it is the final diffeomorphism of a diffeotopy preserving `σ` at every
time with zero flux. -/
theorem mem_ker_endpointFlux_iff {φ : isotopyStabilizer σ.1} :
    φ ∈ (endpointFlux σ).ker ↔
      ∃ (Φ : Diffeotopy J ∞ M) (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.1),
        Φ.final = φ ∧ Φ.flux σ (final_mem_diffeomorphStabilizer hΦ) = 0 := by
  constructor
  · intro hker
    obtain ⟨Φ, hΦ, hfin⟩ := mem_isotopyStabilizer.1 φ.2
    rw [MonoidHom.mem_ker, endpointFlux_apply φ hΦ hfin, ofAdd_eq_one,
      QuotientAddGroup.eq_zero_iff] at hker
    obtain ⟨L, hL, hL₁, hLΦ⟩ := hker
    -- Removing the loop `L` from `Φ` gives a path to `φ` with zero flux.
    refine ⟨L.symm.trans Φ, timeSlice_trans_mem_diffeomorphStabilizer
      (timeSlice_symm_mem_diffeomorphStabilizer hL) hΦ, ?_, ?_⟩
    · rw [Diffeotopy.final_symm_trans, hL₁, inv_one, mul_one, hfin]
    · rw [Φ.flux_symm_trans L σ (final_mem_diffeomorphStabilizer hΦ)
        (final_mem_diffeomorphStabilizer hL), hLΦ, sub_self]
  · rintro ⟨Φ, hΦ, hfin, h₀⟩
    rw [MonoidHom.mem_ker, endpointFlux_apply φ hΦ hfin, h₀, QuotientAddGroup.mk_zero, ofAdd_zero]

/-- **Naturality of the endpoint flux.** For a diffeomorphism `f` preserving `σ`, the endpoint
flux of `f φ f⁻¹` is the image of the endpoint flux of `φ` under the map induced on
`H¹_dR(M) / Γ_σ` by the pullback along `f⁻¹` (`TauCeti.map_symm_mem_fluxGroup`). -/
theorem endpointFlux_mul_mul_inv {f : M ≃ₘ⟮J, J⟯ M} (hf : f ∈ diffeomorphStabilizer σ.1)
    (φ : isotopyStabilizer σ.1) :
    endpointFlux σ ⟨f * φ * f⁻¹, mul_mul_inv_mem_isotopyStabilizer hf φ.2⟩ =
      Multiplicative.ofAdd (QuotientAddGroup.map (fluxGroup σ) (fluxGroup σ)
        (deRhamCohomology.map f.symm f.symm.contMDiff 1).toAddMonoidHom
        (fun _ hc ↦ map_symm_mem_fluxGroup hf hc) (Multiplicative.toAdd (endpointFlux σ φ))) := by
  obtain ⟨Φ, hΦ, h⟩ := mem_isotopyStabilizer.1 φ.2
  rw [endpointFlux_apply φ hΦ h, endpointFlux_apply _
      (timeSlice_transDiffeomorph_mem_diffeomorphStabilizer hf hΦ) (by
      rw [Diffeotopy.final_transDiffeomorph_eq_mul_mul_inv, h]),
    Φ.flux_transDiffeomorph_of_mem_diffeomorphStabilizer hf (final_mem_diffeomorphStabilizer hΦ),
    toAdd_ofAdd]
  -- The coercion of `g.toAddMonoidHom` is `g` (`LinearMap.toAddMonoidHom_coe`).
  exact congrArg Multiplicative.ofAdd (QuotientAddGroup.map_mk (fluxGroup σ) (fluxGroup σ)
    (deRhamCohomology.map f.symm f.symm.contMDiff 1).toAddMonoidHom _ _).symm

/-- **Surjectivity of the endpoint flux.** On a compact Hausdorff boundaryless finite-dimensional
manifold with a symplectic form `σ`, the endpoint flux `G_σ → H¹_dR(M) / Γ_σ` is surjective. -/
theorem endpointFlux_surjective [FiniteDimensional ℝ E] [J.Boundaryless] [T2Space M]
    [CompactSpace M] (hσ : SmoothTwoForm.IsNondegenerate σ.1) :
    Function.Surjective (endpointFlux σ) := by
  intro c
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd c)
  obtain ⟨Φ, hfin, hΦ, hΦa⟩ := Diffeotopy.exists_flux_eq σ hσ a
  refine ⟨⟨Φ.final, final_mem_isotopyStabilizer hΦ⟩, (endpointFlux_apply _ hΦ rfl).trans ?_⟩
  rw [hΦa, ha, ofAdd_toAdd]

end TauCeti
