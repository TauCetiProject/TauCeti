/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Flux.CompactSupport
public import TauCeti.Geometry.Symplectic.Flux.Endpoint

/-!
# The compactly supported flux group and endpoint flux

Let `σ` be a closed two-form on a manifold `M`, for instance a symplectic form on a noncompact
manifold, and let `G_(σ,c) = TauCeti.SmoothForm.compactIsotopyStabilizer σ` be the group of final
diffeomorphisms `φ₁` of the smooth diffeotopies `φ_t` all of whose time slices preserve `σ` and
which are the identity outside one common compact set; for a symplectic form this is
`Symp_(c,0)(M, ω)`. Such a diffeotopy has a compactly supported flux
`Flux_c(φ) ∈ H¹_c(M)` (`TauCeti.Diffeotopy.compactFlux`), additive on pointwise composites and
negated by pointwise inversion (`TauCeti.Diffeotopy.compactFlux_trans`,
`TauCeti.Diffeotopy.compactFlux_symm`). This file shows that, exactly as for the ordinary flux in
`TauCeti.Geometry.Symplectic.Flux.Endpoint`, it descends to a homomorphism on the endpoints:

`TauCeti.compactEndpointFlux σ : G_(σ,c) → H¹_c(M) / Γ_(σ,c)`.

* **The flux group.** The compactly supported fluxes of the compactly supported `σ`-preserving
  loops form an additive subgroup `Γ_(σ,c)` of `H¹_c(M)` (`TauCeti.compactFluxGroup σ`), and two
  compactly supported `σ`-preserving diffeotopies with the same endpoint have compactly supported
  fluxes differing by an element of it
  (`TauCeti.compactFlux_sub_compactFlux_mem_compactFluxGroup`).
* **The endpoint flux.** Hence the compactly supported flux of a path descends to the group
  homomorphism `TauCeti.compactEndpointFlux σ`, written multiplicatively
  (`TauCeti.compactEndpointFlux_apply`). Its kernel consists of the endpoints of the compactly
  supported `σ`-preserving diffeotopies with zero compactly supported flux
  (`TauCeti.mem_ker_compactEndpointFlux_iff`); it contains the endpoints of the compactly
  supported Hamiltonian isotopies (`TauCeti.mem_ker_compactEndpointFlux_of_hasHamiltonian`).
* **Surjectivity.** On a Hausdorff boundaryless finite-dimensional manifold with a symplectic form
  the homomorphism is surjective (`TauCeti.compactEndpointFlux_surjective`), with no compactness
  of `M`, since every class of `H¹_c(M)` is the compactly supported flux of the time-one flow of
  a compactly supported symplectic vector field (`TauCeti.Diffeotopy.exists_compactFlux_eq`).
* **Forgetting supports.** The comparison map `H¹_c(M) → H¹_dR(M)` sends `Γ_(σ,c)` into the flux
  group `Γ_σ` (`TauCeti.toDeRhamCohomology_mem_fluxGroup`), and the induced map on the quotients
  carries the compactly supported endpoint flux to the endpoint flux
  (`TauCeti.map_toAdd_compactEndpointFlux`).
* **Naturality.** For a diffeomorphism `f` preserving `σ`, conjugating a compactly supported
  `σ`-preserving diffeotopy by `f` transports its compactly supported flux by `(f⁻¹)^*`, so
  `Γ_(σ,c)` is invariant under `(f⁻¹)^*` (`TauCeti.map_symm_mem_compactFluxGroup`), and the
  compactly supported endpoint flux of `f φ f⁻¹` is the image of that of `φ`
  (`TauCeti.compactEndpointFlux_mul_mul_inv`).

For an exact form, the compactly supported flux depends only on the endpoint, so the flux group
is trivial (`TauCeti.compactFluxGroup_eq_bot_of_mem_exactForms`). The flux group need not be
trivial in general, and the compactly supported endpoint flux carries more information than the
ordinary one: on the cylinder `ℝ × AddCircle p` the compactly supported shears have zero ordinary
flux but nonzero compactly supported flux (`TauCeti.Geometry.Symplectic.Flux.Cylinder`).

## Main definitions

* `TauCeti.compactFluxGroup σ`: the compactly supported fluxes of compactly supported
  `σ`-preserving loops, an additive subgroup of `H¹_c(M)`.
* `TauCeti.compactEndpointFlux σ`: the homomorphism `G_(σ,c) → H¹_c(M) / Γ_(σ,c)` induced by the
  compactly supported flux.

## Main results

* `TauCeti.compactFlux_sub_compactFlux_mem_compactFluxGroup`: the compactly supported fluxes of
  two paths with the same endpoint differ by an element of `Γ_(σ,c)`.
* `TauCeti.compactEndpointFlux_apply`: the compactly supported endpoint flux of `φ₁` is the class
  of the compactly supported flux of any compactly supported `σ`-preserving diffeotopy ending at
  `φ₁`.
* `TauCeti.mem_ker_compactEndpointFlux_iff`: its kernel.
* `TauCeti.mem_ker_compactEndpointFlux_of_hasHamiltonian`: compactly supported Hamiltonian
  isotopies end in the kernel.
* `TauCeti.compactEndpointFlux_surjective`: surjectivity for a symplectic form.
* `TauCeti.map_toAdd_compactEndpointFlux`: compatibility with the endpoint flux.
* `TauCeti.map_symm_mem_compactFluxGroup`, `TauCeti.compactEndpointFlux_mul_mul_inv`: naturality
  under diffeomorphisms preserving `σ`.

## References

* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 4 (the flux homomorphism on compactly supported symplectomorphisms).
* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

open SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]

variable [T2Space M]

/-! ### The compactly supported flux group -/

variable (σ : closedForms J M 2)

/-- The **compactly supported flux group** `Γ_(σ,c) ⊆ H¹_c(M)` of a closed two-form `σ`: the
compactly supported fluxes of the diffeotopies preserving `σ` at every time which are the
identity outside a common compact set and whose final diffeomorphism is the identity. -/
def compactFluxGroup : AddSubgroup (compactlySupportedDeRhamCohomology J M 1) where
  carrier := {c | ∃ (Φ : Diffeotopy J ∞ M) (K : Set M) (hK : IsCompact K)
    (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ)
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val), Φ.final = 1 ∧
      Φ.compactFlux σ (final_mem_diffeomorphStabilizer hΦ)
        (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK) = c}
  zero_mem' := ⟨Diffeotopy.refl J ∞ M, ∅, isCompact_empty, fun _ _ _ ↦ by simp,
    timeSlice_refl_mem_diffeomorphStabilizer, Diffeotopy.final_refl,
    Diffeotopy.compactFlux_refl σ _ _⟩
  add_mem' := by
    rintro _ _ ⟨Φ, K, hK, hΦK, hΦ, hΦ₁, rfl⟩ ⟨Ψ, L, hL, hΨL, hΨ, hΨ₁, rfl⟩
    refine ⟨Φ.trans Ψ, K ∪ L, hK.union hL, Diffeotopy.eqOn_id_trans hΦK hΨL,
      timeSlice_trans_mem_diffeomorphStabilizer hΦ hΨ, ?_, ?_⟩
    · rw [Diffeotopy.final_trans, hΦ₁, hΨ₁, ← Diffeomorph.mul_def, mul_one]
    · rw [Diffeotopy.compactFlux_trans Φ Ψ σ (final_mem_diffeomorphStabilizer hΦ)
        (final_mem_diffeomorphStabilizer hΨ) _ _ _ _ hK hΦK, add_comm]
  neg_mem' := by
    rintro _ ⟨Φ, K, hK, hΦK, hΦ, hΦ₁, rfl⟩
    refine ⟨Φ.symm, K, hK, Diffeotopy.eqOn_id_symm hΦK,
      timeSlice_symm_mem_diffeomorphStabilizer hΦ, ?_, ?_⟩
    · rw [Diffeotopy.final_symm, hΦ₁, ← Diffeomorph.inv_def, inv_one]
    · exact Φ.compactFlux_symm σ (final_mem_diffeomorphStabilizer hΦ) _ _ _ hK hΦK

variable {σ}

/-- A class lies in the compactly supported flux group exactly when it is the compactly
supported flux of a diffeotopy preserving `σ` at every time, equal to the identity outside a
compact set, whose final diffeomorphism is the identity. -/
theorem mem_compactFluxGroup {c : compactlySupportedDeRhamCohomology J M 1} :
    c ∈ compactFluxGroup σ ↔
      ∃ (Φ : Diffeotopy J ∞ M) (K : Set M) (hK : IsCompact K)
        (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ)
        (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val), Φ.final = 1 ∧
          Φ.compactFlux σ (final_mem_diffeomorphStabilizer hΦ)
            (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK) = c :=
  Iff.rfl

/-- The compactly supported flux of a compactly supported loop preserving `σ` at every time lies
in the compactly supported flux group. -/
theorem compactFlux_mem_compactFluxGroup {Φ : Diffeotopy J ∞ M} {K : Set M} (hK : IsCompact K)
    (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ)
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val) (h : Φ.final = 1)
    (hc : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1) :
    Φ.compactFlux σ (final_mem_diffeomorphStabilizer hΦ) hc ∈ compactFluxGroup σ :=
  ⟨Φ, K, hK, hΦK, hΦ, h, rfl⟩

/-- **Independence of the path up to the compactly supported flux group.** Two compactly
supported diffeotopies preserving `σ` at every time and having the same final diffeomorphism have
compactly supported fluxes differing by an element of the compactly supported flux group: their
difference is the compactly supported flux of the loop `φ_t ∘ ψ_t⁻¹`. -/
theorem compactFlux_sub_compactFlux_mem_compactFluxGroup {Φ Ψ : Diffeotopy J ∞ M} {K L : Set M}
    (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) (hL : IsCompact L)
    (hΨL : ∀ t, EqOn (fun x ↦ Ψ (t, x)) id Lᶜ)
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val)
    (hΨ : ∀ t, Ψ.timeSlice t ∈ diffeomorphStabilizer σ.val) (h : Φ.final = Ψ.final)
    (hcΦ : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1)
    (hcΨ : Ψ.fluxForm σ.val ∈ compactlySupportedForms J M 1) :
    Φ.compactFlux σ (final_mem_diffeomorphStabilizer hΦ) hcΦ -
        Ψ.compactFlux σ (final_mem_diffeomorphStabilizer hΨ) hcΨ ∈ compactFluxGroup σ := by
  refine ⟨Ψ.symm.trans Φ, L ∪ K, hL.union hK,
    Diffeotopy.eqOn_id_trans (Diffeotopy.eqOn_id_symm hΨL) hΦK,
    timeSlice_trans_mem_diffeomorphStabilizer (timeSlice_symm_mem_diffeomorphStabilizer hΨ) hΦ,
    ?_, ?_⟩
  · rw [Diffeotopy.final_symm_trans, h, mul_inv_cancel]
  · exact Φ.compactFlux_symm_trans Ψ σ _ _ _ _ _ _ hL hΨL

/-- **Naturality of the compactly supported flux group.** For a diffeomorphism `f` preserving
`σ`, the pullback along `f⁻¹` maps the compactly supported flux group into itself: it transports
the compactly supported flux of a compactly supported loop `φ_t` to that of the compactly
supported loop `f ∘ φ_t ∘ f⁻¹`. -/
theorem map_symm_mem_compactFluxGroup {f : M ≃ₘ⟮J, J⟯ M} (hf : f ∈ diffeomorphStabilizer σ.val)
    {c : compactlySupportedDeRhamCohomology J M 1} (hc : c ∈ compactFluxGroup σ) :
    compactlySupportedDeRhamCohomology.equivOfDiffeomorph f.symm 1 c ∈ compactFluxGroup σ := by
  obtain ⟨Φ, K, hK, hΦK, hΦ, hΦ₁, rfl⟩ := hc
  refine ⟨Φ.transDiffeomorph f, f '' K, hK.image f.continuous,
    Diffeotopy.eqOn_id_transDiffeomorph f hΦK,
    timeSlice_transDiffeomorph_mem_diffeomorphStabilizer hf hΦ, ?_, ?_⟩
  · rw [Diffeotopy.final_transDiffeomorph_eq_mul_mul_inv, hΦ₁, mul_one, mul_inv_cancel]
  · exact Φ.compactFlux_transDiffeomorph_of_mem_diffeomorphStabilizer hf _ _ _ _

/-- **Forgetting supports maps the compactly supported flux group into the flux group.** The
comparison map `H¹_c(M) → H¹_dR(M)` sends the compactly supported flux of a compactly supported
loop to its flux. -/
theorem toDeRhamCohomology_mem_fluxGroup {c : compactlySupportedDeRhamCohomology J M 1}
    (hc : c ∈ compactFluxGroup σ) :
    compactlySupportedDeRhamCohomology.toDeRhamCohomology J M 1 c ∈ fluxGroup σ := by
  obtain ⟨Φ, K, hK, hΦK, hΦ, hΦ₁, rfl⟩ := hc
  rw [Diffeotopy.toDeRhamCohomology_compactFlux]
  exact flux_mem_fluxGroup hΦ hΦ₁

/-- **The compactly supported flux group of an exact form is trivial.** For `σ = dθ` the
compactly supported flux of a compactly supported diffeotopy is the class of `φ₁^* θ - θ`, which
vanishes for a loop. -/
theorem compactFluxGroup_eq_bot_of_mem_exactForms (hσ : σ.val ∈ exactForms J M 2) :
    compactFluxGroup σ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 ?_
  rintro _ ⟨Φ, K, hK, hΦK, hΦ, hΦ₁, rfl⟩
  exact Φ.compactFlux_eq_zero_of_final_eq_refl σ hσ hΦ₁ _ _ hK hΦK

/-! ### The compactly supported endpoint flux -/

/-- A diffeotopy which is the identity outside some compact set has compactly supported flux
form. -/
private theorem fluxForm_mem_compactlySupportedForms_of_exists {Φ : Diffeotopy J ∞ M}
    (τ : SmoothForm J M ℝ 2) (h : ∃ K, IsCompact K ∧ ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ) :
    Φ.fluxForm τ ∈ compactlySupportedForms J M 1 :=
  Φ.fluxForm_mem_compactlySupportedForms τ h.choose_spec.1 h.choose_spec.2

variable (σ) in
/-- The class of the compactly supported flux of the chosen compactly supported `σ`-preserving
diffeotopy ending at `φ`. It does not depend on the choice (`compactEndpointFluxFun_eq`). -/
private def compactEndpointFluxFun (φ : compactIsotopyStabilizer σ.val) :
    compactlySupportedDeRhamCohomology J M 1 ⧸ compactFluxGroup σ :=
  (mem_compactIsotopyStabilizer.1 φ.property).choose.compactFlux σ
    (final_mem_diffeomorphStabilizer (mem_compactIsotopyStabilizer.1 φ.property).choose_spec.2.1)
    (fluxForm_mem_compactlySupportedForms_of_exists σ.val
      (mem_compactIsotopyStabilizer.1 φ.property).choose_spec.1)

/-- The class of the compactly supported flux of any compactly supported `σ`-preserving
diffeotopy ending at `φ` is the class of the compactly supported flux of the chosen one. -/
private theorem compactEndpointFluxFun_eq (φ : compactIsotopyStabilizer σ.val)
    {Φ : Diffeotopy J ∞ M} {K : Set M} (hK : IsCompact K)
    (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ)
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val) (h : Φ.final = φ) :
    compactEndpointFluxFun σ φ = (Φ.compactFlux σ (final_mem_diffeomorphStabilizer hΦ)
      (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK) :
        compactlySupportedDeRhamCohomology J M 1 ⧸ compactFluxGroup σ) := by
  have hφ := (mem_compactIsotopyStabilizer.1 φ.property).choose_spec
  obtain ⟨L, hL, hΨL⟩ := hφ.1
  exact QuotientAddGroup.eq_iff_sub_mem.2 (compactFlux_sub_compactFlux_mem_compactFluxGroup
    hL hΨL hK hΦK hφ.2.1 hΦ (hφ.2.2.trans h.symm) _ _)

variable (σ) in
/-- The **compactly supported endpoint flux** of a closed two-form `σ`: the homomorphism from the
group of final diffeomorphisms of compactly supported diffeotopies preserving `σ` at every time to
`H¹_c(M) / Γ_(σ,c)`, written multiplicatively, which sends `φ₁` to the class of the compactly
supported flux of any such diffeotopy ending at `φ₁` (`TauCeti.compactEndpointFlux_apply`). -/
def compactEndpointFlux : compactIsotopyStabilizer σ.val →*
    Multiplicative (compactlySupportedDeRhamCohomology J M 1 ⧸ compactFluxGroup σ) where
  toFun φ := Multiplicative.ofAdd (compactEndpointFluxFun σ φ)
  map_one' := by
    rw [compactEndpointFluxFun_eq 1 isCompact_empty (fun _ _ _ ↦ by simp)
      timeSlice_refl_mem_diffeomorphStabilizer (by
        rw [Diffeotopy.final_refl, OneMemClass.coe_one, Diffeomorph.one_def]),
      Diffeotopy.compactFlux_refl, QuotientAddGroup.mk_zero, ofAdd_zero]
  map_mul' φ ψ := by
    obtain ⟨Φ, ⟨K, hK, hΦK⟩, hΦ, hΦ₁⟩ := mem_compactIsotopyStabilizer.1 φ.property
    obtain ⟨Ψ, ⟨L, hL, hΨL⟩, hΨ, hΨ₁⟩ := mem_compactIsotopyStabilizer.1 ψ.property
    rw [compactEndpointFluxFun_eq (φ * ψ) (hL.union hK) (Diffeotopy.eqOn_id_trans hΨL hΦK)
      (timeSlice_trans_mem_diffeomorphStabilizer hΨ hΦ) (by
        rw [Diffeotopy.final_trans, hΦ₁, hΨ₁, ← Diffeomorph.mul_def, MulMemClass.coe_mul]),
      compactEndpointFluxFun_eq φ hK hΦK hΦ hΦ₁, compactEndpointFluxFun_eq ψ hL hΨL hΨ hΨ₁,
      Diffeotopy.compactFlux_trans Ψ Φ σ (final_mem_diffeomorphStabilizer hΨ)
        (final_mem_diffeomorphStabilizer hΦ) _ (Ψ.fluxForm_mem_compactlySupportedForms σ.val hL hΨL)
        (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK) _ hL hΨL,
      QuotientAddGroup.mk_add, ofAdd_add, mul_comm]

/-- **The compactly supported endpoint flux is the compactly supported flux of any path.** For a
diffeotopy `φ_t` preserving `σ` at every time, equal to the identity outside a compact set and
ending at `φ`, the compactly supported endpoint flux of `φ` is the class of the compactly
supported flux of `φ_t` modulo the compactly supported flux group. -/
theorem compactEndpointFlux_apply (φ : compactIsotopyStabilizer σ.val) {Φ : Diffeotopy J ∞ M}
    {K : Set M} (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ)
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val) (h : Φ.final = φ)
    (hc : Φ.fluxForm σ.val ∈ compactlySupportedForms J M 1) :
    compactEndpointFlux σ φ =
      Multiplicative.ofAdd (Φ.compactFlux σ (final_mem_diffeomorphStabilizer hΦ) hc :
        compactlySupportedDeRhamCohomology J M 1 ⧸ compactFluxGroup σ) :=
  congrArg Multiplicative.ofAdd (compactEndpointFluxFun_eq φ hK hΦK hΦ h)

/-- **The kernel of the compactly supported endpoint flux.** An element of the compactly
supported isotopy stabilizer of `σ` has trivial compactly supported endpoint flux exactly when it
is the final diffeomorphism of a compactly supported diffeotopy preserving `σ` at every time with
zero compactly supported flux. -/
theorem mem_ker_compactEndpointFlux_iff {φ : compactIsotopyStabilizer σ.val} :
    φ ∈ (compactEndpointFlux σ).ker ↔
      ∃ (Φ : Diffeotopy J ∞ M) (K : Set M) (hK : IsCompact K)
        (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ)
        (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val), Φ.final = φ ∧
          Φ.compactFlux σ (final_mem_diffeomorphStabilizer hΦ)
            (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK) = 0 := by
  constructor
  · intro hker
    obtain ⟨Φ, ⟨K, hK, hΦK⟩, hΦ, hfin⟩ := mem_compactIsotopyStabilizer.1 φ.property
    rw [MonoidHom.mem_ker, compactEndpointFlux_apply φ hK hΦK hΦ hfin
      (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK), ofAdd_eq_one,
      QuotientAddGroup.eq_zero_iff] at hker
    obtain ⟨Λ, L, hL, hΛL, hΛ, hΛ₁, hΛΦ⟩ := hker
    -- Removing the loop `Λ` from `Φ` gives a compactly supported path to `φ` with zero flux.
    refine ⟨Λ.symm.trans Φ, L ∪ K, hL.union hK,
      Diffeotopy.eqOn_id_trans (Diffeotopy.eqOn_id_symm hΛL) hΦK,
      timeSlice_trans_mem_diffeomorphStabilizer (timeSlice_symm_mem_diffeomorphStabilizer hΛ) hΦ,
      ?_, ?_⟩
    · rw [Diffeotopy.final_symm_trans, hΛ₁, inv_one, mul_one, hfin]
    · rw [Φ.compactFlux_symm_trans Λ σ (final_mem_diffeomorphStabilizer hΦ)
        (final_mem_diffeomorphStabilizer hΛ) _ (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK)
        (Λ.fluxForm_mem_compactlySupportedForms σ.val hL hΛL) _ hL hΛL, hΛΦ, sub_self]
  · rintro ⟨Φ, K, hK, hΦK, hΦ, hfin, h₀⟩
    rw [MonoidHom.mem_ker, compactEndpointFlux_apply φ hK hΦK hΦ hfin
      (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK), h₀,
      QuotientAddGroup.mk_zero, ofAdd_zero]

/-- **Compactly supported Hamiltonian isotopies end in the kernel.** If a diffeotopy `φ_t`
preserving `σ` at every time is the identity outside a compact set and has a Hamiltonian, read
along the motion, which vanishes outside a compact set at every time, then its final
diffeomorphism has trivial compactly supported endpoint flux. -/
theorem mem_ker_compactEndpointFlux_of_hasHamiltonian {Φ : Diffeotopy J ∞ M} {K L : Set M}
    (hK : IsCompact K) (hΦK : ∀ t, EqOn (fun x ↦ Φ (t, x)) id Kᶜ)
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val) {F : M × unitInterval → ℝ}
    (hF : Φ.HasHamiltonian σ.val F) (hL : IsCompact L) (hFL : ∀ x ∉ L, ∀ t, F (x, t) = 0) :
    (⟨Φ.final, final_mem_compactIsotopyStabilizer hK hΦK hΦ⟩ : compactIsotopyStabilizer σ.val) ∈
      (compactEndpointFlux σ).ker :=
  mem_ker_compactEndpointFlux_iff.2
    ⟨Φ, K, hK, hΦK, hΦ, rfl, hF.compactFlux_eq_zero hL hFL _ _⟩

/-- **Naturality of the compactly supported endpoint flux.** For a diffeomorphism `f` preserving
`σ`, the compactly supported endpoint flux of `f φ f⁻¹` is the image of that of `φ` under the map
induced on `H¹_c(M) / Γ_(σ,c)` by the pullback along `f⁻¹`
(`TauCeti.map_symm_mem_compactFluxGroup`). -/
theorem compactEndpointFlux_mul_mul_inv {f : M ≃ₘ⟮J, J⟯ M} (hf : f ∈ diffeomorphStabilizer σ.val)
    (φ : compactIsotopyStabilizer σ.val) :
    compactEndpointFlux σ ⟨f * φ * f⁻¹, mul_mul_inv_mem_compactIsotopyStabilizer hf φ.property⟩ =
      Multiplicative.ofAdd (QuotientAddGroup.map (compactFluxGroup σ) (compactFluxGroup σ)
        (compactlySupportedDeRhamCohomology.equivOfDiffeomorph f.symm 1).toLinearMap.toAddMonoidHom
        (fun _ hc ↦ map_symm_mem_compactFluxGroup hf hc)
        (Multiplicative.toAdd (compactEndpointFlux σ φ))) := by
  obtain ⟨Φ, ⟨K, hK, hΦK⟩, hΦ, h⟩ := mem_compactIsotopyStabilizer.1 φ.property
  have hfK := Diffeotopy.eqOn_id_transDiffeomorph f hΦK
  rw [compactEndpointFlux_apply φ hK hΦK hΦ h (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK),
    compactEndpointFlux_apply _ (hK.image f.continuous) hfK
      (timeSlice_transDiffeomorph_mem_diffeomorphStabilizer hf hΦ) (by
        rw [Diffeotopy.final_transDiffeomorph_eq_mul_mul_inv, h])
      ((Φ.transDiffeomorph f).fluxForm_mem_compactlySupportedForms σ.val (hK.image f.continuous)
        hfK),
    Φ.compactFlux_transDiffeomorph_of_mem_diffeomorphStabilizer hf
      (final_mem_diffeomorphStabilizer hΦ) _ (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK),
    toAdd_ofAdd]
  -- The coercion of `g.toAddMonoidHom` is `g` (`LinearMap.toAddMonoidHom_coe`).
  exact congrArg Multiplicative.ofAdd (QuotientAddGroup.map_mk (compactFluxGroup σ)
    (compactFluxGroup σ)
    (compactlySupportedDeRhamCohomology.equivOfDiffeomorph f.symm 1).toLinearMap.toAddMonoidHom
    _ _).symm

/-- **Forgetting supports.** The map `H¹_c(M) / Γ_(σ,c) → H¹_dR(M) / Γ_σ` induced by the
comparison map `H¹_c(M) → H¹_dR(M)` sends the compactly supported endpoint flux of `φ` to its
endpoint flux. -/
theorem map_toAdd_compactEndpointFlux (φ : compactIsotopyStabilizer σ.val) :
    QuotientAddGroup.map (compactFluxGroup σ) (fluxGroup σ)
        (compactlySupportedDeRhamCohomology.toDeRhamCohomology J M 1).toAddMonoidHom
        (fun _ hc ↦ toDeRhamCohomology_mem_fluxGroup hc)
        (Multiplicative.toAdd (compactEndpointFlux σ φ)) =
      Multiplicative.toAdd
        (endpointFlux σ ⟨φ, compactIsotopyStabilizer_le_isotopyStabilizer φ.property⟩) := by
  obtain ⟨Φ, ⟨K, hK, hΦK⟩, hΦ, hfin⟩ := mem_compactIsotopyStabilizer.1 φ.property
  rw [compactEndpointFlux_apply φ hK hΦK hΦ hfin
      (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK),
    endpointFlux_apply _ hΦ hfin, toAdd_ofAdd, toAdd_ofAdd]
  -- The coercion of `g.toAddMonoidHom` is `g` (`LinearMap.toAddMonoidHom_coe`).
  exact (QuotientAddGroup.map_mk _ _ _ _ _).trans
    (congrArg _ (Diffeotopy.toDeRhamCohomology_compactFlux Φ σ _ _))

/-! ### Surjectivity -/

section Surjective

variable [FiniteDimensional ℝ E] [J.Boundaryless]

/-- **Surjectivity of the compactly supported endpoint flux.** On a Hausdorff boundaryless
finite-dimensional manifold with a closed nondegenerate two-form `σ`, compact or not, the
compactly supported endpoint flux `G_(σ,c) → H¹_c(M) / Γ_(σ,c)` is surjective. -/
theorem compactEndpointFlux_surjective (hσ : SmoothTwoForm.IsNondegenerate σ.val) :
    Function.Surjective (compactEndpointFlux σ) := by
  intro c
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd c)
  obtain ⟨Φ, K, hK, hΦK, hΦ, hΦa⟩ := Diffeotopy.exists_compactFlux_eq σ hσ a
  refine ⟨⟨Φ.final, final_mem_compactIsotopyStabilizer hK hΦK hΦ⟩,
    (compactEndpointFlux_apply _ hK hΦK hΦ rfl
      (Φ.fluxForm_mem_compactlySupportedForms σ.val hK hΦK)).trans ?_⟩
  rw [hΦa, ha, ofAdd_toAdd]

end Surjective

end TauCeti
