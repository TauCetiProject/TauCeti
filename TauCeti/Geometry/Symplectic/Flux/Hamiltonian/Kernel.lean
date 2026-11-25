/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.FiniteDimensional
public import TauCeti.Geometry.Manifold.DeRham.Period
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Eulerian
public import TauCeti.Geometry.Symplectic.Flux.Endpoint
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian.Velocity
public import TauCeti.Geometry.Symplectic.Flux.OrderedFlow
public import TauCeti.Geometry.Symplectic.Flux.Reparam

import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive
import TauCeti.Geometry.Manifold.VectorBundle.Section.Module

/-!
# Symplectic isotopies of zero flux end at Hamiltonian diffeomorphisms

Let `σ` be a symplectic form on a compact connected boundaryless finite-dimensional manifold `M`.
A Hamiltonian diffeotopy has zero flux (`TauCeti.Diffeotopy.IsHamiltonian.flux_eq_zero`), so the
Hamiltonian group `Ham(M, σ)` (`TauCeti.SmoothForm.hamiltonianGroup`) lies in the kernel of the
endpoint flux `G_σ → H¹_dR(M) / Γ_σ` (`TauCeti.endpointFlux`) on the group `G_σ` of final maps of
diffeotopies preserving `σ`. This file proves the converse: if a diffeotopy `φ_t` all of whose maps
preserve `σ` has zero flux, then `φ₁` is the final map of a Hamiltonian diffeotopy
(`TauCeti.Diffeotopy.final_mem_hamiltonianGroup_of_flux_eq_zero`). Hence the kernel of the endpoint
flux is exactly `Ham(M, σ)` (`TauCeti.ker_endpointFlux`). Since the endpoint flux is onto
(`TauCeti.endpointFlux_surjective`), this gives the exact sequence

`1 → Ham(M, σ) → G_σ → H¹_dR(M) / Γ_σ → 0`.

The proof corrects `φ_t` by symplectic flows. Its velocity fields `X_t` are symplectic, and their
classes `[ι_(X_t) σ]` are written in a basis `[ι_(Y i) σ]` of `H¹_dR(M)`, given by complete
symplectic vector fields `Y i`, as `∑ i, a i t [ι_(Y i) σ]`. The coordinates `a i t` are smooth in
`t` (`TauCeti.exists_contDiff_isHamiltonianVectorField_eulerianField_sub_sum`), because they are
combinations of line integrals of `ι_(X_t) σ` along finitely many smooth loops
(`TauCeti.deRhamCohomology.exists_apply_mk_eq_sum_pathIntegral`), and these integrals are smooth
in `t` (`TauCeti.contDiff_pathIntegral_interior_eulerianField`). To read velocity fields at all real
times, `φ_t` is first reparametrized to be stationary near both time ends, which changes neither
its final map nor its flux. With `A i t = ∫₀ᵗ a i`, the ordered flow
`ψ_t = ψ^(Y 0)_(A 0 t) ∘ ⋯ ∘ ψ^(Y (k-1))_(A (k-1) t)` makes `ψ_t⁻¹ ∘ φ_t` a Hamiltonian diffeotopy
(`Diffeotopy.exists_isHamiltonianVectorField_velocity_trans_symm_orderedGlobalFlowDiffeotopy`). A
Hamiltonian diffeotopy has zero flux, so the flux `∑ i, A i 1 [ι_(Y i) σ]` of `ψ` equals that of
`φ`, which vanishes. Then every `A i 1` vanishes, `ψ₁` is the identity, and
`φ₁ = (ψ_t⁻¹ ∘ φ_t)₁` is Hamiltonian.

## Main results

* `TauCeti.exists_contDiff_isHamiltonianVectorField_eulerianField_sub_sum`: the velocity fields of
  a smooth family of symplectomorphisms differ from `∑ i, a i t Y i` by Hamiltonian vector fields,
  with coordinates `a i` smooth in time.
* `TauCeti.Diffeotopy.final_mem_hamiltonianGroup_of_flux_eq_zero`: a diffeotopy preserving `σ` at
  every time with zero flux ends at a Hamiltonian diffeomorphism.
* `TauCeti.ker_endpointFlux`: the kernel of the endpoint flux is the Hamiltonian group.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (Theorem 10.2.5 and its proof).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

open SmoothForm

section Coordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [PreconnectedSpace M] [IsManifold I ∞ M]

/-- **Period coordinates of the velocity fields of a symplectic isotopy.** Let `φ_t`, `t ∈ ℝ`, be a
smooth family of diffeomorphisms, with smooth inverses, all preserving a closed two-form `σ` on a
connected manifold, and let `Y i` be symplectic vector fields whose classes `[ι_(Y i) σ]` form a
finite basis of `H¹_dR(M)`. Then there are smooth functions `a i` of time such that at every time
`t` the Eulerian velocity field `X_t` differs from `∑ i, a i t Y i` by the Hamiltonian vector field
of a smooth function: `[ι_(X_t) σ] = ∑ i, a i t [ι_(Y i) σ]`. -/
theorem exists_contDiff_isHamiltonianVectorField_eulerianField_sub_sum (σ : closedForms I M 2)
    {φ : ℝ → M ≃ M} (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2))
    (hφ' : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ (φ p.1).symm p.2))
    (hφσ : ∀ u, mpullback I I (φ u) (σ.val : RoughForm I M ℝ 2) = σ.val) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (deRhamCohomology I M 1))
    (Y : ι → SmoothTwoForm.symplecticVectorFields σ.val)
    (hY : ∀ i, SmoothTwoForm.interiorClass σ.val (Y i) = b i) :
    ∃ a : ι → ℝ → ℝ, (∀ i, ContDiff ℝ ∞ (a i)) ∧ ∀ u, ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧
      SmoothTwoForm.IsHamiltonianVectorField σ.val f fun x ↦
        eulerianField I φ u x - ∑ i, a i u • (Y i : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) x := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨0, fun _ ↦ contDiff_const, fun _ ↦ ⟨0, contMDiff_const,
      SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x ↦ isEmptyElim x⟩⟩
  have := b.finiteDimensional_of_finite
  -- The velocity fields are smooth symplectic vector fields `Z u`.
  have hZsmooth (u : ℝ) : ContMDiff I I.tangent ∞
      (fun x ↦ (⟨x, eulerianField I φ u x⟩ : TangentBundle I M)) :=
    (contMDiff_eulerianField (m := ∞) (n := ∞) (by simp) hφ hφ').comp
      (contMDiff_const.prodMk contMDiff_id)
  let Z (u : ℝ) : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ := ⟨eulerianField I φ u, hZsmooth u⟩
  have hZ (u : ℝ) : Z u ∈ SmoothTwoForm.symplecticVectorFields σ.val :=
    SmoothTwoForm.mem_symplecticVectorFields_iff.2
      (mextDeriv_interior_eulerianField_eq_zero (hφ.of_le (by simp)) (hφ'.of_le (by simp))
        (((isSmoothForm_def ∞ _).1 (SmoothForm.isSmoothForm σ.val)).mdifferentiable (by simp))
        ((mem_closedForms I σ.val).1 σ.property) hφσ u)
  -- Their contractions `β u`, and the coordinates `a i u` of the classes `[β u]`.
  let β (u : ℝ) : closedForms I M 1 := ⟨SmoothTwoForm.interiorₗ σ.val (Z u),
    (mem_closedForms I _).2 (by
      rw [SmoothTwoForm.coe_interiorₗ]
      exact SmoothTwoForm.mem_symplecticVectorFields_iff.1 (hZ u))⟩
  have hβ (u : ℝ) : ((β u : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1) =
      RoughForm.interior (eulerianField I φ u) σ.val :=
    SmoothTwoForm.coe_interiorₗ _
  refine ⟨fun i u ↦ b.coord i (deRhamCohomology.mk I 1 (β u)), fun i ↦ ?_, fun u ↦ ?_⟩
  · -- Each coordinate is a combination of line integrals along smooth loops, smooth in time.
    obtain ⟨n, γ, c, hγ, hc⟩ := deRhamCohomology.exists_apply_mk_eq_sum_pathIntegral x₀ (b.coord i)
    simp only [hc, hβ]
    exact ContDiff.sum fun j _ ↦ contDiff_const.mul
      (contDiff_pathIntegral_interior_eulerianField (by simp) hφ hφ' σ.val (hγ j).1 0 1)
  -- The class of `Z u - ∑ i, a i u • Y i` vanishes, so this field is Hamiltonian.
  let V : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ :=
    Z u - ∑ i, b.coord i (deRhamCohomology.mk I 1 (β u)) • (Y i : Cₛ^∞⟮I; E, TangentSpace I⟯)
  have hV : V ∈ SmoothTwoForm.symplecticVectorFields σ.val :=
    sub_mem (hZ u) (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Y i).property)
  have hclass : SmoothTwoForm.interiorClass σ.val ⟨V, hV⟩ = 0 := by
    have hsplit : (⟨V, hV⟩ : SmoothTwoForm.symplecticVectorFields σ.val) =
        ⟨Z u, hZ u⟩ - ∑ i, b.coord i (deRhamCohomology.mk I 1 (β u)) • Y i :=
      Subtype.ext (by simp [V])
    rw [hsplit, map_sub, map_sum]
    simp_rw [map_smul, hY]
    rw [SmoothTwoForm.interiorClass_apply, sub_eq_zero]
    exact (b.sum_repr _).symm
  rw [SmoothTwoForm.interiorClass_apply, deRhamCohomology.mk_eq_zero_iff] at hclass
  obtain ⟨f, hf, hdf⟩ := exists_contMDiff_mextDeriv_eq_of_mem_exactForms I hclass
  refine ⟨f, hf, ?_⟩
  convert SmoothTwoForm.isHamiltonianVectorField_iff_interior_eq.2
    ((SmoothTwoForm.coe_interiorₗ _).symm.trans hdf.symm) using 1
  funext x
  simp [V, Z, Finset.sum_apply]

end Coordinates

section Kernel

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

namespace Diffeotopy

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- A diffeotopy preserving `σ` at every time is homotopic, relative to both time ends, to a
diffeotopy whose motion on `[0, 1]` is the restriction of a smooth family `φ_u`, `u ∈ ℝ`, of
diffeomorphisms preserving `σ`. This is `TauCeti.Diffeotopy.exists_homotopic_timeSlice_eq_comp`,
whose time slices `φ_{c u}` are time slices of `Φ` and so preserve `σ`. -/
private theorem exists_homotopic_apply_eq {σ : SmoothForm I M ℝ 2} {Φ : Diffeotopy I ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) :
    ∃ (Φ' : Diffeotopy I ∞ M) (φ : ℝ → M ≃ M), Φ'.Homotopic Φ ∧
      (∀ t, Φ'.timeSlice t ∈ diffeomorphStabilizer σ) ∧
      (∀ (s : unitInterval) (y : M), φ s y = Φ' (s, y)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ (φ p.1).symm p.2) ∧
      ∀ u, mpullback I I (φ u) (σ : RoughForm I M ℝ 2) = σ := by
  obtain ⟨Φ', c, hhom, -, hslice, hφ, hφ'⟩ := Φ.exists_homotopic_timeSlice_eq_comp le_rfl
  have hφ_coe (u : ℝ) : ⇑(Φ.timeSlice (c u)).toEquiv = Φ.timeSlice (c u) :=
    Diffeomorph.coe_toEquiv _
  have hφ_symm (u : ℝ) (y : M) : (Φ.timeSlice (c u)).toEquiv.symm y = Φ.symm (c u, y) := by
    rw [← symm_timeSlice_apply, ← Diffeomorph.coe_toEquiv, Diffeomorph.symm_toEquiv]
  refine ⟨Φ', fun u ↦ (Φ.timeSlice (c u)).toEquiv, hhom, fun t ↦ hslice t ▸ hΦ _,
    fun s y ↦ ?_, hφ.congr fun p ↦ ?_, hφ'.congr fun p ↦ hφ_symm p.1 p.2, fun u ↦ ?_⟩
  · rw [hφ_coe, ← hslice, timeSlice_apply]
  · rw [hφ_coe, timeSlice_apply]
  · rw [hφ_coe]
    exact funext (mem_diffeomorphStabilizer_iff_forall.1 (hΦ (c u)))

variable [CompactSpace M] [PreconnectedSpace M]

/-- **Symplectic isotopies of zero flux end at Hamiltonian diffeomorphisms.** On a compact
connected boundaryless manifold with a symplectic form `σ`, if every map `φ_t` of a diffeotopy
preserves `σ` and its flux vanishes, then `φ₁` lies in the Hamiltonian group `Ham(M, σ)`. -/
theorem final_mem_hamiltonianGroup_of_flux_eq_zero (σ : closedForms I M 2)
    (hσ : SmoothTwoForm.IsNondegenerate σ.val) {Φ : Diffeotopy I ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ.val)
    (h : Φ.flux σ (final_mem_diffeomorphStabilizer hΦ) = 0) :
    Φ.final ∈ hamiltonianGroup σ.val := by
  have hσc : σ.val.IsClosed := (isClosed_def _).2 ((mem_closedForms I σ.val).1 σ.property)
  -- Replace `Φ` by a homotopic diffeotopy `Φ'`, read at all real times as the family `φ`.
  obtain ⟨Φ', φ, hhom, hΦ'σ, hφΦ', hφ, hφ', hφσ⟩ := exists_homotopic_apply_eq hΦ
  have hΦ'flux := (hhom.flux_eq σ (final_mem_diffeomorphStabilizer hΦ'σ) _).trans h
  -- A basis `[ι_(Y i) σ]` of `H¹_dR(M)` by complete symplectic vector fields `Y i`, and the
  -- smooth coordinates `a i` of the velocity classes of `φ` in it.
  let b := Module.finBasis ℝ (deRhamCohomology I M 1)
  set k := Module.finrank ℝ (deRhamCohomology I M 1)
  choose Y hY using fun i ↦ hσ.interiorClass_surjective (b i)
  let Yv (i : Fin k) : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ := Y i
  have hYmem (i : Fin k) : Yv i ∈ SmoothTwoForm.symplecticVectorFields σ.val := (Y i).property
  have hYc (i : Fin k) : IsCompleteVectorField (Yv i) :=
    isCompleteVectorField_of_compactSpace ((Yv i).contMDiff.of_le (by simp))
  obtain ⟨a, ha, hHam⟩ :=
    exists_contDiff_isHamiltonianVectorField_eulerianField_sub_sum σ hφ hφ' hφσ b Y hY
  -- The time functions `A i t = ∫₀ᵗ a i`, and the ordered flow `ψ` of the `Y i` along them.
  let A (i : Fin k) (u : ℝ) : ℝ := ∫ v in (0 : ℝ)..u, a i v
  have hderiv (i : Fin k) : deriv (A i) = a i := funext ((ha i).continuous.deriv_integral _ 0)
  have hA (i : Fin k) : ContDiff ℝ ∞ (A i) :=
    (intervalIntegral.contDiff_primitive_of_contDiff (ha i) 0).of_le (by simp)
  have hA₀ (i : Fin k) : A i 0 = 0 := intervalIntegral.integral_same
  set Ψ := orderedGlobalFlowDiffeotopy le_top (fun i ↦ Yv i) (fun i ↦ (Yv i).contMDiff) hYc A hA
    hA₀
  have hΨσ := timeSlice_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer hσc hYmem hYc A hA hA₀
  -- The velocity fields of `φ'_t` differ from `∑ i, A i'(t) Y i` by Hamiltonian vector fields, so
  -- the corrected isotopy `ψ_t⁻¹ ∘ φ'_t` is Hamiltonian.
  have hHσ : ∀ t, (Φ'.trans Ψ.symm).timeSlice t ∈ diffeomorphStabilizer σ.val :=
    timeSlice_trans_mem_diffeomorphStabilizer hΦ'σ (timeSlice_symm_mem_diffeomorphStabilizer hΨσ)
  have hcorr : (Φ'.trans Ψ.symm).IsHamiltonian σ.val := by
    refine isHamiltonian_iff_forall_isHamiltonianVectorField_velocity.2 ⟨hHσ, fun t ↦ ?_⟩
    obtain ⟨f, hf, hfX⟩ := hHam t
    have hvel (x : M) : Φ'.velocity t x = eulerianField I φ t x :=
      Φ'.velocity_eq_eulerianField (by simp) hφΦ'
        ((hφ.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp))
    obtain ⟨g, hg, hgX⟩ :=
      exists_isHamiltonianVectorField_velocity_trans_symm_orderedGlobalFlowDiffeotopy hσc hYmem
        hYc A hA hA₀ Φ' t hf (by simpa only [hvel, hderiv] using hfX)
    exact ⟨g, hg.mdifferentiable (by simp), hgX⟩
  -- So `ψ` has the zero flux of `φ'`, and it is a loop.
  have hΨflux : Ψ.flux σ (final_mem_diffeomorphStabilizer hΨσ) = 0 := by
    have h0 := hcorr.flux_eq_zero (final_mem_diffeomorphStabilizer hHσ)
    rwa [flux_trans Φ' Ψ.symm σ (final_mem_diffeomorphStabilizer hΦ'σ)
      (final_mem_diffeomorphStabilizer (timeSlice_symm_mem_diffeomorphStabilizer hΨσ)),
      flux_symm Ψ σ (final_mem_diffeomorphStabilizer hΨσ), hΦ'flux, add_zero, neg_eq_zero] at h0
  have hΨfinal : Ψ.final = Diffeomorph.refl I M ∞ :=
    final_orderedGlobalFlowDiffeotopy_eq_refl_of_flux_eq_zero σ hYmem hYc A hA hA₀
      (by simpa only [Yv, Subtype.coe_eta, hY] using b.linearIndependent) _ hΨflux
  refine mem_hamiltonianGroup.2 ⟨Φ'.trans Ψ.symm, hcorr, ?_⟩
  rw [final_trans, final_symm, hΨfinal, hhom.final_eq, Diffeomorph.symm_refl,
    Diffeomorph.trans_refl]

end Diffeotopy

variable [CompactSpace M] [PreconnectedSpace M]

/-- **The kernel of the endpoint flux is the Hamiltonian group.** On a compact connected
boundaryless manifold with a symplectic form `σ`, an element of the group `G_σ` of final maps of
diffeotopies preserving `σ` has trivial endpoint flux exactly when it is a Hamiltonian
diffeomorphism. -/
theorem ker_endpointFlux (σ : closedForms I M 2) (hσ : SmoothTwoForm.IsNondegenerate σ.val) :
    (endpointFlux σ).ker = (hamiltonianGroup σ.val).subgroupOf (isotopyStabilizer σ.val) := by
  refine le_antisymm (fun φ hφ ↦ ?_) (hamiltonianGroup_subgroupOf_le_ker_endpointFlux σ)
  obtain ⟨Φ, hΦ, hfin, h0⟩ := mem_ker_endpointFlux_iff.1 hφ
  exact Subgroup.mem_subgroupOf.2
    (hfin ▸ Diffeotopy.final_mem_hamiltonianGroup_of_flux_eq_zero σ hσ hΦ h0)

end Kernel

end TauCeti
