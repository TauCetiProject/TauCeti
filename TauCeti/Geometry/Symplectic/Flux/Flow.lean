/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Symplectic.Flux
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
import TauCeti.Geometry.Manifold.DifferentialForm.Flow

/-!
# The flux of the flow of a symplectic vector field

Let `σ` be a two-form on a boundaryless finite-dimensional manifold `M` and let `X` be a complete
smooth vector field whose contraction `ι_X σ` is closed, a symplectic vector field
(`TauCeti.SmoothTwoForm.symplecticVectorFields`). Running the flow `ψ` of `X` along a smooth time
function `A : ℝ → ℝ` with `A 0 = 0` gives the diffeotopy `φ_t = ψ_(A t)`, `t ∈ [0, 1]`
(`TauCeti.globalFlowDiffeotopyAlong`); for `A t = a t` it runs the flow for a duration `a`
(`TauCeti.globalFlowDiffeotopy`). This file computes its flux.

The motion `(x, t) ↦ ψ_(A t) x` has velocity `A'(t) X`
(`TauCeti.Diffeotopy.mfderiv_cylinderMap_globalFlowDiffeotopyAlong_time`), so the flux form
`∫₀¹ φ_t^* (ι_(A'(t) X) σ) dt` is the integral of the pullbacks `ψ_(A t)^* (A'(t) ι_X σ)`. The
one-form `ι_X σ` is invariant under the flow of `X`: it is closed by assumption, and its
contraction `σ(X, X)` with `X` vanishes, so Cartan's formula gives `L_X (ι_X σ) = 0`. Hence the
flux form is exactly `(A 1 - A 0) ι_X σ = A 1 ι_X σ`
(`TauCeti.Diffeotopy.fluxForm_globalFlowDiffeotopyAlong`), and `a ι_X σ` for the duration `a`
(`TauCeti.Diffeotopy.fluxForm_globalFlowDiffeotopy`). No closedness or nondegeneracy of `σ` is
needed for this, and `M` need not be compact.

For a closed `σ` the same Cartan argument shows that the flow preserves `σ`, so every map of the
diffeotopy preserves `σ`
(`TauCeti.Diffeotopy.timeSlice_globalFlowDiffeotopyAlong_mem_diffeomorphStabilizer`), and the
flux is the class `A 1 [ι_X σ]` (`TauCeti.Diffeotopy.flux_globalFlowDiffeotopyAlong`).

On a compact manifold every smooth vector field is complete. If moreover `σ` is closed and
nondegenerate, every closed one-form `α` is the contraction of the symplectic vector field
`(σ♭)⁻¹ α`, so every class in `H¹_dR(M)` is the flux of a diffeotopy all of whose maps preserve
`σ`, namely of the time-one flow of such a field (`TauCeti.Diffeotopy.exists_flux_eq`).

## Main results

* `TauCeti.Diffeotopy.fluxForm_globalFlowDiffeotopyAlong`: the flux form of the flow of a
  symplectic vector field `X` along a time function `A` is `A 1 ι_X σ`;
  `TauCeti.Diffeotopy.fluxForm_globalFlowDiffeotopy`: for duration `a` it is `a ι_X σ`.
* `TauCeti.Diffeotopy.timeSlice_globalFlowDiffeotopyAlong_mem_diffeomorphStabilizer`: for closed
  `σ`, every map of that diffeotopy preserves `σ`.
* `TauCeti.Diffeotopy.flux_globalFlowDiffeotopyAlong`: its flux is `A 1 [ι_X σ]`;
  `TauCeti.Diffeotopy.flux_globalFlowDiffeotopy`: for duration `a` it is `a [ι_X σ]`.
* `TauCeti.Diffeotopy.exists_flux_eq`: on a compact manifold with a closed nondegenerate
  two-form, every class in `H¹_dR(M)` is the flux of a symplectic isotopy.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism, and the flux of the flow of a
  symplectic vector field).
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}

/-! ### The flux form -/

/-- The integrand of the flux form of the flow of a symplectic vector field `X`, at time `s` of the
flow: `σ(a X, dψ_s ·)` at `ψ_s x` is `a ι_X σ` at `x`, because the flow preserves the closed form
`ι_X σ`, whose contraction `σ(X, X)` with `X` vanishes. -/
theorem apply_vecCons_smul_mfderiv_flowOf {σ : SmoothTwoForm I M}
    (hX : X ∈ σ.symplecticVectorFields) (hc : IsCompleteVectorField X) (a s : ℝ) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    σ.val (flowOf X s x) (Matrix.vecCons (a • X (flowOf X s x))
      fun i ↦ mfderiv I I (flowOf X s) x (v i)) = a • (σ.interiorₗ X).val x v := by
  have hinv : mpullback I I (flowOf X s) (σ.interiorₗ X).val x = (σ.interiorₗ X).val x :=
    mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero (X.contMDiff.of_le (by simp))
      (by
        rw [SmoothForm.isClosed_def, SmoothTwoForm.coe_interiorₗ]
        exact SmoothTwoForm.mem_symplecticVectorFields_iff.1 hX)
      (by rw [SmoothTwoForm.coe_interiorₗ, RoughForm.interior_self, mextDeriv_zero])
      (hc.mem_flowDomain s x)
  refine ((σ.val _).vecCons_smul _ a _).trans (congrArg (a • ·) ?_)
  rw [← hinv, mpullback_apply, SmoothTwoForm.coe_interiorₗ, RoughForm.interior_apply]

/-- **The flux form of a symplectic flow along a time function.** Let `X` be a complete smooth
vector field whose contraction `ι_X σ` with a two-form `σ` is closed. The diffeotopy which runs the
flow of `X` along a smooth time function `A` with `A 0 = 0` has flux form `A 1 ι_X σ`: the flux
form only sees the total time `A 1` of the flow. Neither closedness nor nondegeneracy of `σ` is
needed. -/
theorem fluxForm_globalFlowDiffeotopyAlong {σ : SmoothTwoForm I M}
    (hX : X ∈ σ.symplecticVectorFields) (hc : IsCompleteVectorField X) (A : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hA₀ : A 0 = 0) :
    (globalFlowDiffeotopyAlong le_top X.contMDiff hc A hA hA₀).fluxForm σ =
      A 1 • σ.interiorₗ X := by
  apply Subtype.ext
  funext x
  rw [fluxForm_apply]
  -- The integrand at time `t` is `A' t ι_X σ`, read in the model space `E [⋀^Fin 1]→L[ℝ] ℝ` of the
  -- integral.
  obtain ⟨c, hc'⟩ : ∃ c : E [⋀^Fin 1]→L[ℝ] ℝ, c = (σ.interiorₗ X).val x := ⟨_, rfl⟩
  refine (intervalIntegral.integral_congr (g := fun t ↦ deriv A t • c) fun t ht ↦ ?_).trans ?_
  · have ht' : ((projIcc (0 : ℝ) 1 zero_le_one t : unitInterval) : ℝ) = t := by
      rw [uIcc_of_le zero_le_one] at ht
      exact congrArg Subtype.val (projIcc_of_mem zero_le_one ht)
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    rw [curryLeft_mfderiv_cylinderMap_apply, mfderiv_cylinderMap_globalFlowDiffeotopyAlong_time]
    simp only [mfderiv_cylinderMap_globalFlowDiffeotopyAlong_space]
    rw [congrFun (cylinderMap_globalFlowDiffeotopyAlong le_top X.contMDiff hc A hA hA₀)
      (x, projIcc 0 1 zero_le_one t), ht']
    rw [hc']
    exact apply_vecCons_smul_mfderiv_flowOf hX hc (deriv A t) _ x v
  · rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_deriv_eq_sub' A rfl
      (fun t _ ↦ (hA.differentiable (by simp)) t) (hA.continuous_deriv (by simp)).continuousOn,
      hA₀, sub_zero, hc']
    exact (congrFun (Submodule.coe_smul (A 1) (σ.interiorₗ X)) x).symm

/-- **The flux form of a symplectic flow.** Let `X` be a complete smooth vector field whose
contraction `ι_X σ` with a two-form `σ` is closed. The diffeotopy which runs the flow of `X` for
duration `a` has flux form `a ι_X σ`. Neither closedness nor nondegeneracy of `σ` is needed. -/
theorem fluxForm_globalFlowDiffeotopy {σ : SmoothTwoForm I M}
    (hX : X ∈ σ.symplecticVectorFields) (hc : IsCompleteVectorField X) (a : ℝ) :
    (globalFlowDiffeotopy le_top X.contMDiff hc a).fluxForm σ = a • σ.interiorₗ X := by
  rw [globalFlowDiffeotopy_eq_globalFlowDiffeotopyAlong, fluxForm_globalFlowDiffeotopyAlong hX,
    mul_one]

/-! ### The flux -/

/-- **Symplectic flows are symplectic isotopies.** For a closed two-form `σ` and a complete smooth
vector field `X` with closed contraction `ι_X σ`, every map of the diffeotopy which runs the flow
of `X` along a smooth time function `A` with `A 0 = 0` preserves `σ`. -/
theorem timeSlice_globalFlowDiffeotopyAlong_mem_diffeomorphStabilizer {σ : SmoothTwoForm I M}
    (hσ : σ.IsClosed) (hX : X ∈ σ.symplecticVectorFields) (hc : IsCompleteVectorField X)
    (A : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hA₀ : A 0 = 0) (t : unitInterval) :
    (globalFlowDiffeotopyAlong le_top X.contMDiff hc A hA hA₀).timeSlice t ∈
      SmoothForm.diffeomorphStabilizer σ := by
  rw [SmoothForm.mem_diffeomorphStabilizer_iff_forall, timeSlice_globalFlowDiffeotopyAlong]
  exact fun x ↦ mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero
    (X.contMDiff.of_le (by simp)) hσ (SmoothTwoForm.mem_symplecticVectorFields_iff.1 hX)
    (hc.mem_flowDomain _ x)

/-- **Symplectic flows are symplectic isotopies.** For a closed two-form `σ` and a complete smooth
vector field `X` with closed contraction `ι_X σ`, every map of the diffeotopy which runs the flow
of `X` for duration `a` preserves `σ`. -/
theorem timeSlice_globalFlowDiffeotopy_mem_diffeomorphStabilizer {σ : SmoothTwoForm I M}
    (hσ : σ.IsClosed) (hX : X ∈ σ.symplecticVectorFields) (hc : IsCompleteVectorField X)
    (a : ℝ) (t : unitInterval) :
    (globalFlowDiffeotopy le_top X.contMDiff hc a).timeSlice t ∈
      SmoothForm.diffeomorphStabilizer σ := by
  rw [globalFlowDiffeotopy_eq_globalFlowDiffeotopyAlong]
  exact timeSlice_globalFlowDiffeotopyAlong_mem_diffeomorphStabilizer hσ hX hc _ _ _ t

/-- **The flux of a symplectic flow along a time function.** For a closed two-form `σ` and a
complete symplectic vector field `X`, the diffeotopy which runs the flow of `X` along a smooth time
function `A` with `A 0 = 0` has flux `A 1 [ι_X σ]`. -/
theorem flux_globalFlowDiffeotopyAlong (σ : closedForms I M 2)
    (hX : X ∈ SmoothTwoForm.symplecticVectorFields σ.val) (hc : IsCompleteVectorField X) (A : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hA₀ : A 0 = 0)
    (hΦ : (globalFlowDiffeotopyAlong le_top X.contMDiff hc A hA hA₀).final ∈
      SmoothForm.diffeomorphStabilizer σ.val) :
    (globalFlowDiffeotopyAlong le_top X.contMDiff hc A hA hA₀).flux σ hΦ =
      A 1 • SmoothTwoForm.interiorClass σ.val ⟨X, hX⟩ := by
  rw [flux_def, SmoothTwoForm.interiorClass_apply, ← map_smul]
  congr 1
  exact Subtype.ext (fluxForm_globalFlowDiffeotopyAlong hX hc A hA hA₀)

/-- **The flux of a symplectic flow.** For a closed two-form `σ` and a complete symplectic vector
field `X`, the diffeotopy which runs the flow of `X` for duration `a` has flux `a [ι_X σ]`. -/
theorem flux_globalFlowDiffeotopy (σ : closedForms I M 2)
    (hX : X ∈ SmoothTwoForm.symplecticVectorFields σ.val) (hc : IsCompleteVectorField X) (a : ℝ)
    (hΦ : (globalFlowDiffeotopy le_top X.contMDiff hc a).final ∈
      SmoothForm.diffeomorphStabilizer σ.val) :
    (globalFlowDiffeotopy le_top X.contMDiff hc a).flux σ hΦ =
      a • SmoothTwoForm.interiorClass σ.val ⟨X, hX⟩ := by
  rw [flux_def, SmoothTwoForm.interiorClass_apply, ← map_smul]
  congr 1
  exact Subtype.ext (fluxForm_globalFlowDiffeotopy hX hc a)

/-- **Every first de Rham class is a flux.** On a compact manifold with a closed nondegenerate
two-form `σ`, every class in `H¹_dR(M)` is the flux of a diffeotopy all of whose maps preserve
`σ`: the time-one flow of the symplectic vector field `(σ♭)⁻¹ α`, for a closed representative
`α` of the class. -/
theorem exists_flux_eq [CompactSpace M] (σ : closedForms I M 2)
    (hσ : SmoothTwoForm.IsNondegenerate σ.val) (c : deRhamCohomology I M 1) :
    ∃ (Φ : Diffeotopy I ∞ M) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val),
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val) ∧ Φ.flux σ hΦ = c := by
  obtain ⟨⟨X, hX⟩, rfl⟩ := hσ.interiorClass_surjective c
  have hc : IsCompleteVectorField X :=
    isCompleteVectorField_of_compactSpace (X.contMDiff.of_le (by simp))
  have hσc : SmoothForm.IsClosed σ.val :=
    (SmoothForm.isClosed_def _).2 ((mem_closedForms I σ.val).1 σ.property)
  have hslice := timeSlice_globalFlowDiffeotopy_mem_diffeomorphStabilizer hσc hX hc 1
  refine ⟨globalFlowDiffeotopy le_top X.contMDiff hc 1, ?_, hslice, ?_⟩
  · rw [final_def]
    exact hslice 1
  · exact (flux_globalFlowDiffeotopy σ hX hc 1 _).trans (one_smul ℝ _)

end Diffeotopy

end TauCeti
