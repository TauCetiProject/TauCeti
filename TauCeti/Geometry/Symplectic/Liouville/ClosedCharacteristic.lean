/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence
public import TauCeti.Geometry.Symplectic.Liouville.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import TauCeti.Geometry.Symplectic.Liouville.Scaling

/-!
# Closed characteristics swept by a Liouville flow

Let `Z` be a complete smooth Liouville vector field of a nondegenerate two-form `σ`,
`L_Z σ = σ`, with flow `ψ`. The flow is conformally symplectic, `ψ_t^* σ = e^t σ`
(`TauCeti.IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul`), so it carries the
characteristic foliation of a hypersurface `Σ` to that of `ψ_t(Σ)`: the level `c` of `F` carries a
closed characteristic contractible in `W` exactly when the level `c` of `F ∘ ψ_{-t}`, which is
`ψ_t(F⁻¹(c))`, carries one contractible in `ψ_t(W)`
(`TauCeti.IsLiouvilleVectorField.hasContractibleClosedCharacteristic_image_flowOf_iff`).

This is the Liouville-flow argument that turns almost existence into existence for hypersurfaces
of contact type. Suppose that near the level `F⁻¹(c)` the flow translates `F`,
`F(ψ_t x) = F(x) + t`, so that the nearby levels `F⁻¹(c + t) = ψ_t(F⁻¹(c))` are swept out of
`F⁻¹(c)` by the flow. Then every nearby value is regular, since `dF(Z) = 1`. If `F⁻¹(c)` has the
contractible almost existence property in `W`, some nearby level `F⁻¹(c')` carries a closed
characteristic contractible in `W`, and flowing it back for time `c - c'` gives a closed
characteristic of `F⁻¹(c)` itself, contractible in `ψ_{c - c'}(W)`
(`TauCeti.IsLiouvilleVectorField.exists_hasContractibleClosedCharacteristic_image_flowOf`). When
`W` is the whole manifold, the closed characteristic is contractible in it
(`TauCeti.IsLiouvilleVectorField.hasContractibleClosedCharacteristic_univ`).

On the completion `M` of a Liouville domain `W`, the function translated by the Liouville flow is
the time coordinate `log r` of the cylindrical end, where `r` is the radial coordinate
(`TauCeti.IsLiouvilleCompletion.log_liouvilleRadialCoordinate_flowOf`); it is smooth outside `W`.
So each level `{log r = T}`, `T > 0`, which is the hypersurface `ψ_T(∂W)`, carries a closed
characteristic contractible in `M` as soon as it has the contractible almost existence property in
`M`
(`TauCeti.IsLiouvilleCompletion.hasContractibleClosedCharacteristic_univ`).

## Main results

* `TauCeti.IsLiouvilleVectorField.hasContractibleClosedCharacteristic_image_flowOf_iff`: the
  Liouville flow conjugates closed characteristics of levels.
* `TauCeti.IsLiouvilleVectorField.exists_hasContractibleClosedCharacteristic_image_flowOf`:
  almost existence gives existence for a level whose neighbours are swept out by the Liouville
  flow.
* `TauCeti.IsLiouvilleCompletion.exists_hasContractibleClosedCharacteristic_image_flowOf`: the
  same for the levels of the time coordinate of the cylindrical end of a completion.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2 (existence of closed characteristics on hypersurfaces of contact type from the
  almost existence theorem).
* C. Viterbo, *A proof of Weinstein's conjecture in ℝ²ⁿ*, Ann. Inst. H. Poincaré Anal. Non
  Linéaire 4 (1987), 337–356.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary E.
-/

public section

open Filter MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {σ : SmoothTwoForm I M} {Z : (x : M) → TangentSpace I x} {W : Set M} {F : M → ℝ} {c : ℝ}

namespace IsLiouvilleVectorField

variable (hZσ : IsLiouvilleVectorField σ.1 Z) (hσ : σ.IsNondegenerate)
  (hc : IsCompleteVectorField Z) (hZ : ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z))
include hZσ hσ hc hZ

/-- **The Liouville flow conjugates closed characteristics.** Let `Z` be a complete smooth
Liouville vector field of a nondegenerate two-form `σ`, with flow `ψ`, and let `F` be
differentiable along its level `F⁻¹(c)`. Then the level `c` of `F ∘ ψ_{-t}`, the image
`ψ_t(F⁻¹(c))`, carries a closed characteristic contractible in `ψ_t(W)` exactly when `F⁻¹(c)`
carries one contractible in `W`. -/
theorem hasContractibleClosedCharacteristic_image_flowOf_iff (t : ℝ)
    (hF : ∀ x, F x = c → MDifferentiableAt I 𝓘(ℝ) F x) :
    σ.HasContractibleClosedCharacteristic (flowOf Z t '' W) (F ∘ flowOf Z (-t)) c ↔
      σ.HasContractibleClosedCharacteristic W F c := by
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := hZ.of_le (by simp)
  set ψ := globalFlowDiffeomorph hc le_top hZ t
  have hψ : ⇑ψ = flowOf Z t := funext fun x ↦ by
    rw [globalFlowDiffeomorph_apply, flowOf_eq_globalFlow hZ1 hc]
  have hψs : ⇑ψ.symm = flowOf Z (-t) := funext fun x ↦ by
    rw [globalFlowDiffeomorph_symm_apply, flowOf_eq_globalFlow hZ1 hc]
  -- The time-`t` map is conformally symplectic, `ψ_t^* σ = e^t σ`.
  have hpull : SmoothForm.mpullback ψ ψ.contMDiff σ = Real.exp t • σ := Subtype.ext <| by
    rw [SmoothForm.coe_mpullback, hψ, flowOf_eq_globalFlow hZ1 hc]
    exact hZσ.mpullback_globalFlow_eq_exp_smul hc (hZ.of_le (by simp)) σ.mdifferentiable t
  rw [← hψ, ← hψs]
  exact hσ.hasContractibleClosedCharacteristic_image_iff_of_mpullback_eq_smul ψ
    (Real.exp_pos t).ne' hpull hF

/-- **Almost existence gives existence along a Liouville flow.** Let `Z` be a complete smooth
Liouville vector field of a nondegenerate two-form `σ`, with flow `ψ`, and let `F` be
differentiable on the band `c - ε < F < c + ε` and translated by the flow there:
`F(ψ_t x) = F(x) + t` whenever both values lie in the band. If the level `F⁻¹(c)` has the
contractible almost existence property in `W`, then it carries a closed characteristic contractible
in `ψ_t(W)` for some `|t| < ε`. -/
theorem exists_hasContractibleClosedCharacteristic_image_flowOf {ε : ℝ} (hε : 0 < ε)
    (hF : ∀ x, F x ∈ Ioo (c - ε) (c + ε) → MDifferentiableAt I 𝓘(ℝ) F x)
    (hFZ : ∀ x t, F x ∈ Ioo (c - ε) (c + ε) → F x + t ∈ Ioo (c - ε) (c + ε) →
      F (flowOf Z t x) = F x + t)
    (h : σ.HasContractibleAlmostExistence W F c) :
    ∃ t ∈ Ioo (-ε) ε, σ.HasContractibleClosedCharacteristic (flowOf Z t '' W) F c := by
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := hZ.of_le (by simp)
  have hψ := flowOf_eq_globalFlow hZ1 hc
  -- Every value in the band is regular: `F` grows at unit speed along the flow, so `dF(Z) = 1`.
  have hreg : ∀ c' ∈ Ioo (c - ε) (c + ε), IsRegularValue I 𝓘(ℝ) F c' :=
    fun _ ↦ isRegularValue_of_apply_globalFlow_eq_add hZ1 hc hF fun x t hx hxt ↦ by
      rw [← hψ]
      exact hFZ x t hx hxt
  -- Some nearby level `F⁻¹(c')` carries a closed characteristic contractible in `W`.
  obtain ⟨c', hc'ε, hcc'⟩ := h.exists_hasContractibleClosedCharacteristic hε hreg
  -- Flow it back to the level `c`, for time `t = c - c'`.
  set t := c - c'
  refine ⟨t, ⟨by linarith [hc'ε.2], by linarith [hc'ε.1]⟩, ?_⟩
  have hct : c' + t ∈ Ioo (c - ε) (c + ε) := by
    rw [add_sub_cancel]
    exact ⟨by linarith, by linarith⟩
  have hinv (y : M) : flowOf Z t (flowOf Z (-t) y) = y := flowOf_flowOf_neg hZ1 hc t y
  have h1 := (hZσ.hasContractibleClosedCharacteristic_image_flowOf_iff hσ hc hZ t
    fun x hx ↦ hF x (hx ▸ hc'ε)).2 hcc'
  refine h1.of_hamiltonianVectorField_eq_smul one_ne_zero (fun x hx ↦ ?_) fun x hx ↦ ?_
  · -- The level `c'` of `F ∘ ψ_{-t}` is the level `c` of `F`.
    rw [Function.comp_apply] at hx
    rw [← hinv x, hFZ _ t (hx ▸ hc'ε) (hx ▸ hct), hx, add_sub_cancel]
  · -- Near this level, `F = F ∘ ψ_{-t} + t`, so the two functions have the same Hamiltonian
    -- vector field there.
    rw [Function.comp_apply] at hx
    have hG : MDifferentiableAt I 𝓘(ℝ) (F ∘ flowOf Z (-t)) x := by
      refine (hF _ (hx ▸ hc'ε)).comp x ?_
      rw [hψ]
      exact (contMDiff_globalFlow_apply hc (n := 1) le_rfl hZ1 (-t) x).mdifferentiableAt
        one_ne_zero
    have heq : F =ᶠ[𝓝 x] (fun z ↦ z + t) ∘ (F ∘ flowOf Z (-t)) := by
      filter_upwards [hG.continuousAt.preimage_mem_nhds ((isOpen_Ioo.inter
        (isOpen_Ioo.preimage (by fun_prop : Continuous fun z : ℝ ↦ z + t))).mem_nhds
          (by rw [Function.comp_apply, hx]; exact ⟨hc'ε, hct⟩))] with y hy
      rw [Function.comp_apply, Function.comp_apply, ← hFZ _ t hy.1 hy.2, hinv]
    rw [one_smul, SmoothTwoForm.hamiltonianVectorField_def, heq.mvfderiv_eq,
      ← SmoothTwoForm.hamiltonianVectorField_def,
      SmoothTwoForm.hamiltonianVectorField_comp (by fun_prop) hG]
    simp

/-- **Almost existence gives existence along a Liouville flow**, for contractibility in the whole
manifold. Under the hypotheses of
`TauCeti.IsLiouvilleVectorField.exists_hasContractibleClosedCharacteristic_image_flowOf`, if the
level `F⁻¹(c)` has the contractible almost existence property in `M`, then it carries a closed
characteristic contractible in `M`. -/
theorem hasContractibleClosedCharacteristic_univ {ε : ℝ}
    (hε : 0 < ε) (hF : ∀ x, F x ∈ Ioo (c - ε) (c + ε) → MDifferentiableAt I 𝓘(ℝ) F x)
    (hFZ : ∀ x t, F x ∈ Ioo (c - ε) (c + ε) → F x + t ∈ Ioo (c - ε) (c + ε) →
      F (flowOf Z t x) = F x + t)
    (h : σ.HasContractibleAlmostExistence univ F c) :
    σ.HasContractibleClosedCharacteristic univ F c := by
  obtain ⟨t, -, ht⟩ := hZσ.exists_hasContractibleClosedCharacteristic_image_flowOf hσ hc hZ hε hF
    hFZ h
  rwa [image_univ_of_surjective (flowOf_surjective (hZ.of_le (by simp)) hc t)] at ht

end IsLiouvilleVectorField

namespace IsLiouvilleCompletion

variable {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {U : Set M} {T : ℝ}

/-- **Almost existence gives existence on the cylindrical end of a completion.** Let `M` be a
completion of the Liouville domain `W`, with Liouville field `Z`, Liouville flow `ψ` and radial
coordinate `r`, and let `T > 0`. If the level `T` of the time coordinate `log r`, the hypersurface
`ψ_T(∂W)`, has the contractible almost existence property in `U`, then it carries a closed
characteristic contractible in `ψ_t(U)` for some `|t| < T`. -/
theorem exists_hasContractibleClosedCharacteristic_image_flowOf (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hT : 0 < T)
    (hae : ω.HasContractibleAlmostExistence U
      (fun x ↦ Real.log (liouvilleRadialCoordinate Z W x)) T) :
    ∃ t ∈ Ioo (-T) T, ω.HasContractibleClosedCharacteristic (flowOf Z t '' U)
      (fun x ↦ Real.log (liouvilleRadialCoordinate Z W x)) T := by
  have hZs := h.contMDiff_of_interior_eq hZ
  have hZσ : IsLiouvilleVectorField ω.1 Z := by
    have := isLiouvilleVectorField_mextDeriv_of_interior_eq (α.isSmoothForm.of_le (by simp))
      (hZs.mdifferentiable (by simp)) (by rw [h.mextDeriv_eq, hZ])
    rwa [h.mextDeriv_eq] at this
  -- The band `0 < log r < 2T` lies outside `W`, where `log r` is smooth.
  have hband (x : M) (hx : Real.log (liouvilleRadialCoordinate Z W x) ∈ Ioo (T - T) (T + T)) :
      x ∉ W := by
    rw [sub_self] at hx
    exact (h.one_lt_liouvilleRadialCoordinate_iff hZ).1 ((Real.log_pos_iff
      (zero_le_one.trans (one_le_liouvilleRadialCoordinate Z W x))).1 hx.1)
  refine hZσ.exists_hasContractibleClosedCharacteristic_image_flowOf h.isNondegenerate
    (h.isCompleteVectorField hZ) hZs hT (fun x hx ↦ ?_) (fun x t hx hxt ↦ ?_) hae
  · exact (h.contMDiffAt_log_liouvilleRadialCoordinate hZ (hband x hx)).mdifferentiableAt
      (by simp)
  · rw [sub_self] at hxt
    exact h.log_liouvilleRadialCoordinate_flowOf hZ (fun hi ↦ hband x hx (interior_subset hi))
      hxt.1.le

/-- **Almost existence gives existence on the cylindrical end of a completion**, for
contractibility in the completion. Let `M` be a completion of the Liouville domain `W`, with
radial coordinate `r`, and let `T > 0`. If the level `T` of `log r`, the hypersurface `ψ_T(∂W)`,
has the contractible almost existence property in `M`, then it carries a closed characteristic
contractible in `M`. -/
theorem hasContractibleClosedCharacteristic_univ
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.1 = α.1) (hT : 0 < T)
    (hae : ω.HasContractibleAlmostExistence univ
      (fun x ↦ Real.log (liouvilleRadialCoordinate Z W x)) T) :
    ω.HasContractibleClosedCharacteristic univ
      (fun x ↦ Real.log (liouvilleRadialCoordinate Z W x)) T := by
  obtain ⟨t, -, ht⟩ := h.exists_hasContractibleClosedCharacteristic_image_flowOf hZ hT hae
  rwa [image_univ_of_surjective (flowOf_surjective ((h.contMDiff_of_interior_eq hZ).of_le
    (by simp)) (h.isCompleteVectorField hZ) t)] at ht

end IsLiouvilleCompletion

end TauCeti
