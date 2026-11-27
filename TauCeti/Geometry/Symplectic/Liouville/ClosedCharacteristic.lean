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
import TauCeti.Geometry.Symplectic.Manifold.Rescale
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

None of this needs `Z` to be complete. The maximal flow `φ` of a Liouville field that is not
complete is still conformally symplectic wherever it is defined
(`TauCeti.IsLiouvilleVectorField.mpullback_flowOf_apply_eq_exp_smul`). So where the time-`t` map
translates `F` by `t`, its differential carries the Hamiltonian vector field of `F` to `eᵗ` times
itself (`TauCeti.IsLiouvilleVectorField.mfderiv_flowOf_hamiltonianVectorField`), and carries
closed characteristics of `F⁻¹(c')` to closed characteristics of `F⁻¹(c' + t)`. If `φ` translates
`F` across a band around `c`, and the motions of the band preserve `W`, almost existence for the
level `c` in `W` gives a closed characteristic of `F⁻¹(c)` contractible in `W`
(`TauCeti.IsLiouvilleVectorField.hasContractibleClosedCharacteristic`):
the times between `0` and `c - c'` move the nearby closed characteristic to the new one inside `W`.
For `W` the whole manifold this is the contact-type step from almost existence to existence; for a
complete field it gives `TauCeti.IsLiouvilleVectorField.hasContractibleClosedCharacteristic_univ`.

On the completion `M` of a Liouville domain `W`, the function translated by the Liouville flow is
the time coordinate `log r` of the cylindrical end, where `r` is the radial coordinate
(`TauCeti.IsLiouvilleCompletion.log_liouvilleRadialCoordinate_flowOf`); it is smooth outside `W`.
So each level `{log r = T}`, `T > 0`, which is the hypersurface `ψ_T(∂W)`, carries a closed
characteristic contractible in `M` as soon as it has the contractible almost existence property in
`M`
(`TauCeti.IsLiouvilleCompletion.hasContractibleClosedCharacteristic_univ`).

## Main results

* `TauCeti.IsLiouvilleVectorField.mfderiv_flowOf_hamiltonianVectorField`: the local Liouville flow
  rescales the Hamiltonian vector field of a function it translates.
* `TauCeti.IsLiouvilleVectorField.hasContractibleClosedCharacteristic`:
  almost existence gives existence for a level whose neighbours are swept out by the local
  Liouville flow, with no completeness assumption.
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

/-! ### The local Liouville flow -/

section Local

variable (hZσ : IsLiouvilleVectorField σ.val Z) (hσ : σ.IsNondegenerate)
  (hZ : ContMDiff I I.tangent 1 (T% Z))
include hZσ hσ hZ

/-- **The local Liouville flow rescales Hamiltonian vector fields.** Let `Z` be a `C¹` Liouville
vector field of a nondegenerate two-form `σ`, with maximal flow `φ`, and let `φₜ` be defined at `x`
and translate `F` near `x`: `F(φₜ y) = F(y) + t` for `y` near `x`. If `F` is differentiable at
`φₜ x`, then `dφₜ(X_F(x)) = eᵗ X_F(φₜ x)`, since `φₜ^* σ = eᵗ σ` at `x`. No completeness of
`Z` is needed. -/
theorem mfderiv_flowOf_hamiltonianVectorField {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z)
    (hFtx : MDifferentiableAt I 𝓘(ℝ) F (flowOf Z t x))
    (hFt : ∀ᶠ y in 𝓝 x, F (flowOf Z t y) = F y + t) :
    mfderiv I I (flowOf Z t) x (σ.hamiltonianVectorField F x) =
      Real.exp t • σ.hamiltonianVectorField F (flowOf Z t x) := by
  have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hφ : MDifferentiableAt I I (flowOf Z t) x :=
    (contMDiffAt_flowOf_comp le_rfl hZ contMDiffAt_const contMDiffAt_id hx).mdifferentiableAt
      one_ne_zero
  -- `dφₜ` is onto: the differential of `φ_{-t}` at `φₜ x` is a right inverse.
  have hrange : σ.hamiltonianVectorField F (flowOf Z t x) ∈
      (mfderiv I I (flowOf Z t) x).range := by
    have h := mfderiv_flowOf_add_apply hZ (neg_mem_flowDomain_flowOf hZ hx)
      (flowOf_neg_flowOf hZ hx) hx (σ.hamiltonianVectorField F (flowOf Z t x))
    rw [neg_add_cancel] at h
    exact ⟨_, h.trans (mfderiv_flowOf_zero_apply_eq_self Z _ _)⟩
  -- `dφₜ` pulls `σ` back to `eᵗ σ` at `x`.
  have hD (u v : TangentSpace I x) : SmoothBundleForm.eval₂ σ (flowOf Z t x)
      (mfderiv I I (flowOf Z t) x u) (mfderiv I I (flowOf Z t) x v) =
        SmoothBundleForm.eval₂ (Real.exp t • σ) x u v := by
    rw [SmoothBundleForm.eval₂_apply, ← mpullback_apply_pair,
      hZσ.mpullback_flowOf_apply_eq_exp_smul hZ σ.mdifferentiable hx, SmoothForm.eval₂_smul,
      SmoothBundleForm.eval₂_apply, ContinuousAlternatingMap.smul_apply]
  -- `dF ∘ dφₜ = dF` at `x`, since `F ∘ φₜ = F + t` near `x`.
  have hF : mvfderiv I (F ∘ flowOf Z t) x = mvfderiv I (fun y ↦ F y + t) x :=
    Filter.EventuallyEq.mvfderiv_eq hFt
  have hmap := (hσ.smul _ hexp).map_hamiltonianVectorField_of_eval₂ (f := F) (g := F) hσ hrange hD
    fun u ↦ by
      rw [← mvfderiv_comp_apply x hFtx hφ, hF, mvfderiv_add_const]
  rw [hσ.hamiltonianVectorField_smul hexp, Pi.smul_apply, map_smul] at hmap
  rw [← hmap, smul_inv_smul₀ hexp]

/-- **Almost existence gives existence along a local Liouville flow.** Let `Z` be a `C¹`
Liouville vector field of a nondegenerate two-form `σ`, not necessarily complete, with maximal flow
`φ`. Let `F` be differentiable on the band `c - ε < F < c + ε`, and let the flow translate `F`
across the band: whenever `F x` and `F x + t` lie in the band, `φₜ x` is defined and
`F(φₜ x) = F(x) + t`. Let these motions preserve `W`, as they do when `W` is the whole manifold. If
the level `F⁻¹(c)` has the contractible almost existence property in `W`, then it carries a closed
characteristic contractible in `W`.

Some nearby level `F⁻¹(c')` carries a closed characteristic contractible in `W`, and `φ_{c - c'}`
carries it to one of `F⁻¹(c)`; the times between `0` and `c - c'` move the first loop to the
second inside `W`. -/
theorem hasContractibleClosedCharacteristic {ε : ℝ}
    (hε : 0 < ε) (hF : ∀ x, F x ∈ Ioo (c - ε) (c + ε) → MDifferentiableAt I 𝓘(ℝ) F x)
    (hFZ : ∀ x t, F x ∈ Ioo (c - ε) (c + ε) → F x + t ∈ Ioo (c - ε) (c + ε) →
      (t, x) ∈ flowDomain Z ∧ F (flowOf Z t x) = F x + t)
    (hW : ∀ x t, x ∈ W → F x ∈ Ioo (c - ε) (c + ε) → F x + t ∈ Ioo (c - ε) (c + ε) →
      flowOf Z t x ∈ W)
    (h : σ.HasContractibleAlmostExistence W F c) :
    σ.HasContractibleClosedCharacteristic W F c := by
  -- Some nearby level `F⁻¹(c')` carries a closed characteristic `γ` contractible in `W`.
  obtain ⟨c', hc', hcc⟩ := h.exists_hasContractibleClosedCharacteristic hε fun _ ↦
    isRegularValue_of_apply_flowOf_eq_add hZ hF fun x t hx hxt ↦ (hFZ x t hx hxt).2
  obtain ⟨T, γ, hT, hγ, -, ⟨s₀, hs₀⟩, hlev, g, hg, hgγ⟩ :=
    SmoothTwoForm.hasContractibleClosedCharacteristic_iff.1 hcc
  -- It is flowed to the level `c` for the time `t = c - c'`; the times `u t`, `u ∈ [0, 1]`, keep
  -- `F` in the band.
  set t := c - c'
  have hcJ : c ∈ Ioo (c - ε) (c + ε) := ⟨by linarith, by linarith⟩
  have hJ (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : c' + u * t ∈ Ioo (c - ε) (c + ε) :=
    (convex_Ioo _ _).add_smul_sub_mem hc' hcJ hu
  have hγJ (s : ℝ) : F (γ s) ∈ Ioo (c - ε) (c + ε) := by rw [hlev]; exact hc'
  have hγtJ (s : ℝ) : F (γ s) + t ∈ Ioo (c - ε) (c + ε) := by
    rw [hlev, add_sub_cancel]; exact hcJ
  have hdom (s : ℝ) : (t, γ s) ∈ flowDomain Z ∧ F (flowOf Z t (γ s)) = c := by
    obtain ⟨hd, he⟩ := hFZ (γ s) t (hγJ s) (hγtJ s)
    rw [hlev, add_sub_cancel] at he
    exact ⟨hd, he⟩
  -- Near each point of `γ`, the time-`t` map translates `F` by `t`.
  have hloc (s : ℝ) : ∀ᶠ y in 𝓝 (γ s), F (flowOf Z t y) = F y + t := by
    have hband : IsOpen {y : ℝ | y ∈ Ioo (c - ε) (c + ε) ∧ y + t ∈ Ioo (c - ε) (c + ε)} :=
      isOpen_Ioo.inter (isOpen_Ioo.preimage (by fun_prop))
    filter_upwards [(hF _ (hγJ s)).continuousAt.preimage_mem_nhds
      (hband.mem_nhds ⟨hγJ s, hγtJ s⟩)] with y hy
    exact (hFZ y t hy.1 hy.2).2
  -- So `φₜ ∘ γ` is an integral curve of `eᵗ X_F`.
  have hγt : IsMIntegralCurve (flowOf Z t ∘ γ)
      ((Real.exp (-t))⁻¹ • σ.hamiltonianVectorField F) := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
    refine hγ.map_of_mfderiv_eq (fun s _ ↦ (contMDiffAt_flowOf_comp le_rfl hZ contMDiffAt_const
      contMDiffAt_id (hdom s).1).mdifferentiableAt one_ne_zero) fun s _ ↦ ?_
    rw [Real.exp_neg, inv_inv, Pi.smul_apply]
    exact hZσ.mfderiv_flowOf_hamiltonianVectorField hσ hZ (hdom s).1 (hF _ ((hdom s).2 ▸ hcJ))
      (hloc s)
  -- Its loop is contractible in `W`.
  have hgF (z : AddCircle T) : F (g z) = c' := by
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact (congrArg F (hgγ s)).trans (hlev s)
  obtain ⟨g', hg', hgg'⟩ := exists_nullhomotopic_flowOf_comp hZ hg
    (fun z ↦ (hFZ _ t (by rw [hgF]; exact hc') (by simpa [hgF] using hJ 1 ⟨zero_le_one, le_rfl⟩)).1)
    (fun z u hu ↦ hW _ _ (g z).property (by rw [hgF]; exact hc') (by rw [hgF]; exact hJ u hu))
  refine (SmoothTwoForm.hasContractibleClosedCharacteristicOfPeriodLE_of_isMIntegralCurve_smul hT
    (Real.exp_pos (-t)).ne' hγt ⟨s₀, fun h ↦ hs₀ ?_⟩ (fun s ↦ (hdom s).2)
    ⟨g', hg', fun s ↦ by rw [hgg', hgγ, Function.comp_apply]⟩).hasContractibleClosedCharacteristic
  -- `φₜ` is injective along `γ`, since `φ_{-t}` undoes it.
  rw [← flowOf_neg_flowOf hZ (hdom s₀).1, ← flowOf_neg_flowOf hZ (hdom 0).1]
  exact congrArg (flowOf Z (-t)) h

end Local

/-! ### The complete Liouville flow -/

section Complete

variable (hZσ : IsLiouvilleVectorField σ.val Z) (hσ : σ.IsNondegenerate)
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
    fun _ ↦ isRegularValue_of_apply_flowOf_eq_add hZ1 hF hFZ
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

omit hZ in
/-- **Almost existence gives existence along a Liouville flow**, for contractibility in the whole
manifold. Under the hypotheses of
`TauCeti.IsLiouvilleVectorField.exists_hasContractibleClosedCharacteristic_image_flowOf`, with `Z`
only `C¹`, if the level `F⁻¹(c)` has the contractible almost existence property in `M`, then it
carries a closed characteristic contractible in `M`. -/
theorem hasContractibleClosedCharacteristic_univ (hZ : ContMDiff I I.tangent 1 (T% Z)) {ε : ℝ}
    (hε : 0 < ε) (hF : ∀ x, F x ∈ Ioo (c - ε) (c + ε) → MDifferentiableAt I 𝓘(ℝ) F x)
    (hFZ : ∀ x t, F x ∈ Ioo (c - ε) (c + ε) → F x + t ∈ Ioo (c - ε) (c + ε) →
      F (flowOf Z t x) = F x + t)
    (h : σ.HasContractibleAlmostExistence univ F c) :
    σ.HasContractibleClosedCharacteristic univ F c :=
  hZσ.hasContractibleClosedCharacteristic hσ hZ hε hF
    (fun x t hx hxt ↦ ⟨hc.mem_flowDomain t x, hFZ x t hx hxt⟩) (fun _ _ _ _ _ ↦ mem_univ _) h

end Complete

end IsLiouvilleVectorField

namespace IsLiouvilleCompletion

variable {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {U : Set M} {T : ℝ}

/-- **Almost existence gives existence on the cylindrical end of a completion.** Let `M` be a
completion of the Liouville domain `W`, with Liouville field `Z`, Liouville flow `ψ` and radial
coordinate `r`, and let `T > 0`. If the level `T` of the time coordinate `log r`, the hypersurface
`ψ_T(∂W)`, has the contractible almost existence property in `U`, then it carries a closed
characteristic contractible in `ψ_t(U)` for some `|t| < T`. -/
theorem exists_hasContractibleClosedCharacteristic_image_flowOf (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hT : 0 < T)
    (hae : ω.HasContractibleAlmostExistence U
      (fun x ↦ Real.log (liouvilleRadialCoordinate Z W x)) T) :
    ∃ t ∈ Ioo (-T) T, ω.HasContractibleClosedCharacteristic (flowOf Z t '' U)
      (fun x ↦ Real.log (liouvilleRadialCoordinate Z W x)) T := by
  have hZs := h.contMDiff_of_interior_eq hZ
  have hZσ : IsLiouvilleVectorField ω.val Z := by
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
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val) (hT : 0 < T)
    (hae : ω.HasContractibleAlmostExistence univ
      (fun x ↦ Real.log (liouvilleRadialCoordinate Z W x)) T) :
    ω.HasContractibleClosedCharacteristic univ
      (fun x ↦ Real.log (liouvilleRadialCoordinate Z W x)) T := by
  obtain ⟨t, -, ht⟩ := h.exists_hasContractibleClosedCharacteristic_image_flowOf hZ hT hae
  rwa [image_univ_of_surjective (flowOf_surjective ((h.contMDiff_of_interior_eq hZ).of_le
    (by simp)) (h.isCompleteVectorField hZ) t)] at ht

end IsLiouvilleCompletion

end TauCeti
