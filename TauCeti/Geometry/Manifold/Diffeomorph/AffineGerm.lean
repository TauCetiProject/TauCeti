/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Germ
public import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Affine extensions of local diffeomorphisms

A smooth map with invertible derivative on an open neighborhood extends, after shrinking the
neighborhood, to a global diffeomorphism between its model spaces. The extension agrees outside
a compact set with its affine tangent map. Both directions have bounded derivatives of every
positive order and temperate growth. These extensions supply the global coordinate changes
used in compactly localized Sobolev estimates.
-/

public section

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem affine_compact_bounds {f : E → F} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (a : F) (L : E →L[ℝ] F)
    (heq : EqOn f (fun x ↦ a + L x) Kᶜ) :
    (∀ n : ℕ, 0 < n → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) ∧
      Function.HasTemperateGrowth f := by
  have hA : ContDiff ℝ ∞ (fun x ↦ a + L x) := contDiff_const.add L.contDiff
  have hs : HasCompactSupport (fun x ↦ f x - (a + L x)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    exact hx (sub_eq_zero.mpr (heq hxK))
  have htemp : Function.HasTemperateGrowth f := by
    have h := (hs.hasTemperateGrowth (hf.sub hA)).add
      ((Function.HasTemperateGrowth.const a).add L.hasTemperateGrowth)
    convert h using 1
    funext x
    simp
  have hd : HasCompactSupport (fun x ↦ fderiv ℝ f x - L) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    have hevent : f =ᶠ[𝓝 x] (fun y ↦ a + L y) :=
      Filter.Eventually.mono (hK.isClosed.isOpen_compl.mem_nhds hxK) fun y hy ↦ heq hy
    have hder : fderiv ℝ f x = L := by
      rw [hevent.fderiv_eq]
      exact ((L.hasFDerivAt.const_add a).fderiv)
    exact hx (sub_eq_zero.mpr hder)
  have hdcd : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ f x - L) :=
    (hf.fderiv_right (by simp)).sub contDiff_const
  refine ⟨?_, htemp⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨C, _, hC⟩ := hd.exists_bound_iteratedFDeriv hdcd m
  refine ⟨C + ‖L‖, fun x ↦ ?_⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have heqD : fderiv ℝ f = (fun x ↦ fderiv ℝ f x - L) + (fun _ ↦ L) := by
    funext x
    simp
  rw [heqD, iteratedFDeriv_add (hdcd.of_le (by simp)) contDiff_const, Pi.add_apply]
  apply (norm_add_le _ _).trans
  exact add_le_add (hC m le_rfl x) (by
    by_cases hm : m = 0
    · subst m
      simp
    · simp [iteratedFDeriv_const_of_ne hm])

namespace ContinuousLinearEquiv

variable [FiniteDimensional ℝ E]

/-- A smooth local diffeomorphism extends near the base point to a global diffeomorphism equal
to its affine tangent map outside a compact subset of the prescribed open neighborhood.
The inverse is affine off the image of this compact set. Both maps have uniformly bounded
positive-order derivatives and temperate growth. No orientation hypothesis is needed. -/
theorem exists_diffeomorph_eventuallyEq_affine (e : E ≃L[ℝ] F)
    {f : E → F} {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (he : HasFDerivAt f (e : E →L[ℝ] F) x₀) :
    ∃ (Φ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (K : Set E),
      IsCompact K ∧ K ⊆ U ∧ ⇑Φ =ᶠ[𝓝 x₀] f ∧
      EqOn Φ (fun x ↦ f x₀ + e (x - x₀)) Kᶜ ∧
      EqOn Φ.symm (fun y ↦ x₀ + e.symm (y - f x₀)) (Φ '' K)ᶜ ∧
      (∀ n : ℕ, 0 < n → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C) ∧
      (∀ n : ℕ, 0 < n → ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ n Φ.symm y‖ ≤ C) ∧
      Function.HasTemperateGrowth Φ ∧ Function.HasTemperateGrowth Φ.symm := by
  let g : E → E := fun x ↦ x₀ + e.symm (f x - f x₀)
  have hg : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ ∞ g x := by
    filter_upwards [hU.mem_nhds hx₀] with x hx
    exact contDiffAt_const.add
      (e.symm.contDiff.contDiffAt.comp x
        (((hf x hx).contDiffAt (hU.mem_nhds hx)).sub contDiffAt_const))
  have hgd : HasFDerivAt g (ContinuousLinearMap.id ℝ E) x₀ := by
    simpa only [g, Function.comp_def, ContinuousLinearEquiv.coe_symm_comp_coe] using
      (e.symm.hasFDerivAt.comp x₀ (he.sub_const (f x₀))).const_add x₀
  obtain ⟨φ, K, hK, hKU, hφK, hφg⟩ :=
    TauCeti.exists_diffeomorph_eventuallyEq_of_det_fderiv_pos (n := ⊤) (by simp)
      hg (by simp [g]) (by
        rw [hgd.fderiv]
        change 0 < LinearMap.det (LinearMap.id : E →ₗ[ℝ] E)
        simp) (hU.mem_nhds hx₀)
  let A : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F :=
    { toEquiv :=
        { toFun := fun x ↦ f x₀ + e (x - x₀)
          invFun := fun y ↦ x₀ + e.symm (y - f x₀)
          left_inv x := by simp
          right_inv y := by simp }
      contMDiff_toFun :=
        (contDiff_const.add (e.contDiff.comp (contDiff_id.sub contDiff_const))).contMDiff
      contMDiff_invFun :=
        (contDiff_const.add (e.symm.contDiff.comp (contDiff_id.sub contDiff_const))).contMDiff }
  let Φ := φ.trans A
  have hΦK : EqOn Φ (fun x ↦ f x₀ + e (x - x₀)) Kᶜ := by
    intro x hx
    change A (φ x) = A x
    simp only [hφK hx, id_eq]
  have hΦinv : EqOn Φ.symm (fun y ↦ x₀ + e.symm (y - f x₀)) (Φ '' K)ᶜ := by
    intro y hy
    have hxK : Φ.symm y ∈ Kᶜ := fun hx ↦
      hy ⟨Φ.symm y, hx, Φ.apply_symm_apply y⟩
    have h : Φ (Φ.symm y) = A (Φ.symm y) := hΦK hxK
    rw [Φ.apply_symm_apply] at h
    change Φ.symm y = A.symm y
    exact A.injective (by simpa using h.symm)
  have hbound := affine_compact_bounds Φ.contDiff hK (f x₀ - e x₀)
    (e : E →L[ℝ] F) (by simpa [map_sub, sub_add_eq_add_sub, add_sub_assoc] using hΦK)
  have hibound := affine_compact_bounds Φ.symm.contDiff (hK.image Φ.continuous)
    (x₀ - e.symm (f x₀)) (e.symm : F →L[ℝ] E)
    (by simpa [map_sub, sub_add_eq_add_sub, add_sub_assoc] using hΦinv)
  refine ⟨Φ, K, hK, hKU, ?_, hΦK, hΦinv, hbound.1, hibound.1, hbound.2, hibound.2⟩
  filter_upwards [hφg] with x hx
  change A (φ x) = f x
  change f x₀ + e (φ x - x₀) = f x
  rw [hx]
  simp [g]

end ContinuousLinearEquiv
