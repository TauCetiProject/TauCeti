/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Germ
public import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace

/-!
# Affine extensions of local diffeomorphisms

A smooth germ with invertible derivative between finite-dimensional real normed spaces extends
to a global diffeomorphism between the model spaces. The extension agrees outside
a compact set with its affine tangent map. Both directions have bounded derivatives of every
positive order and temperate growth. These extensions supply the global coordinate changes
used in compactly localized Sobolev estimates.

The construction adapts
[`TauCeti.exists_diffeomorph_eventuallyEq_of_det_fderiv_pos`](Germ.lean#L287).
Applying the inverse derivative and translating the source and target normalizes the local map to
a fixed-point germ tangent to the identity. The cited theorem supplies its compactly supported
extension; composing with the affine tangent map gives the extension between the two model spaces.
-/

public section

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace ContinuousLinearEquiv

variable [FiniteDimensional ℝ E]

/-- A smooth local diffeomorphism extends near the base point to a global diffeomorphism equal
to its affine tangent map outside a compact subset of any prescribed neighborhood.
The inverse is affine off the image of this compact set. Both maps have uniformly bounded
positive-order derivatives and temperate growth. No orientation hypothesis is needed. -/
theorem exists_diffeomorph_eventuallyEq_affine (e : E ≃L[ℝ] F)
    {f : E → F} {U : Set E} {x₀ : E} (hU : U ∈ 𝓝 x₀)
    (hf : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ ∞ f x) (he : HasFDerivAt f (e : E →L[ℝ] F) x₀) :
    ∃ (Φ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (K : Set E),
      IsCompact K ∧ K ⊆ U ∧ ⇑Φ =ᶠ[𝓝 x₀] f ∧
      EqOn Φ (fun x ↦ f x₀ + e (x - x₀)) Kᶜ ∧
      EqOn Φ.symm (fun y ↦ x₀ + e.symm (y - f x₀)) (Φ '' K)ᶜ ∧
      (∀ n : ℕ, 0 < n → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C) ∧
      (∀ n : ℕ, 0 < n → ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ n Φ.symm y‖ ≤ C) ∧
      Function.HasTemperateGrowth Φ ∧ Function.HasTemperateGrowth Φ.symm := by
  let g : E → E := fun x ↦ x₀ + e.symm (f x - f x₀)
  have hg : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ ∞ g x := by
    filter_upwards [hf] with x hx
    exact contDiffAt_const.add (e.symm.contDiff.contDiffAt.comp x (hx.sub contDiffAt_const))
  have hgd : HasFDerivAt g (ContinuousLinearMap.id ℝ E) x₀ := by
    simpa only [g, Function.comp_def, ContinuousLinearEquiv.coe_symm_comp_coe] using
      (e.symm.hasFDerivAt.comp x₀ (he.sub_const (f x₀))).const_add x₀
  obtain ⟨φ, K, hK, hKU, hφK, hφg⟩ :=
    TauCeti.exists_diffeomorph_eventuallyEq_of_det_fderiv_pos (n := ⊤) (by simp)
      hg (by simp [g]) (by
        rw [hgd.fderiv]
        simp [ContinuousLinearMap.det]) hU
  let A : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F :=
    ((Diffeomorph.smulAdd ∞ (1 : ℝ) (-x₀) one_ne_zero).trans e.toDiffeomorph).trans
      (Diffeomorph.smulAdd ∞ (1 : ℝ) (f x₀) one_ne_zero)
  have hA (x : E) : A x = f x₀ + e (x - x₀) := by
    simp [A, Diffeomorph.coe_trans, sub_eq_add_neg, add_comm]
  have hAi (y : F) : A.symm y = x₀ + e.symm (y - f x₀) := by
    simp [A, Diffeomorph.coe_trans, Diffeomorph.symm_trans', add_comm]
  let Φ := φ.trans A
  have hΦK : EqOn Φ (fun x ↦ f x₀ + e (x - x₀)) Kᶜ := by
    intro x hx
    simp only [Φ, Diffeomorph.coe_trans, Function.comp_apply, hφK hx, id_eq, hA]
  have hΦinv : EqOn Φ.symm (fun y ↦ x₀ + e.symm (y - f x₀)) (Φ '' K)ᶜ := by
    intro y hy
    have hxK : Φ.symm y ∈ Kᶜ := fun hx ↦
      hy ⟨Φ.symm y, hx, Φ.apply_symm_apply y⟩
    have h : y = A (Φ.symm y) := by
      simpa only [hA, Φ.apply_symm_apply] using hΦK hxK
    exact ((congrArg A.symm h).trans (A.symm_apply_apply _)).symm.trans (hAi y)
  have hbound := ContDiff.exists_bound_iteratedFDeriv_pos_and_hasTemperateGrowth_of_eqOn_affine
    Φ.contDiff hK (f x₀ - e x₀)
    (e : E →L[ℝ] F) (by simpa [map_sub, sub_add_eq_add_sub, add_sub_assoc] using hΦK)
  have hibound := ContDiff.exists_bound_iteratedFDeriv_pos_and_hasTemperateGrowth_of_eqOn_affine
    Φ.symm.contDiff (hK.image Φ.continuous)
    (x₀ - e.symm (f x₀)) (e.symm : F →L[ℝ] E)
    (by simpa [map_sub, sub_add_eq_add_sub, add_sub_assoc] using hΦinv)
  refine ⟨Φ, K, hK, hKU, ?_, hΦK, hΦinv, hbound.1, hibound.1, hbound.2, hibound.2⟩
  filter_upwards [hφg] with x hx
  simp only [Φ, Diffeomorph.coe_trans, Function.comp_apply, hx, hA]
  simp [g]

end ContinuousLinearEquiv
