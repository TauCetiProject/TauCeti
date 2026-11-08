/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Isoperimetric
public import TauCeti.MeasureTheory.Integral.Circle.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Boundary control of finite energy on a punctured disc

A finite-energy solution of `∂ₜu = J(u) ∂ₛu` on a punctured disc has its real-direction
energy bounded by the energy of the outer boundary loop, when a constant symplectic form
uniformly tames `J` along its image. The norm comes from a fixed compatible inner product.
Finite energy means square integrability of the operator norm of the full differential;
no extension, bounded image, or boundary decay at the puncture is assumed.

The inner boundary term in the annular estimate disappears along suitable shrinking circles.
Polar integration produces these circles from finite energy. The resulting estimate is the
boundary-energy bound used in the energy-decay argument for removal of singularities.
It does not itself assert extension over the puncture.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5.
-/

public section

open Complex MeasureTheory Set
open scoped ENNReal Real RealInnerProductSpace Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- The real-direction energy of a finite-energy, uniformly tamed solution on a punctured
closed disc is bounded by its outer boundary-loop energy divided by twice the taming constant.
The map is `C²` near every point of the punctured closed disc, including its outer boundary,
and its value at the puncture is unrestricted. -/
theorem integral_norm_fderiv_one_sq_punctured_disc_le {u : ℂ → V}
    {J : V → V →L[ℝ] V} (z₀ : ℂ) {b c : ℝ}
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hb : 0 < b) (hc : 0 < c)
    (hu : ∀ z ∈ {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2)
      {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}) :
    (∫ z in {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      (∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) / (2 * c) := by
  classical
  let D := {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hE := integrableOn_norm_fderiv_one_sq_puncturedClosedDisc z₀ hu henergy
  let B (r : ℝ) := ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2
  let A (a : ℝ) := {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  have hAsub {a : ℝ} (ha : 0 < a) : A a ⊆ D := fun z hz ↦ ⟨ha.trans_le hz.1, hz.2⟩
  -- Finite plane energy supplies shrinking circles with small angular square energy.
  have hsmall {R ε : ℝ} (hR : 0 < R) (hRb : R ≤ b) (hε : 0 < ε) :
      ∃ r ∈ Ioo 0 R, B r < ε :=
    exists_integral_norm_deriv_comp_circleMap_sq_lt z₀ hR hRb hε
      (fun z hz ↦ (hu z hz).differentiableAt (by norm_num)) henergy
  -- Compare each fixed annulus with a larger one whose inner boundary energy is small.
  have hannulus {a : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      (∫ z in A a, ‖fderiv ℝ u z 1‖ ^ 2) ≤ B b / (2 * c) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨r, hr, hBr⟩ := hsmall ha hab (mul_pos (by positivity : 0 < 2 * c) hε)
    have hsub : A a ⊆ A r := fun z hz ↦ ⟨hr.2.le.trans hz.1, hz.2⟩
    have hmono := setIntegral_mono_set (hE.mono_set (hAsub hr.1))
      (ae_of_all _ fun _ ↦ sq_nonneg _) (Filter.Eventually.of_forall hsub)
    have hbound := ω.integral_norm_fderiv_one_sq_annulus_le z₀ hg hr.1
      (hr.2.le.trans hab) hc (fun z hz ↦ hu z (hAsub hr.1 hz))
      (fun z hz ↦ hCR z (hAsub hr.1 hz)) (fun z hz ↦ htame z (hAsub hr.1 hz))
    have h := hmono.trans hbound
    dsimp only [B]
    dsimp only [B] at hBr
    have hden : 0 < 2 * c := by positivity
    rw [le_div_iff₀ hden] at h
    rw [div_add' _ _ _ hden.ne', le_div_iff₀ hden]
    linarith
  -- Exhaust the punctured disc by closed annuli; square integrability justifies the limit.
  exact setIntegral_puncturedClosedDisc_le_of_forall_annulus z₀ hb hE fun a ha hab ↦
    hannulus ha hab

end TauCeti.SymplecticForm
