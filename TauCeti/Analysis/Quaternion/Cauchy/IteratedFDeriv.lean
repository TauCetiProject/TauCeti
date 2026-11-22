/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
public import TauCeti.Analysis.Quaternion.Cauchy.KernelPotential
public import TauCeti.Analysis.Quaternion.Cauchy.Representation
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Differentiated Cauchy–Fueter representations on boxes and affine parallelepipeds

This file builds on `TauCeti.Analysis.Quaternion.Cauchy.KernelPotential`,
`TauCeti.Analysis.Quaternion.Cauchy.CutoffField`, and
`TauCeti.Analysis.Quaternion.Cauchy.Representation` to differentiate the box and affine
Cauchy–Fueter integral representations:

* `TauCeti.iteratedFDeriv_left_cauchyFueter_box`,
  `TauCeti.iteratedFDeriv_right_cauchyFueter_box`,
  `TauCeti.iteratedFDeriv_left_cauchyFueter_affine`,
  `TauCeti.iteratedFDeriv_right_cauchyFueter_affine`: differentiated Cauchy–Fueter integral
  representations on coordinate boxes and positively oriented affine parallelepipeds.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 2 and Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set TauCeti.Quaternion
open scoped ContDiff Quaternion Topology

namespace TauCeti

/-! ### Differentiated Cauchy–Fueter representations on boxes and affine parallelepipeds -/

section BoundaryRepresentations

/-- Shared differentiation under `(1 / (2π²)) • boxBoundarySum` for a bilinearly weighted
Cauchy–Fueter boundary representation. -/
private theorem iteratedFDeriv_eq_smul_boxBoundarySum_bilin {a b : Fin 4 → ℝ}
    (B : ℍ →L[ℝ] ℍ →L[ℝ] ℍ) {φ : (Fin 4 → ℝ) → ℍ} (w : Fin 4 → (Fin 4 → ℝ) → ℍ)
    {f : ℍ → ℍ} {q₀ : ℍ} {δ : ℝ} (hδ : 0 < δ) (m : ℕ)
    (hfeq : f =ᶠ[𝓝 q₀] fun y ↦ (1 / (2 * Real.pi ^ 2)) •
      boxBoundarySum a b (fun i u ↦ B (cauchyFueterKernel (φ u) y) (w i u)))
    (hφ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      AEStronglyMeasurable (fun u ↦ φ (i.insertNth c u))
        (volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))))
    (hw : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ w i (i.insertNth c u))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hsep : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i → ∀ u : Fin 3 → ℝ,
      δ ≤ ‖φ (i.insertNth c u) - q₀‖) :
    iteratedFDeriv ℝ m f q₀ = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i u ↦ iteratedFDeriv ℝ m (fun y ↦ B (cauchyFueterKernel (φ u) y) (w i u)) q₀) := by
  rw [(hfeq.iteratedFDeriv ℝ m).eq_of_nhds]
  simp only [boxBoundarySum_def]
  exact B.iteratedFDeriv_smul_sum_sub_integral_bilin_cauchyFueterKernel (1 / (2 * Real.pi ^ 2))
    (fun i ↦ hφ i (Or.inr rfl)) (fun i ↦ hφ i (Or.inl rfl))
    (fun i ↦ hw i (Or.inr rfl)) (fun i ↦ hw i (Or.inl rfl))
    (fun i ↦ Eventually.of_forall (hsep i (Or.inr rfl)))
    (fun i ↦ Eventually.of_forall (hsep i (Or.inl rfl)))
    m (fun _ ↦ mem_ball_self hδ) (fun _ ↦ mem_ball_self hδ)

/-- Bilinear differentiation under the box Cauchy–Fueter boundary representation. -/
private theorem iteratedFDeriv_cauchyFueter_box_bilin {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (B : ℍ →L[ℝ] ℍ →L[ℝ] ℍ) (w : Fin 4 → (Fin 4 → ℝ) → ℍ)
    (hw : ∀ i, ContinuousOn (w i) (Icc a b))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) (m : ℕ)
    (hrep : ∀ x ∈ pi univ fun i ↦ Ioo (a i) (b i),
      f (dq x) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
        (fun i u ↦ B (cauchyFueterKernel (dq u) (dq x)) (w i u))) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i u ↦ iteratedFDeriv ℝ m
        (fun y ↦ B (cauchyFueterKernel (dq u) y) (w i u)) (dq x₀)) := by
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  obtain ⟨δ, hδ, hball, hdist⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have hfeq : f =ᶠ[𝓝 (dq x₀)] fun y ↦ (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i u ↦ B (cauchyFueterKernel (dq u) y) (w i u)) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with y hy
    obtain ⟨x, hx, rfl⟩ := hball hy
    exact hrep x hx
  refine iteratedFDeriv_eq_smul_boxBoundarySum_bilin B w hδ m hfeq
    (fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ dq _).aestronglyMeasurable)
    (fun i {c} hc ↦ ?_) hdist
  have hc' : c ∈ Icc (a i) (b i) := by
    rcases hc with rfl | rfl
    · exact left_mem_Icc.2 (hab i)
    · exact right_mem_Icc.2 (hab i)
  exact ContinuousOn.integrableOn_insertNth_Icc (hw i) i hc'

/-- Bilinear differentiation under the affine Cauchy–Fueter boundary representation. -/
private theorem iteratedFDeriv_cauchyFueter_affine_bilin
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (B : ℍ →L[ℝ] ℍ →L[ℝ] ℍ) (w : Fin 4 → (Fin 4 → ℝ) → ℍ)
    (hw : ∀ j, ContinuousOn (w j) (Icc (0 : Fin 4 → ℝ) 1))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1) (m : ℕ)
    (hrep : ∀ x : Fin 4 → ℝ, L.symm (x - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1) →
      f (dq x) = (1 / (2 * Real.pi ^ 2)) • ∑ j : Fin 4,
        ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
            B (cauchyFueterKernel (dq (p + L (j.insertNth 1 u))) (dq x))
              (w j (j.insertNth 1 u))) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1,
            B (cauchyFueterKernel (dq (p + L (j.insertNth 0 u))) (dq x))
              (w j (j.insertNth 0 u)))) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • ∑ j : Fin 4,
      ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
          iteratedFDeriv ℝ m (fun y ↦
            B (cauchyFueterKernel (dq (p + L (j.insertNth 1 u))) y)
              (w j (j.insertNth 1 u))) (dq x₀)) -
        ∫ u in Icc (0 : Fin 3 → ℝ) 1,
          iteratedFDeriv ℝ m (fun y ↦
            B (cauchyFueterKernel (dq (p + L (j.insertNth 0 u))) y)
              (w j (j.insertNth 0 u))) (dq x₀)) := by
  obtain ⟨δ, hδ, hball, hdist⟩ := exists_ball_subset_and_le_norm_affine_face (a := 0) (b := 1) hx₀
  have hfeq : f =ᶠ[𝓝 (dq x₀)] fun y ↦ (1 / (2 * Real.pi ^ 2)) •
      boxBoundarySum (0 : Fin 4 → ℝ) 1
        (fun j u ↦ B (cauchyFueterKernel (dq (p + L u)) y) (w j u)) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with y hy
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hball hy
    simpa only [boxBoundarySum_def, Function.comp_def, Pi.zero_apply, Pi.one_apply,
      ← Pi.zero_def, ← Pi.one_def] using hrep (p + L v) (by simpa using hv)
  simpa only [boxBoundarySum_def, Function.comp_def, Pi.zero_apply, Pi.one_apply,
      ← Pi.zero_def, ← Pi.one_def] using
    iteratedFDeriv_eq_smul_boxBoundarySum_bilin B (a := (0 : Fin 4 → ℝ)) (b := 1)
      (φ := fun u ↦ dq (p + L u)) w hδ m hfeq
      (fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ dq _).aestronglyMeasurable)
      (fun j {c} hc ↦ by
        have hmem : c ∈ Icc (0 : ℝ) 1 := by
          rcases hc with rfl | rfl
          · exact left_mem_Icc.2 zero_le_one
          · exact right_mem_Icc.2 zero_le_one
        exact ContinuousOn.integrableOn_insertNth_Icc (hw j) j hmem)
      hdist

/-- Differentiated left Cauchy–Fueter representation on a coordinate box: for every interior point
`x₀ ∈ ∏ i, Ioo (a i) (b i)` and order `m`, `iteratedFDeriv ℝ m f (dq x₀)` is `1 / (2π²)` times the
`boxBoundarySum` of the `m`-th pole derivative of the left Cauchy–Fueter integrand. -/
theorem iteratedFDeriv_left_cauchyFueter_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f (dq '' pi univ fun i ↦ Ioo (a i) (b i)))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) (m : ℕ) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ iteratedFDeriv ℝ m
        (fun y ↦ cauchyFueterKernel (dq x) y * dq (Pi.single i 1) * f (dq x)) (dq x₀)) := by
  simpa only [ContinuousLinearMap.mul_apply', mul_assoc] using
    iteratedFDeriv_cauchyFueter_box_bilin (ContinuousLinearMap.mul ℝ ℍ)
      (fun i x ↦ dq (Pi.single i 1) * f (dq x))
      (fun _ ↦ continuousOn_const.mul (hc.comp (by fun_prop) (mapsTo_image _ _)))
      ha hb m fun x hx ↦ by
        simpa only [ContinuousLinearMap.mul_apply', mul_assoc] using
          left_cauchyFueter_box hc (hf.mono sdiff_subset)
            (fun i ↦ (hx i (mem_univ i)).1) (fun i ↦ (hx i (mem_univ i)).2)

/-- Differentiated right Cauchy–Fueter representation on a coordinate box, preserving the factor
order `f (dq x) * eᵢ * cauchyFueterKernel (dq x) y`. -/
theorem iteratedFDeriv_right_cauchyFueter_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f (dq '' pi univ fun i ↦ Ioo (a i) (b i)))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) (m : ℕ) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ iteratedFDeriv ℝ m
        (fun y ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) y) (dq x₀)) := by
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    iteratedFDeriv_cauchyFueter_box_bilin (ContinuousLinearMap.mul ℝ ℍ).flip
      (fun i x ↦ f (dq x) * dq (Pi.single i 1))
      (fun _ ↦ (hc.comp (by fun_prop) (mapsTo_image _ _)).mul continuousOn_const)
      ha hb m fun x hx ↦ by
        simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
          right_cauchyFueter_box hc (hf.mono sdiff_subset)
            (fun i ↦ (hx i (mem_univ i)).1) (fun i ↦ (hx i (mem_univ i)).2)

/-- Differentiated left Cauchy–Fueter representation on a positively oriented affine parallelepiped,
expressed via the outward face normals `ContinuousLinearMap.affineFaceNormal`. -/
theorem iteratedFDeriv_left_cauchyFueter_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ}
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : LeftFueterOn f (dq '' ((fun u ↦ p + L u) '' pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1) (m : ℕ) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • ∑ j : Fin 4,
      ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
          iteratedFDeriv ℝ m (fun y ↦ cauchyFueterKernel (dq (p + L (j.insertNth 1 u))) y *
            ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
            f (dq (p + L (j.insertNth 1 u)))) (dq x₀)) -
        ∫ u in Icc (0 : Fin 3 → ℝ) 1,
          iteratedFDeriv ℝ m (fun y ↦ cauchyFueterKernel (dq (p + L (j.insertNth 0 u))) y *
            ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
            f (dq (p + L (j.insertNth 0 u)))) (dq x₀)) := by
  simpa only [ContinuousLinearMap.mul_apply', mul_assoc] using
    iteratedFDeriv_cauchyFueter_affine_bilin (ContinuousLinearMap.mul ℝ ℍ)
      (fun j u ↦ ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
        f (dq (p + L u)))
      (fun _ ↦ continuousOn_const.mul
        (hc.comp (by fun_prop) fun _ hu ↦ mem_image_of_mem _ (mem_image_of_mem _ hu)))
      hx₀ m fun x hvx ↦ by
        have hrep := left_cauchyFueter_affine hL hc (hf.mono sdiff_subset) hvx
        rw [hrep]
        simp only [ContinuousLinearMap.rawAffineBoundary_eq, ContinuousLinearMap.mulLeftRight_apply,
          ContinuousLinearMap.mul_apply', mul_assoc, ContinuousLinearEquiv.coe_coe]

/-- Differentiated right Cauchy–Fueter representation on a positively oriented affine
parallelepiped, preserving the factor order `f * affineFaceNormal * cauchyFueterKernel`. -/
theorem iteratedFDeriv_right_cauchyFueter_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ}
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : RightFueterOn f (dq '' ((fun u ↦ p + L u) '' pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1) (m : ℕ) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • ∑ j : Fin 4,
      ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
          iteratedFDeriv ℝ m (fun y ↦ f (dq (p + L (j.insertNth 1 u))) *
            ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
            cauchyFueterKernel (dq (p + L (j.insertNth 1 u))) y) (dq x₀)) -
        ∫ u in Icc (0 : Fin 3 → ℝ) 1,
          iteratedFDeriv ℝ m (fun y ↦ f (dq (p + L (j.insertNth 0 u))) *
            ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
            cauchyFueterKernel (dq (p + L (j.insertNth 0 u))) y) (dq x₀)) := by
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    iteratedFDeriv_cauchyFueter_affine_bilin (ContinuousLinearMap.mul ℝ ℍ).flip
      (fun j u ↦ f (dq (p + L u)) *
        ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j)
      (fun _ ↦ (hc.comp (by fun_prop) fun _ hu ↦
        mem_image_of_mem _ (mem_image_of_mem _ hu)).mul continuousOn_const)
      hx₀ m fun x hvx ↦ by
        have hrep := right_cauchyFueter_affine hL hc (hf.mono sdiff_subset) hvx
        rw [hrep]
        simp only [ContinuousLinearMap.rawAffineBoundary_eq, ContinuousLinearMap.mulLeftRight_apply,
          ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
          ContinuousLinearEquiv.coe_coe]

end BoundaryRepresentations

end TauCeti
