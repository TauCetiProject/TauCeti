/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Cauchy
public import TauCeti.Analysis.Quaternion.Cauchy.Affine
public import TauCeti.Analysis.Quaternion.Kernel

/-!
# Cauchy–Fueter boundary integrals with exterior poles

If the pole lies outside the closed integration region, the kernel is smooth and both
left and right Fueter regular throughout that region. The two-sided Cauchy theorem
therefore gives zero boundary flux for `G * eᵢ * f` when `f` is left regular, and for
`f * eᵢ * G` when `f` is right regular. The order of all three factors is essential.

We prove these statements for coordinate boxes and for affine parallelepipeds, using
the signed cofactor pullback in the latter case. The affine statements allow either
orientation. Continuity is required only on the closed region, and Fueter regularity
only pointwise in the interior; no continuous-derivative hypothesis is used. A pole
on the boundary is excluded, not treated using the kernel's totalized value there.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979),
  199–225, for the Cauchy–Fueter integral formula.
-/

public section

open Quaternion Set

namespace TauCeti

open Quaternion

/-- The left Cauchy–Fueter box boundary sum vanishes when the pole is outside the
closed box. The coefficients retain the order `G * eᵢ * f`. -/
theorem left_cauchyFueter_box_of_not_mem {a b : Fin 4 → ℝ} (hab : a ≤ b)
    {f : ℍ → ℍ} {q₀ : ℍ} (hq₀ : q₀ ∉ dq '' Icc a b)
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i)))) :
    boxBoundarySum a b (fun i x ↦
      cauchyFueterKernel (dq x) q₀ * dq (Pi.single i 1) * f (dq x)) = 0 := by
  apply cauchy_box hab (f := f) (g := fun q ↦ cauchyFueterKernel q q₀) ?_ hc ?_ hf
  · intro q hq
    exact (contDiffAt_cauchyFueterKernel (ne_of_mem_of_not_mem hq hq₀)
      (n := 0)).continuousAt.continuousWithinAt
  · rw [rightFueterOn_iff]
    rintro q ⟨x, hx, rfl⟩
    exact rightFueterAt_cauchyFueterKernel (ne_of_mem_of_not_mem
      (mem_image_of_mem dq (Ioo_subset_Icc_self (pi_univ_Ioo_subset a b hx))) hq₀)

/-- The right Cauchy–Fueter box boundary sum vanishes for an exterior pole, with
coefficients ordered `f * eᵢ * G`. -/
theorem right_cauchyFueter_box_of_not_mem {a b : Fin 4 → ℝ} (hab : a ≤ b)
    {f : ℍ → ℍ} {q₀ : ℍ} (hq₀ : q₀ ∉ dq '' Icc a b)
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i)))) :
    boxBoundarySum a b (fun i x ↦
      f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q₀) = 0 := by
  apply cauchy_box hab (g := f) (f := fun q ↦ cauchyFueterKernel q q₀) hc ?_ hf ?_
  · intro q hq
    exact (contDiffAt_cauchyFueterKernel (ne_of_mem_of_not_mem hq hq₀)
      (n := 0)).continuousAt.continuousWithinAt
  · rw [leftFueterOn_iff]
    rintro q ⟨x, hx, rfl⟩
    exact leftFueterAt_cauchyFueterKernel (ne_of_mem_of_not_mem
      (mem_image_of_mem dq (Ioo_subset_Icc_self (pi_univ_Ioo_subset a b hx))) hq₀)

/-- The left kernel-weighted signed cofactor flux on an affine parallelepiped vanishes
when the pole is outside its closure. Both orientations of the affine chart are allowed. -/
theorem left_cauchyFueter_affine_cofactor_of_not_mem
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p : Fin 4 → ℝ} {f : ℍ → ℍ} {q₀ : ℍ}
    (hq₀ : q₀ ∉ dq '' ((fun u ↦ p + L u) '' Icc 0 1))
    (hc : ContinuousOn (fun x ↦ f (dq x)) ((fun u ↦ p + L u) '' Icc 0 1))
    (hf : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      LeftFueterAt f (dq (p + L u))) :
    boxBoundarySum 0 1 (L.affineFluxPullback p (fun i x ↦
      cauchyFueterKernel (dq x) q₀ * dq (Pi.single i 1) * f (dq x))) = 0 := by
  have hK : ContinuousOn (fun q ↦ cauchyFueterKernel q q₀)
      (dq '' ((fun u ↦ p + L u) '' Icc 0 1)) := fun q hq ↦
    (contDiffAt_cauchyFueterKernel (ne_of_mem_of_not_mem hq hq₀)
      (n := 0)).continuousAt.continuousWithinAt
  have hr u (hu : u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
      RightFueterAt (fun q ↦ cauchyFueterKernel q q₀) (dq (p + L u)) :=
    rightFueterAt_cauchyFueterKernel (ne_of_mem_of_not_mem
      (mem_image_of_mem dq (mem_image_of_mem (fun u ↦ p + L u)
        (Ioo_subset_Icc_self (pi_univ_Ioo_subset 0 1 hu)))) hq₀)
  simpa only [boxBoundarySum_def, Function.comp_def, Pi.zero_def, Pi.one_def,
    dq_single, one_smul] using cauchy_affine_cofactor L p
      (hK.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)) hc hr hf

/-- The right kernel-weighted signed cofactor flux on an affine parallelepiped vanishes
for an exterior pole. The coefficient is `f * eᵢ * G`, not `G * eᵢ * f`. -/
theorem right_cauchyFueter_affine_cofactor_of_not_mem
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p : Fin 4 → ℝ} {f : ℍ → ℍ} {q₀ : ℍ}
    (hq₀ : q₀ ∉ dq '' ((fun u ↦ p + L u) '' Icc 0 1))
    (hc : ContinuousOn (fun x ↦ f (dq x)) ((fun u ↦ p + L u) '' Icc 0 1))
    (hf : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      RightFueterAt f (dq (p + L u))) :
    boxBoundarySum 0 1 (L.affineFluxPullback p (fun i x ↦
      f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q₀)) = 0 := by
  have hK : ContinuousOn (fun q ↦ cauchyFueterKernel q q₀)
      (dq '' ((fun u ↦ p + L u) '' Icc 0 1)) := fun q hq ↦
    (contDiffAt_cauchyFueterKernel (ne_of_mem_of_not_mem hq hq₀)
      (n := 0)).continuousAt.continuousWithinAt
  have hl u (hu : u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
      LeftFueterAt (fun q ↦ cauchyFueterKernel q q₀) (dq (p + L u)) :=
    leftFueterAt_cauchyFueterKernel (ne_of_mem_of_not_mem
      (mem_image_of_mem dq (mem_image_of_mem (fun u ↦ p + L u)
        (Ioo_subset_Icc_self (pi_univ_Ioo_subset 0 1 hu)))) hq₀)
  simpa only [boxBoundarySum_def, Function.comp_def, Pi.zero_def, Pi.one_def,
    dq_single, one_smul] using cauchy_affine_cofactor L p hc
      (hK.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)) hf hl

end TauCeti
