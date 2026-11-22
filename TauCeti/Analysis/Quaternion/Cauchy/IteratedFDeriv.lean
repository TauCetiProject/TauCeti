/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
public import TauCeti.Analysis.Quaternion.Cauchy.KernelPotential
public import TauCeti.Analysis.Quaternion.Cauchy.Representation

/-!
# Differentiated Cauchy–Fueter box-boundary potentials and representations

This file builds on `TauCeti.Analysis.Quaternion.Cauchy.KernelPotential`,
`TauCeti.Analysis.Quaternion.Cauchy.CutoffField`, and
`TauCeti.Analysis.Quaternion.Cauchy.Representation` to differentiate Cauchy–Fueter box-boundary
potentials and the box and affine Cauchy–Fueter integral representations:

* `ContinuousLinearMap.contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel`,
  `ContinuousLinearMap.iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel`,
  `TauCeti.iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_left`,
  `TauCeti.iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_right`: smoothness and iterated
  derivatives of Cauchy–Fueter box boundary potentials for general facewise integrable densities.
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

/-! ### Differentiated Cauchy–Fueter box boundary potentials -/

section BoundaryPotentials

/-- Smoothness at `q₀` of a bilinearly weighted Cauchy–Fueter kernel boundary sum over the faces
of a coordinate box, whenever the pole map is a.e. strongly measurable on each face, each face
weight is integrable on its face, and each face is positively separated from `q₀` almost
everywhere. -/
theorem _root_.ContinuousLinearMap.contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel
    {d : ℕ} {a b : Fin (d + 1) → ℝ}
    {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : G →L[ℝ] ℍ →L[ℝ] E)
    {φ : (Fin (d + 1) → ℝ) → ℍ} {w : Fin (d + 1) → (Fin (d + 1) → ℝ) → G}
    {q₀ : ℍ} {n : ℕ∞}
    (hφ : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      AEStronglyMeasurable (fun u ↦ φ (i.insertNth c u))
        (volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))))
    (hw : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ w i (i.insertNth c u))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hsep : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      ∃ δ > 0, ∀ᵐ u ∂volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)),
        δ ≤ ‖φ (i.insertNth c u) - q₀‖) :
    ContDiffAt ℝ n
      (fun q ↦ boxBoundarySum a b (fun i x ↦ B (w i x) (cauchyFueterKernel (φ x) q))) q₀ := by
  simp only [boxBoundarySum_def]
  refine ContDiffAt.sum fun i _ ↦ ?_
  have hface {c : ℝ} (hc : c = a i ∨ c = b i) :
      ContDiffAt ℝ n
        (fun q ↦ ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          B (w i (i.insertNth c u)) (cauchyFueterKernel (φ (i.insertNth c u)) q)) q₀ := by
    obtain ⟨δ, hδ₀, hδ⟩ := hsep i hc
    simpa only [ContinuousLinearMap.flip_apply] using
      contDiffAt_integral_bilin_cauchyFueterKernel (n := n) B.flip
        (hφ i hc) (hw i hc) hδ (mem_ball_self hδ₀)
  exact (hface (Or.inr rfl)).sub (hface (Or.inl rfl))

/-- Differentiating a bilinearly weighted Cauchy–Fueter kernel boundary sum over the faces of a
coordinate box at any point `q₀` positively separated almost everywhere from each face. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel
    {d : ℕ} {a b : Fin (d + 1) → ℝ}
    {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : G →L[ℝ] ℍ →L[ℝ] E)
    {φ : (Fin (d + 1) → ℝ) → ℍ} {w : Fin (d + 1) → (Fin (d + 1) → ℝ) → G}
    {q₀ : ℍ} (m : ℕ)
    (hφ : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      AEStronglyMeasurable (fun u ↦ φ (i.insertNth c u))
        (volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))))
    (hw : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ w i (i.insertNth c u))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hsep : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      ∃ δ > 0, ∀ᵐ u ∂volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)),
        δ ≤ ‖φ (i.insertNth c u) - q₀‖) :
    iteratedFDeriv ℝ m
        (fun q ↦ boxBoundarySum a b (fun i x ↦ B (w i x) (cauchyFueterKernel (φ x) q))) q₀ =
      boxBoundarySum a b
        (fun i x ↦ (B (w i x)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (cauchyFueterKernel (φ x)) q₀)) := by
  choose δ₁ hδ₁₀ hδ₁ using fun i ↦ hsep i (Or.inr rfl)
  choose δ₀ hδ₀₀ hδ₀ using fun i ↦ hsep i (Or.inl rfl)
  have h := B.flip.iteratedFDeriv_smul_sum_sub_integral_bilin_cauchyFueterKernel
    (ι := Fin (d + 1)) (α := fun _ ↦ Fin d → ℝ)
    (μ := fun i ↦ volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) 1
    (φ₁ := fun i u ↦ φ (i.insertNth (b i) u)) (φ₀ := fun i u ↦ φ (i.insertNth (a i) u))
    (fun i ↦ hφ i (Or.inr rfl)) (fun i ↦ hφ i (Or.inl rfl))
    (w₁ := fun i u ↦ w i (i.insertNth (b i) u)) (w₀ := fun i u ↦ w i (i.insertNth (a i) u))
    (fun i ↦ hw i (Or.inr rfl)) (fun i ↦ hw i (Or.inl rfl))
    hδ₁ hδ₀ m (fun i ↦ mem_ball_self (hδ₁₀ i)) (fun i ↦ mem_ball_self (hδ₀₀ i))
  simp only [one_smul, ContinuousLinearMap.flip_apply] at h
  simp only [boxBoundarySum_def]
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hface {c : ℝ} {δ : ℝ} (hδ_pos : 0 < δ)
      (hδ_ae : ∀ᵐ u ∂volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)),
        δ ≤ ‖φ (i.insertNth c u) - q₀‖) :
      ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          iteratedFDeriv ℝ m
            (fun y ↦ B (w i (i.insertNth c u)) (cauchyFueterKernel (φ (i.insertNth c u)) y)) q₀ =
        ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          (B (w i (i.insertNth c u))).compContinuousMultilinearMap
            (iteratedFDeriv ℝ m (cauchyFueterKernel (φ (i.insertNth c u))) q₀) := by
    refine integral_congr_ae ?_
    filter_upwards [hδ_ae] with u hu
    have hne : φ (i.insertNth c u) ≠ q₀ := sub_ne_zero.mp (norm_pos_iff.mp (hδ_pos.trans_le hu))
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_flip] using
      iteratedFDeriv_bilin_cauchyFueterKernel B.flip hne (w i (i.insertNth c u)) m
  rw [hface (hδ₁₀ i) (hδ₁ i), hface (hδ₀₀ i) (hδ₀ i)]

private theorem exists_pos_ae_le_norm_dq_insertNth_sub {a b : Fin 4 → ℝ} {q₀ : ℍ}
    (hq₀ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), dq (i.insertNth c u) ≠ q₀)
    (i : Fin 4) {c : ℝ} (hc : c = a i ∨ c = b i) :
    ∃ δ > 0, ∀ᵐ u ∂volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)),
      δ ≤ ‖dq (i.insertNth c u) - q₀‖ := by
  obtain ⟨δ, hδ₀, hδ⟩ := exists_pos_le_norm_dq_insertNth_sub (hq₀ i hc)
  exact ⟨δ, hδ₀, (ae_restrict_mem measurableSet_Icc).mono hδ⟩

/-- Differentiating the left Cauchy–Fueter box boundary potential at any point `q₀` off the eight
closed faces of a coordinate box, for any facewise integrable boundary density `g`. -/
theorem iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_left
    {a b : Fin 4 → ℝ} {g : ℍ → ℍ} {q₀ : ℍ} (m : ℕ)
    (hg : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ g (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hq₀ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), dq (i.insertNth c u) ≠ q₀) :
    iteratedFDeriv ℝ m
        (fun q ↦ boxBoundarySum a b
          (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * g (dq x))) q₀ =
      boxBoundarySum a b
        (fun i x ↦ MulOpposite.op (dq (Pi.single i 1) * g (dq x)) •
          iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀) := by
  have h :=
    ContinuousLinearMap.iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel
      ((ContinuousLinearMap.mul ℝ ℍ).flip) (a := a) (b := b)
      (φ := dq) (w := fun i x ↦ dq (Pi.single i 1) * g (dq x)) (q₀ := q₀) m
      (fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ dq _).aestronglyMeasurable)
      (fun i _ hc ↦ (hg i hc).const_mul _)
      (fun i _ hc ↦ exists_pos_ae_le_norm_dq_insertNth_sub hq₀ i hc)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h
  have hfn :
      (fun i x ↦ ((ContinuousLinearMap.mul ℝ ℍ).flip (dq (Pi.single i 1) * g (dq x)))
        |>.compContinuousMultilinearMap (iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀)) =
      fun i x ↦ MulOpposite.op (dq (Pi.single i 1) * g (dq x)) •
        iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀ := by
    funext i x
    refine ContinuousMultilinearMap.ext fun v ↦ ?_
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, MulOpposite.smul_eq_mul_unop]
  simp only [mul_assoc]
  rw [h, hfn]

/-- Differentiating the right Cauchy–Fueter box boundary potential at any point `q₀` off the eight
closed faces of a coordinate box, for any facewise integrable boundary density `g`. -/
theorem iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_right
    {a b : Fin 4 → ℝ} {g : ℍ → ℍ} {q₀ : ℍ} (m : ℕ)
    (hg : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ g (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hq₀ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), dq (i.insertNth c u) ≠ q₀) :
    iteratedFDeriv ℝ m
        (fun q ↦ boxBoundarySum a b
          (fun i x ↦ g (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)) q₀ =
      boxBoundarySum a b
        (fun i x ↦ (g (dq x) * dq (Pi.single i 1)) •
          iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀) := by
  have h := (ContinuousLinearMap.mul ℝ ℍ).iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel
    (a := a) (b := b)
    (φ := dq) (w := fun i x ↦ g (dq x) * dq (Pi.single i 1)) (q₀ := q₀) m
    (fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ dq _).aestronglyMeasurable)
    (fun i _ hc ↦ (hg i hc).mul_const _)
    (fun i _ hc ↦ exists_pos_ae_le_norm_dq_insertNth_sub hq₀ i hc)
  simp only [ContinuousLinearMap.mul_apply'] at h
  have hfn :
      (fun i x ↦ (ContinuousLinearMap.mul ℝ ℍ (g (dq x) * dq (Pi.single i 1)))
        |>.compContinuousMultilinearMap (iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀)) =
      fun i x ↦ (g (dq x) * dq (Pi.single i 1)) •
        iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀ := by
    funext i x
    refine ContinuousMultilinearMap.ext fun v ↦ ?_
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, smul_eq_mul]
  rw [h, hfn]

end BoundaryPotentials

/-! ### Differentiated Cauchy–Fueter representations on boxes and affine parallelepipeds -/

section BoundaryRepresentations

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
  have hface_int (i : Fin 4) {c : ℝ} (hc' : c ∈ Icc (a i) (b i)) :
      IntegrableOn (fun u : Fin 3 → ℝ ↦ w i (i.insertNth c u))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    ((hw i).comp (by fun_prop) fun u hu ↦
      Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩).integrableOn_compact isCompact_Icc
  rw [(hfeq.iteratedFDeriv ℝ m).eq_of_nhds]
  simp only [boxBoundarySum_def]
  exact B.iteratedFDeriv_smul_sum_sub_integral_bilin_cauchyFueterKernel _
    (fun _ ↦ Continuous.aestronglyMeasurable (by fun_prop))
    (fun _ ↦ Continuous.aestronglyMeasurable (by fun_prop))
    (fun i ↦ hface_int i (right_mem_Icc.2 (hab i)))
    (fun i ↦ hface_int i (left_mem_Icc.2 (hab i)))
    (fun i ↦ Eventually.of_forall (hdist i _ (Or.inr rfl)))
    (fun i ↦ Eventually.of_forall (hdist i _ (Or.inl rfl))) m
    (fun _ ↦ mem_ball_self hδ) (fun _ ↦ mem_ball_self hδ)

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
  have hfeq : f =ᶠ[𝓝 (dq x₀)] fun y ↦ (1 / (2 * Real.pi ^ 2)) • ∑ j : Fin 4,
      ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
          B (cauchyFueterKernel (dq (p + L (j.insertNth 1 u))) y)
            (w j (j.insertNth 1 u))) -
        ∫ u in Icc (0 : Fin 3 → ℝ) 1,
          B (cauchyFueterKernel (dq (p + L (j.insertNth 0 u))) y)
            (w j (j.insertNth 0 u))) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with y hy
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hball hy
    exact hrep (p + L v) (by simpa using hv)
  have hface_int (j : Fin 4) {c : ℝ} (hmem : c ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (fun u : Fin 3 → ℝ ↦ w j (j.insertNth c u)) (Icc 0 1) :=
    ((hw j).comp (by fun_prop) fun u hu ↦
      Fin.insertNth_mem_Icc.mpr ⟨hmem, hu⟩).integrableOn_compact isCompact_Icc
  rw [(hfeq.iteratedFDeriv ℝ m).eq_of_nhds]
  exact B.iteratedFDeriv_smul_sum_sub_integral_bilin_cauchyFueterKernel
    (μ := fun _ ↦ volume.restrict (Icc (0 : Fin 3 → ℝ) 1)) _
    (fun _ ↦ Continuous.aestronglyMeasurable (by fun_prop))
    (fun _ ↦ Continuous.aestronglyMeasurable (by fun_prop))
    (fun j ↦ hface_int j (right_mem_Icc.2 zero_le_one))
    (fun j ↦ hface_int j (left_mem_Icc.2 zero_le_one))
    (fun j ↦ Eventually.of_forall (hdist j _ (Or.inr rfl)))
    (fun j ↦ Eventually.of_forall (hdist j _ (Or.inl rfl))) m
    (fun _ ↦ mem_ball_self hδ) (fun _ ↦ mem_ball_self hδ)

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
