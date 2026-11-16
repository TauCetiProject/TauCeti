/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Cauchy.Concentration
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box

/-!
# The cut-off flux and the box Cauchy–Fueter formulas

Multiplying a field `F` by the radial cutoff `ψ(‖q - q₀‖ / ε)` gives the cut-off field
`cauchyFueterCutoffField`, defined in `TauCeti.Analysis.Quaternion.Cutoff`; it removes any
singularity of `F` at the pole `q₀`. That file also proves that for the left
kernel-weighted field `G(q - q₀) * eᵢ * f q` and the right field `f q * eᵢ * G(q - q₀)`,
with `f` left, respectively right, Fueter regular away from the pole, the divergence of the
cut-off field is exactly `cauchyFueterCutoffDensity ε q q₀ • f q`.

The integral identities apply the Bochner divergence theorem to these fields. Concentration
of the cutoff density and eventual agreement with the uncut field on every boundary face
then give `left_cauchyFueter_box` and `right_cauchyFueter_box`, the box representations with
normalization `1 / (2π²)`. All products retain their order, `G * eᵢ * f` on the left and
`f * eᵢ * G` on the right; these are not product-closure theorems for regular functions.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open MeasureTheory Set Filter
open scoped Quaternion Topology

namespace TauCeti

open TauCeti.Quaternion _root_.Quaternion

/-! ### The box formulas -/

/-- The divergence theorem on a box for the cut-off of a field family `F` whose cut-off
divergence is the radial density times `f` in the open box. -/
private theorem boxBoundarySum_cauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {q₀ : ℍ} {F : Fin 4 → ℍ → ℍ} {f : ℍ → ℍ}
    (hF : ∀ i, ContinuousOn (F i) (dq '' Icc a b \ {q₀}))
    (hFd : ∀ q ∈ dq '' pi univ (fun i ↦ Ioo (a i) (b i)), q ≠ q₀ →
      ∀ i, DifferentiableAt ℝ (F i) q)
    (hdiv : ∀ q ∈ dq '' pi univ (fun i ↦ Ioo (a i) (b i)),
      ∑ i : Fin 4, fderiv ℝ (cauchyFueterCutoffField ε q₀ (F i)) q (dq (Pi.single i 1)) =
        cauchyFueterCutoffDensity ε q q₀ • f q)
    (hc : ContinuousOn f (dq '' Icc a b)) :
    boxBoundarySum a b (fun i x ↦ cauchyFueterCutoffField ε q₀ (F i) (dq x)) =
      ∫ x in Icc a b, cauchyFueterCutoffDensity ε (dq x) q₀ • f (dq x) := by
  let D (i : Fin 4) (x : Fin 4 → ℝ) :=
    (fderiv ℝ (cauchyFueterCutoffField ε q₀ (F i)) (dq x)).comp dq
  have hae : (fun x ↦ ∑ i, D i x (Pi.single i 1)) =ᵐ[volume.restrict (Icc a b)]
      (fun x ↦ cauchyFueterCutoffDensity ε (dq x) q₀ • f (dq x)) := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact (ae_restrict_mem (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo).measurableSet).mono
      fun x hx ↦ hdiv _ (mem_image_of_mem _ hx)
  have hi : IntegrableOn (fun x ↦ cauchyFueterCutoffDensity ε (dq x) q₀ • f (dq x))
      (Icc a b) :=
    (integrable_cauchyFueterCutoffDensity hε q₀).integrableOn.smul_continuousOn
      (hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)) isCompact_Icc
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (fun i x ↦ cauchyFueterCutoffField ε q₀ (F i) (dq x)) D ∅ countable_empty
    (fun i ↦ (continuousOn_cauchyFueterCutoffField ε (hF i)).comp
      dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx))
    (fun x hx i ↦
      (differentiableAt_cauchyFueterCutoffField ε
        (fun hp ↦ hFd _ (mem_image_of_mem _ hx.1) hp i)).hasFDerivAt.comp x dq.hasFDerivAt)
    (hi.congr hae.symm)
  rw [integral_congr_ae hae] at h
  simpa only [boxBoundarySum_def] using h.symm

/-- The divergence theorem for the cut-off left Cauchy–Fueter field on a coordinate box.
The right side is the radial-density integral whose limit gives `2π² • f q₀` when `q₀`
lies strictly inside the box; see `tendsto_boxBoundarySum_cauchyFueterCutoffField_left`.
Regularity is required only in the punctured open box, not at the pole. -/
theorem boxBoundarySum_cauchyFueterCutoffField_left {ε : ℝ} (hε : 0 < ε)
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {q₀ : ℍ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {q₀})) :
    boxBoundarySum a b (fun i x ↦ cauchyFueterCutoffField ε q₀
        (fun q ↦ cauchyFueterKernel q q₀ * dq (Pi.single i 1) * f q) (dq x)) =
      ∫ x in Icc a b, cauchyFueterCutoffDensity ε (dq x) q₀ • f (dq x) := by
  have hf := leftFueterOn_iff.mp hf
  exact boxBoundarySum_cauchyFueterCutoffField hε hab
    (fun _ ↦ ((continuousOn_cauchyFueterKernel (notMem_sdiff_of_mem rfl)).mul
      continuousOn_const).mul (hc.mono sdiff_subset))
    (fun q hq hp _ ↦ (((contDiffAt_cauchyFueterKernel (n := 1) hp).differentiableAt
      one_ne_zero).mul_const _).mul (hf q ⟨hq, hp⟩).differentiableAt)
    (fun q hq ↦ sum_fderiv_cauchyFueterCutoffField_left (fun hp ↦ hf q ⟨hq, hp⟩)) hc

/-- The divergence theorem for the cut-off right Cauchy–Fueter field on a coordinate box,
with the coefficients ordered `f * eᵢ * G`. Regularity is required only in the punctured
open box, not at the pole. -/
theorem boxBoundarySum_cauchyFueterCutoffField_right {ε : ℝ} (hε : 0 < ε)
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {q₀ : ℍ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {q₀})) :
    boxBoundarySum a b (fun i x ↦ cauchyFueterCutoffField ε q₀
        (fun q ↦ f q * dq (Pi.single i 1) * cauchyFueterKernel q q₀) (dq x)) =
      ∫ x in Icc a b, cauchyFueterCutoffDensity ε (dq x) q₀ • f (dq x) := by
  have hf := rightFueterOn_iff.mp hf
  exact boxBoundarySum_cauchyFueterCutoffField hε hab
    (fun _ ↦ ((hc.mono sdiff_subset).mul continuousOn_const).mul
      (continuousOn_cauchyFueterKernel (notMem_sdiff_of_mem rfl)))
    (fun q hq hp _ ↦ ((hf q ⟨hq, hp⟩).differentiableAt.mul_const _).mul
      ((contDiffAt_cauchyFueterKernel (n := 1) hp).differentiableAt one_ne_zero))
    (fun q hq ↦ sum_fderiv_cauchyFueterCutoffField_right (fun hp ↦ hf q ⟨hq, hp⟩)) hc

/-- As the excised ball shrinks to an interior pole, the boundary flux of the cut-off
left field tends to `2π²` times the value of the coefficient at that pole. -/
theorem tendsto_boxBoundarySum_cauchyFueterCutoffField_left
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {dq x₀}))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    Tendsto (fun ε : ℝ ↦ boxBoundarySum a b (fun i x ↦ cauchyFueterCutoffField ε (dq x₀)
        (fun q ↦ cauchyFueterKernel q (dq x₀) * dq (Pi.single i 1) * f q) (dq x)))
      (𝓝[>] 0) (𝓝 ((2 * Real.pi ^ 2) • f (dq x₀))) := by
  have h := tendsto_integral_Icc_cauchyFueterCutoff_density
    (hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)) ha hb
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (boxBoundarySum_cauchyFueterCutoffField_left hε
    (fun i ↦ (ha i).le.trans (hb i).le) hc hf).symm

/-- As the excised ball shrinks to an interior pole, the boundary flux of the cut-off
right field tends to `2π²` times the value of the coefficient at that pole. -/
theorem tendsto_boxBoundarySum_cauchyFueterCutoffField_right
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {dq x₀}))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    Tendsto (fun ε : ℝ ↦ boxBoundarySum a b (fun i x ↦ cauchyFueterCutoffField ε (dq x₀)
        (fun q ↦ f q * dq (Pi.single i 1) * cauchyFueterKernel q (dq x₀)) (dq x)))
      (𝓝[>] 0) (𝓝 ((2 * Real.pi ^ 2) • f (dq x₀))) := by
  have h := tendsto_integral_Icc_cauchyFueterCutoff_density
    (hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)) ha hb
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (boxBoundarySum_cauchyFueterCutoffField_right hε
    (fun i ↦ (ha i).le.trans (hb i).le) hc hf).symm

/-- For an interior pole, sufficiently small cutoffs leave every boundary coefficient
unchanged. This holds for every field family, without regularity or continuity. -/
theorem eventually_boxBoundarySum_cauchyFueterCutoffField
    {a b x₀ : Fin 4 → ℝ} (F : Fin 4 → ℍ → ℍ)
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      boxBoundarySum a b (fun i x ↦ cauchyFueterCutoffField ε (dq x₀) (F i) (dq x)) =
        boxBoundarySum a b (fun i x ↦ F i (dq x)) := by
  let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv
  have he (x : Fin 4 → ℝ) : dq x = e x := congrFun coe_dq x
  let U := pi univ (fun i ↦ Ioo (a i) (b i))
  have hU : IsOpen U := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
  have hx₀ : x₀ ∈ U := Set.mem_pi.mpr (fun i _ ↦ ⟨ha i, hb i⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (e.isOpenMap U hU) (e x₀)
    (mem_image_of_mem e hx₀)
  have hdist (i : Fin 4) (c : ℝ) (hc : c = a i ∨ c = b i) (x : Fin 3 → ℝ) :
      δ ≤ ‖dq (i.insertNth c x) - dq x₀‖ := by
    by_contra hn
    have hm := hball (by simpa only [Metric.mem_ball, dist_eq_norm, he] using lt_of_not_ge hn)
    obtain ⟨y, hy, heq⟩ := hm
    have hy' : y = i.insertNth c x := e.injective heq
    have hi := (Set.mem_pi.mp hy) i (mem_univ i)
    rw [hy', Fin.insertNth_apply_same] at hi
    rcases hc with rfl | rfl
    · exact lt_irrefl _ hi.1
    · exact lt_irrefl _ hi.2
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
  simp only [boxBoundarySum_def]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  · apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    exact cauchyFueterCutoffField_of_le hε (hεδ.le.trans (hdist i (b i) (Or.inr rfl) x)) _
  · apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    exact cauchyFueterCutoffField_of_le hε (hεδ.le.trans (hdist i (a i) (Or.inl rfl) x)) _

/-- The left Cauchy–Fueter representation on a box, normalized by `1 / (2π²)`.
Continuity on the closed box and pointwise left regularity in its punctured interior
suffice; in particular no continuity of the derivative is assumed. -/
theorem left_cauchyFueter_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {dq x₀}))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ cauchyFueterKernel (dq x) (dq x₀) * dq (Pi.single i 1) * f (dq x)) := by
  have heq := tendsto_nhds_unique
    ((tendsto_boxBoundarySum_cauchyFueterCutoffField_left hc hf ha hb).congr'
      (eventually_boxBoundarySum_cauchyFueterCutoffField _ ha hb)) tendsto_const_nhds
  have hm : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  rw [← heq, smul_smul, one_div, inv_mul_cancel₀ hm, one_smul]

/-- The right Cauchy–Fueter representation on a box, normalized by `1 / (2π²)`, with `f`
to the left of the surface element and the kernel to its right. Continuity on the closed
box and pointwise right regularity in its punctured interior suffice. -/
theorem right_cauchyFueter_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {dq x₀}))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) (dq x₀)) := by
  have heq := tendsto_nhds_unique
    ((tendsto_boxBoundarySum_cauchyFueterCutoffField_right hc hf ha hb).congr'
      (eventually_boxBoundarySum_cauchyFueterCutoffField _ ha hb)) tendsto_const_nhds
  have hm : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  rw [← heq, smul_smul, one_div, inv_mul_cancel₀ hm, one_smul]

end TauCeti
