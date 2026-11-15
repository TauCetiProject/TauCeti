/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.Quaternion.Analytic
public import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
public import TauCeti.Analysis.Quaternion.Cauchy.Representation
public import TauCeti.Analysis.Quaternion.Harmonic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Connected.Clopen
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Analysis.Analytic.Basic
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Quaternion.Reflection

/-!
# Real analyticity, harmonicity, and uniqueness of Fueter regular functions

Every pointwise left or right Fueter regular function on an open subset of `ℍ` is real analytic,
smooth of every order, and harmonic, and satisfies the four-dimensional analytic uniqueness
principle.

## Quantitative power-series radius

Let `f : ℍ → ℍ` be continuous on a positively oriented affine parallelepiped `C = p + L([0, 1]⁴)`
(or a coordinate box `Icc a b`) and pointwise left or right Fueter regular on its open interior.
For any interior point `q₀ = dq x₀` whose Euclidean distance to each of the eight boundary faces
is at least `δ > 0`, the open ball `eball q₀ ((√2 - 1) δ)` lies strictly inside the open
parallelepiped (because `(√2 - 1) δ < δ` prevents the segment `[q₀, q]` from meeting any boundary
face). On that ball `f` coincides with its Cauchy–Fueter boundary integral
(`TauCeti.left_cauchyFueter_affine`, `TauCeti.right_cauchyFueter_affine`), whose eight compact
face potentials expand into convergent power series on `eball q₀ ((√2 - 1) δ)` by
`TauCeti.hasFPowerSeriesOnBall_sum_integral_cauchyFueterKernel_mul`. Symmetrizing via
`HasFPowerSeriesOnBall.inv_factorial_smul_iteratedFDeriv` yields the canonical Taylor expansion
`n ↦ (n!)⁻¹ • iteratedFDeriv ℝ n f q₀` on `eball q₀ ((√2 - 1) δ)` without reference to any
auxiliary derivative bounds.

## Smoothness, harmonicity, and uniqueness

Choosing a small coordinate cube around each interior point upgrades pointwise Fueter regularity
on a neighbourhood of `q` to `AnalyticAt ℝ f q`, hence `ContDiffAt ℝ n f q` for every `n`. Feeding
second-order differentiability into `TauCeti.LeftFueterOn.laplacian_eq_zero` removes the `C²`
hypothesis from harmonicity, yielding `Δ f q = 0` and `InnerProductSpace.HarmonicOnNhd f s` on
every open set `s`.

Real analyticity also gives the uniqueness principle
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`): two regular functions on a preconnected
open set `s` that agree near one point (in particular, on a nonempty open subset `u ⊆ s`, or to
infinite order `∀ m, iteratedFDeriv ℝ m f q₀ = iteratedFDeriv ℝ m g q₀` at a single point
`q₀ ∈ s`) coincide throughout `s`. By contrast with one-variable complex analysis, an accumulating
zero set does not force a regular function to vanish: `q ↦ t + i x` is both left and right regular
on all of `ℍ` and vanishes on the two-dimensional subspace `{q | q.re = 0 ∧ q.imI = 0}`.

## Main declarations

* `TauCeti.LeftFueterOn.hasFPowerSeriesOnBall_affine`,
  `TauCeti.RightFueterOn.hasFPowerSeriesOnBall_affine`,
  `TauCeti.LeftFueterOn.hasFPowerSeriesOnBall_box`,
  `TauCeti.RightFueterOn.hasFPowerSeriesOnBall_box`: quantitative Taylor expansion on
  `eball (dq x₀) ((√2 - 1) δ)`.
* `TauCeti.LeftFueterOn.analyticAt`, `TauCeti.LeftFueterOn.analyticOnNhd`,
  `TauCeti.LeftFueterOn.contDiffAt`, `TauCeti.LeftFueterOn.contDiffOn` (and right counterparts):
  real analyticity and smoothness of Fueter regular functions.
* `TauCeti.LeftFueterOn.laplacian_eq_zero_of_mem_nhds`,
  `TauCeti.LeftFueterOn.laplacian_eq_zero_of_isOpen`,
  `TauCeti.LeftFueterOn.harmonicAt`, `TauCeti.LeftFueterOn.harmonicOnNhd` (and right counterparts):
  unconditional harmonicity of Fueter regular functions.
* `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq`,
  `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_eqOn_isOpen`,
  `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_iteratedFDeriv_eq` (and right counterparts):
  analytic uniqueness principles from neighbourhood agreement or a single infinite jet.
* `TauCeti.exists_leftFueterOn_and_rightFueterOn_univ_eqOn_zero_accPt`: nonconstant regular
  function vanishing on a codimension-two subspace of accumulation points.

## References

* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, equation (17), Theorem 9, and the remark on p. 10.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set Topology TauCeti.Quaternion
open scoped Laplacian

namespace TauCeti

/-! ### Segment exit lemma and 8-face potential expansion -/

/-- If `u₀` lies in the open box `∏ i, Ioo (a i) (b i)` and every facet image under
`v ↦ dq (p + M v)` sits at distance at least `δ` from `dq (p + M u₀)`, then any `u` with
`‖dq (p + M u) - dq (p + M u₀)‖ < δ` also lies in `∏ i, Ioo (a i) (b i)` (otherwise the segment
`[u₀, u]` meets a facet at distance `t * ‖dq (p + M u) - dq (p + M u₀)‖ < δ`). -/
private theorem mem_pi_Ioo_of_norm_dq_sub_lt {a b p u₀ u : Fin 4 → ℝ}
    (M : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ)
    (ha : ∀ i, a i < u₀ i) (hb : ∀ i, u₀ i < b i)
    {δ : ℝ} (hδ : ∀ (j : Fin 4) {c : ℝ}, (c = a j ∨ c = b j) →
      ∀ w ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
        δ ≤ ‖dq (p + M (j.insertNth c w)) - dq (p + M u₀)‖)
    (hu_lt : ‖dq (p + M u) - dq (p + M u₀)‖ < δ) :
    u ∈ pi univ fun i ↦ Ioo (a i) (b i) := by
  by_contra hu
  have hmem_bd : ∃ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • u₀ + t • u ∈ Icc a b ∧ (1 - t) • u₀ + t • u ∉ pi univ fun i ↦ Ioo (a i) (b i) := by
    by_cases hu_icc : u ∈ Icc a b
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [sub_self, zero_smul, one_smul, zero_add]
      exact ⟨hu_icc, hu⟩
    · have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
        Subtype.preconnectedSpace (convex_Icc 0 1).isPreconnected
      let γ : Icc (0 : ℝ) 1 → Fin 4 → ℝ := fun t ↦ (1 - t.1) • u₀ + t.1 • u
      have hγ : Continuous γ := by fun_prop
      have h0 : (⟨0, left_mem_Icc.2 zero_le_one⟩ : Icc (0 : ℝ) 1) ∈ γ ⁻¹' Icc a b := by
        simpa [γ] using ⟨fun i ↦ (ha i).le, fun i ↦ (hb i).le⟩
      have h1 : (⟨1, right_mem_Icc.2 zero_le_one⟩ : Icc (0 : ℝ) 1) ∉ γ ⁻¹' Icc a b := by
        simpa [γ] using hu_icc
      obtain ⟨τ, hτ⟩ := nonempty_frontier_iff.2 ⟨⟨_, h0⟩, fun hall ↦ h1 (hall ▸ mem_univ _)⟩
      have hfr : γ τ ∈ frontier (Icc a b) := hγ.frontier_preimage_subset (Icc a b) hτ
      have hopen : IsOpen (pi univ fun i ↦ Ioo (a i) (b i)) :=
        isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
      have hsub : (pi univ fun i ↦ Ioo (a i) (b i)) ⊆ interior (Icc a b) :=
        hopen.subset_interior_iff.2 fun x hx ↦
          ⟨fun i ↦ (hx i (mem_univ i)).1.le, fun i ↦ (hx i (mem_univ i)).2.le⟩
      exact ⟨τ.1, τ.2, (isClosed_Icc (a := a) (b := b)).closure_eq ▸ hfr.1,
        fun hin ↦ hfr.2 (hsub hin)⟩
  obtain ⟨t, ht, hv_icc, hv_not⟩ := hmem_bd
  set v := (1 - t) • u₀ + t • u
  have hv_ex : ∃ j : Fin 4, v j ∉ Ioo (a j) (b j) := by
    by_contra! hall
    exact hv_not fun j _ ↦ hall j
  obtain ⟨j, hj⟩ := hv_ex
  have hc : v j = a j ∨ v j = b j := by
    by_cases h1 : v j = a j
    · exact Or.inl h1
    · exact Or.inr (le_antisymm (hv_icc.2 j)
        (not_lt.1 fun hlt ↦ hj ⟨lt_of_le_of_ne' (hv_icc.1 j) h1, hlt⟩))
  have hseg : (1 - t) • u₀ + t • u = j.insertNth (v j) (j.removeNth v) :=
    (j.insertNth_self_removeNth v).symm
  have hw : j.removeNth v ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove) :=
    ⟨fun r ↦ hv_icc.1 (j.succAbove r), fun r ↦ hv_icc.2 (j.succAbove r)⟩
  have hlin : dq (p + M (j.insertNth (v j) (j.removeNth v))) - dq (p + M u₀) =
      t • (dq (p + M u) - dq (p + M u₀)) := by
    rw [← hseg, M.map_add, M.map_smul, M.map_smul]
    have hp_id : p + ((1 - t) • M u₀ + t • M u) = (1 - t) • (p + M u₀) + t • (p + M u) := by
      ext i; simp [Pi.add_apply, Pi.smul_apply]; ring
    rw [hp_id, map_add, map_smul, map_smul]
    module
  have hle : δ ≤ ‖t • (dq (p + M u) - dq (p + M u₀))‖ := hlin ▸ hδ j hc _ hw
  rw [norm_smul, Real.norm_of_nonneg ht.1] at hle
  have hlt : t * ‖dq (p + M u) - dq (p + M u₀)‖ < δ :=
    (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans_lt (by simpa using hu_lt)
  exact not_lt_of_ge hle hlt

/-- A continuous quaternion-valued density on `Icc a b` in `ℝ³` is integrable against the subtype
pullback of Lebesgue measure. -/
private theorem integrable_subtype_comap_Icc {a b : Fin 3 → ℝ} {g : (Fin 3 → ℝ) → ℍ}
    (hg : ContinuousOn g (Icc a b)) :
    Integrable (fun z : Icc a b ↦ g z.1) (Measure.comap Subtype.val volume) := by
  have : IsFiniteMeasure (Measure.comap (Subtype.val : Icc a b → Fin 3 → ℝ) volume) := by
    refine ⟨?_⟩
    rw [Measure.comap_apply _ Subtype.val_injective
      (fun _ hs ↦ measurableSet_Icc.subtype_image hs) _ MeasurableSet.univ,
      image_univ, Subtype.range_coe]
    exact isCompact_Icc.measure_lt_top
  exact hg.domRestrict.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- Power-series expansion on `eball q₀ ((√2 - 1) δ)` of a single compact `Icc` face left
Cauchy–Fueter potential. -/
private theorem exists_hasFPowerSeriesOnBall_setIntegral_Icc_left
    {a b : Fin 3 → ℝ} {φ g : (Fin 3 → ℝ) → ℍ}
    (hφ : ContinuousOn φ (Icc a b)) (hg : ContinuousOn g (Icc a b))
    {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ) (hδ : ∀ u ∈ Icc a b, δ ≤ ‖φ u - q₀‖) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall (fun q ↦ ∫ u in Icc a b, cauchyFueterKernel (φ u) q * g u)
        P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  let φ' : C(Icc a b, ℍ) := ⟨fun z ↦ φ z.1, hφ.domRestrict⟩
  have hne : ∀ z : Icc a b, φ z.1 ≠ q₀ := fun z heq ↦ by
    have hle := hδ z.1 z.2
    rw [heq, sub_self, norm_zero] at hle
    linarith
  refine ⟨_, (hasFPowerSeriesOnBall_integral_cauchyFueterKernel_mul φ' hne hδ₀
    (fun z ↦ hδ z.1 z.2) (integrable_subtype_comap_Icc hg)).congr fun q _ ↦ ?_⟩
  exact integral_subtype_comap measurableSet_Icc fun u ↦ cauchyFueterKernel (φ u) q * g u

/-- Power-series expansion on `eball q₀ ((√2 - 1) δ)` of a single compact `Icc` face right
Cauchy–Fueter potential. -/
private theorem exists_hasFPowerSeriesOnBall_setIntegral_Icc_right
    {a b : Fin 3 → ℝ} {φ g : (Fin 3 → ℝ) → ℍ}
    (hφ : ContinuousOn φ (Icc a b)) (hg : ContinuousOn g (Icc a b))
    {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ) (hδ : ∀ u ∈ Icc a b, δ ≤ ‖φ u - q₀‖) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall (fun q ↦ ∫ u in Icc a b, g u * cauchyFueterKernel (φ u) q)
        P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  let φ' : C(Icc a b, ℍ) := ⟨fun z ↦ φ z.1, hφ.domRestrict⟩
  have hne : ∀ z : Icc a b, φ z.1 ≠ q₀ := fun z heq ↦ by
    have hle := hδ z.1 z.2
    rw [heq, sub_self, norm_zero] at hle
    linarith
  refine ⟨_, (hasFPowerSeriesOnBall_integral_mul_cauchyFueterKernel φ' hne hδ₀
    (fun z ↦ hδ z.1 z.2) (integrable_subtype_comap_Icc hg)).congr fun q _ ↦ ?_⟩
  exact integral_subtype_comap measurableSet_Icc fun u ↦ g u * cauchyFueterKernel (φ u) q

/-- Any quaternion `q ∈ eball (dq x₀) ((√2 - 1) δ)` (`δ > 0`) is of the form `dq x` with
`‖dq x - dq x₀‖ < δ`. -/
private theorem exists_dq_eq_and_norm_sub_lt_of_mem_eball {x₀ : Fin 4 → ℝ} {q : ℍ} {δ : ℝ}
    (hδ₀ : 0 < δ)
    (hq : q ∈ Metric.eball (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ))) :
    ∃ x : Fin 4 → ℝ, dq x = q ∧ ‖dq x - dq x₀‖ < δ := by
  let x := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q
  have hqx : dq x = q := by simp [x, coe_dq]
  refine ⟨x, hqx, ?_⟩
  have h1 : ‖q - dq x₀‖ < (Real.sqrt 2 - 1) * δ := by
    rwa [Metric.mem_eball, edist_dist, dist_eq_norm,
      ENNReal.ofReal_lt_ofReal_iff (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)] at hq
  rw [hqx]
  nlinarith [Real.sqrt_two_lt_three_halves]

/-! ### Quantitative Taylor expansion on affine parallelepipeds and boxes -/

/-- Quantitative Taylor power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` of a function
continuous on a positively oriented affine parallelepiped and left Fueter regular on its interior,
whose eight boundary faces all lie at Euclidean distance at least `δ > 0` from `dq x₀`. -/
theorem LeftFueterOn.hasFPowerSeriesOnBall_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ}
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : LeftFueterOn f (dq '' ((fun u ↦ p + L u) '' pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ (j : Fin 4) {c : ℝ}, (c = 0 ∨ c = 1) →
      ∀ u ∈ Icc (0 : Fin 3 → ℝ) 1, δ ≤ ‖dq (p + L (j.insertNth c u)) - dq x₀‖) :
    HasFPowerSeriesOnBall f (fun n ↦ (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hface_cont (j : Fin 4) (c : ℝ) (hc' : c ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (fun u : Fin 3 → ℝ ↦
        ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
          f (dq (p + L (j.insertNth c u)))) (Icc 0 1) := by
    refine continuousOn_const.mul (hc.comp (by fun_prop) fun u hu ↦ ?_)
    exact mem_image_of_mem _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩))
  choose P₁ hP₁ using fun j : Fin 4 ↦ exists_hasFPowerSeriesOnBall_setIntegral_Icc_left
    (a := 0) (b := 1) (φ := fun u ↦ dq (p + L (j.insertNth 1 u)))
    (by fun_prop) (hface_cont j 1 (right_mem_Icc.2 zero_le_one)) hδ₀ (hδ j (Or.inr rfl))
  choose P₀ hP₀ using fun j : Fin 4 ↦ exists_hasFPowerSeriesOnBall_setIntegral_Icc_left
    (a := 0) (b := 1) (φ := fun u ↦ dq (p + L (j.insertNth 0 u)))
    (by fun_prop) (hface_cont j 0 (left_mem_Icc.2 zero_le_one)) hδ₀ (hδ j (Or.inl rfl))
  have hsum := Finset.univ.hasFPowerSeriesOnBall_fun_sum
    (ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀))
    fun j _ ↦ (hP₁ j).sub (hP₀ j)
  refine ((hsum.const_smul (c := (1 / (2 * Real.pi ^ 2) : ℝ))).congr
    fun q hq ↦ ?_).inv_factorial_smul_iteratedFDeriv
  obtain ⟨x, rfl, hlt⟩ := exists_dq_eq_and_norm_sub_lt_of_mem_eball hδ₀ hq
  have hmem : L.symm (x - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1 :=
    mem_pi_Ioo_of_norm_dq_sub_lt (a := 0) (b := 1) (p := p) L.toLinearMap
      (fun i ↦ (hx₀ i (mem_univ i)).1) (fun i ↦ (hx₀ i (mem_univ i)).2)
      (by simpa using hδ) (by simpa using hlt)
  rw [left_cauchyFueter_affine (x₀ := x) hL hc
    (fun u hu _ ↦ leftFueterOn_iff.mp hf _ (mem_image_of_mem _ (mem_image_of_mem _ hu))) hmem]
  simp only [Pi.smul_apply, Pi.sub_apply, ContinuousLinearMap.rawAffineBoundary_eq,
    ContinuousLinearMap.mulLeftRight_apply, mul_assoc, ContinuousLinearEquiv.coe_coe]

/-- Quantitative Taylor power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` of a function
continuous on a positively oriented affine parallelepiped and right Fueter regular on its
interior. -/
theorem RightFueterOn.hasFPowerSeriesOnBall_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ}
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : RightFueterOn f (dq '' ((fun u ↦ p + L u) '' pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ (j : Fin 4) {c : ℝ}, (c = 0 ∨ c = 1) →
      ∀ u ∈ Icc (0 : Fin 3 → ℝ) 1, δ ≤ ‖dq (p + L (j.insertNth c u)) - dq x₀‖) :
    HasFPowerSeriesOnBall f (fun n ↦ (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hface_cont (j : Fin 4) (c : ℝ) (hc' : c ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (fun u : Fin 3 → ℝ ↦
        f (dq (p + L (j.insertNth c u))) *
          ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) (Icc 0 1) := by
    refine (hc.comp (by fun_prop) fun u hu ↦ ?_).mul continuousOn_const
    exact mem_image_of_mem _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩))
  choose P₁ hP₁ using fun j : Fin 4 ↦ exists_hasFPowerSeriesOnBall_setIntegral_Icc_right
    (a := 0) (b := 1) (φ := fun u ↦ dq (p + L (j.insertNth 1 u)))
    (by fun_prop) (hface_cont j 1 (right_mem_Icc.2 zero_le_one)) hδ₀ (hδ j (Or.inr rfl))
  choose P₀ hP₀ using fun j : Fin 4 ↦ exists_hasFPowerSeriesOnBall_setIntegral_Icc_right
    (a := 0) (b := 1) (φ := fun u ↦ dq (p + L (j.insertNth 0 u)))
    (by fun_prop) (hface_cont j 0 (left_mem_Icc.2 zero_le_one)) hδ₀ (hδ j (Or.inl rfl))
  have hsum := Finset.univ.hasFPowerSeriesOnBall_fun_sum
    (ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀))
    fun j _ ↦ (hP₁ j).sub (hP₀ j)
  refine ((hsum.const_smul (c := (1 / (2 * Real.pi ^ 2) : ℝ))).congr
    fun q hq ↦ ?_).inv_factorial_smul_iteratedFDeriv
  obtain ⟨x, rfl, hlt⟩ := exists_dq_eq_and_norm_sub_lt_of_mem_eball hδ₀ hq
  have hmem : L.symm (x - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1 :=
    mem_pi_Ioo_of_norm_dq_sub_lt (a := 0) (b := 1) (p := p) L.toLinearMap
      (fun i ↦ (hx₀ i (mem_univ i)).1) (fun i ↦ (hx₀ i (mem_univ i)).2)
      (by simpa using hδ) (by simpa using hlt)
  rw [right_cauchyFueter_affine (x₀ := x) hL hc
    (fun u hu _ ↦ rightFueterOn_iff.mp hf _ (mem_image_of_mem _ (mem_image_of_mem _ hu))) hmem]
  simp only [Pi.smul_apply, Pi.sub_apply, ContinuousLinearMap.rawAffineBoundary_eq,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearEquiv.coe_coe]

/-- Quantitative Taylor power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` of a function
continuous on a coordinate box `Icc a b` and left Fueter regular on its open interior, when every
face sits at Euclidean distance at least `δ > 0` from `dq x₀`. -/
theorem LeftFueterOn.hasFPowerSeriesOnBall_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f (dq '' pi univ fun i ↦ Ioo (a i) (b i)))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ (i : Fin 4) {c : ℝ}, (c = a i ∨ c = b i) →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), δ ≤ ‖dq (i.insertNth c u) - dq x₀‖) :
    HasFPowerSeriesOnBall f (fun n ↦ (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  have hface_cont (i : Fin 4) {c : ℝ} (hc' : c ∈ Icc (a i) (b i)) :
      ContinuousOn (fun u : Fin 3 → ℝ ↦ dq (Pi.single i 1) * f (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    refine continuousOn_const.mul (hc.comp (by fun_prop) fun u hu ↦ ?_)
    exact mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩)
  choose P₁ hP₁ using fun i : Fin 4 ↦ exists_hasFPowerSeriesOnBall_setIntegral_Icc_left
    (a := a ∘ i.succAbove) (b := b ∘ i.succAbove) (φ := fun u ↦ dq (i.insertNth (b i) u))
    (by fun_prop) (hface_cont i (right_mem_Icc.2 (hab i))) hδ₀ (hδ i (Or.inr rfl))
  choose P₀ hP₀ using fun i : Fin 4 ↦ exists_hasFPowerSeriesOnBall_setIntegral_Icc_left
    (a := a ∘ i.succAbove) (b := b ∘ i.succAbove) (φ := fun u ↦ dq (i.insertNth (a i) u))
    (by fun_prop) (hface_cont i (left_mem_Icc.2 (hab i))) hδ₀ (hδ i (Or.inl rfl))
  have hsum := Finset.univ.hasFPowerSeriesOnBall_fun_sum
    (ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀))
    fun i _ ↦ (hP₁ i).sub (hP₀ i)
  refine ((hsum.const_smul (c := (1 / (2 * Real.pi ^ 2) : ℝ))).congr
    fun q hq ↦ ?_).inv_factorial_smul_iteratedFDeriv
  obtain ⟨x, rfl, hlt⟩ := exists_dq_eq_and_norm_sub_lt_of_mem_eball hδ₀ hq
  have hmem := mem_pi_Ioo_of_norm_dq_sub_lt (a := a) (b := b) (p := 0) LinearMap.id ha hb
    (by simpa using hδ) (by simpa using hlt)
  rw [left_cauchyFueter_box (x₀ := x) hc
    (hf.mono sdiff_subset) (fun i ↦ (hmem i (mem_univ i)).1) (fun i ↦ (hmem i (mem_univ i)).2)]
  simp only [Pi.smul_apply, Pi.sub_apply, boxBoundarySum_def, mul_assoc]

/-- Quantitative Taylor power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` of a function
continuous on a coordinate box `Icc a b` and right Fueter regular on its open interior. -/
theorem RightFueterOn.hasFPowerSeriesOnBall_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f (dq '' pi univ fun i ↦ Ioo (a i) (b i)))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ (i : Fin 4) {c : ℝ}, (c = a i ∨ c = b i) →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), δ ≤ ‖dq (i.insertNth c u) - dq x₀‖) :
    HasFPowerSeriesOnBall f (fun n ↦ (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  have hface_cont (i : Fin 4) {c : ℝ} (hc' : c ∈ Icc (a i) (b i)) :
      ContinuousOn (fun u : Fin 3 → ℝ ↦ f (dq (i.insertNth c u)) * dq (Pi.single i 1))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    refine (hc.comp (by fun_prop) fun u hu ↦ ?_).mul continuousOn_const
    exact mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩)
  choose P₁ hP₁ using fun i : Fin 4 ↦ exists_hasFPowerSeriesOnBall_setIntegral_Icc_right
    (a := a ∘ i.succAbove) (b := b ∘ i.succAbove) (φ := fun u ↦ dq (i.insertNth (b i) u))
    (by fun_prop) (hface_cont i (right_mem_Icc.2 (hab i))) hδ₀ (hδ i (Or.inr rfl))
  choose P₀ hP₀ using fun i : Fin 4 ↦ exists_hasFPowerSeriesOnBall_setIntegral_Icc_right
    (a := a ∘ i.succAbove) (b := b ∘ i.succAbove) (φ := fun u ↦ dq (i.insertNth (a i) u))
    (by fun_prop) (hface_cont i (left_mem_Icc.2 (hab i))) hδ₀ (hδ i (Or.inl rfl))
  have hsum := Finset.univ.hasFPowerSeriesOnBall_fun_sum
    (ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀))
    fun i _ ↦ (hP₁ i).sub (hP₀ i)
  refine ((hsum.const_smul (c := (1 / (2 * Real.pi ^ 2) : ℝ))).congr
    fun q hq ↦ ?_).inv_factorial_smul_iteratedFDeriv
  obtain ⟨x, rfl, hlt⟩ := exists_dq_eq_and_norm_sub_lt_of_mem_eball hδ₀ hq
  have hmem := mem_pi_Ioo_of_norm_dq_sub_lt (a := a) (b := b) (p := 0) LinearMap.id ha hb
    (by simpa using hδ) (by simpa using hlt)
  rw [right_cauchyFueter_box (x₀ := x) hc
    (hf.mono sdiff_subset) (fun i ↦ (hmem i (mem_univ i)).1) (fun i ↦ (hmem i (mem_univ i)).2)]
  simp only [Pi.smul_apply, Pi.sub_apply, boxBoundarySum_def]

/-! ### Cube-in-ball geometry and local regularity -/

/-- The coordinate cube of half-side `r ≥ 0` centred at `x₀` in `Fin 4 → ℝ` maps under `dq` into
the closed Euclidean ball `closedBall (dq x₀) (2 * r)`. -/
theorem dq_image_Icc_subset_closedBall (x₀ : Fin 4 → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    dq '' Icc (fun j ↦ x₀ j - r) (fun j ↦ x₀ j + r) ⊆ closedBall (dq x₀) (2 * r) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall, dist_eq_norm, ← map_sub, norm_dq]
  have hsq : ‖WithLp.toLp 2 (x - x₀)‖ ^ 2 ≤ (2 * r) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i : Fin 4, ‖(WithLp.toLp 2 (x - x₀)).ofLp i‖ ^ 2
        ≤ ∑ _i : Fin 4, r ^ 2 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hxi : (WithLp.toLp 2 (x - x₀)).ofLp i = x i - x₀ i := rfl
          rw [Real.norm_eq_abs, hxi, sq_le_sq₀ (abs_nonneg _) hr, abs_le]
          exact ⟨by linarith [hx.1 i], by linarith [hx.2 i]⟩
      _ = (2 * r) ^ 2 := by simp [Finset.sum_const]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

/-- Every point on a hyperplane `x i = x₀ i ± r` (`r ≥ 0`) sits at Euclidean quaternion distance at
least `r` from `dq x₀`. -/
theorem le_norm_dq_insertNth_sub (x₀ : Fin 4 → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (i : Fin 4) {c : ℝ} (hc : c = x₀ i - r ∨ c = x₀ i + r) (w : Fin 3 → ℝ) :
    r ≤ ‖dq (i.insertNth c w) - dq x₀‖ := by
  rw [← map_sub, norm_dq]
  have hcoord := PiLp.norm_apply_le (WithLp.toLp 2 (i.insertNth c w - x₀)) i
  simp only [Pi.sub_apply, Fin.insertNth_apply_same, Real.norm_eq_abs] at hcoord
  rcases hc with rfl | rfl
  · simpa [abs_of_nonneg hr] using hcoord
  · simpa [abs_of_nonneg hr] using hcoord

section LocalRegularity

variable {f g : ℍ → ℍ} {s u : Set ℍ} {q q₀ : ℍ}

/-- A function that is left Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem LeftFueterOn.analyticAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) :
    AnalyticAt ℝ f q := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hs
  let x₀ := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q
  have hqx₀ : dq x₀ = q := by simp [x₀, coe_dq]
  set r := R / 2
  have hr : 0 < r := half_pos hR
  have h2r : 2 * r = R := by ring
  have hsub : dq '' Icc (fun j ↦ x₀ j - r) (fun j ↦ x₀ j + r) ⊆ s :=
    (dq_image_Icc_subset_closedBall x₀ hr.le).trans (by rwa [hqx₀, h2r])
  have hf_box : LeftFueterOn f (dq '' Icc (fun j ↦ x₀ j - r) (fun j ↦ x₀ j + r)) :=
    hf.mono hsub
  have hf_open : LeftFueterOn f (dq '' pi univ fun j ↦ Ioo (x₀ j - r) (x₀ j + r)) :=
    hf_box.mono (image_mono fun _ hx ↦
      ⟨fun j ↦ (hx j (mem_univ j)).1.le, fun j ↦ (hx j (mem_univ j)).2.le⟩)
  rw [← hqx₀]
  exact (hf_open.hasFPowerSeriesOnBall_box hf_box.differentiableOn.continuousOn
    (fun j ↦ by linarith) (fun j ↦ by linarith) hr
    (fun i _ hc w _ ↦ le_norm_dq_insertNth_sub x₀ hr.le i hc w)).analyticAt

/-- A function that is right Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem RightFueterOn.analyticAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) :
    AnalyticAt ℝ f q := by
  have hstar : LeftFueterOn (fun x ↦ star (f (star x))) (star '' s) := hf.star_star
  have hnhds : star '' s ∈ 𝓝 (star q) := by
    simpa using (starL' ℝ : ℍ ≃L[ℝ] ℍ).toHomeomorph.isOpenMap.image_mem_nhds hs
  have han := ((starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap.analyticAt _).comp
    ((hstar.analyticAt hnhds).comp ((starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap.analyticAt q))
  exact han.congr (Eventually.of_forall fun x ↦ by simp)

/-- A left Fueter regular function on an open set is real analytic there. -/
theorem LeftFueterOn.analyticOnNhd (hf : LeftFueterOn f s) (hs : IsOpen s) :
    AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- A right Fueter regular function on an open set is real analytic there. -/
theorem RightFueterOn.analyticOnNhd (hf : RightFueterOn f s) (hs : IsOpen s) :
    AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- A function that is left Fueter regular on a neighbourhood of `q` is `C^n` at `q` for every
order `n` (including `∞` and `ω`). -/
theorem LeftFueterOn.contDiffAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n f q :=
  (hf.analyticAt hs).contDiffAt

/-- A function that is right Fueter regular on a neighbourhood of `q` is `C^n` at `q` for every
order `n` (including `∞` and `ω`). -/
theorem RightFueterOn.contDiffAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n f q :=
  (hf.analyticAt hs).contDiffAt

/-- A left Fueter regular function on an open set is `C^n` (in particular `C^∞`) there. -/
theorem LeftFueterOn.contDiffOn (hf : LeftFueterOn f s) (hs : IsOpen s) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-- A right Fueter regular function on an open set is `C^n` (in particular `C^∞`) there. -/
theorem RightFueterOn.contDiffOn (hf : RightFueterOn f s) (hs : IsOpen s) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-- A function that is left Fueter regular on a neighbourhood of `q` has vanishing Laplacian at `q`,
with no auxiliary smoothness assumption. -/
theorem LeftFueterOn.laplacian_eq_zero_of_mem_nhds (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) :
    Δ f q = 0 :=
  hf.laplacian_eq_zero hs
    (((hf.contDiffAt hs (n := 2)).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)

/-- A function that is right Fueter regular on a neighbourhood of `q` has vanishing Laplacian at
`q`, with no auxiliary smoothness assumption. -/
theorem RightFueterOn.laplacian_eq_zero_of_mem_nhds (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) :
    Δ f q = 0 :=
  hf.laplacian_eq_zero hs
    (((hf.contDiffAt hs (n := 2)).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)

/-- Every left Fueter regular function on an open set has vanishing Laplacian there. -/
theorem LeftFueterOn.laplacian_eq_zero_of_isOpen (hf : LeftFueterOn f s) (hs : IsOpen s)
    (hq : q ∈ s) : Δ f q = 0 :=
  hf.laplacian_eq_zero_of_mem_nhds (hs.mem_nhds hq)

/-- Every right Fueter regular function on an open set has vanishing Laplacian there. -/
theorem RightFueterOn.laplacian_eq_zero_of_isOpen (hf : RightFueterOn f s) (hs : IsOpen s)
    (hq : q ∈ s) : Δ f q = 0 :=
  hf.laplacian_eq_zero_of_mem_nhds (hs.mem_nhds hq)

/-- A function that is left Fueter regular on a neighbourhood of `q` is harmonic at `q` in the
sense of `InnerProductSpace.HarmonicAt`. -/
theorem LeftFueterOn.harmonicAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) :
    InnerProductSpace.HarmonicAt f q :=
  ⟨hf.contDiffAt hs, (eventually_mem_nhds_iff.2 hs).mono fun _ hy ↦
    hf.laplacian_eq_zero_of_mem_nhds hy⟩

/-- A function that is right Fueter regular on a neighbourhood of `q` is harmonic at `q` in the
sense of `InnerProductSpace.HarmonicAt`. -/
theorem RightFueterOn.harmonicAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) :
    InnerProductSpace.HarmonicAt f q :=
  ⟨hf.contDiffAt hs, (eventually_mem_nhds_iff.2 hs).mono fun _ hy ↦
    hf.laplacian_eq_zero_of_mem_nhds hy⟩

/-- A left Fueter regular function on an open set is harmonic in a neighbourhood of that set. -/
theorem LeftFueterOn.harmonicOnNhd (hf : LeftFueterOn f s) (hs : IsOpen s) :
    InnerProductSpace.HarmonicOnNhd f s :=
  fun _ hq ↦ hf.harmonicAt (hs.mem_nhds hq)

/-- A right Fueter regular function on an open set is harmonic in a neighbourhood of that set. -/
theorem RightFueterOn.harmonicOnNhd (hf : RightFueterOn f s) (hs : IsOpen s) :
    InnerProductSpace.HarmonicOnNhd f s :=
  fun _ hq ↦ hf.harmonicAt (hs.mem_nhds hq)

/-! ### Uniqueness principles and codimension-two sharpness -/

/-- A left Fueter regular function on a preconnected open set that vanishes near one point vanishes
on the entire set. -/
theorem LeftFueterOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hzero : f =ᶠ[𝓝 q₀] 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hq₀ hzero

/-- A right Fueter regular function on a preconnected open set that vanishes near one point
vanishes on the entire set. -/
theorem RightFueterOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hf : RightFueterOn f s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hzero : f =ᶠ[𝓝 q₀] 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hq₀ hzero

/-- Two left Fueter regular functions on a preconnected open set that agree on a neighbourhood of
one point agree on the entire set. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hfg : f =ᶠ[𝓝 q₀] g) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hconn hq₀ hfg

/-- Two right Fueter regular functions on a preconnected open set that agree on a neighbourhood of
one point agree on the entire set. -/
theorem RightFueterOn.eqOn_of_preconnected_of_eventuallyEq
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hfg : f =ᶠ[𝓝 q₀] g) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hconn hq₀ hfg

/-- Two left Fueter regular functions on a preconnected open set `s` that agree on a nonempty open
subset `u ⊆ s` agree on all of `s`. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_eqOn_isOpen
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hu : IsOpen u) (hne : u.Nonempty) (hus : u ⊆ s) (hfg : EqOn f g u) : EqOn f g s :=
  let ⟨_, hq₀⟩ := hne
  hf.eqOn_of_preconnected_of_eventuallyEq hg hs hconn (hus hq₀)
    (Filter.eventuallyEq_of_mem (hu.mem_nhds hq₀) hfg)

/-- Two right Fueter regular functions on a preconnected open set `s` that agree on a nonempty open
subset `u ⊆ s` agree on all of `s`. -/
theorem RightFueterOn.eqOn_of_preconnected_of_eqOn_isOpen
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hu : IsOpen u) (hne : u.Nonempty) (hus : u ⊆ s) (hfg : EqOn f g u) : EqOn f g s :=
  let ⟨_, hq₀⟩ := hne
  hf.eqOn_of_preconnected_of_eventuallyEq hg hs hconn (hus hq₀)
    (Filter.eventuallyEq_of_mem (hu.mem_nhds hq₀) hfg)

/-- A left Fueter regular function on a preconnected open set whose iterated real derivatives of
every order vanish at a single point `q₀ ∈ s` vanishes on all of `s`. -/
theorem LeftFueterOn.eqOn_zero_of_preconnected_of_iteratedFDeriv_eq_zero
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hjet : ∀ m : ℕ, iteratedFDeriv ℝ m f q₀ = 0) : EqOn f 0 s :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs hconn hq₀
    ((hf.analyticAt (hs.mem_nhds hq₀)).eventuallyEq_zero_of_iteratedFDeriv_eq_zero hjet)

/-- A right Fueter regular function on a preconnected open set whose iterated real derivatives of
every order vanish at a single point `q₀ ∈ s` vanishes on all of `s`. -/
theorem RightFueterOn.eqOn_zero_of_preconnected_of_iteratedFDeriv_eq_zero
    (hf : RightFueterOn f s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hjet : ∀ m : ℕ, iteratedFDeriv ℝ m f q₀ = 0) : EqOn f 0 s :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs hconn hq₀
    ((hf.analyticAt (hs.mem_nhds hq₀)).eventuallyEq_zero_of_iteratedFDeriv_eq_zero hjet)

/-- Two left Fueter regular functions on a preconnected open set whose iterated real derivatives of
every order agree at one point `q₀ ∈ s` agree on all of `s`. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_iteratedFDeriv_eq
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hjet : ∀ m : ℕ, iteratedFDeriv ℝ m f q₀ = iteratedFDeriv ℝ m g q₀) :
    EqOn f g s := by
  have hsub : LeftFueterOn (f - g) s :=
    leftFueterOn_iff.mpr fun x hx ↦ (leftFueterOn_iff.mp hf x hx).sub (leftFueterOn_iff.mp hg x hx)
  have hzero : EqOn (f - g) 0 s :=
    hsub.eqOn_zero_of_preconnected_of_iteratedFDeriv_eq_zero hs hconn hq₀ fun m ↦ by
      rw [iteratedFDeriv_sub_apply (hf.contDiffAt (hs.mem_nhds hq₀))
        (hg.contDiffAt (hs.mem_nhds hq₀)), hjet m, sub_self]
  intro x hx
  exact sub_eq_zero.1 (hzero hx)

/-- Two right Fueter regular functions on a preconnected open set whose iterated real derivatives
of every order agree at one point `q₀ ∈ s` agree on all of `s`. -/
theorem RightFueterOn.eqOn_of_preconnected_of_iteratedFDeriv_eq
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hjet : ∀ m : ℕ, iteratedFDeriv ℝ m f q₀ = iteratedFDeriv ℝ m g q₀) :
    EqOn f g s := by
  have hsub : RightFueterOn (f - g) s :=
    rightFueterOn_iff.mpr fun x hx ↦
      (rightFueterOn_iff.mp hf x hx).sub (rightFueterOn_iff.mp hg x hx)
  have hzero : EqOn (f - g) 0 s :=
    hsub.eqOn_zero_of_preconnected_of_iteratedFDeriv_eq_zero hs hconn hq₀ fun m ↦ by
      rw [iteratedFDeriv_sub_apply (hf.contDiffAt (hs.mem_nhds hq₀))
        (hg.contDiffAt (hs.mem_nhds hq₀)), hjet m, sub_self]
  intro x hx
  exact sub_eq_zero.1 (hzero hx)

end LocalRegularity

/-- Unlike one-variable holomorphic functions, Fueter regular functions are not determined by
vanishing on a set with accumulation points: `q ↦ t + i x` is nonzero, both left and right Fueter
regular on all of `ℍ`, and vanishes on the two-dimensional subspace `{q | q.re = 0 ∧ q.imI = 0}`,
every point of which is an accumulation point of that subspace. -/
theorem exists_leftFueterOn_and_rightFueterOn_univ_eqOn_zero_accPt :
    ∃ (f : ℍ → ℍ) (Z : Set ℍ),
      LeftFueterOn f univ ∧ RightFueterOn f univ ∧ Z.Nonempty ∧
      (∀ z ∈ Z, AccPt z (𝓟 Z)) ∧ EqOn f 0 Z ∧ f ≠ 0 := by
  refine ⟨fun q : ℍ ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ), {q : ℍ | q.re = 0 ∧ q.imI = 0},
    ?_, ?_, ⟨0, by simp⟩, ?_, ?_, ?_⟩
  · simpa using leftFueterOn_coeComplex_comp (U := univ) isOpen_univ differentiableOn_id
  · simpa using rightFueterOn_coeComplex_comp (U := univ) isOpen_univ differentiableOn_id
  · intro z hz
    rw [accPt_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    set w : ℍ := z + ⟨0, 0, ε / 2, 0⟩
    have hw_ne : w ≠ z := by
      intro heq
      have h := congrArg QuaternionAlgebra.imJ heq
      simp [w] at h
      linarith
    have hw_mem : w ∈ U := hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : w - z = dq ![0, 0, ε / 2, 0] := by ext <;> simp [w, dq_apply]
      rw [hsub, norm_dq]
      have hsq : ‖WithLp.toLp 2 (![0, 0, ε / 2, 0] : Fin 4 → ℝ)‖ ^ 2 = (ε / 2) ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_four]
        simp [abs_of_pos hε]
      have hnorm : ‖WithLp.toLp 2 (![0, 0, ε / 2, 0] : Fin 4 → ℝ)‖ = ε / 2 :=
        (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 hsq
      linarith)
    exact ⟨w, ⟨hw_mem, by simp [w, hz.1], by simp [w, hz.2]⟩, hw_ne⟩
  · rintro z ⟨hre, him⟩
    ext <;> simp [hre, him]
  · intro hf0
    have h1 := congrFun hf0 1
    simpa using congrArg QuaternionAlgebra.re h1

end TauCeti
