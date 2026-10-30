/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.MeasureTheory.Measure.Lebesgue.GaussianBall
-- Proof-only: negation-invariant restrictions and densities, the product comparison on symmetric
-- convex sets, Tonelli along an orthogonal decomposition, products of densities, the volume of
-- `PiLp 2` as a product and the area of a disc.
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Integral.SymmetricConvexComparison
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# Vaaler's cube-slicing theorem

Every central slice of the cube `[-1, 1] ^ ι` by a linear subspace `V` of dimension `k` has
`k`-dimensional volume at least `2 ^ k` (Vaaler 1979). Every central slice of the unit polydisc of
`ℂ ^ ι` by a complex subspace of dimension `k` has real volume at least `π ^ k`. This file proves
both along the route of Bombieri–Gubler, Appendix C.3.

1. **The Gauss measure against a product of balls** (Lemma C.3.7). Let `B = ∏ i, B i` be a product
   of closed balls `B i ⊆ α i`, each of volume one, in finite-dimensional real inner product spaces.
   Then the Gauss measure of every measurable convex set `A ⊆ ∀ i, α i` with `-A = A` is at most
   `volume (A ∩ B)`. For a single ball this is
   `TauCeti.setLIntegral_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_closedBall`, and
   `TauCeti.pi_apply_le_pi_apply_of_forall_convex` passes it to products, since the Gauss density
   and the indicator of a ball are log-concave and even.
2. **Central slices** (the slicing step of Theorem C.3.8). If `Q ⊆ E` is measurable, convex and
   symmetric, and the Gauss measure of every measurable symmetric convex set `A` is at most
   `volume (A ∩ Q)`, then every central slice `V ∩ Q` has volume at least one in `V`. Apply the
   hypothesis to the slab `A` of points within distance `ε` of `V`. Its Gauss measure is at least
   `exp (-π ε ^ 2) * volume (closedBall (0 : Vᗮ) ε)`, because the Gauss density factors along
   `E = Vᗮ ⊕ V`. The parallel slices `V ∩ (Q - w)` of `Q` are at most as large as the central one
   (Brunn's principle, `Convex.measure_preimage_prodMk_le_measure_preimage_prodMk_zero`), so
   `volume (A ∩ Q) ≤ volume (V ∩ Q) * volume (closedBall (0 : Vᗮ) ε)`. Let `ε` tend to `0`.
3. **Products of balls.** In the `L²` product `PiLp 2 α`, whose volume is the product of the
   volumes of the factors, the first step supplies the hypothesis of the second for the product
   `{x | ∀ i, ‖x i‖ ≤ ρ i}` of balls of volume one, so its central slices have volume at least one.
4. **The cube and the polydisc.** The cube `[-1/2, 1/2] ^ ι` is a product of intervals of length
   one, and scaling by `2` gives `2 ^ k`. The polydisc of radius `1 / √π` is a product of discs of
   area one, and scaling by `√π` in real dimension `2 * k` gives `π ^ k`.

No dominated convergence is needed in the second step, because Brunn's principle bounds every
parallel slice by the central one.

## Main results

* `TauCeti.setLIntegral_prod_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_pi`: Bombieri–Gubler,
  Lemma C.3.7, the Gauss measure of a symmetric convex set against a product of balls of volume
  one.
* `Submodule.one_le_volume_preimage_coe`: the slicing step of Bombieri–Gubler, Theorem C.3.8, every
  central slice of a symmetric convex set that dominates the Gauss measure has volume at least one.
* `Submodule.one_le_volume_setOf_forall_norm_le`: every central slice of a product of balls of
  volume one has volume at least one.
* `Submodule.two_pow_finrank_le_volume_setOf_forall_abs_le_one`: **Vaaler's cube-slicing
  theorem**.
* `Submodule.pi_pow_finrank_le_volume_setOf_forall_norm_le_one`: its complex counterpart, for the
  unit polydisc.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma C.3.7 and Theorem C.3.8.
* J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific J. Math. **83**
  (1979), 543–553.

The thickening argument that bounds the parallel slices by the central one follows the
Apache-2.0 formalization of Vaaler's theorem in `rwst/Subspace-Theorems` (file
`ArithmeticHeights/CubeSlicing.lean`), by Ralf Stephan.
-/

public section

open MeasureTheory Measure Metric Set Module
open scoped ENNReal Real Pointwise

namespace TauCeti

section ClosedBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The single-ball comparison as a comparison of measures: the Gauss measure is dominated on
symmetric convex sets by the volume restricted to a closed ball of volume one. -/
private lemma withDensity_apply_le_restrict_apply {ρ : ℝ} (hρ : volume (closedBall (0 : E) ρ) = 1)
    {s : Set E} (hs : MeasurableSet s) (hsc : Convex ℝ s) (hneg : ∀ x ∈ s, -x ∈ s) :
    volume.withDensity (fun x : E ↦ ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2))) s ≤
      volume.restrict (closedBall (0 : E) ρ) s := by
  rw [withDensity_apply _ hs, restrict_apply hs]
  refine setLIntegral_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_closedBall hρ.ge hs ?_
  -- A symmetric convex set contains the midpoint `0` of `x` and `-x`, so it is star-shaped.
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact starConvex_empty 0
  refine hsc.starConvex ?_
  simpa using hsc hx (hneg x hx) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)

end ClosedBall

section ProductOfBalls

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)]
  [∀ i, InnerProductSpace ℝ (α i)] [∀ i, FiniteDimensional ℝ (α i)] [∀ i, MeasurableSpace (α i)]
  [∀ i, BorelSpace (α i)]

/-- **The Gauss measure against a product of balls** (Bombieri–Gubler, Lemma C.3.7). Let
`closedBall (0 : α i) (ρ i)` have volume one in each of finitely many finite-dimensional real inner
product spaces `α i`. Then for every measurable convex set `A ⊆ ∀ i, α i` with `-A = A`,

`∫⁻ x in A, ∏ i, exp (-π ‖x i‖ ^ 2) ≤ volume (A ∩ univ.pi fun i ↦ closedBall 0 (ρ i))`.

Such radii exist by `TauCeti.exists_volume_closedBall_eq_one`. Unlike Bombieri–Gubler, `A` need
not be closed. -/
theorem setLIntegral_prod_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_pi {ρ : ι → ℝ}
    (hρ : ∀ i, volume (closedBall (0 : α i) (ρ i)) = 1) {A : Set (∀ i, α i)}
    (hA : MeasurableSet A) (hAc : Convex ℝ A) (hneg : ∀ x ∈ A, -x ∈ A) :
    ∫⁻ x in A, ∏ i, ENNReal.ofReal (Real.exp (-π * ‖x i‖ ^ 2)) ≤
      volume (A ∩ univ.pi fun i ↦ closedBall 0 (ρ i)) := by
  set g : ∀ i, α i → ℝ≥0∞ := fun i x ↦ ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2))
  have hg (i : ι) : Measurable (g i) := by fun_prop
  have hgneg (i : ι) (x : α i) : g i (-x) = g i x := by simp only [g, norm_neg]
  have hball (i : ι) : -closedBall (0 : α i) (ρ i) = closedBall 0 (ρ i) := by simp
  have : ∀ i, ((volume : Measure (α i)).withDensity (g i)).IsNegInvariant := fun i ↦
    isNegInvariant_withDensity (hgneg i)
  have : ∀ i, ((volume : Measure (α i)).restrict (closedBall 0 (ρ i))).IsNegInvariant :=
    fun i ↦ isNegInvariant_restrict (hball i)
  have h := pi_apply_le_pi_apply_of_forall_convex
    (μ := fun i ↦ (volume : Measure (α i)).withDensity (g i))
    (ν := fun i ↦ (volume : Measure (α i)).restrict (closedBall 0 (ρ i)))
    (fun i _ hθ₀ hθ₁ ↦ (hasPrekopaLeindler_volume (α i) hθ₀ hθ₁).withDensity hθ₀ hθ₁ (hg i)
      (logConcave_ofReal_exp_neg_mul_sq_norm Real.pi_pos.le))
    (fun i _ hθ₀ hθ₁ ↦ (hasPrekopaLeindler_volume (α i) hθ₀ hθ₁).restrict hθ₀ hθ₁
      measurableSet_closedBall (convex_closedBall 0 (ρ i)))
    (fun i _ hs hsc hsneg ↦ withDensity_apply_le_restrict_apply (hρ i) hs hsc hsneg) hA hAc hneg
  rwa [pi_withDensity _ hg, ← restrict_pi_pi, withDensity_apply _ hA, restrict_apply hA,
    ← volume_pi] at h

end ProductOfBalls

section CentralSlice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- In the decomposition `E = Vᗮ ⊕ V`, the point `w + v` lies within distance `ε` of `V` exactly
when `‖w‖ ≤ ε`. -/
private lemma add_mem_preimage_starProjection_iff (V : Submodule ℝ E) (w : Vᗮ) (v : V)
    (ε : ℝ) :
    (w : E) + v ∈ Vᗮ.starProjection ⁻¹' closedBall 0 ε ↔ w ∈ closedBall (0 : Vᗮ) ε := by
  have hv : Vᗮ.starProjection (v : E) = 0 := by
    rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff.2
      (V.le_orthogonal_orthogonal v.2), ZeroMemClass.coe_zero]
  simp only [mem_preimage, map_add, hv, add_zero, Submodule.starProjection_mem_subspace_eq_self,
    mem_closedBall_zero_iff, Submodule.norm_coe]

/-- The Gauss measure of the slab of points within distance `ε` of `V` is at least
`exp (-π ε ^ 2)` times the volume of the `ε`-ball of `Vᗮ`: the Gauss density factors along
`E = Vᗮ ⊕ V`, its integral over `V` is one, and it is at least `exp (-π ε ^ 2)` on the ball. -/
private lemma mul_volume_closedBall_le_setLIntegral (V : Submodule ℝ E) (ε : ℝ) :
    ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume (closedBall (0 : Vᗮ) ε) ≤
      ∫⁻ x in Vᗮ.starProjection ⁻¹' closedBall 0 ε, ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2)) := by
  classical
  set g : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2))
  have hg : Measurable g := by fun_prop
  have hA : MeasurableSet (Vᗮ.starProjection ⁻¹' closedBall 0 ε) :=
    measurableSet_closedBall.preimage (by fun_prop)
  have hsplit (w : Vᗮ) (v : V) : g (w + v) = g w * g v := by
    simp only [g]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← mul_add, norm_add_sq_real,
      V.inner_left_of_mem_orthogonal v.2 w.2, mul_zero, add_zero]
  calc ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume (closedBall (0 : Vᗮ) ε)
      = ∫⁻ w in closedBall (0 : Vᗮ) ε, ENNReal.ofReal (Real.exp (-π * ε ^ 2)) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ w in closedBall (0 : Vᗮ) ε, g w :=
        setLIntegral_mono' measurableSet_closedBall fun w hw ↦ by
          have : ‖(w : E)‖ ^ 2 ≤ ε ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 hw) 2
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          nlinarith [Real.pi_pos]
    _ = ∫⁻ w : Vᗮ, ∫⁻ v : V, (Vᗮ.starProjection ⁻¹' closedBall 0 ε).indicator g (w + v) := by
        rw [← lintegral_indicator measurableSet_closedBall]
        refine lintegral_congr fun w ↦ ?_
        by_cases hw : w ∈ closedBall (0 : Vᗮ) ε
        · rw [indicator_of_mem hw]
          simp only [indicator_apply, add_mem_preimage_starProjection_iff, hw, ↓reduceIte, hsplit]
          rw [lintegral_const_mul _ (f := fun v : V ↦ g v) (hg.comp measurable_subtype_coe)]
          simp only [g, Submodule.norm_coe, lintegral_ofReal_exp_neg_pi_mul_sq_norm, mul_one]
        · rw [indicator_of_notMem hw]
          simp only [indicator_apply, add_mem_preimage_starProjection_iff, hw, ↓reduceIte,
            lintegral_zero]
    _ = ∫⁻ x in Vᗮ.starProjection ⁻¹' closedBall 0 ε, g x := by
        rw [← Submodule.lintegral_eq_lintegral_lintegral_add V (hg.indicator hA).aemeasurable,
          lintegral_indicator hA]

/-- The part of a symmetric convex set `Q` within distance `ε` of `V` has volume at most
`volume (V ∩ Q)` times the volume of the `ε`-ball of `Vᗮ`: by Brunn's principle, every slice
`{v ∈ V | w + v ∈ Q}` parallel to `V` is at most as large as the central one. -/
private lemma volume_inter_le_mul_volume_closedBall {Q : Set E} (hQ : MeasurableSet Q)
    (hQc : Convex ℝ Q) (hQneg : ∀ x ∈ Q, -x ∈ Q) (V : Submodule ℝ E) (ε : ℝ) :
    volume (Vᗮ.starProjection ⁻¹' closedBall 0 ε ∩ Q) ≤
      volume (((↑) : V → E) ⁻¹' Q) * volume (closedBall (0 : Vᗮ) ε) := by
  classical
  set S : Set (Vᗮ × V) := (fun p ↦ (p.1 : E) + p.2) ⁻¹' Q
  have hS : MeasurableSet S := hQ.preimage (by fun_prop)
  have hslice (w : Vᗮ) : volume (Prod.mk w ⁻¹' S) ≤ volume (((↑) : V → E) ⁻¹' Q) := by
    have h := Convex.measure_preimage_prodMk_le_measure_preimage_prodMk_zero
      (fun _ hθ₀ hθ₁ ↦ hasPrekopaLeindler_volume V hθ₀ hθ₁) hS
      (hQc.linear_preimage (Vᗮ.subtype.coprod V.subtype)) (fun p hp ↦ by
        simpa only [S, mem_preimage, Prod.fst_neg, Prod.snd_neg, Submodule.coe_neg, neg_add]
          using hQneg _ hp) w
    have h0 : Prod.mk (0 : Vᗮ) ⁻¹' S = ((↑) : V → E) ⁻¹' Q := by
      ext v
      simp [S]
    exact h0 ▸ h
  have hAQ : MeasurableSet (Vᗮ.starProjection ⁻¹' closedBall 0 ε ∩ Q) :=
    (measurableSet_closedBall.preimage (by fun_prop)).inter hQ
  rw [← lintegral_indicator_one hAQ,
    Submodule.lintegral_eq_lintegral_lintegral_add V (measurable_one.indicator hAQ).aemeasurable,
    ← setLIntegral_const, ← lintegral_indicator measurableSet_closedBall]
  refine lintegral_mono fun w ↦ ?_
  have hmem (w : Vᗮ) (v : V) : (w : E) + v ∈ Vᗮ.starProjection ⁻¹' closedBall 0 ε ∩ Q ↔
      w ∈ closedBall (0 : Vᗮ) ε ∧ v ∈ Prod.mk w ⁻¹' S := by
    rw [mem_inter_iff, add_mem_preimage_starProjection_iff]
    rfl
  by_cases hw : w ∈ closedBall (0 : Vᗮ) ε
  · rw [indicator_of_mem hw]
    calc ∫⁻ v : V, (Vᗮ.starProjection ⁻¹' closedBall 0 ε ∩ Q).indicator 1 ((w : E) + v)
        = ∫⁻ v : V, (Prod.mk w ⁻¹' S).indicator 1 v :=
          lintegral_congr fun v ↦ by simp only [indicator_apply, hmem, hw, true_and, Pi.one_apply]
      _ = volume (Prod.mk w ⁻¹' S) := lintegral_indicator_one (measurable_prodMk_left hS)
      _ ≤ _ := hslice w
  · rw [indicator_of_notMem hw]
    simp only [indicator_apply, hmem, hw, false_and, ↓reduceIte, lintegral_zero, le_refl]

/-- **Central slices of a set that dominates the Gauss measure** (the slicing step of
Bombieri–Gubler, Theorem C.3.8). Let `Q ⊆ E` be measurable, convex and symmetric about the
origin, and suppose that the Gauss measure `∫⁻ x in A, exp (-π ‖x‖ ^ 2)` of every measurable
convex set `A` with `-A = A` is at most `volume (A ∩ Q)`. Then for every subspace `V`, the central
slice `V ∩ Q` has volume at least one, computed in `V`.

The hypothesis holds for a product of balls of volume one, by
`TauCeti.setLIntegral_prod_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_pi`. -/
theorem _root_.Submodule.one_le_volume_preimage_coe (V : Submodule ℝ E) {Q : Set E}
    (hQ : MeasurableSet Q) (hQc : Convex ℝ Q) (hQneg : ∀ x ∈ Q, -x ∈ Q)
    (hgauss : ∀ A : Set E, MeasurableSet A → Convex ℝ A → (∀ x ∈ A, -x ∈ A) →
      ∫⁻ x in A, ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2)) ≤ volume (A ∩ Q)) :
    1 ≤ volume (((↑) : V → E) ⁻¹' Q) := by
  -- Apply the hypothesis to the slab of the points within distance `ε` of `V`.
  have key (ε : ℝ) (hε : 0 < ε) :
      ENNReal.ofReal (Real.exp (-π * ε ^ 2)) ≤ volume (((↑) : V → E) ⁻¹' Q) := by
    refine (ENNReal.mul_le_mul_iff_left (measure_closedBall_pos volume (0 : Vᗮ) hε).ne'
      measure_closedBall_lt_top.ne).1 ?_
    refine (mul_volume_closedBall_le_setLIntegral V ε).trans <|
      (hgauss _ (measurableSet_closedBall.preimage (by fun_prop))
        ((convex_closedBall 0 ε).linear_preimage Vᗮ.starProjection.toLinearMap)
        fun x hx ↦ ?_).trans (volume_inter_le_mul_volume_closedBall hQ hQc hQneg V ε)
    simpa only [mem_preimage, map_neg, mem_closedBall_zero_iff, norm_neg] using hx
  -- Let `ε` tend to `0`.
  have hlim : Filter.Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (-π * ε ^ 2)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have h : Continuous fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (-π * ε ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε ↦ key ε hε)

end CentralSlice

section ProductOfBallsSlice

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)]
  [∀ i, InnerProductSpace ℝ (α i)] [∀ i, FiniteDimensional ℝ (α i)] [∀ i, MeasurableSpace (α i)]
  [∀ i, BorelSpace (α i)]

/-- **Central slices of a product of balls of volume one.** Let `closedBall (0 : α i) (ρ i)` have
volume one in each of finitely many finite-dimensional real inner product spaces `α i`. Then every
central slice of the product `{x | ∀ i, ‖x i‖ ≤ ρ i}` of these balls by a real subspace `V` of the
`L²` product `PiLp 2 α` has volume at least one, computed in `V`.

The cube `[-1, 1] ^ ι` and the unit polydisc of `ℂ ^ ι` are dilates of such products. -/
theorem _root_.Submodule.one_le_volume_setOf_forall_norm_le {ρ : ι → ℝ}
    (hρ : ∀ i, volume (closedBall (0 : α i) (ρ i)) = 1) (V : Submodule ℝ (PiLp 2 α)) :
    1 ≤ volume {x : V | ∀ i, ‖(x : PiLp 2 α) i‖ ≤ ρ i} := by
  set Q : Set (PiLp 2 α) := {x | ∀ i, ‖x i‖ ≤ ρ i}
  have hQe : Q = WithLp.ofLp ⁻¹' univ.pi fun i ↦ closedBall (0 : α i) (ρ i) := by
    ext x
    simp [Q]
  -- The volume of `PiLp 2 α` is the product of the volumes of the factors.
  have he := (PiLp.volume_preserving_symm_measurableEquiv_toLp α).symm
  have hQ : MeasurableSet Q := hQe ▸ he.symm.measurable
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_closedBall)
  have hQc : Convex ℝ Q := hQe ▸ (convex_pi fun i _ ↦ convex_closedBall 0 (ρ i)).linear_preimage
    (WithLp.linearEquiv 2 ℝ (∀ i, α i)).toLinearMap
  have hQneg (x) (hx : x ∈ Q) : -x ∈ Q := by simpa [Q] using hx
  refine V.one_le_volume_preimage_coe hQ hQc hQneg fun A hA hAc hneg ↦ ?_
  have h := setLIntegral_prod_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_pi hρ
    (he.measurable hA) (hAc.linear_preimage (WithLp.linearEquiv 2 ℝ (∀ i, α i)).symm.toLinearMap)
    (fun x hx ↦ by simpa using hneg _ hx)
  calc ∫⁻ x in A, ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2))
      = ∫⁻ y in WithLp.toLp 2 ⁻¹' A, ENNReal.ofReal (Real.exp (-π * ‖WithLp.toLp 2 y‖ ^ 2)) :=
        (he.setLIntegral_comp_preimage_emb (MeasurableEquiv.toLp 2 (∀ i, α i)).measurableEmbedding
          _ A).symm
    _ = ∫⁻ y in WithLp.toLp 2 ⁻¹' A, ∏ i, ENNReal.ofReal (Real.exp (-π * ‖y i‖ ^ 2)) := by
      refine lintegral_congr fun y ↦ ?_
      rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, Real.exp_sum,
        ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le]
    _ ≤ volume (WithLp.toLp 2 ⁻¹' A ∩ univ.pi fun i ↦ closedBall (0 : α i) (ρ i)) := h
    _ = volume (A ∩ Q) := by
      rw [← he.measure_preimage (hA.inter hQ).nullMeasurableSet, hQe, preimage_inter,
        preimage_preimage]
      simp [MeasurableEquiv.coe_toLp]

end ProductOfBallsSlice

section Cube

variable {ι : Type*} [Fintype ι]

/-- **Vaaler's cube-slicing theorem.** Every central slice of the cube `[-1, 1] ^ ι` by a
subspace `V` of `EuclideanSpace ℝ ι` has volume at least `2 ^ finrank ℝ V`, computed in `V`. -/
theorem _root_.Submodule.two_pow_finrank_le_volume_setOf_forall_abs_le_one
    (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    2 ^ finrank ℝ V ≤ volume {x : V | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} := by
  -- The cube of side one is the product of the intervals `closedBall 0 (1 / 2)` of length one.
  have h := V.one_le_volume_setOf_forall_norm_le (α := fun _ : ι ↦ ℝ) (ρ := fun _ ↦ 1 / 2)
    fun _ ↦ by simp [Real.volume_closedBall]
  -- Scale the slice of the cube of side one by `2`.
  have hscale : {x : V | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} =
      (2 : ℝ) • {x : V | ∀ i, ‖(x : EuclideanSpace ℝ ι) i‖ ≤ 1 / 2} := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem₀ two_ne_zero]
    simp only [mem_ofPred_eq, Submodule.coe_smul, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_mul, abs_inv, abs_two]
    refine forall_congr' fun i ↦ ?_
    constructor <;> intro h <;> linarith
  rw [hscale, addHaar_smul, abs_of_nonneg (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]
  exact le_mul_of_one_le_right' h

end Cube

section Polydisc

variable {ι : Type*} [Fintype ι]

/-- **Central slices of the unit polydisc.** Every central slice of the unit polydisc
`{x | ∀ i, ‖x i‖ ≤ 1}` of `ℂ ^ ι` by a complex subspace `V` of `EuclideanSpace ℂ ι` has real
volume at least `π ^ finrank ℂ V`, computed in the real subspace `V.restrictScalars ℝ`.

This is the complex counterpart of Vaaler's cube-slicing theorem
`Submodule.two_pow_finrank_le_volume_setOf_forall_abs_le_one`: the polydisc is the product of the
discs of radius `1 / √π`, of area one, dilated by `√π`, and `V` has real dimension
`2 * finrank ℂ V`. -/
theorem _root_.Submodule.pi_pow_finrank_le_volume_setOf_forall_norm_le_one
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ENNReal.ofReal π ^ finrank ℂ V ≤
      volume {x : V.restrictScalars ℝ | ∀ i, ‖(x : EuclideanSpace ℂ ι) i‖ ≤ 1} := by
  have hsqrt : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  -- The disc of radius `1 / √π` has area one.
  have hρ : volume (closedBall (0 : ℂ) (1 / √π)) = 1 := by
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    simp [Real.pi_pos.le, Real.pi_pos.ne']
  have h := (V.restrictScalars ℝ).one_le_volume_setOf_forall_norm_le (α := fun _ : ι ↦ ℂ)
    fun _ ↦ hρ
  -- As a real subspace, `V` has dimension `2 * finrank ℂ V`.
  have hrank : finrank ℝ (V.restrictScalars ℝ) = 2 * finrank ℂ V := by
    rw [((Submodule.restrictScalarsEquiv ℝ ℂ _ V).restrictScalars ℝ).finrank_eq,
      ← Complex.finrank_real_complex, Module.finrank_mul_finrank]
  -- Scale the slice of the polydisc of radius `1 / √π` by `√π`.
  have hscale : {x : V.restrictScalars ℝ | ∀ i, ‖(x : EuclideanSpace ℂ ι) i‖ ≤ 1} =
      √π • {x : V.restrictScalars ℝ | ∀ i, ‖(x : EuclideanSpace ℂ ι) i‖ ≤ 1 / √π} := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem₀ hsqrt.ne']
    simp only [mem_ofPred_eq, Submodule.coe_smul, PiLp.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hsqrt]
    refine forall_congr' fun i ↦ ?_
    rw [one_div, mul_le_iff_le_one_right (inv_pos.2 hsqrt)]
  rw [hscale, addHaar_smul, hrank, abs_of_nonneg (by positivity), pow_mul,
    Real.sq_sqrt Real.pi_pos.le, ENNReal.ofReal_pow Real.pi_pos.le]
  exact le_mul_of_one_le_right' h

end Polydisc

end TauCeti
