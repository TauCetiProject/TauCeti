/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Hyperplane
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Boundary energy estimates on infinite strips

For a map that is `C¹` near the closed strip in the Euclidean product `ℝ × E`, finite value
and derivative energies on
`(a, b) × E` imply `L²` integrability on both boundary hyperplanes. Their combined squared
`L²` norm is bounded by the interior value energy with coefficient `2 / (b - a) + 1`, plus
the derivative energy. Compact support and integrability outside the strip are not required.
The target may be any real inner product space.

For scalar whole-space `H¹` functions, the two existing hyperplane traces are controlled by
the Sobolev norm restricted to the strip. Consequently extensions agreeing on the strip have
the same two boundary traces. This supplies the boundary estimate and extension-independence
needed to construct an `H¹` trace on a strip; it does not construct an extension of every
strip Sobolev function.

The finite-interval fundamental-theorem-of-calculus argument is the flat-boundary trace
argument of L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5, with an affine
weight replacing the compact-support condition at infinity.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Topology
open scoped Distributions Gradient ENNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- The infinite open strip between the normal coordinates `a` and `b`, with the Euclidean
product norm. It is empty when `b ≤ a`. -/
def normalStrip (a b : ℝ) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | a < (WithLp.ofLp x).1 ∧ (WithLp.ofLp x).1 < b},
    (isOpen_lt continuous_const (WithLp.prod_continuous_ofLp 2 ℝ E).fst).inter
      (isOpen_lt (WithLp.prod_continuous_ofLp 2 ℝ E).fst continuous_const)⟩

/-- Membership in the strip means that the normal coordinate lies between its endpoints. -/
@[simp]
theorem mem_normalStrip (a b : ℝ) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalStrip (E := E) a b ↔ a < (WithLp.ofLp x).1 ∧ (WithLp.ofLp x).1 < b :=
  Iff.rfl

variable [MeasurableSpace E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The normal-line estimate on a finite strip, before integrating the transverse variable. -/
private theorem norm_sq_boundary_le_integral_line_energy
    {u : WithLp 2 (ℝ × E) → F} {a b : ℝ}
    (hu : ∀ x, (WithLp.ofLp x).1 ∈ Icc a b → ContDiffAt ℝ 1 u x) (hab : a < b)
    (y : E) : ‖u (WithLp.toLp 2 (a, y))‖ ^ 2 +
      ‖u (WithLp.toLp 2 (b, y))‖ ^ 2 ≤
      ∫ t in Ioo a b, (2 / (b - a) + 1) * ‖u (WithLp.toLp 2 (t, y))‖ ^ 2 +
        ‖fderiv ℝ u (WithLp.toLp 2 (t, y))‖ ^ 2 := by
  let C := 2 / (b - a) + 1
  let energy := fun x : WithLp 2 (ℝ × E) ↦ C * ‖u x‖ ^ 2 + ‖fderiv ℝ u x‖ ^ 2
  have hpath : ContDiff ℝ 1 (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
      (contDiff_id.prodMk contDiff_const)
  have hg : ∀ t ∈ Icc a b,
      ContDiffAt ℝ 1 (fun s : ℝ ↦ u (WithLp.toLp 2 (s, y))) t := fun t ht ↦
    (hu _ (by simpa only [WithLp.ofLp_toLp] using ht)).comp t hpath.contDiffAt
  have hgc : ContinuousOn (fun s : ℝ ↦ u (WithLp.toLp 2 (s, y))) (Icc a b) :=
    fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv (fun s : ℝ ↦ u (WithLp.toLp 2 (s, y)))) (Icc a b) :=
    fun t ht ↦ ((hg t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun s : ℝ ↦ ‖fderiv ℝ u (WithLp.toLp 2 (s, y))‖ ^ 2)
      (Icc a b) := fun t ht ↦
    (((hu _ (by simpa only [WithLp.ofLp_toLp] using ht)).continuousAt_fderiv
      one_ne_zero).comp hpath.continuous.continuousAt).norm.pow 2 |>.continuousWithinAt
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (fun s : ℝ ↦ u (WithLp.toLp 2 (s, y))) t =
      fderiv ℝ u (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (1, (0 : E))) := by
    have hp : HasDerivAt (fun s : ℝ ↦ WithLp.toLp 2 (s, y))
        (WithLp.toLp 2 (1, (0 : E))) t :=
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    exact (((hu _ (by simpa only [WithLp.ofLp_toLp] using ht)).differentiableAt
      one_ne_zero).hasFDerivAt.comp_hasDerivAt t hp).deriv
  have hmono : (∫ t in a..b, C * ‖u (WithLp.toLp 2 (t, y))‖ ^ 2 +
      ‖deriv (fun s : ℝ ↦ u (WithLp.toLp 2 (s, y))) t‖ ^ 2) ≤
      ∫ t in a..b, energy (WithLp.toLp 2 (t, y)) :=
    intervalIntegral.integral_mono_on hab.le
    (((continuousOn_const.mul (hgc.norm.pow 2)).add
      (hdc.norm.pow 2)).intervalIntegrable_of_Icc hab.le)
    (((continuousOn_const.mul (hgc.norm.pow 2)).add
      hfc).intervalIntegrable_of_Icc hab.le)
    (fun t ht ↦ by
      dsimp only [energy, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
      rw [hderiv t ht]
      apply add_le_add le_rfl
      apply (sq_le_sq₀ (norm_nonneg _)
        (fderiv ℝ u (WithLp.toLp 2 (t, y))).opNorm_nonneg).mpr
      simpa only [WithLp.norm_toLp_fst, norm_one, mul_one] using
        (fderiv ℝ u (WithLp.toLp 2 (t, y))).le_opNorm
          (WithLp.toLp 2 (1, (0 : E))))
  simpa only [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] using
    (norm_sq_add_norm_sq_le_integral_norm_sq_add_norm_deriv_sq hg hab).trans hmono

private theorem integrable_boundary_norm_sq_add_and_le
    {u : WithLp 2 (ℝ × E) → F} {a b : ℝ}
    (hu : ∀ x, (WithLp.ofLp x).1 ∈ Icc a b → ContDiffAt ℝ 1 u x) (hab : a < b)
    (hv : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (normalStrip (E := E) a b) volume)
    (hd : IntegrableOn (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) (normalStrip (E := E) a b) volume) :
    Integrable (fun y : E ↦ ‖u (WithLp.toLp 2 (a, y))‖ ^ 2 +
      ‖u (WithLp.toLp 2 (b, y))‖ ^ 2) volume ∧
    (∫ y : E, ‖u (WithLp.toLp 2 (a, y))‖ ^ 2 + ‖u (WithLp.toLp 2 (b, y))‖ ^ 2) ≤
      ∫ x in normalStrip (E := E) a b,
        (2 / (b - a) + 1) * ‖u x‖ ^ 2 + ‖fderiv ℝ u x‖ ^ 2 := by
  let C := 2 / (b - a) + 1
  let energy := fun x : WithLp 2 (ℝ × E) ↦ C * ‖u x‖ ^ 2 + ‖fderiv ℝ u x‖ ^ 2
  have he : IntegrableOn energy (normalStrip (E := E) a b) volume := (hv.const_mul C).add hd
  -- Express the finite interior energy in product coordinates.
  have hpre : WithLp.toLp 2 ⁻¹' (normalStrip (E := E) a b : Set (WithLp 2 (ℝ × E))) =
      (Ioo a b) ×ˢ (univ : Set E) := by
    ext z
    simp only [mem_preimage, SetLike.mem_coe, mem_normalStrip, mem_prod, mem_Ioo,
      mem_univ, and_true]
  have hprod : Integrable (fun z : ℝ × E ↦ energy (WithLp.toLp 2 z))
      ((volume.restrict (Ioo a b)).prod volume) := by
    have hp := ((WithLp.volume_preserving_toLp ℝ E).integrableOn_comp_preimage
      (MeasurableEquiv.toLp 2 (ℝ × E)).measurableEmbedding).mpr he
    rw [hpre] at hp
    simpa only [IntegrableOn, Function.comp_def, Measure.volume_eq_prod,
      ← Measure.restrict_prod_eq_prod_univ] using hp
  have hline (y : E) := norm_sq_boundary_le_integral_line_energy hu hab y
  -- Boundary integrability is a consequence of domination, before applying Fubini.
  have hboundary (c : ℝ) (hc : c ∈ Icc a b) :
      Continuous (fun y : E ↦ u (WithLp.toLp 2 (c, y))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (hu _ (by simpa only [WithLp.ofLp_toLp] using hc)).continuousAt.comp
      (by fun_prop)
  have hmeas : AEStronglyMeasurable (fun y : E ↦ ‖u (WithLp.toLp 2 (a, y))‖ ^ 2 +
      ‖u (WithLp.toLp 2 (b, y))‖ ^ 2) volume :=
    ((hboundary a ⟨le_rfl, hab.le⟩).norm.pow 2 |>.add
      ((hboundary b ⟨hab.le, le_rfl⟩).norm.pow 2)).aestronglyMeasurable
  have hi := hprod.integral_prod_right.mono' hmeas (Filter.Eventually.of_forall fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hline y)
  refine ⟨hi, (integral_mono hi hprod.integral_prod_right hline).trans_eq ?_⟩
  rw [← integral_prod_symm _ hprod, Measure.restrict_prod_eq_prod_univ, Set.prod_univ]
  have hcoord := (WithLp.volume_preserving_toLp ℝ E).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (ℝ × E)).measurableEmbedding energy
    (normalStrip (E := E) a b)
  rw [hpre] at hcoord
  simpa only [Measure.volume_eq_prod, Set.prod_univ] using hcoord

/-- Finite value and derivative energies in a strip imply square integrability on either
boundary hyperplane. No integrability of the boundary restriction is assumed. -/
theorem memLp_hyperplane_of_integrableOn_strip
    {u : WithLp 2 (ℝ × E) → F} {a b : ℝ}
    (hu : ∀ x, (WithLp.ofLp x).1 ∈ Icc a b → ContDiffAt ℝ 1 u x) (hab : a < b)
    (hv : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (normalStrip (E := E) a b) volume)
    (hd : IntegrableOn (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) (normalStrip (E := E) a b) volume)
    {c : ℝ} (hc : c = a ∨ c = b) : MemLp (fun y ↦ u (WithLp.toLp 2 (c, y))) 2 volume := by
  have hi := (integrable_boundary_norm_sq_add_and_le hu hab hv hd).1
  have hm : AEStronglyMeasurable (fun y : E ↦ u (WithLp.toLp 2 (c, y))) volume := by
    have hcc : c ∈ Icc a b := by rcases hc with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
    apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (hu _ (by simpa only [WithLp.ofLp_toLp] using hcc)).continuousAt.comp
      (by fun_prop)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine hi.mono' (hm.norm.pow 2) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rcases hc with h | h
  · rw [h]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [h]
    exact le_add_of_nonneg_left (sq_nonneg _)

/-- The combined squared `L²` norms of both boundary restrictions are controlled by the
value and derivative energies inside the strip, with an explicit width-dependent coefficient.
Their integrability follows from the two interior energy hypotheses. -/
theorem integral_boundary_norm_sq_le_integral_strip_energy
    {u : WithLp 2 (ℝ × E) → F} {a b : ℝ}
    (hu : ∀ x, (WithLp.ofLp x).1 ∈ Icc a b → ContDiffAt ℝ 1 u x) (hab : a < b)
    (hv : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (normalStrip (E := E) a b) volume)
    (hd : IntegrableOn (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) (normalStrip (E := E) a b) volume) :
    (∫ y : E, ‖u (WithLp.toLp 2 (a, y))‖ ^ 2) +
      (∫ y : E, ‖u (WithLp.toLp 2 (b, y))‖ ^ 2) ≤
      ∫ x in normalStrip (E := E) a b,
        (2 / (b - a) + 1) * ‖u x‖ ^ 2 + ‖fderiv ℝ u x‖ ^ 2 := by
  rw [← integral_add
    ((memLp_hyperplane_of_integrableOn_strip hu hab hv hd (Or.inl rfl)).integrable_norm_pow
      (by norm_num))
    ((memLp_hyperplane_of_integrableOn_strip hu hab hv hd (Or.inr rfl)).integrable_norm_pow
      (by norm_num))]
  exact (integrable_boundary_norm_sq_add_and_le hu hab hv hd).2

private theorem strip_energy_ofTestFunction
    (a b : ℝ) (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    IntegrableOn (fun x ↦ ‖φ x‖ ^ 2) (normalStrip (E := E) a b) volume ∧
    IntegrableOn (fun x ↦ ‖fderiv ℝ φ x‖ ^ 2) (normalStrip (E := E) a b) volume ∧
    (∫ x in normalStrip (E := E) a b, ‖φ x‖ ^ 2 + ‖fderiv ℝ φ x‖ ^ 2) =
      ‖W1p.restrictL (show normalStrip (E := E) a b ≤ ⊤ from le_top)
        (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ ^ 2 := by
  let v : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalStrip (E := E) a b) 2 :=
    W1p.restrictL (show normalStrip (E := E) a b ≤ ⊤ from le_top)
    (W1p.ofTestFunctionₗ volume ⊤ 2 φ)
  have hv : W1p.value v =ᵐ[volume.restrict (normalStrip (E := E) a b)] φ := by
    apply (W1p.value_restrictL_ae le_top _).trans
    rw [W1p.value_ofTestFunctionₗ]
    have hφ := testFunctionLp_apply_ae (mu := volume) 2 φ
    simp only [Opens.coe_top, Measure.restrict_univ] at hφ
    exact ae_restrict_of_ae hφ
  have hg : W1p.gradient v =ᵐ[volume.restrict (normalStrip (E := E) a b)] ∇ φ := by
    apply (W1p.gradient_restrictL_ae le_top _).trans
    rw [W1p.gradient_ofTestFunctionₗ]
    have hφ := gradientTestFunctionLp_apply_ae (mu := volume) 2 φ
    simp only [Opens.coe_top, Measure.restrict_univ] at hφ
    exact ae_restrict_of_ae hφ
  have hi : IntegrableOn (fun x ↦ ‖φ x‖ ^ 2) (normalStrip (E := E) a b) volume := by
    refine ((Lp.memLp (W1p.value v)).integrable_norm_pow (by norm_num)).congr ?_
    filter_upwards [hv] with x hx
    rw [hx]
  have hdi : IntegrableOn (fun x ↦ ‖fderiv ℝ φ x‖ ^ 2)
      (normalStrip (E := E) a b) volume := by
    refine ((Lp.memLp (W1p.gradient v)).integrable_norm_pow (by norm_num)).congr ?_
    filter_upwards [hg] with x hx
    rw [hx, norm_gradient_eq_norm_fderiv]
  refine ⟨hi, hdi, ?_⟩
  -- The value and gradient characteristic equations preserve the strip energy.
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
    ← W1p.integral_value_sq_eq_norm_value_sq,
    ← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq,
    ← integral_add (Lp.memLp (W1p.value v)).integrable_sq
      ((Lp.memLp (W1p.gradient v)).integrable_norm_pow (by norm_num))]
  apply integral_congr_ae
  filter_upwards [hv, hg] with x hx hy
  simp only [hx, hy, Real.norm_eq_abs, sq_abs, norm_gradient_eq_norm_fderiv]

private theorem norm_sq_hyperplaneTrace_ofTestFunction
    (c : ℝ) (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ‖W1p.hyperplaneTrace ENNReal.ofNat_ne_top c (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ ^ 2 =
      ∫ y : E, ‖φ (WithLp.toLp 2 (c, y))‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [W1p.hyperplaneTrace_ofTestFunction_apply_ae (p := 2) (by norm_num) c φ] with y hy
  rw [hy]

private theorem integral_strip_energy_le_weighted_energy
    {u : WithLp 2 (ℝ × E) → F} {a b : ℝ} (hab : a < b)
    (hv : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (normalStrip (E := E) a b) volume)
    (hd : IntegrableOn (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) (normalStrip (E := E) a b) volume) :
    (∫ x in normalStrip (E := E) a b,
      (2 / (b - a) + 1) * ‖u x‖ ^ 2 + ‖fderiv ℝ u x‖ ^ 2) ≤
    (2 / (b - a) + 1) * (∫ x in normalStrip (E := E) a b,
      ‖u x‖ ^ 2 + ‖fderiv ℝ u x‖ ^ 2) := by
  have hC : 1 ≤ 2 / (b - a) + 1 := by
    have : 0 ≤ 2 / (b - a) := by positivity
    linarith
  rw [← integral_const_mul]
  apply integral_mono ((hv.const_mul _).add hd) ((hv.add hd).const_mul _)
  intro x
  dsimp only [Pi.add_apply]
  nlinarith [sq_nonneg ‖fderiv ℝ u x‖]

private theorem norm_sq_hyperplaneTrace_add_le_strip_ofTestFunction
    {a b : ℝ} (hab : a < b) (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ‖W1p.hyperplaneTrace ENNReal.ofNat_ne_top a (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ ^ 2 +
      ‖W1p.hyperplaneTrace ENNReal.ofNat_ne_top b (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ ^ 2 ≤
      (2 / (b - a) + 1) * ‖W1p.restrictL
        (show normalStrip (E := E) a b ≤ ⊤ from le_top)
        (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ ^ 2 := by
  obtain ⟨hi, hdi, henergy⟩ := strip_energy_ofTestFunction a b φ
  have heq := congrArg₂ (· + ·) (norm_sq_hyperplaneTrace_ofTestFunction a φ)
    (norm_sq_hyperplaneTrace_ofTestFunction b φ)
  have hboundary := integral_boundary_norm_sq_le_integral_strip_energy
    (fun x _ ↦ (φ.contDiff.of_le (by norm_num)).contDiffAt)
    hab hi hdi
  exact heq.le.trans (hboundary.trans
    ((integral_strip_energy_le_weighted_energy hab hi hdi).trans_eq
      (congrArg ((2 / (b - a) + 1) * ·) henergy)))

/-- The combined squared norms of the two flat traces of a whole-space `H¹` function are
bounded by its Sobolev norm restricted to the strip. The bound uses no energy outside it. -/
theorem W1p.norm_sq_hyperplaneTrace_add_le_strip
    {a b : ℝ} (hab : a < b)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2) :
    ‖W1p.hyperplaneTrace ENNReal.ofNat_ne_top a u‖ ^ 2 +
        ‖W1p.hyperplaneTrace ENNReal.ofNat_ne_top b u‖ ^ 2 ≤
      (2 / (b - a) + 1) *
        ‖W1p.restrictL (show normalStrip (E := E) a b ≤ ⊤ from le_top) u‖ ^ 2 := by
  let R : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2 →L[ℝ]
      W1p volume (normalStrip (E := E) a b) 2 := W1p.restrictL le_top
  have hclosed : IsClosed {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2 |
      ‖W1p.hyperplaneTrace ENNReal.ofNat_ne_top a u‖ ^ 2 +
          ‖W1p.hyperplaneTrace ENNReal.ofNat_ne_top b u‖ ^ 2 ≤
        (2 / (b - a) + 1) *
          ‖W1p.restrictL (show normalStrip (E := E) a b ≤ ⊤ from le_top) u‖ ^ 2} :=
    isClosed_le
      (((W1p.hyperplaneTrace (E := E) (p := 2) ENNReal.ofNat_ne_top a).continuous.norm.pow 2).add
        ((W1p.hyperplaneTrace (E := E) (p := 2) ENNReal.ofNat_ne_top b).continuous.norm.pow 2))
      (continuous_const.mul (R.continuous.norm.pow 2))
  exact (W1p.denseRange_ofTestFunctionₗ_top
    (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 2) (by norm_num)).induction_on u
      hclosed (norm_sq_hyperplaneTrace_add_le_strip_ofTestFunction hab)

private theorem restrictL_eq_of_value_ae_eq_strip
    {a b : ℝ} {u v : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2}
    (hvalue : W1p.value u =ᵐ[volume.restrict (normalStrip (E := E) a b)] W1p.value v) :
    W1p.restrictL (show normalStrip (E := E) a b ≤ ⊤ from le_top) u =
      W1p.restrictL (show normalStrip (E := E) a b ≤ ⊤ from le_top) v := by
  apply W1p.ext_value
  apply Lp.ext
  exact ((W1p.value_restrictL_ae le_top u).trans hvalue).trans
    (W1p.value_restrictL_ae le_top v).symm

private theorem hyperplaneTrace_eq_zero_of_restrictL_eq_zero
    {a b : ℝ} (hab : a < b)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2)
    (hu : W1p.restrictL (show normalStrip (E := E) a b ≤ ⊤ from le_top) u = 0)
    {c : ℝ} (hc : c = a ∨ c = b) : W1p.hyperplaneTrace ENNReal.ofNat_ne_top c u = 0 := by
  have hb := W1p.norm_sq_hyperplaneTrace_add_le_strip hab u
  have hright : (2 / (b - a) + 1) *
      ‖W1p.restrictL (show normalStrip (E := E) a b ≤ ⊤ from le_top) u‖ ^ 2 = 0 := by
    simp only [hu, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
  have hz := sq_add_sq_eq_zero.mp (le_antisymm (hb.trans_eq hright)
    (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  rcases hc with rfl | rfl
  · exact norm_eq_zero.mp hz.1
  · exact norm_eq_zero.mp hz.2

/-- Whole-space `H¹` extensions whose values agree almost everywhere on the strip have the
same traces on either boundary. Equality of the gradients is not an additional hypothesis. -/
theorem W1p.hyperplaneTrace_eq_of_value_ae_eq_strip
    {a b : ℝ} (hab : a < b)
    {u v : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2}
    (hvalue : W1p.value u =ᵐ[volume.restrict (normalStrip (E := E) a b)] W1p.value v)
    {c : ℝ} (hc : c = a ∨ c = b) :
    W1p.hyperplaneTrace ENNReal.ofNat_ne_top c u =
      W1p.hyperplaneTrace ENNReal.ofNat_ne_top c v := by
  have heq := restrictL_eq_of_value_ae_eq_strip hvalue
  have hzero := hyperplaneTrace_eq_zero_of_restrictL_eq_zero hab (u - v)
    (by rw [ContinuousLinearMap.map_sub, heq, sub_self]) hc
  rw [ContinuousLinearMap.map_sub] at hzero
  exact sub_eq_zero.mp hzero

end TauCeti
