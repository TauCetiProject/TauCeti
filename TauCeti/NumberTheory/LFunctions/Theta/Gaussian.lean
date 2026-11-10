/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PoissonSummation
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction
public import TauCeti.NumberTheory.LFunctions.Theta.UnitFundamentalDomain

/-!
# Archimedean Gaussians and the unit-invariant theta kernel

Hecke's theta kernel has one positive parameter per infinite place, not just a radial
parameter. The Gaussian `archGaussian y x` is `exp (-π ∑ w, y w * |x w|²)`; a complex place
occurs once in this sum, in accordance with the Euclidean pairing `mixedInner`.

For positive parameters, the coordinatewise square-root dilation identifies this Gaussian with
the standard Euclidean Schwartz Gaussian. Its sum over any discrete lattice converges absolutely,
and the resulting theta series is continuous on the positive parameters
(`continuousAt_latticeTheta`), being dominated by its value at any smaller positive parameter
(`norm_latticeTheta_le`).
The sum `latticeTheta L y` is invariant under the parameter action of a unit when `L` is an ideal
lattice. This invariance is what allows integration over a fundamental domain on the norm-one
surface, rather than a divergent sum over infinitely many generators of each ideal.

The construction uses `SchwartzMap.gaussian` and `ZLattice.summable_poisson_left`; it does not
introduce another generic Euclidean Gaussian or a theta function on the upper half-plane.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§3 and 5.
-/

public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding TauCeti.NumberField.Units
open scoped Real SchwartzMap nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The archimedean Gaussian with one parameter per infinite place. A complex coordinate
counts once, not twice; the quadratic form is positive definite when every parameter is positive. -/
def archGaussian (y : realSpace K) (x : mixedSpace K) : ℂ :=
  ↑(Real.exp (-Real.pi * ∑ w, y w * normAtPlace w x ^ 2))

theorem archGaussian_apply (y : realSpace K) (x : mixedSpace K) :
    archGaussian y x = ↑(Real.exp (-Real.pi * ∑ w, y w * normAtPlace w x ^ 2)) := (rfl)

@[simp]
theorem archGaussian_zero (y : realSpace K) : archGaussian y 0 = 1 := by
  simp [archGaussian_apply]

/-- Archimedean Gaussians are positive real-valued. -/
theorem archGaussian_re_pos (y : realSpace K) (x : mixedSpace K) :
    0 < (archGaussian y x).re := Real.exp_pos _

@[simp]
theorem archGaussian_im (y : realSpace K) (x : mixedSpace K) :
    (archGaussian y x).im = 0 := (rfl)

/-- Moving a unit from the lattice variable to the parameters squares its absolute values. -/
theorem archGaussian_unit_smul (u : (𝓞 K)ˣ) (y : realSpace K) (x : mixedSpace K) :
    archGaussian y (u • x) = archGaussian (unitScale u y) x := by
  rw [archGaussian_apply, archGaussian_apply]
  congr 3
  apply Finset.sum_congr rfl
  intro w _
  rw [← congrFun (unitScale_sq_normAtPlace u x) w, unitScale_apply, unitScale_apply]
  ring

open scoped Classical in
/-- Coordinatewise dilation by `√(y w)` on the mixed space. Positivity makes it invertible;
its Euclidean Gaussian is the Gaussian at the parameter `y`. -/
def archGaussianDilation (y : realSpace K) (hy : ∀ w, 0 < y w) :
    mixedSpace K ≃L[ℝ] mixedSpace K :=
  let a := mixedSpaceOfRealSpace (fun w ↦ √(y w))
  have ha : IsUnit a := isUnit_iff_norm_ne_zero.mpr <|
    mixedEmbedding.norm_ne_zero_iff.mpr fun w ↦ by
      rw [normAtPlace_mixedSpaceOfRealSpace (Real.sqrt_nonneg _)]
      exact (Real.sqrt_pos.mpr (hy w)).ne'
  LinearEquiv.toContinuousLinearEquiv (ha.unit.mulLeftLinearEquiv ℝ (mixedSpace K))

@[simp]
theorem archGaussianDilation_apply (y : realSpace K) (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) :
    archGaussianDilation y hy x = mixedSpaceOfRealSpace (fun w ↦ √(y w)) * x := by
  simp [archGaussianDilation]

/-- The dilation multiplies the squared absolute value at `w` by `y w`. -/
theorem normAtPlace_archGaussianDilation_sq (y : realSpace K) (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (archGaussianDilation y hy x) ^ 2 = y w * normAtPlace w x ^ 2 := by
  rw [archGaussianDilation_apply, map_mul,
    normAtPlace_mixedSpaceOfRealSpace (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hy w).le]

/-- The Gaussian at the parameter `y` is the Gaussian at the constant parameter `1` after the
square-root dilation by `y`. -/
theorem archGaussian_one_archGaussianDilation (y : realSpace K) (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) : archGaussian 1 (archGaussianDilation y hy x) = archGaussian y x := by
  simp only [archGaussian_apply, normAtPlace_archGaussianDilation_sq, Pi.one_apply, one_mul]

/-- At a constant parameter, the Gaussian uses the Euclidean mixed-space pairing. -/
theorem archGaussian_const (t : ℝ) (x : mixedSpace K) :
    archGaussian (fun _ ↦ t) x = ↑(Real.exp (-Real.pi * (t * mixedInner K x x))) := by
  rw [archGaussian_apply, ← Finset.mul_sum, ← mixedInner_self_eq_sum]

/-- At the constant parameter `1`, the Gaussian uses the Euclidean mixed-space pairing. -/
theorem archGaussian_one (x : mixedSpace K) :
    archGaussian (1 : realSpace K) x = ↑(Real.exp (-Real.pi * mixedInner K x x)) := by
  simpa only [Pi.one_def, one_mul] using archGaussian_const (K := K) 1 x

open scoped Classical in
/-- The archimedean Gaussian is the standard Euclidean Gaussian after square-root dilation. -/
theorem archGaussian_eq_gaussian (y : realSpace K) (hy : ∀ w, 0 < y w) (x : mixedSpace K) :
    archGaussian y x = SchwartzMap.gaussian (V := euclidean.mixedSpace K)
      (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos)
      ((euclidean.toMixed K).symm (archGaussianDilation y hy x)) := by
  have hnorm : ‖(euclidean.toMixed K).symm (archGaussianDilation y hy x)‖ ^ 2 =
      ∑ w, y w * normAtPlace w x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      ← NumberField.mixedEmbedding.mixedInner_toMixed]
    simp only [ContinuousLinearEquiv.apply_symm_apply, mixedInner_self_eq_sum,
      normAtPlace_archGaussianDilation_sq]
  rw [archGaussian_apply, SchwartzMap.gaussian_apply, ← Complex.ofReal_pow, hnorm]
  simp

open scoped Classical in
/-- The archimedean Gaussian as a Schwartz function, obtained from the Euclidean Gaussian
by an invertible linear change of variables. -/
def archGaussianSchwartz (y : realSpace K) (hy : ∀ w, 0 < y w) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((archGaussianDilation y hy).trans (euclidean.toMixed K).symm)
    (SchwartzMap.gaussian (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos))

@[simp]
theorem archGaussianSchwartz_apply (y : realSpace K) (hy : ∀ w, 0 < y w) (x : mixedSpace K) :
    archGaussianSchwartz y hy x = archGaussian y x := by
  rw [archGaussianSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, ContinuousLinearEquiv.trans_apply]
  exact (archGaussian_eq_gaussian y hy x).symm

/-- Absolute convergence of the archimedean Gaussian over a discrete lattice, without a
full-rank assumption. -/
theorem summable_archGaussian (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    (y : realSpace K) (hy : ∀ w, 0 < y w) :
    Summable fun x : L ↦ archGaussian y x := by
  classical
  simpa using ZLattice.summable_poisson_left L (archGaussianSchwartz y hy) 0

/-- Absolute convergence of the archimedean Gaussian over a discrete lattice, in norm. -/
theorem summable_norm_archGaussian (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    (y : realSpace K) (hy : ∀ w, 0 < y w) :
    Summable fun x : L ↦ ‖archGaussian y x‖ :=
  summable_norm_iff.mpr (summable_archGaussian L y hy)

/-- Increasing the parameters decreases the archimedean Gaussian. -/
theorem norm_archGaussian_le {y y' : realSpace K} (h : ∀ w, y' w ≤ y w) (x : mixedSpace K) :
    ‖archGaussian y x‖ ≤ ‖archGaussian y' x‖ := by
  simp only [archGaussian_apply, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
    Real.exp_le_exp, neg_mul, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_right (h w) (sq_nonneg _)) Real.pi_pos.le

/-- The archimedean Gaussian at a fixed point depends continuously on the parameters. -/
theorem continuous_archGaussian (x : mixedSpace K) :
    Continuous fun y : realSpace K ↦ archGaussian y x := by
  simp only [archGaussian_apply]
  fun_prop

/-- The theta kernel of a lattice at a parameter with one coordinate per infinite place.
Its defining series converges when `L` is discrete and all the coordinates of `y` are positive. -/
def latticeTheta (L : Submodule ℤ (mixedSpace K)) (y : realSpace K) : ℂ :=
  ∑' x : L, archGaussian y x

theorem latticeTheta_def (L : Submodule ℤ (mixedSpace K)) (y : realSpace K) :
    latticeTheta L y = ∑' x : L, archGaussian y x := (rfl)

/-- The archimedean Gaussian is not summable over a non-discrete lattice: it is continuous with
value `1` at `0`, but `0` is a limit of other lattice points. -/
theorem not_summable_archGaussian_of_not_discreteTopology (L : Submodule ℤ (mixedSpace K))
    (hL : ¬ DiscreteTopology L) (y : realSpace K) : ¬ Summable fun x : L ↦ archGaussian y x := by
  intro hs
  have hg : Continuous fun x : L ↦ archGaussian y x := by
    simp only [archGaussian_apply]
    fun_prop
  have hne : (nhdsWithin (0 : L) {0}ᶜ).NeBot := by
    rw [Filter.neBot_iff]
    intro h
    exact hL (discreteTopology_iff_isOpen_singleton_zero.2
      ((isOpen_singleton_iff_punctured_nhds _).2 h))
  have h1 : Filter.Tendsto (fun x : L ↦ archGaussian y x) (nhdsWithin (0 : L) {0}ᶜ) (nhds 1) := by
    simpa using (hg.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun x : L ↦ archGaussian y x) (nhdsWithin (0 : L) {0}ᶜ) (nhds 0) :=
    hs.tendsto_cofinite_zero.mono_left (nhdsNE_le_cofinite 0)
  exact one_ne_zero (tendsto_nhds_unique h1 h2)

/-- The theta series of a non-discrete lattice is `0`, by the convention for non-summable
series. -/
theorem latticeTheta_eq_zero_of_not_discreteTopology (L : Submodule ℤ (mixedSpace K))
    (hL : ¬ DiscreteTopology L) (y : realSpace K) : latticeTheta L y = 0 :=
  tsum_eq_zero_of_not_summable (not_summable_archGaussian_of_not_discreteTopology L hL y)

/-- The zero lattice point supplies the constant term `1`. -/
theorem latticeTheta_eq_one_add (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    (y : realSpace K) (hy : ∀ w, 0 < y w) :
    latticeTheta L y = 1 + ∑' x : {x : L // x ≠ 0}, archGaussian y x := by
  classical
  rw [latticeTheta_def, ← (summable_archGaussian L y hy).sum_add_tsum_subtype_compl {0}]
  simp only [Finset.sum_singleton, Submodule.coe_zero, archGaussian_zero]
  congr 1
  let e : {x : L // x ∉ ({0} : Finset L)} ≃ {x : L // x ≠ 0} :=
    Equiv.subtypeEquivRight fun x ↦ by simp
  exact e.tsum_eq (fun x ↦ archGaussian y (x : L))

/-- The theta series is dominated by its value at any smaller positive parameter; for a discrete
lattice that value is a positive real number, and for a non-discrete one both sides are `0`. -/
theorem norm_latticeTheta_le (L : Submodule ℤ (mixedSpace K))
    {y y' : realSpace K} (hy' : ∀ w, 0 < y' w) (h : ∀ w, y' w ≤ y w) :
    ‖latticeTheta L y‖ ≤ ‖latticeTheta L y'‖ := by
  by_cases hL : DiscreteTopology L
  swap
  · simp [latticeTheta_eq_zero_of_not_discreteTopology L hL]
  have hy : ∀ w, 0 < y w := fun w ↦ (hy' w).trans_le (h w)
  have hnorm : ‖latticeTheta L y'‖ = ∑' x : L, ‖archGaussian y' x‖ := by
    simp only [latticeTheta_def, archGaussian_apply, Complex.norm_real, Real.norm_eq_abs,
      Real.abs_exp, ← Complex.ofReal_tsum]
    exact abs_of_nonneg (tsum_nonneg fun _ ↦ (Real.exp_pos _).le)
  rw [hnorm, latticeTheta_def]
  exact (norm_tsum_le_tsum_norm (summable_norm_archGaussian L y hy)).trans
    ((summable_norm_archGaussian L y hy).tsum_le_tsum (fun x ↦ norm_archGaussian_le h x)
      (summable_norm_archGaussian L y' hy'))

/-- The theta series is continuous at every positive parameter: for a discrete lattice, on the
parameters bounded below by a positive constant, its terms are dominated by the Gaussian at that
constant. -/
theorem continuousAt_latticeTheta (L : Submodule ℤ (mixedSpace K))
    {y₀ : realSpace K} (hy₀ : ∀ w, 0 < y₀ w) : ContinuousAt (latticeTheta L) y₀ := by
  by_cases hL : DiscreteTopology L
  swap
  · rw [show latticeTheta L = 0 from
      funext (latticeTheta_eq_zero_of_not_discreteTopology L hL)]
    exact continuousAt_const
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_min_image Finset.univ y₀ Finset.univ_nonempty
  set δ := y₀ w₀ / 2
  have hδ : 0 < δ := half_pos (hy₀ w₀)
  have hU : IsOpen {y : realSpace K | ∀ w, δ < y w} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w ↦ isOpen_lt continuous_const (continuous_apply w)
  have hy₀U : y₀ ∈ {y : realSpace K | ∀ w, δ < y w} := fun w ↦
    (half_lt_self (hy₀ w₀)).trans_le (hw₀ w (Finset.mem_univ w))
  have hcont : ContinuousOn (latticeTheta L) {y : realSpace K | ∀ w, δ < y w} :=
    continuousOn_tsum (fun x ↦ (continuous_archGaussian (x : mixedSpace K)).continuousOn)
      (summable_norm_archGaussian L (fun _ ↦ δ) fun _ ↦ hδ)
      fun x y hy ↦ norm_archGaussian_le (fun w ↦ (hy w).le) x
  exact hcont.continuousAt (hU.mem_nhds hy₀U)

/-- The theta series of an ideal lattice descends to the quotient of positive parameters
by the unit action. No restriction on the unit rank is needed. -/
@[simp]
theorem latticeTheta_unitScale (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ)
    (y : realSpace K) :
    latticeTheta (idealLattice K I) (unitScale u y) = latticeTheta (idealLattice K I) y := by
  simp only [latticeTheta_def]
  conv_rhs => rw [← (u.unitSMulIdealLatticeEquiv I).tsum_eq]
  exact tsum_congr fun x ↦ by
    rw [Units.unitSMulIdealLatticeEquiv_apply, archGaussian_unit_smul]

end TauCeti.LFunctions
