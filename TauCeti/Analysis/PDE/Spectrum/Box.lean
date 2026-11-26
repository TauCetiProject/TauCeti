/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Basic
public import TauCeti.Analysis.PDE.ClassicalSolution
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.Deriv.Second
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Fourier.SineCosineSeries
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Dirichlet spectrum of `-Δ` on a box

On a product of bounded intervals `(aᵢ,bᵢ)`, the products
`∏ᵢ sin (kᵢ π (xᵢ - aᵢ) / (bᵢ - aᵢ))`, with positive integer indices, are nonzero
Dirichlet eigenfunctions of `-Δ`, with eigenvalue `∑ᵢ (kᵢ π / (bᵢ - aᵢ))²`.
We prove the classical equation and vanishing on the frontier, then realize these functions
in `H¹₀` with their weak eigenfunction identity. No smoothness of the boundary is needed.

Conversely, these separated modes exhaust the spectrum. They are complete: a function integrable
on the box and orthogonal to all of them vanishes
(`TauCeti.PDE.ae_eq_zero_of_forall_setIntegral_mul_boxSineMode_eq_zero`, from the completeness
of the product sine system `TauCeti.ae_eq_zero_of_forall_setIntegral_mul_prod_sin_eq_zero`). The
energy form of `-Δ` is symmetric, so an eigenfunction with eigenvalue `κ` is orthogonal to the
modes with other eigenvalues; subtracting its projection onto the finitely many modes with
eigenvalue `κ` leaves a function orthogonal to every mode. Hence every Dirichlet eigenfunction is
a finite combination of separated modes with the same eigenvalue
(`TauCeti.PDE.exists_finset_value_ae_eq_sum_boxSineMode`), and the Dirichlet eigenvalues of `-Δ`
on the box are exactly the sums `∑ᵢ (kᵢ π / (bᵢ - aᵢ))²`
(`TauCeti.PDE.isDirichletEigenvalue_laplacian_boxDomain_iff`). An eigenvalue may have several
separated modes: on `(0, π)²` the value `5 = 1² + 2² = 2² + 1²` is attained twice.

The passage from classical to weak eigenfunctions uses
`TauCeti.PDE.exists_value_ae_eq_and_energyFormH1_eq_of_laplacian_eq`.
The coordinate calculation uses `TauCeti.fderiv_fderiv_prod_comp_eval_apply_single_single`.

## References

* L. C. Evans, *Partial Differential Equations*, §6.5.1 (Dirichlet eigenvalues and
  separation of variables).
-/

public section

noncomputable section

open Bornology InnerProductSpace Laplacian MeasureTheory Set TopologicalSpace
open scoped BigOperators

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι]

/-- The product of the open intervals `(aᵢ,bᵢ)` in Euclidean space. -/
def boxDomain (a b : ι → ℝ) : Opens (EuclideanSpace ℝ ι) :=
  ⟨⋂ i, (fun x : EuclideanSpace ℝ ι ↦ x i) ⁻¹' Ioo (a i) (b i),
    isOpen_iInter_of_finite fun i ↦ isOpen_Ioo.preimage
      (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i)⟩

@[simp]
theorem mem_boxDomain {a b : ι → ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ boxDomain a b ↔ ∀ i, x i ∈ Ioo (a i) (b i) := by
  simp only [boxDomain, Opens.mem_mk, mem_iInter, mem_preimage]

/-- The closure of the open box is contained in the corresponding closed box, including
when one of the intervals is empty. -/
theorem closure_boxDomain_subset (a b : ι → ℝ) :
    closure (boxDomain a b : Set (EuclideanSpace ℝ ι)) ⊆
      {x | ∀ i, x i ∈ Icc (a i) (b i)} := by
  intro x hx i
  have hsub : (boxDomain a b : Set (EuclideanSpace ℝ ι)) ⊆
      (fun y : EuclideanSpace ℝ ι ↦ y i) ⁻¹' Icc (a i) (b i) :=
    fun y hy ↦ Ioo_subset_Icc_self (mem_boxDomain.mp hy i)
  exact closure_minimal hsub (isClosed_Icc.preimage
    (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i)) hx

/-- A finite product of bounded intervals is bounded in the Euclidean norm. -/
theorem isBounded_boxDomain (a b : ι → ℝ) :
    IsBounded (boxDomain a b : Set (EuclideanSpace ℝ ι)) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)
  have hc : IsCompact (e ⁻¹' Icc a b) := e.toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  exact hc.isBounded.subset fun x hx ↦
    ⟨fun i ↦ (mem_boxDomain.mp hx i).1.le, fun i ↦ (mem_boxDomain.mp hx i).2.le⟩

/-- A point on the frontier of a box lies on at least one of its coordinate faces. -/
theorem exists_eq_endpoint_of_mem_frontier_boxDomain {a b : ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hx : x ∈ frontier (boxDomain a b : Set (EuclideanSpace ℝ ι))) :
    ∃ i, x i = a i ∨ x i = b i := by
  have hc := closure_boxDomain_subset a b (frontier_subset_closure hx)
  by_contra! h
  have hi : x ∈ boxDomain a b := mem_boxDomain.mpr fun i ↦
    ⟨lt_of_le_of_ne (hc i).1 (h i).1.symm, lt_of_le_of_ne (hc i).2 (h i).2⟩
  exact disjoint_frontier_iff_isOpen.mpr (boxDomain a b).isOpen |>.notMem_of_mem_right hi hx

/-- A box `∏ⱼ (aⱼ, bⱼ)` with `aⱼ < bⱼ` for every `j` is nonempty: it contains its centre. -/
theorem nonempty_boxDomain {a b : ι → ℝ} (hab : ∀ j, a j < b j) :
    (boxDomain a b : Set (EuclideanSpace ℝ ι)).Nonempty :=
  ⟨WithLp.toLp 2 fun j ↦ (a j + b j) / 2, mem_boxDomain.2 fun j ↦
    ⟨by simp; linarith [hab j], by simp; linarith [hab j]⟩⟩

/-- A function continuous on the closure of a box is integrable on the box, for every measure
that is finite on compact sets. -/
theorem integrableOn_boxDomain {E : Type*} [NormedAddCommGroup E] {a b : ι → ℝ}
    {mu : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasureOnCompacts mu]
    {F : EuclideanSpace ℝ ι → E} (hF : ContinuousOn F (closure (boxDomain a b))) :
    IntegrableOn F (boxDomain a b) mu :=
  (hF.integrableOn_compact (isBounded_boxDomain a b).isCompact_closure).mono_set subset_closure

/-- The line through `x` parallel to the `i`-th axis meets the box in its `i`-th side exactly when
the other coordinates of `x` lie in the box. -/
theorem toLp_update_mem_boxDomain_iff [DecidableEq ι] {a b : ι → ℝ} {i : ι} (x : ι → ℝ)
    (t : ℝ) :
    WithLp.toLp 2 (Function.update x i t) ∈ (boxDomain a b : Set (EuclideanSpace ℝ ι)) ↔
      t ∈ Ioo (a i) (b i) ∧ ∀ j ≠ i, x j ∈ Ioo (a j) (b j) := by
  simp only [SetLike.mem_coe, mem_boxDomain]
  refine ⟨fun h ↦ ⟨by simpa using h i, fun j hj ↦ by simpa [hj] using h j⟩, fun h j ↦ ?_⟩
  by_cases hj : j = i
  · subst hj
    simpa using h.1
  · simpa [hj] using h.2 j hj

/-- A part of the hyperplane `xᵢ = aᵢ` misses the box `∏ⱼ (aⱼ, bⱼ)`. -/
theorem disjoint_boxDomain_of_forall_apply_eq_left {a b : ι → ℝ} {i : ι}
    {Γ : Set (EuclideanSpace ℝ ι)} (hΓ : ∀ x ∈ Γ, x i = a i) :
    Disjoint Γ (boxDomain a b : Set (EuclideanSpace ℝ ι)) :=
  Set.disjoint_left.2 fun x hx hxΩ ↦ by
    have := (mem_boxDomain.1 hxΩ i).1
    rw [hΓ x hx] at this
    exact lt_irrefl _ this

/-- Along the line through `x` parallel to the `i`-th axis, the integral over the box is the
integral over the `i`-th side when the other coordinates of `x` lie in the box, and `0`
otherwise. -/
theorem lintegral_indicator_boxDomain_toLp_update [DecidableEq ι] {a b : ι → ℝ} {i : ι}
    (F : EuclideanSpace ℝ ι → ENNReal) (x : ι → ℝ) :
    ∫⁻ t, (boxDomain a b : Set (EuclideanSpace ℝ ι)).indicator F
        (WithLp.toLp 2 (Function.update x i t)) =
      if ∀ j ≠ i, x j ∈ Ioo (a j) (b j) then
        ∫⁻ t in Ioo (a i) (b i), F (WithLp.toLp 2 (Function.update x i t)) else 0 := by
  classical
  split_ifs with hx
  · rw [← lintegral_indicator measurableSet_Ioo]
    congr 1
    ext t
    simp only [Set.indicator_apply, toLp_update_mem_boxDomain_iff, and_iff_left hx]
  · simp only [Set.indicator_apply, toLp_update_mem_boxDomain_iff, hx, and_false, ite_false,
      lintegral_zero]

/-- **Comparison of integrals over a box along the lines parallel to one axis.** If `F, G ≥ 0` are
continuous and the integral of `F` over each segment of the box parallel to the `i`-th axis is at
most that of `G`, then `∫_Ω F ≤ ∫_Ω G`, for every additive Haar measure. -/
theorem setIntegral_boxDomain_le [DecidableEq ι] {a b : ι → ℝ} {i : ι}
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure] {F G : EuclideanSpace ℝ ι → ℝ}
    (hF : Continuous F) (hG : Continuous G) (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (h : ∀ x : ι → ℝ, (∀ j ≠ i, x j ∈ Ioo (a j) (b j)) →
      ∫⁻ t in Ioo (a i) (b i), ENNReal.ofReal (F (WithLp.toLp 2 (Function.update x i t))) ≤
        ∫⁻ t in Ioo (a i) (b i), ENNReal.ofReal (G (WithLp.toLp 2 (Function.update x i t)))) :
    ∫ x in boxDomain a b, F x ∂mu ≤ ∫ x in boxDomain a b, G x ∂mu := by
  have hΩ : MeasurableSet (boxDomain a b : Set (EuclideanSpace ℝ ι)) :=
    (boxDomain a b).isOpen.measurableSet
  rw [← ENNReal.ofReal_le_ofReal_iff (setIntegral_nonneg hΩ fun x _ => hG0 x),
    ofReal_integral_eq_lintegral_ofReal (f := F) (integrableOn_boxDomain hF.continuousOn)
      (ae_of_all _ hF0),
    ofReal_integral_eq_lintegral_ofReal (f := G) (integrableOn_boxDomain hG.continuousOn)
      (ae_of_all _ hG0),
    ← lintegral_indicator hΩ, ← lintegral_indicator hΩ]
  refine lintegral_le_lintegral_of_forall_lintegral_update_le mu
    (hF.measurable.ennreal_ofReal.indicator hΩ) (hG.measurable.ennreal_ofReal.indicator hΩ) i
    fun x => ?_
  rw [lintegral_indicator_boxDomain_toLp_update, lintegral_indicator_boxDomain_toLp_update]
  split_ifs with hx
  · exact h x hx
  · exact le_rfl

/-- The separated sine mode of a rectangular box, extended smoothly to the whole space. -/
def boxSineMode (a b : ι → ℝ) (k : ι → ℕ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i, Real.sin ((k i * Real.pi / (b i - a i)) * (x i - a i))

/-- The product formula for the separated sine mode. -/
theorem boxSineMode_def (a b : ι → ℝ) (k : ι → ℕ) (x : EuclideanSpace ℝ ι) :
    boxSineMode a b k x =
      ∏ i, Real.sin ((k i * Real.pi / (b i - a i)) * (x i - a i)) := (rfl)

/-- The separated modes are smooth on the whole Euclidean space. -/
theorem contDiff_boxSineMode (a b : ι → ℝ) (k : ι → ℕ) :
    ContDiff ℝ ⊤ (boxSineMode a b k) := by
  have _ : ContDiff ℝ ⊤ (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) :=
    PiLp.contDiff_ofLp
  unfold boxSineMode
  fun_prop

/-- The separated sine modes vanish on every face of the box. -/
theorem boxSineMode_eq_zero_of_mem_frontier {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    (k : ι → ℕ) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ frontier (boxDomain a b : Set (EuclideanSpace ℝ ι))) :
    boxSineMode a b k x = 0 := by
  classical
  obtain ⟨i, hi | hi⟩ := exists_eq_endpoint_of_mem_frontier_boxDomain hx
  · exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hi, div_mul_cancel₀ _ (sub_pos.mpr (hab i)).ne']
    exact Real.sin_nat_mul_pi (k i)

/-- The classical separated-variable equation for the Dirichlet Laplacian. -/
theorem laplacian_boxSineMode (a b : ι → ℝ) (k : ι → ℕ) (x : EuclideanSpace ℝ ι) :
    Δ (boxSineMode a b k) x =
      -(∑ i, (k i * Real.pi / (b i - a i)) ^ 2) * boxSineMode a b k x := by
  classical
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)
  let f : (ι → ℝ) → ℝ := fun y ↦
    ∏ i, Real.sin ((k i * Real.pi / (b i - a i)) * (y i - a i))
  have he : boxSineMode a b k = f ∘ e := by
    funext y
    rw [boxSineMode_def]
    simp only [Function.comp_apply, f, e, PiLp.continuousLinearEquiv_apply]
  rw [he, laplacian_comp_continuousLinearEquiv_right_apply e (EuclideanSpace.basisFun ι ℝ)]
  have hterm (i : ι) :
      iteratedFDeriv ℝ 2 f (e x) ![e (EuclideanSpace.basisFun ι ℝ i),
        e (EuclideanSpace.basisFun ι ℝ i)] =
      -(k i * Real.pi / (b i - a i)) ^ 2 * boxSineMode a b k x := by
    have hb : e (EuclideanSpace.basisFun ι ℝ i) = Pi.single i 1 := by
      rw [EuclideanSpace.basisFun_apply, PiLp.coe_continuousLinearEquiv]
      exact PiLp.ofLp_single 2 i 1
    simp only [iteratedFDeriv_two_apply, hb, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [fderiv_fderiv_prod_comp_eval_apply_single_single
      (φ := fun j t ↦ Real.sin ((k j * Real.pi / (b j - a j)) * (t - a j)))
      (fun j ↦ by fun_prop) i]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    have hD (c d t : ℝ) : deriv (deriv (fun s ↦ Real.sin (c * (s - d)))) t =
        -c ^ 2 * Real.sin (c * (t - d)) := by
      have h := congrFun (iteratedDeriv_comp_sub_const (n := 2)
        (f := fun s ↦ Real.sin (c * s)) (s := d)) t
      rw [iteratedDeriv_comp_mul_left] at h
      simpa [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_sin,
        Real.deriv_cos', smul_eq_mul, mul_comm] using h
    rw [hD, boxSineMode_def, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [e, PiLp.continuousLinearEquiv_apply, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.sum_neg_distrib, ← he]

private theorem exists_boxSineMode_eq_one {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {k : ι → ℕ} (hk : ∀ i, 0 < k i) :
    ∃ x ∈ boxDomain a b, boxSineMode a b k x = 1 := by
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ a i + (b i - a i) / (2 * k i)
  have hk' (i : ι) : (1 : ℝ) ≤ k i := by exact_mod_cast hk i
  have hba (i : ι) : 0 < b i - a i := sub_pos.mpr (hab i)
  refine ⟨x, mem_boxDomain.mpr (fun i ↦ ?_), ?_⟩
  · have hki : (0 : ℝ) < k i := lt_of_lt_of_le zero_lt_one (hk' i)
    have hpos : 0 < (b i - a i) / (2 * k i) := div_pos (hba i) (by positivity)
    have hlt : (b i - a i) / (2 * k i) < b i - a i :=
      div_lt_self (hba i) (by linarith [hk' i])
    simp only [x]
    constructor <;> linarith
  · rw [boxSineMode_def]
    apply Finset.prod_eq_one
    intro i _
    have harg : (k i * Real.pi / (b i - a i)) * (x i - a i) = Real.pi / 2 := by
      simp only [x]
      field_simp [(hba i).ne', (lt_of_lt_of_le zero_lt_one (hk' i)).ne']
      ring
    rw [harg, Real.sin_pi_div_two]

variable [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]

/-- The separated sine mode is the value of an `H¹₀` function satisfying the weak
Dirichlet eigenfunction identity. This also allows zero indices, when the mode vanishes. -/
theorem exists_value_ae_eq_boxSineMode_and_energyFormH1_eq {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) (k : ι → ℕ) :
    ∃ u : W1p0 mu (boxDomain a b) 2,
      W1p.value (u : W1p mu (boxDomain a b) 2)
        =ᵐ[mu.restrict (boxDomain a b : Set (EuclideanSpace ℝ ι))] boxSineMode a b k ∧
      ∀ v : W1p0 mu (boxDomain a b) 2,
        energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p mu (boxDomain a b) 2)
          (v : W1p mu (boxDomain a b) 2) =
        (∑ i, (k i * Real.pi / (b i - a i)) ^ 2) *
          ⟪W1p.value (u : W1p mu (boxDomain a b) 2),
            W1p.value (v : W1p mu (boxDomain a b) 2)⟫_ℝ :=
  exists_value_ae_eq_and_energyFormH1_eq_of_laplacian_eq (isBounded_boxDomain a b)
    ((contDiff_boxSineMode a b k).of_le le_top).contDiffOn
    (contDiff_boxSineMode a b k).continuous.continuousOn
    (fun _ hx ↦ boxSineMode_eq_zero_of_mem_frontier hab k hx)
    (fun x _ ↦ laplacian_boxSineMode a b k x)

/-- Every positive multi-index gives a Dirichlet eigenvalue of `-Δ` on a box. Its
nonzero eigenfunction is the product of the corresponding one-dimensional sine modes. -/
theorem isDirichletEigenvalue_laplacian_boxDomain {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) {k : ι → ℕ} (hk : ∀ i, 0 < k i) :
    IsDirichletEigenvalue mu (boxDomain a b) (fun _ ↦ 1) 0 0
      (∑ i, (k i * Real.pi / (b i - a i)) ^ 2) := by
  obtain ⟨u, hu, heq⟩ := exists_value_ae_eq_boxSineMode_and_energyFormH1_eq (mu := mu) hab k
  refine (isDirichletEigenvalue_iff_setIntegral _).mpr
    ⟨u, fun h0 ↦ ?_, fun v ↦ by rw [heq v, W1p.inner_value_eq_setIntegral]⟩
  have hval : W1p.value (u : W1p mu (boxDomain a b) 2) = 0 := by
    rw [← W1p0.valueL_apply, h0, map_zero]
  have hz : EqOn (boxSineMode a b k) 0 (boxDomain a b) := by
    refine Measure.eqOn_open_of_ae_eq (μ := mu) ?_ (boxDomain a b).isOpen
      (contDiff_boxSineMode a b k).continuous.continuousOn continuousOn_const
    filter_upwards [hu, Lp.coeFn_zero ℝ 2
      (mu.restrict (boxDomain a b : Set (EuclideanSpace ℝ ι)))] with x h1 h2
    rw [← h1, hval, h2]
  obtain ⟨x, hx, hpeak⟩ := exists_boxSineMode_eq_one hab hk
  simpa [hpeak] using hz hx

omit [DecidableEq ι] in
/-- **Completeness of the separated modes on a box.** A function integrable on a box and
orthogonal to every separated sine mode with positive indices vanishes almost everywhere on the
box. -/
theorem ae_eq_zero_of_forall_setIntegral_mul_boxSineMode_eq_zero {a b : ι → ℝ}
    {g : EuclideanSpace ℝ ι → ℝ} (hg : IntegrableOn g (boxDomain a b) mu)
    (h : ∀ k : ι → ℕ, (∀ i, 0 < k i) →
      ∫ x in boxDomain a b, g x * boxSineMode a b k x ∂mu = 0) :
    g =ᵐ[mu.restrict (boxDomain a b)] 0 := by
  -- Reduce from the Haar measure `mu` to the volume, a positive multiple of it.
  set c := mu.addHaarScalarFactor volume
  have hmu : mu = c • volume := Measure.isAddLeftInvariant_eq_smul mu volume
  have hc : c ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure mu volume).ne'
  rw [hmu, Measure.restrict_smul]
  refine Measure.ae_smul_measure ?_ _
  rw [hmu, IntegrableOn, Measure.restrict_smul, ENNReal.smul_def,
    integrable_smul_measure (by exact_mod_cast hc) ENNReal.coe_ne_top] at hg
  -- Read `g` on `ι → ℝ`, where the product sine system is complete.
  let T := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hT : MeasurePreserving T volume volume := PiLp.volume_preserving_toLp ι
  have hpre : T ⁻¹' (boxDomain a b : Set (EuclideanSpace ℝ ι)) =
      univ.pi fun i => Ioo (a i) (b i) := by
    ext y
    simp [T]
  have hTΩ : MeasurePreserving T (volume.restrict (univ.pi fun i => Ioo (a i) (b i)))
      (volume.restrict (boxDomain a b : Set (EuclideanSpace ℝ ι))) := by
    rw [← hpre]
    exact hT.restrict_preimage (boxDomain a b).isOpen.measurableSet
  have hzero := ae_eq_zero_of_forall_setIntegral_mul_prod_sin_eq_zero (g := g ∘ T)
    (hTΩ.integrable_comp_emb T.measurableEmbedding |>.2 hg) fun k hk => by
      have hk' := h k hk
      rw [hmu, Measure.restrict_smul, integral_smul_nnreal_measure, smul_eq_zero] at hk'
      rw [← hk'.resolve_left hc, ← hTΩ.integral_comp']
      congr 1 with y
      simp only [Function.comp_apply, boxSineMode_def]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [T, MeasurableEquiv.coe_toLp, PiLp.toLp_apply]
      ring_nf
  have hge : (g ∘ T) ∘ T.symm = g := funext fun x => by simp
  rw [← hge]
  exact (hTΩ.symm T).quasiMeasurePreserving.ae_eq_comp hzero

omit [DecidableEq ι] in
/-- Only finitely many positive multi-indices give the same separated eigenvalue: `κ` bounds
each index, since `kᵢ ≤ kᵢ² ≤ κ ((bᵢ - aᵢ) / π)²`. -/
private theorem finite_setOf_forall_pos_and_sum_sq_eq {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    (kappa : ℝ) :
    {k : ι → ℕ | (∀ i, 0 < k i) ∧
      ∑ i, (k i * Real.pi / (b i - a i)) ^ 2 = kappa}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_ge (kappa * ∑ i, ((b i - a i) / Real.pi) ^ 2)
  refine (Set.Finite.pi fun _ ↦ Set.finite_Iic N).subset fun k hk ↦
    Set.mem_univ_pi.2 fun i ↦ Set.mem_Iic.2 ?_
  have hL : 0 < b i - a i := sub_pos.2 (hab i)
  have hk1 : (1 : ℝ) ≤ k i := by exact_mod_cast hk.1 i
  have hκ : 0 ≤ kappa := hk.2 ▸ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have h3 : (k i * Real.pi / (b i - a i)) ^ 2 ≤ kappa :=
    hk.2 ▸ Finset.single_le_sum (fun j _ ↦ sq_nonneg (k j * Real.pi / (b j - a j)))
      (Finset.mem_univ i)
  have h4 : ((b i - a i) / Real.pi) ^ 2 ≤ ∑ j, ((b j - a j) / Real.pi) ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ((b j - a j) / Real.pi)) (Finset.mem_univ i)
  have hsq : (k i : ℝ) ^ 2 =
      (k i * Real.pi / (b i - a i)) ^ 2 * ((b i - a i) / Real.pi) ^ 2 := by
    field_simp
  have : (k i : ℝ) ≤ N := calc
    (k i : ℝ) ≤ (k i : ℝ) ^ 2 := by nlinarith
    _ ≤ kappa * ((b i - a i) / Real.pi) ^ 2 := by rw [hsq]; gcongr
    _ ≤ kappa * ∑ j, ((b j - a j) / Real.pi) ^ 2 := by gcongr
    _ ≤ N := hN
  exact_mod_cast this

/-- Given `H¹₀` realizations `φ k` of the separated modes, an eigenfunction with eigenvalue `κ`
lies in the span of the realizations whose eigenvalue is `κ`. Its orthogonal projection onto that
finite-dimensional span differs from it by a function orthogonal to every mode, which vanishes by
completeness. -/
private theorem value_mem_span_of_energyFormH1_eq {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {φ : (ι → ℕ) → W1p0 mu (boxDomain a b) 2}
    (hφ : ∀ k, W1p.value (φ k : W1p mu (boxDomain a b) 2)
      =ᵐ[mu.restrict (boxDomain a b : Set (EuclideanSpace ℝ ι))] boxSineMode a b k)
    (hφeq : ∀ k (v : W1p0 mu (boxDomain a b) 2),
      energyFormH1 (fun _ ↦ 1) 0 0 (φ k : W1p mu (boxDomain a b) 2)
          (v : W1p mu (boxDomain a b) 2) =
        (∑ i, (k i * Real.pi / (b i - a i)) ^ 2) *
          ⟪W1p.value (φ k : W1p mu (boxDomain a b) 2), W1p.value (v : W1p mu (boxDomain a b) 2)⟫_ℝ)
    {kappa : ℝ} {u : W1p0 mu (boxDomain a b) 2}
    (hu : ∀ v : W1p0 mu (boxDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p mu (boxDomain a b) 2)
          (v : W1p mu (boxDomain a b) 2) =
        kappa * ⟪W1p.value (u : W1p mu (boxDomain a b) 2),
          W1p.value (v : W1p mu (boxDomain a b) 2)⟫_ℝ) :
    W1p.value (u : W1p mu (boxDomain a b) 2) ∈ Submodule.span ℝ
      ((fun k ↦ W1p.value (φ k : W1p mu (boxDomain a b) 2)) ''
        {k | (∀ i, 0 < k i) ∧ ∑ i, (k i * Real.pi / (b i - a i)) ^ 2 = kappa}) := by
  have : IsFiniteMeasure (mu.restrict (boxDomain a b : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 (isBounded_boxDomain a b).measure_lt_top.ne
  have hsymm : ∀ᵐ x ∂mu.restrict (boxDomain a b : Set (EuclideanSpace ℝ ι)),
      ((fun _ ↦ (1 : Matrix ι ι ℝ)) x).IsSymm := ae_of_all _ fun _ ↦ Matrix.isSymm_one
  set ψ := fun k ↦ W1p.value (φ k : W1p mu (boxDomain a b) 2)
  set S : Set (ι → ℕ) := {k | (∀ i, 0 < k i) ∧ ∑ i, (k i * Real.pi / (b i - a i)) ^ 2 = kappa}
  set V := Submodule.span ℝ (ψ '' S)
  have : FiniteDimensional ℝ V :=
    FiniteDimensional.span_of_finite ℝ ((finite_setOf_forall_pos_and_sum_sq_eq hab kappa).image ψ)
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  set w := W1p.value (u : W1p mu (boxDomain a b) 2) -
    V.starProjection (W1p.value (u : W1p mu (boxDomain a b) 2))
  -- The remainder `w` is orthogonal to every mode: to those in `V` by construction, and to the
  -- others because their eigenvalues differ from `κ`.
  have hw (k : ι → ℕ) (hk : ∀ i, 0 < k i) : ⟪w, ψ k⟫_ℝ = 0 := by
    by_cases hkS : k ∈ S
    · rw [real_inner_comm]
      exact V.inner_right_of_mem_orthogonal (Submodule.subset_span ⟨k, hkS, rfl⟩)
        (V.sub_starProjection_mem_orthogonal _)
    · have hne : ∑ i, (k i * Real.pi / (b i - a i)) ^ 2 ≠ kappa := fun h ↦ hkS ⟨hk, h⟩
      have hV : V ≤ (ℝ ∙ ψ k)ᗮ := Submodule.span_le.2 <| by
        rintro _ ⟨j, hj, rfl⟩
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.2
          (inner_value_eq_zero_of_energyFormH1_eq_of_ne hsymm (hj.2 ▸ hne) (hφeq k) (hφeq j))
      have hP := Submodule.mem_orthogonal_singleton_iff_inner_right.1
        (hV (V.starProjection_apply_mem (W1p.value (u : W1p mu (boxDomain a b) 2))))
      rw [inner_sub_left, real_inner_comm (ψ k)
        (V.starProjection (W1p.value (u : W1p mu (boxDomain a b) 2))), hP,
        inner_value_eq_zero_of_energyFormH1_eq_of_ne hsymm hne.symm hu (hφeq k), sub_zero]
  have hw0 : w = 0 := by
    refine Lp.ext ((ae_eq_zero_of_forall_setIntegral_mul_boxSineMode_eq_zero
      ((Lp.memLp w).integrable one_le_two) fun k hk ↦ ?_).trans (Lp.coeFn_zero _ _ _).symm)
    rw [← hw k hk, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hφ k] with x hx
    simp [ψ, hx, mul_comm]
  have hP : W1p.value (u : W1p mu (boxDomain a b) 2) =
      V.starProjection (W1p.value (u : W1p mu (boxDomain a b) 2)) := sub_eq_zero.1 hw0
  rw [hP]
  exact V.starProjection_apply_mem _

/-- **Dirichlet eigenfunctions on a box are products of sines.** Every solution `u ∈ H¹₀` of the
Dirichlet eigenvalue identity for `-Δ` on the box `∏ᵢ (aᵢ, bᵢ)` with eigenvalue `κ` is, almost
everywhere, a finite linear combination of separated sine modes `boxSineMode a b k` whose indices
are positive and whose eigenvalue `∑ᵢ (kᵢ π / (bᵢ - aᵢ))²` is `κ`. -/
theorem exists_finset_value_ae_eq_sum_boxSineMode {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {kappa : ℝ} {u : W1p0 mu (boxDomain a b) 2}
    (hu : ∀ v : W1p0 mu (boxDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p mu (boxDomain a b) 2)
          (v : W1p mu (boxDomain a b) 2) =
        kappa * ⟪W1p.value (u : W1p mu (boxDomain a b) 2),
          W1p.value (v : W1p mu (boxDomain a b) 2)⟫_ℝ) :
    ∃ (s : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ),
      (∀ k ∈ s, (∀ i, 0 < k i) ∧ ∑ i, (k i * Real.pi / (b i - a i)) ^ 2 = kappa) ∧
      W1p.value (u : W1p mu (boxDomain a b) 2)
        =ᵐ[mu.restrict (boxDomain a b : Set (EuclideanSpace ℝ ι))]
          fun x ↦ ∑ k ∈ s, c k * boxSineMode a b k x := by
  classical
  choose φ hφ hφeq using fun k : ι → ℕ ↦
    exists_value_ae_eq_boxSineMode_and_energyFormH1_eq (mu := mu) hab k
  obtain ⟨l, hl, hlu⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).1
    (value_mem_span_of_energyFormH1_eq hab hφ hφeq hu)
  refine ⟨l.support, l, fun k hk ↦ (Finsupp.mem_supported ℝ l).1 hl hk, ?_⟩
  rw [← hlu]
  -- The value of a finite combination of the realizations is the combination of the modes.
  refine (Lp.coeFn_linearCombination l _).trans ?_
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  filter_upwards [eventuallyEq_sum fun k _ ↦ (hφ k).const_smul (l k)] with x hx
  simpa using hx

/-- **The Dirichlet spectrum of `-Δ` on a box.** The Dirichlet eigenvalues of `-Δ` on the box
`∏ᵢ (aᵢ, bᵢ)` are exactly the sums `∑ᵢ (kᵢ π / (bᵢ - aᵢ))²` with positive integers `kᵢ`: the
homogeneous Dirichlet problem `-Δu = κ u` has a nonzero weak solution in `H¹₀` of the box exactly
for these `κ`. -/
theorem isDirichletEigenvalue_laplacian_boxDomain_iff {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {kappa : ℝ} :
    IsDirichletEigenvalue mu (boxDomain a b) (fun _ ↦ 1) 0 0 kappa ↔
      ∃ k : ι → ℕ, (∀ i, 0 < k i) ∧ kappa = ∑ i, (k i * Real.pi / (b i - a i)) ^ 2 := by
  refine ⟨fun hkappa ↦ ?_, fun ⟨k, hk, hkappa⟩ ↦
    hkappa ▸ isDirichletEigenvalue_laplacian_boxDomain hab hk⟩
  obtain ⟨u, hu0, hu⟩ := (isDirichletEigenvalue_iff kappa).1 hkappa
  obtain ⟨s, c, hs, hsum⟩ := exists_finset_value_ae_eq_sum_boxSineMode hab hu
  rcases s.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
  · -- With no admissible mode, the eigenfunction would vanish.
    refine absurd (Subtype.ext (W1p.ext_value (Lp.ext ?_))) hu0
    rw [ZeroMemClass.coe_zero, W1p.value_zero]
    filter_upwards [hsum, Lp.coeFn_zero ℝ 2
      (mu.restrict (boxDomain a b : Set (EuclideanSpace ℝ ι)))] with x h1 h2
    rw [h1, h2]
    simp
  · exact ⟨k, (hs k hk).1, (hs k hk).2.symm⟩

end TauCeti.PDE
