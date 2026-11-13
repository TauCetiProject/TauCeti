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

/-!
# Separated Dirichlet eigenfunctions on a box

On a product of bounded intervals `(aᵢ,bᵢ)`, the products
`∏ᵢ sin (kᵢ π (xᵢ - aᵢ) / (bᵢ - aᵢ))`, with positive integer indices, are nonzero
Dirichlet eigenfunctions of `-Δ`, with eigenvalue `∑ᵢ (kᵢ π / (bᵢ - aᵢ))²`.
We prove the classical equation and vanishing on the frontier, then realize these functions
in `H¹₀` with their weak eigenfunction identity. No smoothness of the boundary is needed.
This file does not assert completeness of the separated family.

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

end TauCeti.PDE
