/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.EigenCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.InvSqrtAdd
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# The bounded transform and Baaj–Julg commutator theorem

For a self-adjoint `A : H →ₗ.[ℂ] H` with compact resolvent, the **bounded transform**
`F_A = A (1 + A²)⁻¹/²` (`LinearPMap.boundedTransform`) is a self-adjoint contraction satisfying
`1 - F_A² = (1 + A²)⁻¹`. Whenever `T : H →L[ℂ] H` preserves `D(A)` with bounded commutator
`[A, T] = C` on `D(A)`, `[F_A, T]` is compact with `‖[F_A, T]‖ ≤ (5 / 4) ‖C‖`.

## Main definitions & results

* `LinearPMap.boundedTransform`, `LinearPMap.isSelfAdjoint_boundedTransform`,
  `LinearPMap.norm_boundedTransform_le_one`, `LinearPMap.one_sub_boundedTransform_mul_self`.
* `LinearPMap.isCompactOperator_commutator_boundedTransform`,
  `LinearPMap.norm_commutator_boundedTransform_le`: the Baaj–Julg commutator theorem.

## References

* S. Baaj and P. Julg, *C. R. Acad. Sci. Paris Sér. I Math.* 296 (1983), 875–878.
* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProductSpace lp

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-! ### The bounded transform `A (1 + A²)⁻¹/²` -/

section BoundedTransform

private theorem norm_div_sqrt_one_add_sq_le_one (t : ℝ) :
    ‖((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, add_comm 1 (t ^ 2)] using
    Real.abs_div_sqrt_sq_add_le_one zero_le_one t

/-- The **bounded transform** (or Woronowicz–Baaj–Julg transform) `F_A = A (1 + A²)⁻¹/²` of a
self-adjoint operator `A` with compact resolvent, defined via the bounded eigenbasis functional
calculus of `t ↦ t / √(1 + t²)`. -/
def boundedTransform (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    H →L[ℂ] H :=
  A.boundedEigenCalculus hA h (fun t ↦ ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ))
    ⟨1, norm_div_sqrt_one_add_sq_le_one⟩

variable (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

/-- In any orthonormal eigenbasis of `A`, the bounded transform acts diagonally by
`λᵢ / √(1 + λᵢ²)`. -/
theorem boundedTransform_eq_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    (m : ℓ^∞(ι, ℂ)) (hm : ∀ i, m i = ((lam i / Real.sqrt (1 + lam i ^ 2) : ℝ) : ℂ)) :
    A.boundedTransform hA h = b.diagonal m :=
  A.boundedEigenCalculus_eq_diagonal hA h b hb _ _ m hm

/-- On an eigenvector of `A` with real eigenvalue `r`, the bounded transform multiplies by
`r / √(1 + r²)`. -/
theorem boundedTransform_apply_of_apply_eq_smul (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) :
    A.boundedTransform hA h x = ((r / Real.sqrt (1 + r ^ 2) : ℝ) : ℂ) • (x : H) :=
  A.boundedEigenCalculus_apply_of_apply_eq_smul hA h _ x hx

/-- The bounded transform is self-adjoint. -/
theorem isSelfAdjoint_boundedTransform : IsSelfAdjoint (A.boundedTransform hA h) :=
  A.isSelfAdjoint_boundedEigenCalculus hA h _ fun _ ↦ by simp

/-- The star of the bounded transform is itself. -/
@[simp]
theorem star_boundedTransform : star (A.boundedTransform hA h) = A.boundedTransform hA h :=
  (A.isSelfAdjoint_boundedTransform hA h).star_eq

/-- The bounded transform is a contraction: `‖A (1 + A²)⁻¹/²‖ ≤ 1`. -/
theorem norm_boundedTransform_le_one : ‖A.boundedTransform hA h‖ ≤ 1 :=
  A.norm_boundedEigenCalculus_le hA h _ zero_le_one norm_div_sqrt_one_add_sq_le_one

private theorem inv_one_add_sq_add_boundedTransform_sq (t : ℝ) :
    (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) +
      ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) = 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hid : (1 + t ^ 2)⁻¹ + (t / Real.sqrt (1 + t ^ 2)) * (t / Real.sqrt (1 + t ^ 2)) = 1 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hpos.le, ← sq]
    field_simp
  exact_mod_cast hid

/-- **`1 - F_A² = (1 + A²)⁻¹`.** -/
theorem one_sub_boundedTransform_mul_self :
    1 - A.boundedTransform hA h * A.boundedTransform hA h = A.invOneAddSq := by
  have hinv_bdd : ∃ C, ∀ t : ℝ, ‖(((1 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ C := ⟨1, fun t ↦ by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith)⟩
  have hsq_bdd : ∃ C, ∀ t : ℝ,
      ‖((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖ ≤ C :=
    ⟨1, fun t ↦ by
      simpa [norm_mul] using mul_le_mul (norm_div_sqrt_one_add_sq_le_one t)
        (norm_div_sqrt_one_add_sq_le_one t) (norm_nonneg _) zero_le_one⟩
  have hsum_bdd : ∃ C, ∀ t : ℝ, ‖(((1 + t ^ 2)⁻¹ : ℝ) : ℂ) +
      ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖ ≤ C :=
    ⟨1, fun t ↦ by rw [inv_one_add_sq_add_boundedTransform_sq]; simp⟩
  rw [← A.boundedEigenCalculus_invOneAddSq hA h hinv_bdd, sub_eq_iff_eq_add, boundedTransform,
    ← A.boundedEigenCalculus_mul hA h _ _ hsq_bdd,
    ← A.boundedEigenCalculus_add hA h hinv_bdd hsq_bdd hsum_bdd,
    ← A.boundedEigenCalculus_one hA h ⟨1, fun _ ↦ by simp⟩]
  exact A.boundedEigenCalculus_congr hA h _ _ fun t ↦
    (inv_one_add_sq_add_boundedTransform_sq t).symm

/-- **`F_A² - 1 = -(1 + A²)⁻¹`.** -/
theorem boundedTransform_mul_self_sub_one :
    A.boundedTransform hA h * A.boundedTransform hA h - 1 = -A.invOneAddSq := by
  rw [← neg_sub, one_sub_boundedTransform_mul_self]

/-- The defect `F_A² - 1` of the bounded transform is compact. -/
theorem isCompactOperator_boundedTransform_mul_self_sub_one :
    IsCompactOperator ⇑(A.boundedTransform hA h * A.boundedTransform hA h - 1) := by
  rw [boundedTransform_mul_self_sub_one, FunLike.coe_neg]
  exact (h.isCompactOperator_invOneAddSq hA.I_mem_resolventSet).neg

/-- Unitary conjugation commutes with the bounded transform. -/
theorem boundedTransform_unitaryConj {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') :
    (unitaryConj U A).boundedTransform (isSelfAdjoint_unitaryConj hA)
      ((hasCompactResolvent_unitaryConj_iff U).2 h) =
      U.conjStarAlgEquiv (A.boundedTransform hA h) :=
  A.boundedEigenCalculus_unitaryConj hA h U _ _

/-- Any bounded operator preserving `D(A)` and anticommuting with `A` anticommutes with `F_A`. -/
theorem mul_boundedTransform_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.property⟩) :
    γ * A.boundedTransform hA h = -(A.boundedTransform hA h * γ) :=
  A.mul_boundedEigenCalculus_of_anticommute hA h hγdom hγA _ fun t ↦ by simp [neg_div]

/-! ### The Baaj–Julg commutator theorem -/

private theorem norm_inv_one_add_max_add_sq_le (r t : ℝ) :
    ‖(((1 + max r 0 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ (1 + max r 0)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity)]
  exact inv_anti₀ (by linarith [le_max_right r 0]) (by linarith [sq_nonneg t])

private theorem norm_div_one_add_max_add_sq_le (r t : ℝ) :
    ‖((t / (1 + max r 0 + t ^ 2) : ℝ) : ℂ)‖ ≤ (2 * Real.sqrt (1 + max r 0))⁻¹ := by
  have ha : 0 < 1 + max r 0 := by linarith [le_max_right r 0]
  have hd : 0 < 1 + max r 0 + t ^ 2 := by positivity
  have h2 : 0 < 2 * Real.sqrt (1 + max r 0) := by positivity
  have hsq : 2 * Real.sqrt (1 + max r 0) * |t| ≤ 1 + max r 0 + t ^ 2 := by
    have h1 := Real.sq_sqrt ha.le
    nlinarith [sq_abs t, sq_nonneg (Real.sqrt (1 + max r 0) - |t|)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hd, div_le_iff₀ hd,
    ← mul_le_mul_iff_right₀ h2, ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul]
  exact hsq

private theorem norm_div_one_add_max_sub_le (r₁ r₂ t : ℝ) :
    ‖((t / (1 + max r₁ 0 + t ^ 2) : ℝ) : ℂ) +
      (-1 : ℂ) * ((t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ)‖ ≤ |r₁ - r₂| := by
  have hd1 : 0 < 1 + max r₁ 0 + t ^ 2 := by linarith [le_max_right r₁ 0, sq_nonneg t]
  have hd2 : 0 < 1 + max r₂ 0 + t ^ 2 := by linarith [le_max_right r₂ 0, sq_nonneg t]
  have hdiff : ((t / (1 + max r₁ 0 + t ^ 2) : ℝ) : ℂ) +
      (-1 : ℂ) * ((t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ) =
      (((t * (max r₂ 0 - max r₁ 0)) /
        ((1 + max r₁ 0 + t ^ 2) * (1 + max r₂ 0 + t ^ 2)) : ℝ) : ℂ) := by
    exact_mod_cast (by field_simp; ring :
      t / (1 + max r₁ 0 + t ^ 2) + (-1) * (t / (1 + max r₂ 0 + t ^ 2)) =
        t * (max r₂ 0 - max r₁ 0) / ((1 + max r₁ 0 + t ^ 2) * (1 + max r₂ 0 + t ^ 2)))
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (mul_pos hd1 hd2), div_le_iff₀ (mul_pos hd1 hd2)]
  have ht_le : |t| ≤ 1 + max r₁ 0 + t ^ 2 := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t, le_max_right r₁ 0]
  have h1_le : 1 ≤ 1 + max r₂ 0 + t ^ 2 := by nlinarith [le_max_right r₂ 0]
  have hmax : |max r₂ 0 - max r₁ 0| ≤ |r₁ - r₂| := by
    rw [abs_sub_comm]; exact abs_max_sub_max_le_abs r₁ r₂ 0
  calc |t| * |max r₂ 0 - max r₁ 0|
      ≤ (1 + max r₁ 0 + t ^ 2) * |r₁ - r₂| := mul_le_mul ht_le hmax (abs_nonneg _) hd1.le
    _ = |r₁ - r₂| * ((1 + max r₁ 0 + t ^ 2) * 1) := by ring
    _ ≤ |r₁ - r₂| * ((1 + max r₁ 0 + t ^ 2) * (1 + max r₂ 0 + t ^ 2)) := by gcongr

private def bjRes (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) (r : ℝ) : H →L[ℂ] H :=
  A.boundedEigenCalculus hA h (fun t ↦ (((1 + max r 0 + t ^ 2)⁻¹ : ℝ) : ℂ))
    ⟨(1 + max r 0)⁻¹, norm_inv_one_add_max_add_sq_le r⟩

private def bjMulRes (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) (r : ℝ) : H →L[ℂ] H :=
  A.boundedEigenCalculus hA h (fun t ↦ ((t / (1 + max r 0 + t ^ 2) : ℝ) : ℂ))
    ⟨(2 * Real.sqrt (1 + max r 0))⁻¹, norm_div_one_add_max_add_sq_le r⟩

private theorem bjRes_apply_basis {ι : Type*} {b : HilbertBasis ι ℂ H} {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    {r : ℝ} (hr : 0 ≤ r) (k : ι) :
    bjRes hA h r (b k) = (((1 + r + lam k ^ 2)⁻¹ : ℝ) : ℂ) • b k := by
  obtain ⟨hk, hAk⟩ := hb k
  simpa only [bjRes, max_eq_left hr] using A.boundedEigenCalculus_apply_of_apply_eq_smul hA h
    ⟨(1 + max r 0)⁻¹, norm_inv_one_add_max_add_sq_le r⟩ ⟨b k, hk⟩ hAk

private theorem bjMulRes_apply_basis {ι : Type*} {b : HilbertBasis ι ℂ H} {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    {r : ℝ} (hr : 0 ≤ r) (k : ι) :
    bjMulRes hA h r (b k) = ((lam k / (1 + r + lam k ^ 2) : ℝ) : ℂ) • b k := by
  obtain ⟨hk, hAk⟩ := hb k
  simpa only [bjMulRes, max_eq_left hr] using A.boundedEigenCalculus_apply_of_apply_eq_smul hA h
    ⟨(2 * Real.sqrt (1 + max r 0))⁻¹, norm_div_one_add_max_add_sq_le r⟩ ⟨b k, hk⟩ hAk

private theorem isCompactOperator_bjMulRes (r : ℝ) : IsCompactOperator (bjMulRes hA h r) := by
  refine A.isCompactOperator_boundedEigenCalculus hA h _ ?_
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.Eventually, Filter.mem_cocompact]
  refine ⟨Metric.closedBall 0 ε⁻¹, isCompact_closedBall 0 ε⁻¹, fun t ht ↦ ?_⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
  have hd : 0 < 1 + max r 0 + t ^ 2 := by positivity
  have ht0 : 0 < |t| := (inv_pos.2 hε).trans ht
  rw [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_of_pos hd]
  calc |t| / (1 + max r 0 + t ^ 2)
      < |t| / t ^ 2 := by
        gcongr; exacts [by rw [← sq_abs]; positivity, by linarith [le_max_right r 0]]
    _ = |t|⁻¹ := by rw [← sq_abs t, sq, div_mul_cancel_left₀ ht0.ne']
    _ < ε := (inv_lt_comm₀ ht0 hε).2 ht

private theorem continuous_bjMulRes : Continuous (bjMulRes hA h) := by
  refine LipschitzWith.continuous (K := 1) fun r₁ r₂ ↦ ?_
  rw [ENNReal.coe_one, one_mul, edist_dist, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg,
    dist_eq_norm, Real.dist_eq]
  have hneg : ∃ C, ∀ t : ℝ, ‖(-1 : ℂ) * ((t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ)‖ ≤ C :=
    ⟨_, fun t ↦ by simpa using norm_div_one_add_max_add_sq_le r₂ t⟩
  rw [bjMulRes, bjMulRes, sub_eq_add_neg, ← neg_one_smul ℂ,
    ← A.boundedEigenCalculus_smul hA h (-1) _ hneg,
    ← A.boundedEigenCalculus_add hA h _ hneg ⟨|r₁ - r₂|, norm_div_one_add_max_sub_le r₁ r₂⟩]
  exact A.norm_boundedEigenCalculus_le hA h _ (abs_nonneg _) (norm_div_one_add_max_sub_le r₁ r₂)

private theorem inner_commutator_basis (hA : IsSelfAdjoint A) {ι : Type*} {b : HilbertBasis ι ℂ H}
    {lam : ι → ℝ} (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    {T C : H →L[ℂ] H} (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.property⟩ - T (A x) = C x) (i j : ι) :
    ⟪b i, C (b j)⟫_ℂ = ((lam i - lam j : ℝ) : ℂ) * ⟪b i, T (b j)⟫_ℂ := by
  obtain ⟨hi, hAi⟩ := hb i
  obtain ⟨hj, hAj⟩ := hb j
  rw [← hC ⟨b j, hj⟩, inner_sub_right, hAj, _root_.map_smul, inner_smul_right,
    ← hA.isFormalAdjoint ⟨b i, hi⟩ ⟨T (b j), hTdom _ hj⟩, hAi, inner_smul_left]
  simp only [Complex.conj_ofReal, Complex.ofReal_sub]; ring

private theorem inner_selfAdjoint_diag_commutator {ι : Type*} (b : HilbertBasis ι ℂ H)
    {P T : H →L[ℂ] H} (hP : IsSelfAdjoint P) {g : ι → ℝ} (hPg : ∀ k, P (b k) = (g k : ℂ) • b k)
    (i j : ι) :
    ⟪b i, (P * T - T * P) (b j)⟫_ℂ = ((g i - g j : ℝ) : ℂ) * ⟪b i, T (b j)⟫_ℂ := by
  have hPadj : P.adjoint = P := (ContinuousLinearMap.star_eq_adjoint _).symm.trans hP.star_eq
  simp only [_root_.sub_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    inner_sub_right]
  rw [← ContinuousLinearMap.adjoint_inner_left P, hPadj, hPg i, hPg j, inner_smul_left,
    _root_.map_smul, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.ofReal_sub]; ring

private theorem inner_selfAdjoint_diag_sandwich {ι : Type*} (b : HilbertBasis ι ℂ H)
    {P C : H →L[ℂ] H} (hP : IsSelfAdjoint P) {g : ι → ℝ} (hPg : ∀ k, P (b k) = (g k : ℂ) • b k)
    (i j : ι) :
    ⟪b i, (P * C * P) (b j)⟫_ℂ = ((g i * g j : ℝ) : ℂ) * ⟪b i, C (b j)⟫_ℂ := by
  have hPadj : P.adjoint = P := (ContinuousLinearMap.star_eq_adjoint _).symm.trans hP.star_eq
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left P, hPadj, hPg i, hPg j, inner_smul_left,
    _root_.map_smul, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.ofReal_mul]; ring

private theorem bjMulRes_commutator {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.property⟩ - T (A x) = C x) {r : ℝ} (hr : 0 ≤ r) :
    bjMulRes hA h r * T - T * bjMulRes hA h r =
      ((1 + r : ℝ) : ℂ) • (bjRes hA h r * C * bjRes hA h r) -
        bjMulRes hA h r * C * bjMulRes hA h r := by
  obtain ⟨_, b, lam, hb⟩ := hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h
  have hQ_sa : IsSelfAdjoint (bjMulRes hA h r) :=
    A.isSelfAdjoint_boundedEigenCalculus hA h _ fun _ ↦ by simp
  have hR_sa : IsSelfAdjoint (bjRes hA h r) :=
    A.isSelfAdjoint_boundedEigenCalculus hA h _ fun _ ↦ by simp
  refine b.ext_inner_apply b fun i j ↦ ?_
  rw [inner_selfAdjoint_diag_commutator b hQ_sa (bjMulRes_apply_basis hA h hb hr) i j]
  simp only [_root_.sub_apply, _root_.smul_apply, inner_sub_right, inner_smul_right,
    inner_selfAdjoint_diag_sandwich b hR_sa (bjRes_apply_basis hA h hb hr) i j,
    inner_selfAdjoint_diag_sandwich b hQ_sa (bjMulRes_apply_basis hA h hb hr) i j,
    inner_commutator_basis hA hb hTdom hC i j]
  have hd₁ : (1 : ℝ) + r + lam i ^ 2 ≠ 0 := by positivity
  have hd₂ : (1 : ℝ) + r + lam j ^ 2 ≠ 0 := by positivity
  have hidC : ((lam i / (1 + r + lam i ^ 2) - lam j / (1 + r + lam j ^ 2) : ℝ) : ℂ) =
      ((1 + r : ℝ) : ℂ) * (((1 + r + lam i ^ 2)⁻¹ * (1 + r + lam j ^ 2)⁻¹ : ℝ) : ℂ) *
          ((lam i - lam j : ℝ) : ℂ) -
        (((lam i / (1 + r + lam i ^ 2)) * (lam j / (1 + r + lam j ^ 2)) : ℝ) : ℂ) *
          ((lam i - lam j : ℝ) : ℂ) := by
    exact_mod_cast (by field_simp; ring :
      lam i / (1 + r + lam i ^ 2) - lam j / (1 + r + lam j ^ 2) =
        (1 + r) * ((1 + r + lam i ^ 2)⁻¹ * (1 + r + lam j ^ 2)⁻¹) * (lam i - lam j) -
          (lam i / (1 + r + lam i ^ 2)) * (lam j / (1 + r + lam j ^ 2)) * (lam i - lam j))
  rw [hidC]; ring

private theorem norm_bjMulRes_commutator_le {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.property⟩ - T (A x) = C x) {r : ℝ} (hr : 0 ≤ r) :
    ‖bjMulRes hA h r * T - T * bjMulRes hA h r‖ ≤ (5 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := by
  rw [bjMulRes_commutator hA h hTdom hC hr]
  have h1r : 0 < 1 + r := by linarith
  have hR : ‖bjRes hA h r‖ ≤ (1 + r)⁻¹ := by
    simpa only [bjRes, max_eq_left hr] using A.norm_boundedEigenCalculus_le hA h
      ⟨_, norm_inv_one_add_max_add_sq_le r⟩ (by positivity) (norm_inv_one_add_max_add_sq_le r)
  have hQ : ‖bjMulRes hA h r‖ ≤ (2 * Real.sqrt (1 + r))⁻¹ := by
    simpa only [bjMulRes, max_eq_left hr] using A.norm_boundedEigenCalculus_le hA h
      ⟨_, norm_div_one_add_max_add_sq_le r⟩ (by positivity) (norm_div_one_add_max_add_sq_le r)
  have hterm1 : ‖((1 + r : ℝ) : ℂ) • (bjRes hA h r * C * bjRes hA h r)‖ ≤ ‖C‖ * (1 + r)⁻¹ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1r]
    calc (1 + r) * ‖bjRes hA h r * C * bjRes hA h r‖
        ≤ (1 + r) * (‖bjRes hA h r‖ * ‖C‖ * ‖bjRes hA h r‖) := by
          gcongr; exact norm_mul₃_le
      _ ≤ (1 + r) * ((1 + r)⁻¹ * ‖C‖ * (1 + r)⁻¹) := by gcongr
      _ = ‖C‖ * (1 + r)⁻¹ := by field_simp
  have hterm2 : ‖bjMulRes hA h r * C * bjMulRes hA h r‖ ≤ (1 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := by
    have hs0 : Real.sqrt (1 + r) ≠ 0 := (Real.sqrt_pos.2 h1r).ne'
    calc ‖bjMulRes hA h r * C * bjMulRes hA h r‖
        ≤ ‖bjMulRes hA h r‖ * ‖C‖ * ‖bjMulRes hA h r‖ := norm_mul₃_le
      _ ≤ (2 * Real.sqrt (1 + r))⁻¹ * ‖C‖ * (2 * Real.sqrt (1 + r))⁻¹ := by gcongr
      _ = (1 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := by
          field_simp; rw [Real.sq_sqrt h1r.le]; ring
  calc ‖((1 + r : ℝ) : ℂ) • (bjRes hA h r * C * bjRes hA h r) -
          bjMulRes hA h r * C * bjMulRes hA h r‖
      ≤ _ := norm_sub_le _ _
    _ ≤ ‖C‖ * (1 + r)⁻¹ + (1 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := add_le_add hterm1 hterm2
    _ = (5 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := by ring

private def bjIntegrand (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) (T : H →L[ℂ] H)
    (r : ℝ) : H →L[ℂ] H :=
  (Real.pi⁻¹ * (Real.sqrt r)⁻¹ : ℝ) • (bjMulRes hA h r * T - T * bjMulRes hA h r)

private theorem continuousOn_bjIntegrand (T : H →L[ℂ] H) :
    ContinuousOn (bjIntegrand hA h T) (Ioi 0) :=
  (continuousOn_const.mul (ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn
    fun _ hr ↦ (Real.sqrt_pos.2 hr).ne')).smul
    (((continuous_bjMulRes hA h).mul continuous_const).sub
      (continuous_const.mul (continuous_bjMulRes hA h))).continuousOn

private theorem norm_bjIntegrand_le {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.property⟩ - T (A x) = C x) {r : ℝ} (hr : 0 < r) :
    ‖bjIntegrand hA h T r‖ ≤ (5 / 4 * Real.pi⁻¹ * ‖C‖) * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹) := by
  rw [bjIntegrand, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.pi⁻¹ * (Real.sqrt r)⁻¹ * ‖bjMulRes hA h r * T - T * bjMulRes hA h r‖
      ≤ Real.pi⁻¹ * (Real.sqrt r)⁻¹ * ((5 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹) := by
        gcongr; exact norm_bjMulRes_commutator_le hA h hTdom hC hr.le
    _ = 5 / 4 * Real.pi⁻¹ * ‖C‖ * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹) := by ring

private theorem integrableOn_bjIntegrand {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.property⟩ - T (A x) = C x) :
    IntegrableOn (bjIntegrand hA h T) (Ioi 0) := by
  have hdom : IntegrableOn
      (fun r : ℝ ↦ (5 / 4 * Real.pi⁻¹ * ‖C‖) * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹)) (Ioi 0) :=
    (TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add zero_lt_one).const_mul _
  refine hdom.mono' ((continuousOn_bjIntegrand hA h T).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact norm_bjIntegrand_le hA h hTdom hC hr

private noncomputable def bjKernel (μ r : ℝ) : ℂ :=
  ((Real.pi⁻¹ * (μ * ((Real.sqrt r)⁻¹ * (1 + μ ^ 2 + r)⁻¹)) : ℝ) : ℂ)

private theorem integrableOn_bjKernel (μ : ℝ) : IntegrableOn (bjKernel μ) (Ioi 0) :=
  Complex.ofRealCLM.integrable_comp
    (((TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add (a := 1 + μ ^ 2)
      (by positivity)).const_mul μ).const_mul Real.pi⁻¹)

private theorem integral_bjKernel (μ : ℝ) :
    ∫ r in Ioi (0 : ℝ), bjKernel μ r = ((μ / Real.sqrt (1 + μ ^ 2) : ℝ) : ℂ) := by
  change ∫ r in Ioi (0 : ℝ), Complex.ofRealCLM
    (Real.pi⁻¹ * (μ * ((Real.sqrt r)⁻¹ * (1 + μ ^ 2 + r)⁻¹))) =
      Complex.ofRealCLM (μ / Real.sqrt (1 + μ ^ 2))
  rw [Complex.ofRealCLM.integral_comp_comm
    (((TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add (a := 1 + μ ^ 2)
      (by positivity)).const_mul μ).const_mul Real.pi⁻¹),
    integral_const_mul, integral_const_mul,
    TauCeti.integral_Ioi_inv_sqrt_mul_inv_add (by positivity)]
  congr 1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

private theorem commutator_boundedTransform_eq_integral {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.property⟩ - T (A x) = C x) :
    A.boundedTransform hA h * T - T * A.boundedTransform hA h =
      ∫ r in Ioi (0 : ℝ), bjIntegrand hA h T r := by
  obtain ⟨_, b, lam, hb⟩ := hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h
  have hint := integrableOn_bjIntegrand hA h hTdom hC
  refine b.ext_inner_apply b fun i j ↦ ?_
  have hF_eig (k) : A.boundedTransform hA h (b k) =
      ((lam k / Real.sqrt (1 + lam k ^ 2) : ℝ) : ℂ) • b k :=
    A.boundedTransform_apply_of_apply_eq_smul hA h ⟨_, (hb k).1⟩ (hb k).2
  have hQ_sa (r : ℝ) : IsSelfAdjoint (bjMulRes hA h r) :=
    A.isSelfAdjoint_boundedEigenCalculus hA h _ fun _ ↦ by simp
  have hL_comm : ⟪b i, (∫ r in Ioi (0 : ℝ), bjIntegrand hA h T r) (b j)⟫_ℂ =
      ∫ r in Ioi (0 : ℝ), ⟪b i, bjIntegrand hA h T r (b j)⟫_ℂ :=
    (((innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ H (b j))).integral_comp_comm hint).symm
  have hinner (r : ℝ) (hr : 0 < r) : ⟪b i, bjIntegrand hA h T r (b j)⟫_ℂ =
      (bjKernel (lam i) r - bjKernel (lam j) r) * ⟪b i, T (b j)⟫_ℂ := by
    rw [bjIntegrand, _root_.smul_apply, ← Complex.coe_smul, inner_smul_right,
      inner_selfAdjoint_diag_commutator b (hQ_sa r) (bjMulRes_apply_basis hA h hb hr.le) i j,
      bjKernel, bjKernel, add_right_comm 1 r (lam i ^ 2), add_right_comm 1 r (lam j ^ 2),
      div_eq_mul_inv, div_eq_mul_inv]
    push_cast; ring
  rw [inner_selfAdjoint_diag_commutator b (A.isSelfAdjoint_boundedTransform hA h) hF_eig i j,
    hL_comm, setIntegral_congr_fun measurableSet_Ioi hinner, integral_mul_const,
    integral_sub (integrableOn_bjKernel (lam i)) (integrableOn_bjKernel (lam j)),
    integral_bjKernel, integral_bjKernel]
  push_cast; ring

private theorem integral_mem_of_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : Submodule ℂ E} (hK : _root_.IsClosed (K : Set E)) {f : α → E}
    (hf : Integrable f μ) (hmem : ∀ᵐ a ∂μ, f a ∈ K) :
    ∫ a, f a ∂μ ∈ K := by
  have : _root_.IsClosed (K : Set E) := hK
  rw [← Submodule.Quotient.mk_eq_zero]
  change K.mkQL (∫ a, f a ∂μ) = 0
  rw [← K.mkQL.integral_comp_comm hf]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hmem] with a ha
  change Submodule.Quotient.mk (f a) = 0
  rwa [Submodule.Quotient.mk_eq_zero]

/-- **Baaj–Julg compactness theorem.** If a bounded operator `T` preserves the domain of `A` and
has bounded commutator `[A, T]` on `D(A)`, then `[F_A, T]` is a compact operator. -/
theorem isCompactOperator_commutator_boundedTransform {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.property⟩ - T (A x) = C x) :
    IsCompactOperator ⇑(A.boundedTransform hA h * T - T * A.boundedTransform hA h) := by
  rw [commutator_boundedTransform_eq_integral hA h hTdom hC]
  refine integral_mem_of_isClosed (K := compactOperator (RingHom.id ℂ) H H)
    isClosed_setOfPred_isCompactOperator (integrableOn_bjIntegrand hA h hTdom hC)
    (Filter.Eventually.of_forall fun r ↦ ?_)
  have hcomm : IsCompactOperator ⇑(bjMulRes hA h r * T - T * bjMulRes hA h r) := by
    rw [FunLike.coe_sub]
    exact ((isCompactOperator_bjMulRes hA h r).mul_right T).sub
      ((isCompactOperator_bjMulRes hA h r).mul_left T)
  rw [bjIntegrand, ← Complex.coe_smul]
  exact (compactOperator (RingHom.id ℂ) H H).smul_mem _ hcomm

/-- **Baaj–Julg norm estimate.** If a bounded operator `T` preserves the domain of `A` and
`[A, T] = C` on `D(A)` for a bounded operator `C`, then `‖[F_A, T]‖ ≤ (5 / 4) ‖C‖`. -/
theorem norm_commutator_boundedTransform_le {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.property⟩ - T (A x) = C x) :
    ‖A.boundedTransform hA h * T - T * A.boundedTransform hA h‖ ≤ 5 / 4 * ‖C‖ := by
  rw [commutator_boundedTransform_eq_integral hA h hTdom hC]
  have hint := integrableOn_bjIntegrand hA h hTdom hC
  have hdom : IntegrableOn
      (fun r : ℝ ↦ (5 / 4 * Real.pi⁻¹ * ‖C‖) * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹)) (Ioi 0) :=
    (TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add zero_lt_one).const_mul _
  calc ‖∫ r in Ioi (0 : ℝ), bjIntegrand hA h T r‖
      ≤ ∫ r in Ioi (0 : ℝ), ‖bjIntegrand hA h T r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioi (0 : ℝ), (5 / 4 * Real.pi⁻¹ * ‖C‖) * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹) :=
        setIntegral_mono_on hint.norm hdom measurableSet_Ioi fun _ hr ↦
          norm_bjIntegrand_le hA h hTdom hC hr
    _ = 5 / 4 * Real.pi⁻¹ * ‖C‖ * (Real.pi / Real.sqrt 1) := by
        rw [integral_const_mul, TauCeti.integral_Ioi_inv_sqrt_mul_inv_add zero_lt_one]
    _ = 5 / 4 * ‖C‖ := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        rw [Real.sqrt_one, div_one]; field_simp

end BoundedTransform

end LinearPMap
