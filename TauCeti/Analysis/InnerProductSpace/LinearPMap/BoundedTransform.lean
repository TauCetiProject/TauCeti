/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.EigenCalculus
public import TauCeti.Topology.Algebra.Module.LinearPMap.Sylvester
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.InvSqrtAdd
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The bounded transform and Baaj–Julg commutator theorem

For a self-adjoint `A : H →ₗ.[ℂ] H` with compact resolvent, the **bounded transform**
`F_A = A (1 + A²)⁻¹/²` (`LinearPMap.boundedTransform`) is a self-adjoint contraction satisfying
`1 - F_A² = (1 + A²)⁻¹`. Whenever `T : H →L[ℂ] H` solves a domain-aware Sylvester equation
`SylvesterEquation A A T C` (`[A, T] = C` on `D(A)`), `[F_A, T]` is compact with
`‖[F_A, T]‖ ≤ (5 / 4) ‖C‖`.

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

open Filter MeasureTheory Set TauCeti Topology
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

private def boundedTransformSymbol : BoundedBorelFunction ℝ :=
  BoundedBorelFunction.ofFunction (fun t ↦ ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ))
    (Continuous.measurable <| by fun_prop (disch := intro t; positivity))
    ⟨1, zero_le_one, norm_div_sqrt_one_add_sq_le_one⟩

private theorem norm_boundedTransformSymbol_le (t : ℝ) :
    ‖boundedTransformSymbol t‖ ≤ 1 := by
  simpa only [boundedTransformSymbol, BoundedBorelFunction.ofFunction_apply] using
    norm_div_sqrt_one_add_sq_le_one t

private theorem norm_inv_one_add_sq_le_one (t : ℝ) :
    ‖(((1 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity)]
  exact inv_le_one_of_one_le₀ (by nlinarith)

private def invOneAddSqSymbol : BoundedBorelFunction ℝ :=
  BoundedBorelFunction.ofFunction (fun t ↦ (((1 + t ^ 2)⁻¹ : ℝ) : ℂ))
    (Continuous.measurable <| by fun_prop (disch := intro t; positivity))
    ⟨1, zero_le_one, norm_inv_one_add_sq_le_one⟩

private theorem norm_invOneAddSqSymbol_le (t : ℝ) :
    ‖invOneAddSqSymbol t‖ ≤ 1 := by
  simpa only [invOneAddSqSymbol, BoundedBorelFunction.ofFunction_apply] using
    norm_inv_one_add_sq_le_one t

/-- The **bounded transform** (or Woronowicz–Baaj–Julg transform) `F_A = A (1 + A²)⁻¹/²` of a
self-adjoint operator `A` with compact resolvent, defined via the bounded eigenbasis functional
calculus of `t ↦ t / √(1 + t²)`. -/
def boundedTransform (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    H →L[ℂ] H :=
  A.boundedEigenCalculus hA h boundedTransformSymbol ⟨1, norm_boundedTransformSymbol_le⟩

variable (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

private theorem boundedTransform_eq_integral :
    A.boundedTransform hA h = (A.spectralPVM hA).integral boundedTransformSymbol :=
  A.boundedEigenCalculus_eq_integral hA h boundedTransformSymbol ⟨1, norm_boundedTransformSymbol_le⟩

/-- In any orthonormal eigenbasis of `A`, the bounded transform acts diagonally by
`λᵢ / √(1 + λᵢ²)`. -/
theorem boundedTransform_eq_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    (m : ℓ^∞(ι, ℂ)) (hm : ∀ i, m i = ((lam i / Real.sqrt (1 + lam i ^ 2) : ℝ) : ℂ)) :
    A.boundedTransform hA h = b.diagonal m :=
  A.boundedEigenCalculus_eq_diagonal hA h b hb _ _ m fun i ↦ by
    simpa only [boundedTransformSymbol, BoundedBorelFunction.ofFunction_apply] using hm i

/-- On an eigenvector of `A` with real eigenvalue `r`, the bounded transform multiplies by
`r / √(1 + r²)`. -/
theorem boundedTransform_apply_of_apply_eq_smul (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) :
    A.boundedTransform hA h x = ((r / Real.sqrt (1 + r ^ 2) : ℝ) : ℂ) • (x : H) := by
  rw [boundedTransform, A.boundedEigenCalculus_apply_of_apply_eq_smul hA h
      ⟨1, norm_boundedTransformSymbol_le⟩ x hx,
    boundedTransformSymbol, BoundedBorelFunction.ofFunction_apply]

/-- The bounded transform is self-adjoint. -/
theorem isSelfAdjoint_boundedTransform : IsSelfAdjoint (A.boundedTransform hA h) := by
  rw [IsSelfAdjoint, boundedTransform_eq_integral, ← map_star]
  congr 1
  ext t
  simp [boundedTransformSymbol]

/-- The star of the bounded transform is itself. -/
@[simp]
theorem star_boundedTransform : star (A.boundedTransform hA h) = A.boundedTransform hA h :=
  (A.isSelfAdjoint_boundedTransform hA h).star_eq

/-- The bounded transform is a contraction: `‖A (1 + A²)⁻¹/²‖ ≤ 1`. -/
theorem norm_boundedTransform_le_one : ‖A.boundedTransform hA h‖ ≤ 1 := by
  rw [boundedTransform_eq_integral]
  exact (A.spectralPVM hA).norm_integral_le zero_le_one norm_boundedTransformSymbol_le

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
  have hinv_fn : (invOneAddSqSymbol : ℝ → ℂ) = fun t ↦ (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) := by
    ext t
    simp [invOneAddSqSymbol]
  have hinv_int : (A.spectralPVM hA).integral invOneAddSqSymbol = A.invOneAddSq := by
    rw [← A.boundedEigenCalculus_eq_integral hA h invOneAddSqSymbol ⟨1, norm_invOneAddSqSymbol_le⟩]
    simp_rw [hinv_fn]
    exact A.boundedEigenCalculus_invOneAddSq hA h ⟨1, norm_inv_one_add_sq_le_one⟩
  rw [boundedTransform_eq_integral, ← hinv_int, ← map_mul, ← map_one (A.spectralPVM hA).integral,
    ← _root_.map_sub (A.spectralPVM hA).integral]
  congr 1
  ext t
  simp only [BoundedBorelFunction.sub_apply, BoundedBorelFunction.one_apply,
    BoundedBorelFunction.mul_apply, boundedTransformSymbol, invOneAddSqSymbol,
    BoundedBorelFunction.ofFunction_apply]
  exact sub_eq_iff_eq_add.2 (inv_one_add_sq_add_boundedTransform_sq t).symm

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
theorem boundedTransform_conj {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') :
    (A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).boundedTransform (hA.conj U)
      ((hasCompactResolvent_conj_iff (U : H ≃L[ℂ] H')).2 h) =
      U.conjStarAlgEquiv (A.boundedTransform hA h) :=
  A.boundedEigenCalculus_conj hA h U _ _

/-- Any bounded operator preserving `D(A)` and anticommuting with `A` anticommutes with `F_A`. -/
theorem mul_boundedTransform_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.property⟩) :
    γ * A.boundedTransform hA h = -(A.boundedTransform hA h * γ) :=
  A.mul_boundedEigenCalculus_of_anticommute hA h hγdom hγA _ fun t ↦ by
    simp [boundedTransformSymbol, neg_div]

/-! ### The Baaj–Julg commutator theorem -/

private def bjShift (r : ℝ) : ℝ := Real.sqrt (1 + max r 0)

private theorem one_le_bjShift (r : ℝ) : 1 ≤ bjShift r :=
  Real.one_le_sqrt.2 (by linarith [le_max_right r 0])

private theorem bjShift_pos (r : ℝ) : 0 < bjShift r :=
  zero_lt_one.trans_le (one_le_bjShift r)

private theorem sq_bjShift (r : ℝ) : bjShift r ^ 2 = 1 + max r 0 :=
  Real.sq_sqrt (by linarith [le_max_right r 0])

private theorem continuous_bjShift : Continuous bjShift :=
  Real.continuous_sqrt.comp (continuous_const.add (continuous_id.max continuous_const))

private def bjMulRes (A : H →ₗ.[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  -(2 : ℂ)⁻¹ • (A.resolvent (Complex.I * bjShift r) + A.resolvent (-Complex.I * bjShift r))

private theorem mem_resolventSet_I_bjShift (hA : IsSelfAdjoint A) (r : ℝ) :
    Complex.I * bjShift r ∈ A.resolventSet :=
  hA.mem_resolventSet_I_mul (bjShift_pos r).ne'

private theorem mem_resolventSet_neg_I_bjShift (hA : IsSelfAdjoint A) (r : ℝ) :
    -Complex.I * bjShift r ∈ A.resolventSet := by
  rw [neg_mul, ← mul_neg, ← Complex.ofReal_neg]
  exact hA.mem_resolventSet_I_mul (neg_ne_zero.2 (bjShift_pos r).ne')

private theorem adjoint_resolvent_I_bjShift (hA : IsSelfAdjoint A) (r : ℝ) :
    (A.resolvent (Complex.I * bjShift r)).adjoint = A.resolvent (-Complex.I * bjShift r) := by
  rw [hA.adjoint_resolvent (mem_resolventSet_I_bjShift hA r), map_mul, Complex.conj_I,
    Complex.conj_ofReal]

private theorem isSelfAdjoint_bjMulRes (hA : IsSelfAdjoint A) (r : ℝ) :
    IsSelfAdjoint (bjMulRes A r) := by
  have hadj2 : (A.resolvent (-Complex.I * bjShift r)).adjoint =
      A.resolvent (Complex.I * bjShift r) := by
    rw [← adjoint_resolvent_I_bjShift hA r, ContinuousLinearMap.adjoint_adjoint]
  rw [bjMulRes, ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint.map_smulₛₗ,
    _root_.map_add ContinuousLinearMap.adjoint, adjoint_resolvent_I_bjShift hA r, hadj2, add_comm]
  congr 1
  simp [Complex.ext_iff]

private theorem bjMulRes_apply_basis (hA : IsSelfAdjoint A) {ι : Type*} {b : HilbertBasis ι ℂ H}
    {lam : ι → ℝ} (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    {r : ℝ} (hr : 0 ≤ r) (k : ι) :
    bjMulRes A r (b k) = ((lam k / (1 + r + lam k ^ 2) : ℝ) : ℂ) • b k := by
  obtain ⟨hk, hAk⟩ := hb k
  have h1 := resolvent_apply_of_apply_eq_smul (mem_resolventSet_I_bjShift hA r) ⟨b k, hk⟩ hAk
  have h2 := resolvent_apply_of_apply_eq_smul (mem_resolventSet_neg_I_bjShift hA r) ⟨b k, hk⟩ hAk
  rw [bjMulRes, _root_.smul_apply, _root_.add_apply, h1, h2, ← add_smul, smul_smul]
  congr 1
  set s : ℝ := bjShift r
  have hs0 : s ≠ 0 := (bjShift_pos r).ne'
  have hs2 : s ^ 2 = 1 + r := by rw [sq_bjShift, max_eq_left hr]
  have hpos1 : Complex.I * (s : ℂ) - (lam k : ℂ) ≠ 0 :=
    fun heq ↦ hs0 (by simpa using congrArg Complex.im heq)
  have hpos2 : -Complex.I * (s : ℂ) - (lam k : ℂ) ≠ 0 :=
    fun heq ↦ hs0 (by simpa using congrArg Complex.im heq)
  have hs2c : (s : ℂ) ^ 2 = ((1 + r : ℝ) : ℂ) := by exact_mod_cast hs2
  have hprod : (Complex.I * (s : ℂ) - (lam k : ℂ)) * (-Complex.I * (s : ℂ) - (lam k : ℂ)) =
      ((1 + r + lam k ^ 2 : ℝ) : ℂ) := by
    calc (Complex.I * (s : ℂ) - (lam k : ℂ)) * (-Complex.I * (s : ℂ) - (lam k : ℂ))
        = (lam k : ℂ) ^ 2 - (Complex.I ^ 2) * (s : ℂ) ^ 2 := by ring
      _ = (lam k : ℂ) ^ 2 + (s : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
      _ = ((1 + r + lam k ^ 2 : ℝ) : ℂ) := by rw [hs2c]; push_cast; ring
  rw [inv_add_inv hpos1 hpos2, hprod]
  push_cast
  have _ : (1 : ℝ) + r + lam k ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem isCompactOperator_bjMulRes (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (r : ℝ) : IsCompactOperator ⇑(bjMulRes A r) := by
  rw [bjMulRes, FunLike.coe_smul, FunLike.coe_add]
  have hc1 := (hA.hasCompactResolvent_iff_isCompactOperator_resolvent
    (z := Complex.I * bjShift r) (by simp [(bjShift_pos r).ne'])).1 h
  have hc2 := (hA.hasCompactResolvent_iff_isCompactOperator_resolvent
    (z := -Complex.I * bjShift r) (by simp [(bjShift_pos r).ne'])).1 h
  exact (compactOperator (RingHom.id ℂ) H H).smul_mem _
    ((compactOperator (RingHom.id ℂ) H H).add_mem hc1 hc2)

private theorem norm_resolvent_I_mul_sub_le (hA : IsSelfAdjoint A) {t₁ t₂ : ℝ}
    (ht₁ : 1 ≤ t₁) (ht₂ : 1 ≤ t₂) :
    ‖A.resolvent (Complex.I * t₁) - A.resolvent (Complex.I * t₂)‖ ≤ ‖t₁ - t₂‖ := by
  have h1 := hA.mem_resolventSet_I_mul (zero_lt_one.trans_le ht₁).ne'
  have h2 := hA.mem_resolventSet_I_mul (zero_lt_one.trans_le ht₂).ne'
  rw [resolvent_sub_resolvent h1 h2, norm_smul]
  have hsub : ‖Complex.I * (t₂ : ℂ) - Complex.I * (t₁ : ℂ)‖ = ‖t₁ - t₂‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
      norm_sub_rev]
  have hn1 : ‖A.resolvent (Complex.I * t₁)‖ ≤ 1 := by
    refine (hA.norm_resolvent_I_mul_le (zero_lt_one.trans_le ht₁).ne').trans ?_
    rw [abs_of_pos (zero_lt_one.trans_le ht₁)]
    exact inv_le_one_of_one_le₀ ht₁
  have hn2 : ‖A.resolvent (Complex.I * t₂)‖ ≤ 1 := by
    refine (hA.norm_resolvent_I_mul_le (zero_lt_one.trans_le ht₂).ne').trans ?_
    rw [abs_of_pos (zero_lt_one.trans_le ht₂)]
    exact inv_le_one_of_one_le₀ ht₂
  calc ‖Complex.I * (t₂ : ℂ) - Complex.I * (t₁ : ℂ)‖ *
          ‖A.resolvent (Complex.I * t₁) ∘L A.resolvent (Complex.I * t₂)‖
      ≤ ‖t₁ - t₂‖ * (‖A.resolvent (Complex.I * t₁)‖ * ‖A.resolvent (Complex.I * t₂)‖) := by
        rw [hsub]; gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖t₁ - t₂‖ * (1 * 1) := by gcongr
    _ = ‖t₁ - t₂‖ := by ring

private theorem continuous_bjMulRes (hA : IsSelfAdjoint A) : Continuous (bjMulRes A) := by
  have hcont_pos : Continuous fun r ↦ A.resolvent (Complex.I * bjShift r) := by
    have hon : ContinuousOn (fun t : ℝ ↦ A.resolvent (Complex.I * t)) (Ici 1) := by
      rw [Metric.continuousOn_iff]
      intro t ht ε hε
      refine ⟨ε, hε, fun t' ht' htt' ↦ ?_⟩
      rw [dist_eq_norm] at htt' ⊢
      exact (norm_resolvent_I_mul_sub_le hA ht' ht).trans_lt htt'
    exact hon.comp_continuous continuous_bjShift one_le_bjShift
  have hcont_neg : Continuous fun r ↦ A.resolvent (-Complex.I * bjShift r) := by
    have hfun : (fun r ↦ A.resolvent (-Complex.I * bjShift r)) =
        fun r ↦ ContinuousLinearMap.adjoint (A.resolvent (Complex.I * bjShift r)) := by
      ext1 r
      exact (adjoint_resolvent_I_bjShift hA r).symm
    rw [hfun]
    exact ContinuousLinearMap.adjoint.continuous.comp hcont_pos
  unfold bjMulRes
  exact (continuous_const (y := -(2 : ℂ)⁻¹)).smul (hcont_pos.add hcont_neg)

omit [CompleteSpace H] in
private theorem resolvent_mul_sub_mul_resolvent {T C : H →L[ℂ] H}
    (hTC : SylvesterEquation A A T C) {z : ℂ} (hz : z ∈ A.resolventSet) :
    A.resolvent z * T - T * A.resolvent z = A.resolvent z * C * A.resolvent z := by
  ext y
  simp only [_root_.sub_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  have hmem : A.resolvent z y ∈ A.domain := resolvent_mem_domain hz y
  have hTmem : T (A.resolvent z y) ∈ A.domain := hTC.mapsTo_domain ⟨A.resolvent z y, hmem⟩
  have hstep : z • T (A.resolvent z y) - A ⟨T (A.resolvent z y), hTmem⟩ =
      T y - C (A.resolvent z y) := by
    have hC := hTC.equation ⟨A.resolvent z y, hmem⟩
    have hR := smul_sub_apply_resolvent hz y
    dsimp only at hC
    calc z • T (A.resolvent z y) - A ⟨T (A.resolvent z y), hTmem⟩
        = (z • T (A.resolvent z y) - T (A ⟨A.resolvent z y, hmem⟩)) - C (A.resolvent z y) := by
            rw [← hC]; abel
      _ = T (z • A.resolvent z y - A ⟨A.resolvent z y, hmem⟩) - C (A.resolvent z y) := by
            rw [T.map_sub, ContinuousLinearMap.map_smul]
      _ = T y - C (A.resolvent z y) := by rw [hR]
  have happ := congrArg (A.resolvent z) hstep
  rw [resolvent_smul_sub_apply hz ⟨T (A.resolvent z y), hTmem⟩, (A.resolvent z).map_sub] at happ
  exact sub_eq_iff_eq_add'.2 (eq_add_of_sub_eq happ.symm)

private theorem norm_bjMulRes_commutator_le (hA : IsSelfAdjoint A) {T C : H →L[ℂ] H}
    (hTC : SylvesterEquation A A T C) {r : ℝ} (hr : 0 ≤ r) :
    ‖bjMulRes A r * T - T * bjMulRes A r‖ ≤ ‖C‖ * (1 + r)⁻¹ := by
  have hcomm : bjMulRes A r * T - T * bjMulRes A r =
      -(2 : ℂ)⁻¹ • (A.resolvent (Complex.I * bjShift r) * C * A.resolvent (Complex.I * bjShift r) +
        A.resolvent (-Complex.I * bjShift r) * C * A.resolvent (-Complex.I * bjShift r)) := by
    rw [bjMulRes, smul_mul_assoc, mul_smul_comm, ← smul_sub, add_mul, mul_add, add_sub_add_comm,
      resolvent_mul_sub_mul_resolvent hTC (mem_resolventSet_I_bjShift hA r),
      resolvent_mul_sub_mul_resolvent hTC (mem_resolventSet_neg_I_bjShift hA r)]
  have hs0 : bjShift r ≠ 0 := (bjShift_pos r).ne'
  have hs2 : bjShift r ^ 2 = 1 + r := by rw [sq_bjShift, max_eq_left hr]
  have hn_pos : ‖A.resolvent (Complex.I * bjShift r)‖ ≤ (bjShift r)⁻¹ := by
    simpa only [abs_of_pos (bjShift_pos r)] using hA.norm_resolvent_I_mul_le hs0
  have hn_neg : ‖A.resolvent (-Complex.I * bjShift r)‖ ≤ (bjShift r)⁻¹ := by
    simpa only [← adjoint_resolvent_I_bjShift hA r, ContinuousLinearMap.adjoint.norm_map] using
      hn_pos
  have hterm_pos :
      ‖A.resolvent (Complex.I * bjShift r) * C * A.resolvent (Complex.I * bjShift r)‖ ≤
        ‖C‖ * (1 + r)⁻¹ := by
    calc ‖A.resolvent (Complex.I * bjShift r) * C * A.resolvent (Complex.I * bjShift r)‖
        ≤ ‖A.resolvent (Complex.I * bjShift r)‖ * ‖C‖ * ‖A.resolvent (Complex.I * bjShift r)‖ :=
          norm_mul₃_le
      _ ≤ (bjShift r)⁻¹ * ‖C‖ * (bjShift r)⁻¹ := by
          gcongr; exact mul_nonneg (inv_nonneg.2 (bjShift_pos r).le) (norm_nonneg C)
      _ = ‖C‖ * (bjShift r ^ 2)⁻¹ := by ring
      _ = ‖C‖ * (1 + r)⁻¹ := by rw [hs2]
  have hterm_neg :
      ‖A.resolvent (-Complex.I * bjShift r) * C * A.resolvent (-Complex.I * bjShift r)‖ ≤
        ‖C‖ * (1 + r)⁻¹ := by
    calc ‖A.resolvent (-Complex.I * bjShift r) * C * A.resolvent (-Complex.I * bjShift r)‖
        ≤ ‖A.resolvent (-Complex.I * bjShift r)‖ * ‖C‖ *
            ‖A.resolvent (-Complex.I * bjShift r)‖ := norm_mul₃_le
      _ ≤ (bjShift r)⁻¹ * ‖C‖ * (bjShift r)⁻¹ := by
          gcongr; exact mul_nonneg (inv_nonneg.2 (bjShift_pos r).le) (norm_nonneg C)
      _ = ‖C‖ * (bjShift r ^ 2)⁻¹ := by ring
      _ = ‖C‖ * (1 + r)⁻¹ := by rw [hs2]
  rw [hcomm, norm_smul, norm_neg, norm_inv, Complex.norm_ofNat]
  calc (2 : ℝ)⁻¹ *
          ‖A.resolvent (Complex.I * bjShift r) * C * A.resolvent (Complex.I * bjShift r) +
            A.resolvent (-Complex.I * bjShift r) * C * A.resolvent (-Complex.I * bjShift r)‖
      ≤ (2 : ℝ)⁻¹ * (‖C‖ * (1 + r)⁻¹ + ‖C‖ * (1 + r)⁻¹) := by
        gcongr; exact (norm_add_le _ _).trans (add_le_add hterm_pos hterm_neg)
    _ = ‖C‖ * (1 + r)⁻¹ := by ring

private def bjIntegrand (A : H →ₗ.[ℂ] H) (T : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  (Real.pi⁻¹ * (Real.sqrt r)⁻¹ : ℝ) • (bjMulRes A r * T - T * bjMulRes A r)

private theorem continuousOn_bjIntegrand (hA : IsSelfAdjoint A) (T : H →L[ℂ] H) :
    ContinuousOn (bjIntegrand A T) (Ioi 0) :=
  (continuousOn_const.mul (ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn
    fun _ hr ↦ (Real.sqrt_pos.2 hr).ne')).smul
    (((continuous_bjMulRes hA).mul continuous_const).sub
      (continuous_const.mul (continuous_bjMulRes hA))).continuousOn

private def bjMajorant (c r : ℝ) : ℝ :=
  (Real.pi⁻¹ * c) * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹)

private theorem integrableOn_bjMajorant (c : ℝ) : IntegrableOn (bjMajorant c) (Ioi 0) :=
  (TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add zero_lt_one).const_mul _

private theorem integral_bjMajorant (c : ℝ) :
    ∫ r in Ioi (0 : ℝ), bjMajorant c r = c := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [bjMajorant, integral_const_mul,
    TauCeti.integral_Ioi_inv_sqrt_mul_inv_add zero_lt_one, Real.sqrt_one, div_one]
  field_simp

private theorem norm_bjIntegrand_le (hA : IsSelfAdjoint A) {T C : H →L[ℂ] H}
    (hTC : SylvesterEquation A A T C) {r : ℝ} (hr : 0 < r) :
    ‖bjIntegrand A T r‖ ≤ bjMajorant ‖C‖ r := by
  rw [bjIntegrand, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), bjMajorant]
  calc Real.pi⁻¹ * (Real.sqrt r)⁻¹ * ‖bjMulRes A r * T - T * bjMulRes A r‖
      ≤ Real.pi⁻¹ * (Real.sqrt r)⁻¹ * (‖C‖ * (1 + r)⁻¹) := by
        gcongr; exact norm_bjMulRes_commutator_le hA hTC hr.le
    _ = Real.pi⁻¹ * ‖C‖ * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹) := by ring

private theorem integrableOn_bjIntegrand (hA : IsSelfAdjoint A) {T C : H →L[ℂ] H}
    (hTC : SylvesterEquation A A T C) :
    IntegrableOn (bjIntegrand A T) (Ioi 0) := by
  refine (integrableOn_bjMajorant ‖C‖).mono'
    ((continuousOn_bjIntegrand hA T).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact norm_bjIntegrand_le hA hTC hr

private def bjKernelReal (μ r : ℝ) : ℝ :=
  Real.pi⁻¹ * (μ * ((Real.sqrt r)⁻¹ * (1 + μ ^ 2 + r)⁻¹))

private def bjKernel (μ r : ℝ) : ℂ :=
  Complex.ofRealCLM (bjKernelReal μ r)

private theorem integrableOn_bjKernelReal (μ : ℝ) : IntegrableOn (bjKernelReal μ) (Ioi 0) :=
  ((TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add (a := 1 + μ ^ 2)
    (by positivity)).const_mul μ).const_mul Real.pi⁻¹

private theorem integrableOn_bjKernel (μ : ℝ) : IntegrableOn (bjKernel μ) (Ioi 0) :=
  Complex.ofRealCLM.integrable_comp (integrableOn_bjKernelReal μ)

private theorem integral_bjKernel (μ : ℝ) :
    ∫ r in Ioi (0 : ℝ), bjKernel μ r = ((μ / Real.sqrt (1 + μ ^ 2) : ℝ) : ℂ) := by
  rw [show (∫ r in Ioi (0 : ℝ), bjKernel μ r) =
      Complex.ofRealCLM (∫ r in Ioi (0 : ℝ), bjKernelReal μ r) from
      Complex.ofRealCLM.integral_comp_comm (integrableOn_bjKernelReal μ),
    Complex.ofRealCLM_apply]
  congr 1
  rw [show (∫ r in Ioi (0 : ℝ), bjKernelReal μ r) =
      Real.pi⁻¹ * (μ * ∫ r in Ioi (0 : ℝ), (Real.sqrt r)⁻¹ * (1 + μ ^ 2 + r)⁻¹) from by
        simp only [bjKernelReal, integral_const_mul],
    TauCeti.integral_Ioi_inv_sqrt_mul_inv_add (a := 1 + μ ^ 2) (by positivity)]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

private theorem commutator_boundedTransform_eq_integral {T C : H →L[ℂ] H}
    (hTC : SylvesterEquation A A T C) :
    A.boundedTransform hA h * T - T * A.boundedTransform hA h =
      ∫ r in Ioi (0 : ℝ), bjIntegrand A T r := by
  obtain ⟨_, b, lam, hb⟩ := hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h
  have hint := integrableOn_bjIntegrand hA hTC
  refine b.ext_inner_apply b fun i j ↦ ?_
  have hF_eig (k) : A.boundedTransform hA h (b k) =
      ((lam k / Real.sqrt (1 + lam k ^ 2) : ℝ) : ℂ) • b k :=
    A.boundedTransform_apply_of_apply_eq_smul hA h ⟨_, (hb k).1⟩ (hb k).2
  have hL_comm : ⟪b i, (∫ r in Ioi (0 : ℝ), bjIntegrand A T r) (b j)⟫_ℂ =
      ∫ r in Ioi (0 : ℝ), ⟪b i, bjIntegrand A T r (b j)⟫_ℂ :=
    (((innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ H (b j))).integral_comp_comm hint).symm
  have hinner (r : ℝ) (hr : 0 < r) : ⟪b i, bjIntegrand A T r (b j)⟫_ℂ =
      (bjKernel (lam i) r - bjKernel (lam j) r) * ⟪b i, T (b j)⟫_ℂ := by
    rw [bjIntegrand, _root_.smul_apply, ← Complex.coe_smul, inner_smul_right,
      b.inner_selfAdjoint_diag_commutator (isSelfAdjoint_bjMulRes hA r)
        (g := fun k ↦ lam k / (1 + r + lam k ^ 2)) (bjMulRes_apply_basis hA hb hr.le) i j]
    simp only [bjKernel, bjKernelReal, Complex.ofRealCLM_apply, RCLike.ofReal_sub,
      Complex.coe_algebraMap, add_right_comm 1 r]
    push_cast; ring
  rw [b.inner_selfAdjoint_diag_commutator (A.isSelfAdjoint_boundedTransform hA h)
      (g := fun k ↦ lam k / Real.sqrt (1 + lam k ^ 2)) hF_eig i j,
    hL_comm, setIntegral_congr_fun measurableSet_Ioi hinner, integral_mul_const,
    integral_sub (integrableOn_bjKernel (lam i)) (integrableOn_bjKernel (lam j)),
    integral_bjKernel, integral_bjKernel, RCLike.ofReal_sub]
  simp only [RCLike.ofReal_div, Complex.ofReal_div]
  rfl

/-- **Baaj–Julg compactness theorem.** If `T` and `C` satisfy the domain-aware Sylvester equation
`A T - T A = C`, then `[F_A, T]` is a compact operator. -/
theorem isCompactOperator_commutator_boundedTransform {T C : H →L[ℂ] H}
    (hTC : SylvesterEquation A A T C) :
    IsCompactOperator ⇑(A.boundedTransform hA h * T - T * A.boundedTransform hA h) := by
  rw [commutator_boundedTransform_eq_integral hA h hTC]
  refine MeasureTheory.integral_mem_of_isClosed (K := compactOperator (RingHom.id ℂ) H H)
    isClosed_setOfPred_isCompactOperator (integrableOn_bjIntegrand hA hTC)
    (Filter.Eventually.of_forall fun r ↦ ?_)
  have hcomm : IsCompactOperator ⇑(bjMulRes A r * T - T * bjMulRes A r) := by
    rw [FunLike.coe_sub]
    exact ((isCompactOperator_bjMulRes hA h r).mul_right T).sub
      ((isCompactOperator_bjMulRes hA h r).mul_left T)
  rw [bjIntegrand, ← Complex.coe_smul]
  exact (compactOperator (RingHom.id ℂ) H H).smul_mem _ hcomm

/-- **Baaj–Julg norm estimate.** If `T` and `C` satisfy the domain-aware Sylvester equation
`A T - T A = C`, then `‖[F_A, T]‖ ≤ (5 / 4) ‖C‖`. -/
theorem norm_commutator_boundedTransform_le {T C : H →L[ℂ] H}
    (hTC : SylvesterEquation A A T C) :
    ‖A.boundedTransform hA h * T - T * A.boundedTransform hA h‖ ≤ 5 / 4 * ‖C‖ := by
  rw [commutator_boundedTransform_eq_integral hA h hTC]
  have hint := integrableOn_bjIntegrand hA hTC
  calc ‖∫ r in Ioi (0 : ℝ), bjIntegrand A T r‖
      ≤ ∫ r in Ioi (0 : ℝ), ‖bjIntegrand A T r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioi (0 : ℝ), bjMajorant ‖C‖ r :=
        setIntegral_mono_on hint.norm (integrableOn_bjMajorant ‖C‖) measurableSet_Ioi fun _ hr ↦
          norm_bjIntegrand_le hA hTC hr
    _ = ‖C‖ := integral_bjMajorant ‖C‖
    _ ≤ 5 / 4 * ‖C‖ := by linarith [norm_nonneg C]

end BoundedTransform

end LinearPMap
