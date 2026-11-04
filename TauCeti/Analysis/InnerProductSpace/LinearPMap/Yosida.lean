/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, Adam Bornemann
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.Normed.Operator.Dense
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Imaginary-shift Yosida approximations of self-adjoint operators

For a self-adjoint partial operator `A` and real `r`, set
`A_r = -r² R(ir) - ir I`. The positive and negative shifts are obtained by choosing `r`
positive or negative. Their average is self-adjoint, and these averages commute pairwise.
The scaled resolvents `ir R(ir)` converge strongly to the identity as `|r|` tends to infinity;
hence the approximants converge to `A` on its domain. The estimates include the zero Hilbert
space. No spectral measure is required.

## Provenance

Adapted and generalized from
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` in the Kitware DKPS
formalization (Jon Crall and Claude Opus 5, Apache-2.0). That file adapts the definitions and
approximation arguments from Spectra's `YosidaHille/Approximation/{Helpers,Defs}.lean`,
commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`. Original notice: Copyright (c) 2026
Spectra Formalization Project; Authors: Adam Bornemann; Apache-2.0.
Here the shift is any real number, the resolvent and adjoint laws are native, and strong
convergence extends from the dense domain using `ContinuousLinearMap.tendsto_apply_of_dense`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, Chapter VIII.
-/

public section

open Complex Filter
open scoped Topology

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (A : H →ₗ.[ℂ] H)

/-- The imaginary-shift Yosida approximation `-r² R(ir) - ir I`. -/
noncomputable def imaginaryYosidaApproximation (r : ℝ) : H →L[ℂ] H :=
  -((r : ℂ) ^ 2 • A.resolvent (I * r)) - (I * r) • 1

/-- The self-adjoint average of the positive- and negative-shift approximations. -/
noncomputable def symmetricYosidaApproximation (r : ℝ) : H →L[ℂ] H :=
  (-((r : ℂ) ^ 2 / 2)) • (A.resolvent (I * r) + A.resolvent (-I * r))

/-- The formula for the imaginary-shift approximation. -/
theorem imaginaryYosidaApproximation_def (r : ℝ) :
    A.imaginaryYosidaApproximation r = -((r : ℂ) ^ 2 • A.resolvent (I * r)) - (I * r) • 1 :=
  (rfl)

/-- The symmetric approximation is the average of the two opposite shifts. -/
theorem symmetricYosidaApproximation_eq_avg (r : ℝ) :
    A.symmetricYosidaApproximation r =
      (1 / 2 : ℂ) • (A.imaginaryYosidaApproximation r + A.imaginaryYosidaApproximation (-r)) := by
  simp only [symmetricYosidaApproximation, imaginaryYosidaApproximation, Complex.ofReal_neg,
    mul_neg, neg_mul, neg_sq]
  module

variable {A}

/-- The imaginary-shift approximation at zero is zero. -/
@[simp] theorem imaginaryYosidaApproximation_zero : A.imaginaryYosidaApproximation 0 = 0 := by
  simp [imaginaryYosidaApproximation]

/-- The symmetric approximation at zero is zero. -/
@[simp] theorem symmetricYosidaApproximation_zero : A.symmetricYosidaApproximation 0 = 0 := by
  simp [symmetricYosidaApproximation]

variable [CompleteSpace H]

/-- The normalized imaginary resolvent is a contraction. -/
theorem _root_.IsSelfAdjoint.norm_smul_resolvent_I_mul_le_one (hA : IsSelfAdjoint A) (r : ℝ) :
    ‖(I * (r : ℂ)) • A.resolvent (I * r)‖ ≤ 1 := by
  by_cases hr : r = 0
  · simp [hr]
  have him : (I * (r : ℂ)).im ≠ 0 := by simpa using hr
  calc
    ‖(I * (r : ℂ)) • A.resolvent (I * r)‖
        = |r| * ‖A.resolvent (I * r)‖ := by simp [norm_smul]
    _ ≤ |r| * |r|⁻¹ := by
      gcongr
      simpa using hA.norm_resolvent_le him
    _ = 1 := mul_inv_cancel₀ (abs_ne_zero.mpr hr)

/-- On its domain the imaginary-shift approximation factors through the normalized resolvent. -/
theorem _root_.IsSelfAdjoint.imaginaryYosidaApproximation_apply (hA : IsSelfAdjoint A)
    {r : ℝ} (hr : r ≠ 0) (x : A.domain) :
    A.imaginaryYosidaApproximation r x = (I * (r : ℂ)) • A.resolvent (I * r) (A x) := by
  have hz := hA.mem_resolventSet_of_im_ne_zero (by simpa using hr : (I * (r : ℂ)).im ≠ 0)
  have h := resolvent_smul_sub_apply hz x
  rw [_root_.map_sub, _root_.map_smul] at h
  simp only [imaginaryYosidaApproximation, _root_.sub_apply,
    _root_.neg_apply, _root_.smul_apply,
    one_apply_eq_self]
  have hR : A.resolvent (I * r) (A x) = (I * (r : ℂ)) • A.resolvent (I * r) x - x :=
    eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (eq_add_of_sub_eq h).symm)
  rw [hR]
  simp only [smul_sub, smul_smul]
  have hs : (I * (r : ℂ)) * (I * (r : ℂ)) = -(r : ℂ) ^ 2 := by
    calc (I * (r : ℂ)) * (I * (r : ℂ)) = (I * I) * (r : ℂ) ^ 2 := by ring
         _ = -(r : ℂ) ^ 2 := by rw [I_mul_I, neg_one_mul]
  rw [hs, neg_smul]

/-- The imaginary-shift approximation has norm at most `2 |r|`. -/
theorem _root_.IsSelfAdjoint.norm_imaginaryYosidaApproximation_le
    (hA : IsSelfAdjoint A) (r : ℝ) : ‖A.imaginaryYosidaApproximation r‖ ≤ 2 * |r| := by
  by_cases hr : r = 0
  · simp [hr]
  have hR : ‖A.resolvent (I * r)‖ ≤ |r|⁻¹ :=
    by simpa using hA.norm_resolvent_le (by simpa using hr : (I * (r : ℂ)).im ≠ 0)
  have hfirst : ‖(r : ℂ) ^ 2 • A.resolvent (I * r)‖ ≤ |r| := by
    calc
      ‖(r : ℂ) ^ 2 • A.resolvent (I * r)‖ = |r| ^ 2 * ‖A.resolvent (I * r)‖ := by
        simp [norm_smul, norm_pow]
      _ ≤ |r| ^ 2 * |r|⁻¹ := mul_le_mul_of_nonneg_left hR (sq_nonneg _)
      _ = |r| := by field_simp
  have hone : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  have hsecond : ‖(I * (r : ℂ)) • (1 : H →L[ℂ] H)‖ ≤ |r| := by
    rw [norm_smul, norm_mul, norm_I, Complex.norm_real, one_mul]
    exact (mul_le_mul_of_nonneg_left hone (abs_nonneg r)).trans_eq (mul_one _)
  exact (norm_sub_le _ _).trans (by simpa [norm_neg, two_mul] using add_le_add hfirst hsecond)

/-- The approximations at opposite imaginary shifts are adjoints of one another. -/
theorem _root_.IsSelfAdjoint.adjoint_imaginaryYosidaApproximation
    (hA : IsSelfAdjoint A) (r : ℝ) :
    (A.imaginaryYosidaApproximation r).adjoint = A.imaginaryYosidaApproximation (-r) := by
  by_cases hr : r = 0
  · simp [hr]
  have hz := hA.mem_resolventSet_of_im_ne_zero (by simpa using hr : (I * (r : ℂ)).im ≠ 0)
  rw [← ContinuousLinearMap.star_eq_adjoint]
  simp only [imaginaryYosidaApproximation, star_sub, star_neg, star_smul, star_one]
  rw [ContinuousLinearMap.star_eq_adjoint, hA.adjoint_resolvent hz]
  simp only [star_pow, Complex.star_def, _root_.map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.ofReal_neg, neg_sq, mul_neg, neg_mul, neg_smul, sub_neg_eq_add]

/-- The symmetric Yosida approximation is self-adjoint. -/
theorem _root_.IsSelfAdjoint.isSelfAdjoint_symmetricYosidaApproximation
    (hA : IsSelfAdjoint A) (r : ℝ) : IsSelfAdjoint (A.symmetricYosidaApproximation r) := by
  rw [isSelfAdjoint_iff, symmetricYosidaApproximation_eq_avg, star_smul, star_add]
  simp only [ContinuousLinearMap.star_eq_adjoint, hA.adjoint_imaginaryYosidaApproximation,
    neg_neg]
  simp [add_comm]

/-- Symmetric Yosida approximations commute pairwise. -/
theorem _root_.IsSelfAdjoint.commute_symmetricYosidaApproximation
    (hA : IsSelfAdjoint A) (r s : ℝ) :
    Commute (A.symmetricYosidaApproximation r) (A.symmetricYosidaApproximation s) := by
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  have hp (t : ℝ) (ht : t ≠ 0) : I * (t : ℂ) ∈ A.resolventSet :=
    hA.mem_resolventSet_of_im_ne_zero (by simpa using ht)
  have hn (t : ℝ) (ht : t ≠ 0) : -I * (t : ℂ) ∈ A.resolventSet :=
    hA.mem_resolventSet_of_im_ne_zero (by simpa using neg_ne_zero.mpr ht)
  unfold symmetricYosidaApproximation
  refine Commute.smul_left ?_ _ |>.smul_right _
  refine Commute.add_left ?_ ?_ <;> refine Commute.add_right ?_ ?_ <;>
    first
      | exact resolvent_comm (hp r hr) (hp s hs)
      | exact resolvent_comm (hp r hr) (hn s hs)
      | exact resolvent_comm (hn r hr) (hp s hs)
      | exact resolvent_comm (hn r hr) (hn s hs)

/-- The normalized imaginary resolvents converge strongly to the identity as `|r| → ∞`. -/
theorem _root_.IsSelfAdjoint.tendsto_smul_resolvent_I_mul
    (hA : IsSelfAdjoint A) (x : H) :
    Tendsto (fun r : ℝ => (I * (r : ℂ)) • A.resolvent (I * r) x) (cocompact ℝ) (𝓝 x) := by
  apply ContinuousLinearMap.tendsto_apply_of_dense (g := (1 : H →L[ℂ] H))
    hA.dense_domain (.of_forall (hA.norm_smul_resolvent_I_mul_le_one)) _ x
  intro y hy
  have hn : ∀ᶠ r : ℝ in cocompact ℝ, r ≠ 0 :=
    by simpa using (isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact
  have hzero : Tendsto (fun r : ℝ => A.resolvent (I * r) (A ⟨y, hy⟩))
      (cocompact ℝ) (𝓝 0) := by
    have hinv := (tendsto_norm_cocompact_atTop (E := ℝ)).inv_tendsto_atTop
    have hbound : Tendsto (fun r : ℝ => ‖r‖⁻¹ * ‖A ⟨y, hy⟩‖) (cocompact ℝ) (𝓝 0) := by
      simpa using hinv.mul_const (‖A ⟨y, hy⟩‖)
    apply squeeze_zero_norm' _ hbound
    filter_upwards [hn] with r hr
    calc ‖A.resolvent (I * r) (A ⟨y, hy⟩)‖
        ≤ ‖A.resolvent (I * r)‖ * ‖A ⟨y, hy⟩‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖r‖⁻¹ * ‖A ⟨y, hy⟩‖ := by
        gcongr
        simpa using hA.norm_resolvent_le (by simpa using hr : (I * (r : ℂ)).im ≠ 0)
  have hlim : Tendsto (fun r : ℝ => y + A.resolvent (I * r) (A ⟨y, hy⟩))
      (cocompact ℝ) (𝓝 y) := by simpa using tendsto_const_nhds.add hzero
  have hEq : (fun r : ℝ => y + A.resolvent (I * r) (A ⟨y, hy⟩)) =ᶠ[cocompact ℝ]
      (fun r : ℝ => (I * (r : ℂ)) • A.resolvent (I * r) y) := by
    filter_upwards [hn] with r hr
    have hz := hA.mem_resolventSet_of_im_ne_zero (by simpa using hr : (I * (r : ℂ)).im ≠ 0)
    have h := resolvent_smul_sub_apply hz ⟨y, hy⟩
    rw [_root_.map_sub, _root_.map_smul] at h
    exact (eq_add_of_sub_eq h).symm
  simpa only [_root_.smul_apply, one_apply_eq_self] using hlim.congr' hEq

/-- Imaginary-shift Yosida approximations converge to the original operator on its domain,
for both positive and negative shifts escaping to infinity. -/
theorem _root_.IsSelfAdjoint.tendsto_imaginaryYosidaApproximation_apply
    (hA : IsSelfAdjoint A) (x : A.domain) :
    Tendsto (fun r : ℝ => A.imaginaryYosidaApproximation r x) (cocompact ℝ) (𝓝 (A x)) := by
  apply (hA.tendsto_smul_resolvent_I_mul (A x)).congr'
  filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with r hr
  exact (hA.imaginaryYosidaApproximation_apply (by simpa using hr) x).symm

/-- The symmetric approximations converge to the original operator on its domain. -/
theorem _root_.IsSelfAdjoint.tendsto_symmetricYosidaApproximation_apply
    (hA : IsSelfAdjoint A) (x : A.domain) :
    Tendsto (fun r : ℝ => A.symmetricYosidaApproximation r x) (cocompact ℝ) (𝓝 (A x)) := by
  have hneg := (hA.tendsto_imaginaryYosidaApproximation_apply x).comp
    (Homeomorph.neg ℝ).isClosedEmbedding.tendsto_cocompact
  have h := ((hA.tendsto_imaginaryYosidaApproximation_apply x).add hneg).const_smul (1 / 2 : ℂ)
  simpa [symmetricYosidaApproximation_eq_avg, _root_.smul_apply,
    _root_.add_apply, ← smul_add, ← two_smul ℂ, smul_smul] using h

end LinearPMap
