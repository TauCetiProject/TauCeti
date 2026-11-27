/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, Adam Bornemann
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.Normed.Operator.LinearPMap.Yosida
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

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, Chapter VIII.
-/

public section

open Complex Filter
open scoped Topology

namespace LinearPMap

section NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (A : H →ₗ.[ℂ] H)

/-- The imaginary-shift Yosida approximation `-r² R(ir) - ir I`. -/
noncomputable def imaginaryYosidaApproximation (r : ℝ) : H →L[ℂ] H :=
  LinearPMap.yosidaApproximation A (I * r)

/-- The imaginary-shift approximation is the generic Yosida approximation at `ir`. -/
theorem imaginaryYosidaApproximation_eq_yosidaApproximation (r : ℝ) :
    A.imaginaryYosidaApproximation r = A.yosidaApproximation (I * r) := by
  rw [imaginaryYosidaApproximation]

/-- The average of the positive- and negative-shift approximations; self-adjoint when `A` is
(see `IsSelfAdjoint.isSelfAdjoint_symmetricYosidaApproximation`). -/
noncomputable def symmetricYosidaApproximation (r : ℝ) : H →L[ℂ] H :=
  (-((r : ℂ) ^ 2 / 2)) • (A.resolvent (I * r) + A.resolvent (-I * r))

/-- The resolvent formula for the symmetric approximation. -/
theorem symmetricYosidaApproximation_def (r : ℝ) :
    A.symmetricYosidaApproximation r =
      (-((r : ℂ) ^ 2 / 2)) • (A.resolvent (I * r) + A.resolvent (-I * r)) := by
  rw [symmetricYosidaApproximation]

/-- The formula for the imaginary-shift approximation. -/
theorem imaginaryYosidaApproximation_def (r : ℝ) :
    A.imaginaryYosidaApproximation r = -((r : ℂ) ^ 2 • A.resolvent (I * r)) - (I * r) • 1 := by
  rw [imaginaryYosidaApproximation_eq_yosidaApproximation,
    LinearPMap.yosidaApproximation_def]
  simp [mul_pow]

/-- The symmetric approximation is the average of the two opposite shifts. -/
theorem symmetricYosidaApproximation_eq_avg (r : ℝ) :
    A.symmetricYosidaApproximation r =
      (1 / 2 : ℂ) • (A.imaginaryYosidaApproximation r + A.imaginaryYosidaApproximation (-r)) := by
  simp only [symmetricYosidaApproximation_def, imaginaryYosidaApproximation_def, Complex.ofReal_neg,
    mul_neg, neg_mul, neg_sq]
  module

variable {A}

/-- The imaginary-shift approximation at zero is zero. -/
@[simp] theorem imaginaryYosidaApproximation_zero : A.imaginaryYosidaApproximation 0 = 0 := by
  simp [imaginaryYosidaApproximation_def]

/-- The symmetric approximation at zero is zero. -/
@[simp] theorem symmetricYosidaApproximation_zero : A.symmetricYosidaApproximation 0 = 0 := by
  simp [symmetricYosidaApproximation_def]

end NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

/-- The normalized imaginary resolvent is a contraction. -/
theorem _root_.IsSelfAdjoint.norm_smul_resolvent_I_mul_le_one (hA : IsSelfAdjoint A) (r : ℝ) :
    ‖(I * (r : ℂ)) • A.resolvent (I * r)‖ ≤ 1 := by
  by_cases hr : r = 0
  · simp [hr]
  calc
    ‖(I * (r : ℂ)) • A.resolvent (I * r)‖
        = |r| * ‖A.resolvent (I * r)‖ := by simp [norm_smul]
    _ ≤ |r| * |r|⁻¹ := by
      gcongr
      exact hA.norm_resolvent_I_mul_le hr
    _ = 1 := mul_inv_cancel₀ (abs_ne_zero.mpr hr)

/-- The imaginary-shift approximation has norm at most `2 |r|`. -/
theorem _root_.IsSelfAdjoint.norm_imaginaryYosidaApproximation_le
    (hA : IsSelfAdjoint A) (r : ℝ) : ‖A.imaginaryYosidaApproximation r‖ ≤ 2 * |r| := by
  have hres := hA.norm_smul_resolvent_I_mul_le_one r
  rw [norm_smul] at hres
  simpa [imaginaryYosidaApproximation_eq_yosidaApproximation] using
    (LinearPMap.norm_yosidaApproximation_le hres)

/-- The approximations at opposite imaginary shifts are adjoints of one another. -/
theorem _root_.IsSelfAdjoint.adjoint_imaginaryYosidaApproximation
    (hA : IsSelfAdjoint A) (r : ℝ) :
    (A.imaginaryYosidaApproximation r).adjoint = A.imaginaryYosidaApproximation (-r) := by
  by_cases hr : r = 0
  · simp [hr]
  have hz := hA.mem_resolventSet_I_mul hr
  rw [← ContinuousLinearMap.star_eq_adjoint]
  simp only [imaginaryYosidaApproximation_def, star_sub, star_neg, star_smul, star_one]
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
  rw [symmetricYosidaApproximation_eq_avg, symmetricYosidaApproximation_eq_avg]
  refine Commute.smul_left ?_ _ |>.smul_right _
  have hcomm (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
      Commute (A.imaginaryYosidaApproximation u) (A.imaginaryYosidaApproximation v) :=
    LinearPMap.yosidaApproximation_comm
      (hA.mem_resolventSet_I_mul hu) (hA.mem_resolventSet_I_mul hv)
  exact (hcomm r s hr hs).add_left (hcomm (-r) s (neg_ne_zero.mpr hr) hs) |>.add_right
    ((hcomm r (-s) hr (neg_ne_zero.mpr hs)).add_left
      (hcomm (-r) (-s) (neg_ne_zero.mpr hr) (neg_ne_zero.mpr hs)))

/-- The normalized imaginary resolvents converge strongly to the identity as `|r| → ∞`. -/
theorem _root_.IsSelfAdjoint.tendsto_smul_resolvent_I_mul_apply
    (hA : IsSelfAdjoint A) (x : H) :
    Tendsto (fun r : ℝ => (I * (r : ℂ)) • A.resolvent (I * r) x) (cocompact ℝ) (𝓝 x) := by
  have hn : ∀ᶠ r : ℝ in cocompact ℝ, r ≠ 0 :=
    by simpa using (isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact
  apply LinearPMap.tendsto_smul_resolvent_apply
    (hn.mono fun _ hr => hA.mem_resolventSet_I_mul hr) _
    (.of_forall (hA.norm_smul_resolvent_I_mul_le_one)) hA.dense_domain x
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _
    (tendsto_norm_cocompact_atTop (E := ℝ)).inv_tendsto_atTop
  filter_upwards [hn] with r hr
  simpa using hA.norm_resolvent_I_mul_le hr

/-- Imaginary-shift Yosida approximations converge to the original operator on its domain,
for both positive and negative shifts escaping to infinity. -/
theorem _root_.IsSelfAdjoint.tendsto_imaginaryYosidaApproximation_apply
    (hA : IsSelfAdjoint A) (x : A.domain) :
    Tendsto (fun r : ℝ => A.imaginaryYosidaApproximation r x) (cocompact ℝ) (𝓝 (A x)) := by
  apply LinearPMap.tendsto_yosidaApproximation_apply _ x
    (hA.tendsto_smul_resolvent_I_mul_apply (A x))
  filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with r hr
  exact hA.mem_resolventSet_I_mul (by simpa using hr)

/-- The symmetric approximations converge to the original operator on its domain. -/
theorem _root_.IsSelfAdjoint.tendsto_symmetricYosidaApproximation_apply
    (hA : IsSelfAdjoint A) (x : A.domain) :
    Tendsto (fun r : ℝ => A.symmetricYosidaApproximation r x) (cocompact ℝ) (𝓝 (A x)) := by
  have hneg := (hA.tendsto_imaginaryYosidaApproximation_apply x).comp
    (Homeomorph.neg ℝ).isClosedEmbedding.tendsto_cocompact
  have h := ((hA.tendsto_imaginaryYosidaApproximation_apply x).add hneg).const_smul (1 / 2 : ℂ)
  have havg : (1 / 2 : ℂ) • (A x + A x) = A x := by module
  rw [havg] at h
  simpa [symmetricYosidaApproximation_eq_avg, _root_.smul_apply, _root_.add_apply] using h

end LinearPMap
