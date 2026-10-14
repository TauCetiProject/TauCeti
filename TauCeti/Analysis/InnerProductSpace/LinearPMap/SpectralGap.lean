/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Resolvents of self-adjoint partial linear maps across a spectral gap

Let `A` be a self-adjoint partial linear map on a complex Hilbert space, and suppose that its
spectrum avoids the real interval `(c - s, c + s)` for some `s > 0`. Then `c` is a resolvent
point and `‖R(c)‖ ≤ s⁻¹`; equivalently, `s ‖x‖ ≤ ‖c • x - A x‖` on the domain of `A`.

The resolvent `R(c)` is a bounded self-adjoint operator, so its norm is its spectral radius. A
nonzero spectral value `μ` of `R(c)` corresponds to the spectral value `c - μ⁻¹` of `A`, which
is real because `A` is self-adjoint; the gap forces `|μ⁻¹| ≥ s`, that is `|μ| ≤ s⁻¹`.

This runs in the opposite direction to the lower-bound criterion
`IsSelfAdjoint.norm_resolvent_le_of_norm_le`, which produces a resolvent bound from a lower bound
for the shift. Such shifted inverses turn spectral separation into the operator estimates used in
perturbation bounds for spectral subspaces.

## Main results

* `IsSelfAdjoint.norm_resolvent_le_of_spectrum_gap`: if the spectrum avoids `(c - s, c + s)`, then
  `‖R(c)‖ ≤ s⁻¹`.
* `IsSelfAdjoint.mul_norm_le_norm_smul_sub_of_spectrum_gap`: under the same hypothesis,
  `s ‖x‖ ≤ ‖c • x - A x‖` for every `x` in the domain.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Chapter VIII.
-/

public section

namespace TauCeti

open _root_.LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E} {c s : ℝ}

/-- If the spectrum of a self-adjoint partial linear map avoids `(c - s, c + s)`, then every
spectral value of the resolvent `R(c)` has modulus at most `s⁻¹`. -/
private theorem norm_le_of_mem_spectrum_resolvent (hA : IsSelfAdjoint A) (hs : 0 < s)
    (hgap : ∀ t : ℝ, |t - c| < s → (t : ℂ) ∉ A.spectrum) (hc : (c : ℂ) ∈ A.resolventSet)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A.resolvent (c : ℂ))) : ‖μ‖ ≤ s⁻¹ := by
  by_contra! hlt
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hlt
    exact (inv_pos.mpr hs).not_gt hlt
  refine (TauCeti.LinearPMap.notMem_spectrum_resolvent_iff hc hμ0).mpr ?_ hμ
  have hinv : ‖μ⁻¹‖ < s := by
    rw [norm_inv]
    exact inv_lt_of_inv_lt₀ hs hlt
  by_cases him : μ⁻¹.im = 0
  · -- The point `c - μ⁻¹` is real and lies in the gap.
    have heq : (c : ℂ) - μ⁻¹ = ((c - μ⁻¹.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [heq]
    by_contra hmem
    refine hgap _ ?_ ((A.mem_spectrum_iff _).mpr hmem)
    rw [sub_sub_cancel_left, abs_neg]
    exact (Complex.abs_re_le_norm _).trans_lt hinv
  · -- The point `c - μ⁻¹` is nonreal.
    refine hA.mem_resolventSet_of_im_ne_zero ?_
    simpa using him

/-- **Resolvent bound across a spectral gap.** If the spectrum of a self-adjoint partial linear
map on a complex Hilbert space avoids the real interval `(c - s, c + s)` with `s > 0`, then the
resolvent at `c` has norm at most `s⁻¹`. The point `c` itself is a resolvent point, since it lies
in the gap. -/
theorem _root_.IsSelfAdjoint.norm_resolvent_le_of_spectrum_gap (hA : IsSelfAdjoint A)
    (hs : 0 < s) (hgap : ∀ t : ℝ, |t - c| < s → (t : ℂ) ∉ A.spectrum) :
    ‖A.resolvent (c : ℂ)‖ ≤ s⁻¹ := by
  have hc : (c : ℂ) ∈ A.resolventSet := by
    simpa using hgap c (by simpa using hs)
  have hR : IsSelfAdjoint (A.resolvent (c : ℂ)) :=
    hA.isSelfAdjoint_resolvent hc (by simp)
  rw [← hR.toReal_spectralRadius_complex_eq_norm]
  refine ENNReal.toReal_le_of_le_ofReal (inv_nonneg.mpr hs.le) (iSup₂_le fun μ hμ => ?_)
  have hμ' : ‖μ‖ ≤ s⁻¹ := by
    rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, Set.mem_singleton_iff] at hμ
    rcases hμ with hμ | rfl
    · exact norm_le_of_mem_spectrum_resolvent hA hs hgap hc hμ
    · simpa using hs.le
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  exact ENNReal.ofReal_le_ofReal hμ'

/-- **Lower bound across a spectral gap.** If the spectrum of a self-adjoint partial linear map on
a complex Hilbert space avoids the real interval `(c - s, c + s)` with `s > 0`, then the shift
`c - A` is bounded below by `s` on the domain. -/
theorem _root_.IsSelfAdjoint.mul_norm_le_norm_smul_sub_of_spectrum_gap (hA : IsSelfAdjoint A)
    (hs : 0 < s) (hgap : ∀ t : ℝ, |t - c| < s → (t : ℂ) ∉ A.spectrum) (x : A.domain) :
    s * ‖(x : E)‖ ≤ ‖(c : ℂ) • (x : E) - A x‖ := by
  have hc : (c : ℂ) ∈ A.resolventSet := by
    simpa using hgap c (by simpa using hs)
  rw [← le_inv_mul_iff₀ hs]
  calc
    ‖(x : E)‖ = ‖A.resolvent (c : ℂ) ((c : ℂ) • (x : E) - A x)‖ := by
      rw [resolvent_smul_sub_apply hc]
    _ ≤ ‖A.resolvent (c : ℂ)‖ * ‖(c : ℂ) • (x : E) - A x‖ := (A.resolvent _).le_opNorm _
    _ ≤ s⁻¹ * ‖(c : ℂ) • (x : E) - A x‖ := by
      gcongr
      exact hA.norm_resolvent_le_of_spectrum_gap hs hgap

end TauCeti
