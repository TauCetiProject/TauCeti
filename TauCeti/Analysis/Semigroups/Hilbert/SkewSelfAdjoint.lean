/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.RestrictScalars
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.Semigroups.Dissipative.Basic
import TauCeti.Analysis.Semigroups.Dissipative.Hilbert

/-!
# Skew multiples of self-adjoint operators

Multiplication by either sign of `i` turns a self-adjoint partial linear map `A` on a complex
Hilbert space into an m-dissipative real partial linear map: the quadratic form of `± i • A` is
purely imaginary, and the range condition `1 - (± i • A)` surjective is the surjectivity of the
deficiency shifts `∓ i - A` of `A`.  This is the input Lumer--Phillips needs to generate the
unitary group `e^{itA}` from both ends.  As in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint`, the scalar is a general `c` with
`c.re = 0` and `‖c‖ = 1`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem re_inner_smul_apply_apply_eq_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {c : ℂ} (hc : c.re = 0) (x : A.domain) : (inner ℂ (c • A x) (x : E)).re = 0 := by
  calc
    (inner ℂ (c • A x) (x : E)).re = (inner ℂ (A (c • x)) (x : E)).re := by rw [map_smul]
    _ = (inner ℂ (c • (x : E)) (A x)).re :=
      congrArg Complex.re (hA.isFormalAdjoint (c • x) x)
    _ = 0 := hA.re_inner_smul_apply_eq_zero hc x

private theorem isDissipative_smul_restrictScalarsReal {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {c : ℂ} (hc : c.re = 0) :
    TauCeti.Semigroups.IsDissipative ((c • A).restrictScalarsReal) := by
  let _ : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  apply (TauCeti.Semigroups.isDissipative_iff_real_inner_nonpos _).mpr
  intro x
  let xA : A.domain := ⟨(x : E), x.property⟩
  rw [real_inner_eq_re_inner]
  change (inner ℂ (c • A xA) (xA : E)).re ≤ 0
  rw [re_inner_smul_apply_apply_eq_zero hA hc xA]

private theorem surjective_one_sub_smul_restrictScalarsReal {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ = 1) :
    Function.Surjective fun x : (c • A).restrictScalarsReal.domain =>
      (1 : ℝ) • (x : E) - (c • A).restrictScalarsReal x := by
  intro y
  have hc' : ((starRingEnd ℂ) c).re = 0 := by rw [Complex.conj_re]; exact hc
  have hc1' : ‖(starRingEnd ℂ) c‖ = 1 := by rw [Complex.norm_conj]; exact hc1
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]
    norm_num
  obtain ⟨x, hx⟩ := hA.surjective_smul_sub hc' hc1' ((starRingEnd ℂ) c • y)
  refine ⟨x, ?_⟩
  change (1 : ℝ) • (x : E) - c • A x = y
  have hcx := congrArg (c • ·) hx
  simpa [smul_sub, smul_smul, hcc] using hcx

/-- **`± i • A` is m-dissipative for self-adjoint `A`.** For a unimodular purely imaginary
scalar `c`, the real restriction of `c • A` is dissipative, because its quadratic form is purely
imaginary, and `1 - c • A` is surjective, because the deficiency shift `conj c - A` is. -/
theorem _root_.IsSelfAdjoint.isMDissipative_smul_restrictScalarsReal {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ = 1) :
    TauCeti.Semigroups.IsMDissipative ((c • A).restrictScalarsReal) :=
  (isDissipative_smul_restrictScalarsReal hA hc).isMDissipative one_pos
    (surjective_one_sub_smul_restrictScalarsReal hA hc hc1)

end LinearPMap

end
