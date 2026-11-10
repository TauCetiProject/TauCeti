/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Pseudoconvex.Morse
import TauCeti.Topology.Maps.Proper.Metric

/-!
# Examples: relative Morse perturbation of a degenerate strictly plurisubharmonic exhaustion

Strict plurisubharmonicity of a smooth exhaustion `ψ` on a complex manifold requires
`Hess ψ(v, v) + Hess ψ(I • v, I • v) > 0` for every nonzero tangent vector `v`, not positive
definiteness or even nondegeneracy of the real Hessian `Hess ψ` itself. A strictly plurisubharmonic
exhaustion can therefore have degenerate critical points and fail to be a Morse function, while
already being regular (hence Morse) outside a compact set.

On `ℂ` with coordinates `z = x + i y`, the polynomial exhaustion `ψ(z) = 2 x² + y⁴` illustrates
this phenomenon concretely:

* `ψ` is smooth, nonnegative, and proper (`‖z‖² ≤ ψ(z) + 1`).
* Its real Hessian quadratic form at `z` is `v ↦ 4 v.re² + 12 z.im² v.im²`, so
  `Hess ψ(z)(v) + Hess ψ(z)(I • v) = (4 + 12 z.im²) ‖v‖² > 0` for `v ≠ 0`: `ψ` is strictly
  plurisubharmonic at every point of `ℂ`.
* At the origin `z = 0`, `fderiv ℝ ψ 0 = 0` and `fderiv ℝ (fderiv ℝ ψ) 0 I = 0`, so `0` is a
  degenerate critical point and `ψ` is **not** a Morse function (`¬ IsMorse 𝓘(ℝ, ℂ) ψ`).
* On `{0}ᶜ`, `fderiv ℝ ψ z ≠ 0`, so `ψ` is already Morse on the open neighbourhood `{0}ᶜ` of the
  closed exterior `{z : ℂ | 1 ≤ ‖z‖}`.

Applying
`TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt_sub_compl`
produces a smooth proper bounded-below strictly plurisubharmonic Morse exhaustion `g` on `ℂ` with
`|g - ψ| < 1` everywhere, equal to `ψ` on a neighbourhood of `{z : ℂ | 1 ≤ ‖z‖}`, genuinely
different from `ψ` inside the unit disc (`(g : ℂ → ℝ) ≠ ψ`), and having critical points only of
real Morse index `0` or `1`.

## Used results

* `TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt_sub_compl`:
  relative Morse perturbation of a smooth proper bounded-below strictly plurisubharmonic
  exhaustion.
* `TauCeti.criticalCount_eq_zero_of_isManifoldStrictlyPlurisubharmonicAt`: critical counts vanish
  above the complex dimension.
* `TauCeti.isStrictlyPlurisubharmonicAt_iff_hessianQuadraticForm`: strict plurisubharmonicity tested
  via `Hess ψ(v) + Hess ψ(I • v) > 0`.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

open Complex Set Topology
open scoped ContDiff Manifold

namespace TauCeti.PseudoconvexExhaustionExample

/-- The degenerate strictly plurisubharmonic polynomial exhaustion `ψ(z) = 2 (Re z)² + (Im z)⁴` on
`ℂ`. -/
def quarticExhaustion (z : ℂ) : ℝ :=
  2 * z.re ^ 2 + z.im ^ 4

private theorem quarticExhaustion_eq_clm :
    quarticExhaustion = fun z : ℂ ↦ 2 * (reCLM z) ^ 2 + (imCLM z) ^ 4 :=
  funext fun z ↦ by simp only [quarticExhaustion, reCLM_apply, imCLM_apply]

/-- `quarticExhaustion` is smooth on `ℂ`. -/
theorem contDiff_quarticExhaustion : ContDiff ℝ ∞ quarticExhaustion := by
  rw [quarticExhaustion_eq_clm]
  fun_prop

private theorem norm_sq_le_quarticExhaustion_add_one (z : ℂ) :
    ‖z‖ ^ 2 ≤ quarticExhaustion z + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold quarticExhaustion
  nlinarith [sq_nonneg (z.im ^ 2 - 1 / 2), sq_nonneg z.re]

/-- `quarticExhaustion` is a proper map into `ℝ`. -/
theorem isProperMap_quarticExhaustion : IsProperMap quarticExhaustion := by
  refine isProperMap_iff_isCompact_preimage.mpr
    ⟨contDiff_quarticExhaustion.continuous, fun K hK ↦ ?_⟩
  obtain ⟨b, hb⟩ := hK.bddAbove
  refine ((isProperMap_norm_sq_sub (0 : ℂ)).isCompact_preimage
    (isCompact_Icc (a := 0) (b := max b 0 + 1))).of_isClosed_subset
    (hK.isClosed.preimage contDiff_quarticExhaustion.continuous) fun z hz ↦ ?_
  simp only [mem_preimage, sub_zero, mem_Icc]
  exact ⟨by positivity, (norm_sq_le_quarticExhaustion_add_one z).trans
    (add_le_add_left ((hb hz).trans (le_max_left b 0)) 1)⟩

private theorem hasFDerivAt_quarticExhaustion (z : ℂ) :
    HasFDerivAt quarticExhaustion ((4 * z.re) • reCLM + (4 * z.im ^ 3) • imCLM) z := by
  rw [quarticExhaustion_eq_clm]
  have hre : HasFDerivAt (fun w : ℂ ↦ 2 * (reCLM w) ^ 2) ((4 * z.re) • reCLM) z := by
    convert (reCLM.hasFDerivAt.pow 2).const_mul 2 using 1
    ext v
    simp only [smul_apply, reCLM_apply, smul_eq_mul]
    ring
  have him : HasFDerivAt (fun w : ℂ ↦ (imCLM w) ^ 4) ((4 * z.im ^ 3) • imCLM) z := by
    convert imCLM.hasFDerivAt.pow 4 using 1
    ext v
    simp only [smul_apply, imCLM_apply, smul_eq_mul]
    ring
  exact hre.add him

private theorem fderiv_quarticExhaustion (z : ℂ) :
    fderiv ℝ quarticExhaustion z = (4 * z.re) • reCLM + (4 * z.im ^ 3) • imCLM :=
  (hasFDerivAt_quarticExhaustion z).fderiv

private theorem hasFDerivAt_fderiv_quarticExhaustion (z : ℂ) :
    HasFDerivAt (fderiv ℝ quarticExhaustion)
      ((4 • reCLM).smulRight reCLM + ((12 * z.im ^ 2) • imCLM).smulRight imCLM) z := by
  simp only [funext fderiv_quarticExhaustion, ← reCLM_apply, ← imCLM_apply]
  have hre : HasFDerivAt (fun w : ℂ ↦ (4 * reCLM w) • reCLM)
      ((4 • reCLM).smulRight reCLM) z := by
    convert (reCLM.hasFDerivAt.const_mul 4).smul_const reCLM using 1
    ext v w
    simp [smul_eq_mul, mul_assoc]
  have him : HasFDerivAt (fun w : ℂ ↦ (4 * (imCLM w) ^ 3) • imCLM)
      (((12 * z.im ^ 2) • imCLM).smulRight imCLM) z := by
    convert ((imCLM.hasFDerivAt.pow 3).const_mul 4).smul_const imCLM using 1
    ext v w
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, imCLM_apply, smul_eq_mul]
    ring
  exact hre.add him

private theorem hessianQuadraticForm_quarticExhaustion (z v : ℂ) :
    hessianQuadraticForm quarticExhaustion z v = 4 * v.re ^ 2 + 12 * z.im ^ 2 * v.im ^ 2 := by
  rw [hessianQuadraticForm_apply, (hasFDerivAt_fderiv_quarticExhaustion z).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, reCLM_apply, imCLM_apply,
    smul_eq_mul]
  ring

/-- `quarticExhaustion` is strictly plurisubharmonic at every point of `ℂ`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_quarticExhaustion (z : ℂ) :
    IsManifoldStrictlyPlurisubharmonicAt ℂ quarticExhaustion z := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff]
  simp only [manifoldLeviForm_eq_leviForm, ← isStrictlyPlurisubharmonicAt_iff,
    isStrictlyPlurisubharmonicAt_iff_hessianQuadraticForm]
  intro v hv
  rw [hessianQuadraticForm_quarticExhaustion, hessianQuadraticForm_quarticExhaustion]
  simp only [smul_eq_mul, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, even_two.neg_pow,
    mul_im]
  have hv0 : 0 < Complex.normSq v := Complex.normSq_pos.mpr hv
  rw [Complex.normSq_apply] at hv0
  nlinarith [sq_nonneg z.im, sq_nonneg v.re, sq_nonneg v.im]

/-- `quarticExhaustion` has a degenerate critical point at `0` in the imaginary direction, so it is
not a Morse function. -/
theorem not_isMorse_quarticExhaustion : ¬ IsMorse 𝓘(ℝ, ℂ) quarticExhaustion := by
  rw [isMorse_modelSpace_iff, hasNondegenerateCriticalPointsOn_iff]
  rintro ⟨-, hmorse⟩
  have hcrit : fderiv ℝ quarticExhaustion 0 = 0 := by
    rw [fderiv_quarticExhaustion]
    simp
  have hnd := hmorse (mem_univ (0 : ℂ)) hcrit
  have hker : fderiv ℝ (fderiv ℝ quarticExhaustion) 0 I = 0 := by
    rw [(hasFDerivAt_fderiv_quarticExhaustion 0).fderiv]
    ext w
    simp
  exact I_ne_zero (hnd.isInvertible.injective (hker.trans (map_zero _).symm))

/-- Away from `0`, `quarticExhaustion` has no critical points and is therefore Morse. -/
theorem isMorseOn_quarticExhaustion_compl_zero :
    IsMorseOn 𝓘(ℝ, ℂ) quarticExhaustion ({0}ᶜ) := by
  rw [isMorseOn_modelSpace_iff, hasNondegenerateCriticalPointsOn_iff]
  refine ⟨contDiff_quarticExhaustion.contDiffOn, fun z hz hcrit ↦ absurd ?_ hz⟩
  apply Complex.ext
  · have h1 := congr($hcrit 1)
    simp only [fderiv_quarticExhaustion, add_apply, smul_apply, reCLM_apply, one_re, smul_eq_mul,
      mul_one, imCLM_apply, one_im, mul_zero, add_zero, zero_apply, zero_re] at h1 ⊢
    linarith
  · have hI := congr($hcrit I)
    simp only [fderiv_quarticExhaustion, add_apply, smul_apply, reCLM_apply, I_re, smul_eq_mul,
      mul_zero, imCLM_apply, I_im, mul_one, zero_add, zero_apply, zero_im] at hI ⊢
    have hpow : z.im ^ 3 = 0 := by linarith
    exact eq_zero_of_pow_eq_zero hpow

/-- The degenerate strictly plurisubharmonic exhaustion `ψ(z) = 2 (Re z)² + (Im z)⁴` on `ℂ` is not
Morse, yet relative perturbation produces a smooth proper bounded-below strictly plurisubharmonic
Morse exhaustion `g ≠ ψ` within `C⁰` distance `1` of `ψ` that agrees with `ψ` on a neighbourhood
of `{z : ℂ | 1 ≤ ‖z‖}` and has no critical points of index above `1`. -/
theorem exists_isMorse_ne_quarticExhaustion :
    ¬ IsMorse 𝓘(ℝ, ℂ) quarticExhaustion ∧
    ∃ g : C^∞⟮𝓘(ℝ, ℂ), ℂ; 𝓘(ℝ), ℝ⟯,
      (g : ℂ → ℝ) ≠ quarticExhaustion ∧
      IsMorse 𝓘(ℝ, ℂ) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ z, IsManifoldStrictlyPlurisubharmonicAt ℂ g z) ∧
      (∀ j, 1 < j → criticalCount 𝓘(ℝ, ℂ) g j = 0) ∧
      (∀ z, |g z - quarticExhaustion z| < 1) ∧
      tsupport (fun z ↦ g z - quarticExhaustion z) ⊆ {z : ℂ | 1 ≤ ‖z‖}ᶜ := by
  refine ⟨not_isMorse_quarticExhaustion, ?_⟩
  have hC : IsClosed {z : ℂ | 1 ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  have hCV : {z : ℂ | 1 ≤ ‖z‖} ⊆ ({0}ᶜ : Set ℂ) := by
    rintro z (hz : 1 ≤ ‖z‖) rfl
    norm_num at hz
  obtain ⟨g, hgm, hgp, hg_bdd, hg_pos, -, hgf, hgs⟩ :=
    exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt_sub_compl
      (contMDiff_iff_contDiff.mpr contDiff_quarticExhaustion)
      isProperMap_quarticExhaustion
      ⟨0, by rintro _ ⟨z, rfl⟩; unfold quarticExhaustion; positivity⟩
      isManifoldStrictlyPlurisubharmonicAt_quarticExhaustion
      hC hCV isMorseOn_quarticExhaustion_compl_zero
  refine ⟨g, fun hge ↦ not_isMorse_quarticExhaustion (hge ▸ hgm), hgm, hgp, hg_bdd, hg_pos,
    fun j hj ↦ criticalCount_eq_zero_of_isManifoldStrictlyPlurisubharmonicAt
      (g.contMDiff.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) (fun z _ ↦ hg_pos z)
      (by simpa [Module.finrank_self] using hj),
    hgf, hgs⟩

end TauCeti.PseudoconvexExhaustionExample
