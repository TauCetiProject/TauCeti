/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Action
import TauCeti.Analysis.CStarAlgebra.Module.Semidef

/-!
# The special factorization of vectors in Hilbert C⋆-modules

Every vector `x` of a complete Hilbert C⋆-module `E` over a possibly nonunital C⋆-algebra `A`
factors uniquely as `x = ⟪y, y⟫_A • y`, and then `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 / 3)`. For a right
Hilbert `A`-module, written `CStarModule Aᵐᵒᵖ E`, this is the factorization `x = y ⟨y, y⟩_A`; in
particular every vector is a product `x = y a` of a vector and a coefficient. This lets arguments
about module-compact operators and about the separation of vectors place a coefficient of a
prescribed form on the right of an arbitrary vector.

The vector `y` is the limit of the vectors `f_ε(s) • x` as `ε → 0`, where `s = ⟪x, x⟫_A ^ (1 / 3)`
and `f_ε(u) = u / (u ^ 2 + ε ^ 2)` approximates `u ↦ u⁻¹` on the spectrum of `s`. The functions
`f_ε` vanish at `0`, so only the nonunital continuous functional calculus is used. Completeness of
`E` is needed for the limit to exist; uniqueness holds because any solution `y` is that limit.

## Main declarations

* `CStarModule.existsUnique_inner_self_smul_eq`: every `x` is `⟪y, y⟫_A • y` for a unique `y`.
* `CStarModule.inner_self_eq_nnrpow_of_inner_self_smul_eq`: if `x = ⟪y, y⟫_A • y`, then
  `⟪y, y⟫_A = ⟪x, x⟫_A ^ (1 / 3)`.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Proposition 2.31, whose proof is followed here.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
-/

public section

open Filter Topology NNReal

namespace CStarModule

/-! ### Inner products of functional-calculus multiples of a vector -/

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

section Algebraic

variable [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

section Calculus

/-! Throughout, `⟪x, x⟫_A = w(s)` for a real function `w` vanishing at `0`. Then the inner
products of the vectors `f(s) • x` are computed by the functional calculus at `s`. -/

variable {x : E} {s : A} {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
  (hxs : cfcₙ w s = inner A x x)
  {f g : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) (hg : Continuous g) (hg0 : g 0 = 0)
include hw hw0 hxs hf hf0

/-- The inner product of `f(s) • x` with `x` is `(w f)(s)`. -/
private lemma inner_cfcₙ_smul_left :
    inner A (cfcₙ f s • x) x = cfcₙ (fun u ↦ w u * f u) s := by
  rw [inner_op_smul_left, (IsSelfAdjoint.cfcₙ (f := f)).star_eq, cfcₙ_mul w f s, hxs]

/-- The inner product of `x` with `f(s) • x` is `(f w)(s)`. -/
private lemma inner_smul_cfcₙ_smul :
    inner A x (cfcₙ f s • x) = cfcₙ (fun u ↦ f u * w u) s := by
  rw [inner_op_smul_right, cfcₙ_mul f w s, hxs]

include hg hg0 in
/-- The inner product of `f(s) • x` with `g(s) • x` is `(g w f)(s)`. -/
private lemma inner_cfcₙ_smul_cfcₙ_smul :
    inner A (cfcₙ f s • x) (cfcₙ g s • x) = cfcₙ (fun u ↦ g u * w u * f u) s := by
  rw [inner_op_smul_left, inner_smul_cfcₙ_smul hw hw0 hxs hg hg0,
    (IsSelfAdjoint.cfcₙ (f := f)).star_eq, cfcₙ_mul (fun u ↦ g u * w u) f s]

/-- The defect `f(s) • x - x` has inner square the functional calculus of `w(u) (f u - 1)²`,
in expanded form. -/
private lemma inner_cfcₙ_smul_sub_self :
    inner A (cfcₙ f s • x - x) (cfcₙ f s • x - x) =
      cfcₙ (fun u ↦ f u * w u * f u - w u * f u - (f u * w u - w u)) s := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    inner_cfcₙ_smul_cfcₙ_smul hw hw0 hxs hf hf0 hf hf0, inner_cfcₙ_smul_left hw hw0 hxs hf hf0,
    inner_smul_cfcₙ_smul hw hw0 hxs hf hf0, ← hxs,
    cfcₙ_sub (fun u ↦ f u * w u * f u - w u * f u) (fun u ↦ f u * w u - w u) s,
    cfcₙ_sub (fun u ↦ f u * w u * f u) (fun u ↦ w u * f u) s,
    cfcₙ_sub (fun u ↦ f u * w u) w s]

end Calculus

variable [StarOrderedRing A]

/-- If `x = ⟪y, y⟫_A • y`, then `⟪y, y⟫_A` is the cube root `⟪x, x⟫_A ^ (1 / 3)`, since
`⟪x, x⟫_A = ⟪y, y⟫_A ^ 3`. Completeness is not needed. -/
theorem inner_self_eq_nnrpow_of_inner_self_smul_eq {x y : E} (h : inner A y y • y = x) :
    inner A y y = inner A x x ^ (3⁻¹ : ℝ≥0) := by
  have hx : inner A x x = inner A y y * inner A y y * inner A y y := by
    rw [← h, inner_op_smul_left, inner_op_smul_right, isSelfAdjoint_inner_self.star_eq]
  rw [hx, ← CFC.nnrpow_three _ inner_self_nonneg,
    CFC.nnrpow_nnrpow_inv _ three_ne_zero inner_self_nonneg]

/-! ### Estimates for the approximants `f_ε(s) • x`, with `f_ε(u) = u / (u ^ 2 + ε ^ 2)` -/

/-- The approximant `f_ε(u) = u / (u ^ 2 + ε ^ 2)` of `u ↦ u⁻¹`, which vanishes at `0`. -/
private noncomputable def invApprox (ε u : ℝ) : ℝ := u / (u ^ 2 + ε ^ 2)

/-- For `ε > 0`, the denominator `u ^ 2 + ε ^ 2` never vanishes, so `f_ε` is continuous. -/
private lemma continuous_invApprox {ε : ℝ} (hε : 0 < ε) : Continuous (invApprox ε) :=
  continuous_id.div (by fun_prop) fun u ↦ (by positivity : 0 < u ^ 2 + ε ^ 2).ne'

/-- `f_ε(0) = 0`, so only the nonunital functional calculus is needed. -/
@[simp]
private lemma invApprox_zero (ε : ℝ) : invApprox ε 0 = 0 := by
  simp [invApprox]

/-- The scalar bound `u (c ^ 2 / (u ^ 2 + c ^ 2)) ^ 2 ≤ c / 2` behind the approximation
estimates. -/
private lemma mul_sq_div_sq_add_sq_le (u : ℝ) {c : ℝ} (hc : 0 < c) :
    u * (c ^ 2 / (u ^ 2 + c ^ 2)) ^ 2 ≤ c / 2 := by
  rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
  have h1 : 2 * u * c ≤ u ^ 2 + c ^ 2 := two_mul_le_add_sq u c
  have h2 : c ^ 2 ≤ u ^ 2 + c ^ 2 := by nlinarith [sq_nonneg u]
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) hc.le]

section Approximants

variable {x : E} {s : A} (hs : 0 ≤ s)
include hs

/-- If `⟪y, y⟫_A = s` and `s • y = x`, then `‖f_ε(s) • x - y‖ ^ 2 ≤ ε / 2`. -/
private lemma norm_cfcₙ_smul_sub_sq_le_of_inner_self_eq {y : E} (hyy : inner A y y = s)
    (hsy : s • y = x) {ε : ℝ} (hε : 0 < ε) :
    ‖cfcₙ (invApprox ε) s • x - y‖ ^ 2 ≤ ε / 2 := by
  have hf := continuous_invApprox hε
  have hg : Continuous fun u : ℝ ↦ invApprox ε u * u := hf.mul continuous_id
  -- `f_ε(s) • (s • y) = g(s) • y` with `g(u) = u ^ 2 / (u ^ 2 + ε ^ 2)`.
  have hfs : cfcₙ (invApprox ε) s * s = cfcₙ (fun u : ℝ ↦ invApprox ε u * u) s := by
    rw [cfcₙ_mul (invApprox ε) (fun u ↦ u) s hf.continuousOn (by simp) continuousOn_id rfl,
      cfcₙ_id' ℝ s]
  rw [← hsy, ← (semigroupAction A E).mul_smul, hfs, norm_sq_eq A,
    inner_cfcₙ_smul_sub_self continuous_id' rfl ((cfcₙ_id' ℝ s).trans hyy.symm) hg (by simp)]
  refine norm_cfcₙ_le fun u hu ↦ ?_
  have hu : 0 ≤ u := quasispectrum_nonneg_of_nonneg s hs u hu
  -- The integrand is `u (1 - g(u)) ^ 2 = u (ε ^ 2 / (u ^ 2 + ε ^ 2)) ^ 2 ≤ ε / 2`.
  have heq : invApprox ε u * u * u * (invApprox ε u * u) -
      u * (invApprox ε u * u) - (invApprox ε u * u * u - u) =
      u * (ε ^ 2 / (u ^ 2 + ε ^ 2)) ^ 2 := by
    unfold invApprox
    field_simp
    ring
  rw [Real.norm_eq_abs, heq, abs_of_nonneg (by positivity)]
  exact mul_sq_div_sq_add_sq_le u hε

variable (hss : s * s * s = inner A x x)
include hss

/-- `⟪x, x⟫_A` is the functional calculus of `u ↦ u ^ 3` at its cube root `s`. -/
private lemma cfcₙ_cube_eq_inner_self : cfcₙ (fun u : ℝ ↦ u * u * u) s = inner A x x := by
  rw [cfcₙ_mul (fun u : ℝ ↦ u * u) (fun u ↦ u) s, cfcₙ_mul (fun u : ℝ ↦ u) (fun u ↦ u) s,
    cfcₙ_id' ℝ s, hss]

/-- The Cauchy estimate `‖f_ε(s) • x - f_δ(s) • x‖ ^ 2 ≤ ε + δ`. -/
private lemma norm_cfcₙ_smul_sub_cfcₙ_smul_sq_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ‖cfcₙ (invApprox ε) s • x - cfcₙ (invApprox δ) s • x‖ ^ 2 ≤ ε + δ := by
  have hd : Continuous fun u : ℝ ↦ invApprox ε u - invApprox δ u :=
    (continuous_invApprox hε).sub (continuous_invApprox hδ)
  rw [← CStarModule.sub_smul, ← cfcₙ_sub (invApprox ε) (invApprox δ) s
    (continuous_invApprox hε).continuousOn (by simp) (continuous_invApprox hδ).continuousOn
    (by simp), norm_sq_eq A, inner_cfcₙ_smul_cfcₙ_smul (by fun_prop) (by simp)
      (cfcₙ_cube_eq_inner_self hs hss) hd (by simp) hd (by simp)]
  refine norm_cfcₙ_le fun u hu ↦ ?_
  have hu : 0 ≤ u := quasispectrum_nonneg_of_nonneg s hs u hu
  -- With `P = ε ^ 2 / (u ^ 2 + ε ^ 2)` and `Q = δ ^ 2 / (u ^ 2 + δ ^ 2)`, the integrand is
  -- `u (Q - P) ^ 2 ≤ u P ^ 2 + u Q ^ 2`, and `u P ^ 2 ≤ ε / 2`, `u Q ^ 2 ≤ δ / 2`.
  have heq : (invApprox ε u - invApprox δ u) * (u * u * u) * (invApprox ε u - invApprox δ u) =
      u * (δ ^ 2 / (u ^ 2 + δ ^ 2) - ε ^ 2 / (u ^ 2 + ε ^ 2)) ^ 2 := by
    unfold invApprox
    field_simp
    ring
  rw [Real.norm_eq_abs, heq, abs_of_nonneg (by positivity)]
  have hPQ : 0 ≤ u * (2 * (δ ^ 2 / (u ^ 2 + δ ^ 2)) * (ε ^ 2 / (u ^ 2 + ε ^ 2))) := by
    positivity
  nlinarith [mul_sq_div_sq_add_sq_le u hε, mul_sq_div_sq_add_sq_le u hδ]

/-- `‖⟪f_ε(s) • x, f_ε(s) • x⟫_A - s‖ ≤ ε`. -/
private lemma norm_inner_cfcₙ_smul_sub_le {ε : ℝ} (hε : 0 < ε) :
    ‖inner A (cfcₙ (invApprox ε) s • x) (cfcₙ (invApprox ε) s • x) - s‖ ≤ ε := by
  have hf := continuous_invApprox hε
  rw [inner_cfcₙ_smul_cfcₙ_smul (by fun_prop) (by simp) (cfcₙ_cube_eq_inner_self hs hss) hf
    (by simp) hf (by simp)]
  nth_rw 2 [← cfcₙ_id' ℝ s]
  rw [← cfcₙ_sub (fun u ↦ invApprox ε u * (u * u * u) * invApprox ε u) (fun u : ℝ ↦ u) s
    ((hf.mul (by fun_prop)).mul hf).continuousOn (by simp)]
  refine norm_cfcₙ_le fun u hu ↦ ?_
  have hu : 0 ≤ u := quasispectrum_nonneg_of_nonneg s hs u hu
  -- The integrand is `-u ε ^ 2 (2 u ^ 2 + ε ^ 2) / (u ^ 2 + ε ^ 2) ^ 2`.
  have heq : invApprox ε u * (u * u * u) * invApprox ε u - u =
      -(u * ε ^ 2 * (2 * u ^ 2 + ε ^ 2) / (u ^ 2 + ε ^ 2) ^ 2) := by
    unfold invApprox
    field_simp
    ring
  rw [Real.norm_eq_abs, heq, abs_neg, abs_of_nonneg (by positivity),
    div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (two_mul_le_add_sq u ε)
      (by positivity : 0 ≤ ε * (u ^ 2 + ε ^ 2)), mul_nonneg hu (sq_nonneg ε)]

/-- `‖s • f_ε(s) • x - x‖ ^ 2 ≤ ε ^ 3`. -/
private lemma norm_smul_cfcₙ_smul_sub_sq_le {ε : ℝ} (hε : 0 < ε) :
    ‖s • cfcₙ (invApprox ε) s • x - x‖ ^ 2 ≤ ε ^ 3 := by
  have hf := continuous_invApprox hε
  have hg : Continuous fun u : ℝ ↦ u * invApprox ε u := continuous_id.mul hf
  -- `s • f_ε(s) • x = g(s) • x` with `g(u) = u ^ 2 / (u ^ 2 + ε ^ 2)`.
  have hsf : s * cfcₙ (invApprox ε) s = cfcₙ (fun u : ℝ ↦ u * invApprox ε u) s := by
    rw [cfcₙ_mul (fun u : ℝ ↦ u) (invApprox ε) s continuousOn_id rfl hf.continuousOn (by simp),
      cfcₙ_id' ℝ s]
  rw [← (semigroupAction A E).mul_smul, hsf, norm_sq_eq A,
    inner_cfcₙ_smul_sub_self (by fun_prop) (by simp) (cfcₙ_cube_eq_inner_self hs hss) hg
      (by simp)]
  refine norm_cfcₙ_le fun u hu ↦ ?_
  have hu : 0 ≤ u := quasispectrum_nonneg_of_nonneg s hs u hu
  -- The integrand is `u ^ 3 (1 - g(u)) ^ 2 = u ^ 3 ε ^ 4 / (u ^ 2 + ε ^ 2) ^ 2 ≤ ε ^ 3`.
  have heq : u * invApprox ε u * (u * u * u) * (u * invApprox ε u) -
      u * u * u * (u * invApprox ε u) - (u * invApprox ε u * (u * u * u) - u * u * u) =
      u ^ 3 * ε ^ 4 / (u ^ 2 + ε ^ 2) ^ 2 := by
    unfold invApprox
    field_simp
    ring
  rw [Real.norm_eq_abs, heq, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have h1 : 2 * u ^ 3 * ε ≤ u ^ 4 + u ^ 2 * ε ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg (u - ε))]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ ε ^ 3), pow_pos hε 7,
    mul_nonneg (pow_nonneg hu 3) (pow_pos hε 4).le]

end Approximants

end Algebraic

/-! ### The special factorization -/

variable [StarOrderedRing A] [NormedAddCommGroup E] [Module ℂ E] [SMul A E] [CStarModule A E]
  [CompleteSpace E]

/-- For a cube root `s ≥ 0` of `⟪x, x⟫_A`, the vectors `f_ε(s) • x` converge, along
`ε = 1 / (n + 1)`, to a vector `y` with `⟪y, y⟫_A = s` and `s • y = x`. -/
private lemma exists_inner_self_eq_and_smul_eq {x : E} {s : A} (hs : 0 ≤ s)
    (hss : s * s * s = inner A x x) : ∃ y : E, inner A y y = s ∧ s • y = x := by
  have hε0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  set z : ℕ → E := fun n ↦ cfcₙ (invApprox (1 / ((n : ℝ) + 1))) s • x
  -- `‖z n - z m‖ ^ 2 ≤ 1 / (n + 1) + 1 / (m + 1)`, so `z` is a Cauchy sequence.
  obtain ⟨y, hy⟩ : ∃ y, Tendsto z atTop (𝓝 y) := by
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0
      (fun N ↦ √(2 * (1 / ((N : ℝ) + 1)))) (fun n m N hn hm ↦ ?_) ?_)
    · rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
      refine Real.sqrt_le_sqrt ((norm_cfcₙ_smul_sub_cfcₙ_smul_sq_le hs hss
        Nat.one_div_pos_of_nat Nat.one_div_pos_of_nat).trans ?_)
      have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
      have hm' : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
      linarith
    · simpa using (hε0.const_mul 2).sqrt
  refine ⟨y, ?_, ?_⟩
  · -- `⟪z n, z n⟫_A → s`, and `⟪z n, z n⟫_A → ⟪y, y⟫_A` by continuity of the inner product,
    -- stated in Mathlib for the `NormedSpace` structure that the `CStarModule` axioms provide.
    have hlim : Tendsto (fun n ↦ inner A (z n) (z n)) atTop (𝓝 s) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun _ ↦ norm_inner_cfcₙ_smul_sub_le hs hss Nat.one_div_pos_of_nat) hε0
    let _ : NormedSpace ℂ E := .ofCore (normedSpaceCore A)
    exact tendsto_nhds_unique
      ((continuous_inner (A := A)).tendsto (y, y) |>.comp (hy.prodMk_nhds hy)) hlim
  · -- `s • z n → s • y` since the action of `s` is bounded, and `s • z n → x`.
    let _ := distribSMul A E
    have hsy : Tendsto (fun n ↦ s • z n) atTop (𝓝 (s • y)) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun n ↦ show ‖s • z n - s • y‖ ≤ ‖s‖ * ‖z n - y‖ by
          rw [← smul_sub]; exact TauCeti.PosSemidefCStarModule.norm_smul_le s _)
        (by simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hy).const_mul ‖s‖)
    have hb : Tendsto (fun n : ℕ ↦ √((1 / ((n : ℝ) + 1)) ^ 3)) atTop (𝓝 0) := by
      simpa using (hε0.pow 3).sqrt
    have hsx : Tendsto (fun n ↦ s • z n) atTop (𝓝 x) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun _ ↦ (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
          (norm_smul_cfcₙ_smul_sub_sq_le hs hss Nat.one_div_pos_of_nat)) hb
    exact tendsto_nhds_unique hsy hsx

/-- **Special factorization in a Hilbert C⋆-module.** Every vector `x` of a complete Hilbert
C⋆-module over a possibly nonunital C⋆-algebra factors uniquely as `x = ⟪y, y⟫_A • y`. The
coefficient `⟪y, y⟫_A` is then `⟪x, x⟫_A ^ (1 / 3)`, by
`CStarModule.inner_self_eq_nnrpow_of_inner_self_smul_eq`. For a right Hilbert `A`-module
`CStarModule Aᵐᵒᵖ E` this is the factorization `x = y ⟨y, y⟩_A`, because `inner Aᵐᵒᵖ y y • y` is
the right action of `⟨y, y⟩_A = unop (inner Aᵐᵒᵖ y y)` on `y`. -/
theorem existsUnique_inner_self_smul_eq (x : E) : ∃! y : E, inner A y y • y = x := by
  set s : A := inner A x x ^ (3⁻¹ : ℝ≥0) with hs_def
  have hs : 0 ≤ s := CFC.nnrpow_nonneg
  have hss : s * s * s = inner A x x := by
    rw [← CFC.nnrpow_three s hs, hs_def, CFC.nnrpow_inv_nnrpow _ three_ne_zero inner_self_nonneg]
  obtain ⟨y, hyy, hsy⟩ := exists_inner_self_eq_and_smul_eq hs hss
  refine ⟨y, by simp only [hyy, hsy], fun y' (hy' : inner A y' y' • y' = x) ↦ ?_⟩
  -- Every solution `y'` has `⟪y', y'⟫_A = s`, and is then the limit of the vectors
  -- `f_ε(s) • x`; so `y' = y`.
  have hy's : inner A y' y' = s := inner_self_eq_nnrpow_of_inner_self_smul_eq hy'
  rw [hy's] at hy'
  have hε0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : Tendsto (fun n : ℕ ↦ √(1 / ((n : ℝ) + 1) / 2)) atTop (𝓝 0) := by
    simpa using (hε0.div_const 2).sqrt
  have hlim : ∀ {v : E}, inner A v v = s → s • v = x →
      Tendsto (fun n : ℕ ↦ cfcₙ (invApprox (1 / ((n : ℝ) + 1))) s • x) atTop (𝓝 v) :=
    fun hvv hsv ↦
    tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun _ ↦ (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
        (norm_cfcₙ_smul_sub_sq_le_of_inner_self_eq hs hvv hsv Nat.one_div_pos_of_nat)) hb
  exact tendsto_nhds_unique (hlim hy's hy') (hlim hyy hsy)

end CStarModule
