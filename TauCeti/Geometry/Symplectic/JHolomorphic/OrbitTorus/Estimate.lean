/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.NormalOperator
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Fourier.TwistedWirtinger
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# A uniform `L²` bound for the orbit-torus operator twisted along the circle

Let `D u = ∂s u + A u`, `A u = J₀ ∂t u + S(t) u`, be the model normal operator of an orbit torus
(`TauCeti.orbitTorusOperator`), with `J₀` skew-adjoint and `S(t)` symmetric. Its four twisted
versions act on maps `u : ℝ × ℝ → V` with `u (s + ℓ, t) = ε₁ u (s, t)` and
`u (s, t + d) = ε₂ u (s, t)`. For the two characters twisted along the circle factor
(`ε₁ = -1`), `D` has no kernel
(`TauCeti.eq_zero_of_orbitTorusOperator_eq_zero_of_antiperiodic`). This file proves the
quantitative form of that statement: over the fundamental rectangle,

`(π / ℓ) ^ 2 ∫ ‖u‖ ^ 2 ≤ ∫ ‖D u‖ ^ 2`

(`TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_sq_orbitTorusOperator_of_antiperiodic`).
By the energy identity `∫ ‖D u‖ ^ 2 = ∫ (‖∂s u‖ ^ 2 + ‖A u‖ ^ 2)`
(`TauCeti.setIntegral_norm_sq_orbitTorusOperator`) it suffices to bound `∫ ‖∂s u‖ ^ 2` below,
which is the Poincaré inequality for antiperiodic functions of `s`
(`TauCeti.mul_integral_norm_sq_le_integral_norm_sq_of_eq_neg`) integrated over `t`. For `ε₂ = 1`
the constant is sharp: equality holds for `u (s, t) = cos (π s / ℓ) • v` with `S = 0`.

The constant depends only on the length `ℓ` of the circle factor, not on `J₀` or on the path `S`.
So the bound holds uniformly along every path of such operators, for instance along
`τ ↦ ∂s + J₀ ∂t + τ S(t)`, `τ ∈ [0, 1]`, which joins `D` to the complex-linear reference operator
`∂s + J₀ ∂t` when `J₀` is a complex structure. It also applies to the formal adjoint
`-∂s + A = -(∂s + (-J₀) ∂t + (-S(t)))`, since `-J₀` is skew-adjoint and `-S(t)` is symmetric.

For `n ≥ 1` and `d > 0`, on the cover of the torus `(ℝ / ℓℤ) × (ℝ / dℤ)` with deck group
spanned by `(k ℓ, 0)` and `(a ℓ, n d)`, a map twisted by `-1` along `(k ℓ, 0)` and by `ε₂`
along `(a ℓ, n d)` is twisted by a sign along `(0, k n d)`, and the bound holds on the rectangle
`[0, k ℓ] × [0, k n d]` with constant `(π / (k ℓ)) ^ 2`
(`TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_sq_orbitTorusOperator_of_cover`).

These are `L²` estimates for `C²` maps. The Fredholm realization of the twisted operators on
Sobolev completions is separate.

## Main results

* `TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_sq_orbitTorusOperator_of_antiperiodic`:
  the bound `(π / ℓ) ^ 2 ∫ ‖u‖ ^ 2 ≤ ∫ ‖D u‖ ^ 2` for maps antiperiodic in `s`.
* `TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_sq_orbitTorusOperator_of_cover`: the
  same bound on a finite cover, with constant `(π / (k ℓ)) ^ 2`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. Salamon, *Lectures on Floer homology*, in Symplectic Geometry and Topology,
  IAS/Park City Math. Ser. 7 (1999), Section 2, for the operator `∂s + A` with `A` self-adjoint.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Real RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J₀ : V →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {u : ℝ × ℝ → V} {ε₂ ℓ d : ℝ}

/-- For a `C¹` map antiperiodic in `s` with period `ℓ > 0`, the antiperiodic Poincaré
inequality in `s`, integrated over `t ∈ [0, d]`, bounds `∫ ‖∂s u‖ ^ 2` over the rectangle
`[0, ℓ] × [0, d]` below by `(π / ℓ) ^ 2 ∫ ‖u‖ ^ 2`. -/
private theorem mul_setIntegral_norm_sq_le_setIntegral_norm_sq_fderiv (hℓ : 0 < ℓ)
    (hu : ContDiff ℝ 1 u) (hs : ∀ s t, u (s + ℓ, t) = -u (s, t)) :
    (π / ℓ) ^ 2 * ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, ‖u z‖ ^ 2 ≤
      ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 := by
  have hu0 := hu.continuous
  have : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hR : IsCompact (Icc (0 : ℝ) ℓ ×ˢ Icc 0 d) := isCompact_Icc.prod isCompact_Icc
  -- Integrate over `t` the inequality on each horizontal segment `[0, ℓ] × {t}`.
  rw [← integral_const_mul, ← one_mul (∫ z in _, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2)]
  refine setIntegral_rect_le_mul_of_forall_setIntegral_le_symm
    ((Continuous.continuousOn (by fun_prop)).integrableOn_compact hR)
    ((Continuous.continuousOn (by fun_prop)).integrableOn_compact hR) fun t _ => ?_
  rw [integral_const_mul, one_mul]
  -- For each `t`, the Poincaré inequality for the antiperiodic map `s ↦ u (s, t)`.
  have hg : ContDiff ℝ 1 fun s => u (s, t) := hu.comp (contDiff_id.prodMk contDiff_const)
  have hgg' (s : ℝ) :
      HasDerivAt (fun s => u (s, t)) (fderiv ℝ u (s, t) stdComplexLineReal) s :=
    ((hu.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_prodMk_left s t)
  have hg'c : ContinuousOn (fun s => fderiv ℝ u (s, t) stdComplexLineReal) (Icc 0 ℓ) :=
    (Continuous.continuousOn (by fun_prop))
  have h := mul_integral_norm_sq_le_integral_norm_sq_of_eq_neg hℓ
    hg.contDiffOn.absolutelyContinuousOnInterval
    (Filter.Eventually.of_forall fun s _ => hgg' s)
    (hg'c.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioc
      Ioc_subset_Icc_self 2)
    (by simpa using hs 0 t)
  simpa only [sub_zero, intervalIntegral.integral_of_le hℓ.le,
    ← integral_Icc_eq_integral_Ioc] using h

/-- **The `L²` bound for the circle-twisted orbit-torus operator.** Let `V` be
finite-dimensional, `J₀` skew-adjoint and `S` a continuous path of symmetric operators. For a
`C²` map `u` which is antiperiodic in `s` with period `ℓ > 0` and twisted periodic in `t` with
period `d` and a sign `ε₂`, the operator `D = ∂s + J₀ ∂t + S(t)` satisfies
`(π / ℓ) ^ 2 ∫ ‖u‖ ^ 2 ≤ ∫ ‖D u‖ ^ 2` over the fundamental rectangle `[0, ℓ] × [0, d]`. The
constant does not depend on `J₀` or `S`. -/
theorem mul_setIntegral_norm_sq_le_setIntegral_norm_sq_orbitTorusOperator_of_antiperiodic
    (hℓ : 0 < ℓ) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hu : ContDiff ℝ 2 u) (hε₂ : ε₂ ^ 2 = 1)
    (hs : ∀ s t, u (s + ℓ, t) = -u (s, t)) (ht : ∀ s t, u (s, t + d) = ε₂ • u (s, t)) :
    (π / ℓ) ^ 2 * ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, ‖u z‖ ^ 2 ≤
      ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, ‖orbitTorusOperator J₀ S u z‖ ^ 2 := by
  have hR : IsCompact (Icc (0 : ℝ) ℓ ×ˢ Icc 0 d) := isCompact_Icc.prod isCompact_Icc
  have hu0 := hu.continuous
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  rw [setIntegral_norm_sq_orbitTorusOperator (ε₁ := -1) hJ₀ hS hScont hu (by norm_num) hε₂
    (fun s t => by rw [hs, neg_one_smul]) ht]
  refine (mul_setIntegral_norm_sq_le_setIntegral_norm_sq_fderiv hℓ (hu.of_le (by norm_num))
    hs).trans (setIntegral_mono_on ?_ ?_ (measurableSet_Icc.prod measurableSet_Icc)
      fun z _ => le_add_of_nonneg_right (sq_nonneg _))
  · exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact hR
  · exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact hR

/-- **The `L²` bound on a finite cover.** Let `k ≥ 1`, `n ∈ ℕ` and `a ∈ ℤ`. Under the
hypotheses of
`mul_setIntegral_norm_sq_le_setIntegral_norm_sq_orbitTorusOperator_of_antiperiodic`, a `C²` map
twisted by `-1` along `(k ℓ, 0)` and by the sign `ε₂` along `(a ℓ, n d)` satisfies
`(π / (k ℓ)) ^ 2 ∫ ‖u‖ ^ 2 ≤ ∫ ‖D u‖ ^ 2` over the rectangle `[0, k ℓ] × [0, k n d]`. These
translations generate the deck group of a finite cover of the torus `(ℝ / ℓℤ) × (ℝ / dℤ)` when
`n ≥ 1` and `d > 0`; otherwise the rectangle is degenerate and the bound reads `0 ≤ 0`. -/
theorem mul_setIntegral_norm_sq_le_setIntegral_norm_sq_orbitTorusOperator_of_cover
    (hℓ : 0 < ℓ) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hu : ContDiff ℝ 2 u) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k)
    {a : ℤ} (hs : ∀ s t, u (s + k * ℓ, t) = -u (s, t))
    (ht : ∀ s t, u (s + a * ℓ, t + n * d) = ε₂ • u (s, t)) :
    (π / (k * ℓ)) ^ 2 * ∫ z in Icc (0 : ℝ) (k * ℓ) ×ˢ Icc 0 (k * n * d), ‖u z‖ ^ 2 ≤
      ∫ z in Icc (0 : ℝ) (k * ℓ) ×ˢ Icc 0 (k * n * d), ‖orbitTorusOperator J₀ S u z‖ ^ 2 := by
  -- The integer combination `k (a ℓ, n d) - a (k ℓ, 0) = (0, k n d)` twists `u` in `t` by the
  -- sign `ε₂ ^ k (-1) ^ a`.
  set p₁ : ℝ × ℝ := ((k : ℝ) * ℓ, 0)
  set p₂ : ℝ × ℝ := ((a : ℝ) * ℓ, (n : ℝ) * d)
  have h₁ : Function.Antiperiodic u p₁ := fun ⟨s, t⟩ => by
    rw [Prod.mk_add_mk, add_zero]; exact hs s t
  have h₂ (z : ℝ × ℝ) (j : ℕ) : u (z + j • p₂) = ε₂ ^ j • u z := by
    induction j generalizing z with
    | zero => simp
    | succ j ih =>
      rw [succ_nsmul, ← add_assoc, pow_succ', ← smul_smul, ← ih]
      exact ht (z + j • p₂).1 (z + j • p₂).2
  have hε : (ε₂ ^ k * ((a.negOnePow : ℤ) : ℝ)) ^ 2 = 1 := by
    simp [mul_pow, hε₂, pow_right_comm _ _ 2]
  have ht' (s t : ℝ) :
      u (s, t + k * n * d) = (ε₂ ^ k * ((a.negOnePow : ℤ) : ℝ)) • u (s, t) := by
    have hz : (s, t + k * n * d) = ((s, t) - a • p₁) + k • p₂ := by
      ext <;> simp [p₁, p₂] <;> ring
    rw [hz, h₂, h₁.sub_zsmul_eq, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  exact mul_setIntegral_norm_sq_le_setIntegral_norm_sq_orbitTorusOperator_of_antiperiodic
    (mul_pos (Nat.cast_pos.2 hk) hℓ) hJ₀ hS hScont hu hε hs ht'

end TauCeti
