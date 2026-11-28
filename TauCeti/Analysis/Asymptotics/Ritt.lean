/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Analysis.Asymptotics.Expansion.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Complex.Sector.Bounds
import TauCeti.Analysis.Complex.Sector.Deriv

/-!
# Ritt's theorem: differentiating order relations in sectors

Let `f` be holomorphic in the sector `S = {z | R < |z|, |ph z| < θ}` with `f(z) = O(|z|^ν)` as
`z → ∞` in `S`, where `ν` is real. Ritt's theorem (DLMF §2.1(ii)) states that
`f'(z) = O(|z|^(ν - 1))` as `z → ∞` in every closed subsector `|ph z| ≤ θ'` with `θ' < θ`, and
the same with `o` in place of `O`. Consequently a Poincaré expansion `f(z) ∼ ∑ aₙ z⁻ⁿ` in `S`
may be differentiated termwise in every such closed subsector.

The proof is Cauchy's estimate for the derivative on discs whose radii are a fixed multiple of
the distance of their centers to the vertex. By compactness of the arc of unit directions of the
subsector, such discs around the nonzero points of the closed subsector stay in the open sector
`|ph w| < θ`; once the center also satisfies `‖z‖ > 2 max R 0`, the disc clears the radial cutoff
and lies in `S`.

## Main results

* `Asymptotics.isBigO_deriv_of_isBigO_sector`, `Asymptotics.isLittleO_deriv_of_isLittleO_sector`:
  Ritt's theorem with `O` and with `o`.
* `Asymptotics.HasAsymptoticExpansion.deriv_sector`: termwise differentiation of a Poincaré
  expansion at infinity in a sector.

The sector geometry is in `TauCeti.Analysis.Complex.Sector.Bounds`, the pointwise and eventual
Cauchy estimates in a sector (`TauCeti.exists_pos_eventually_norm_deriv_le_sector`) are in
`TauCeti.Analysis.Complex.Sector.Deriv`, and the comparison of real powers of comparable numbers
is `TauCeti.rpow_le_two_rpow_abs_mul`.

The statements and proofs are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`,
`DLMF/AsymptoticApproximations/Basics/Calculus.lean` and
`DLMFMathlib/Analysis/Complex/Sector.lean`, where the sectors may have any bisector.
-/

public section

noncomputable section

open Filter Metric Set Bornology Finset
open scoped Topology Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Asymptotics

open Complex TauCeti

/-- **Ritt's theorem** (DLMF §2.1(ii)): if `f` is holomorphic on `{R < ‖z‖, |arg z| < θ}` and
`f(z) = O(‖z‖ ^ ν)` as `z → ∞` in `|arg z| < θ`, then `f'(z) = O(‖z‖ ^ (ν - 1))` as `z → ∞` in
every closed subsector `|arg z| ≤ θ'` with `θ' < θ`. -/
theorem isBigO_deriv_of_isBigO_sector {f : ℂ → E} {R θ θ' ν : ℝ} (hθ' : θ' < θ)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖ ∧ |arg z| < θ})
    (hO : f =O[cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}] fun z => ‖z‖ ^ ν) :
    deriv f =O[cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'}] fun z => ‖z‖ ^ (ν - 1) := by
  obtain ⟨K, -, hb⟩ := exists_pos_eventually_norm_deriv_le_sector (E := E) hθ' ν
  obtain ⟨C, hbound⟩ := hO.bound
  refine IsBigO.of_bound (K * C) ?_
  have h := hb f R C hf (by
    filter_upwards [hbound] with z hz
    rwa [Real.norm_of_nonneg (by positivity)] at hz)
  filter_upwards [h] with z hz
  rwa [Real.norm_of_nonneg (by positivity)]

/-- **Ritt's theorem** with `o` (DLMF §2.1(ii)): if `f` is holomorphic on
`{R < ‖z‖, |arg z| < θ}` and `f(z) = o(‖z‖ ^ ν)` as `z → ∞` in `|arg z| < θ`, then
`f'(z) = o(‖z‖ ^ (ν - 1))` as `z → ∞` in every closed subsector `|arg z| ≤ θ'` with
`θ' < θ`. -/
theorem isLittleO_deriv_of_isLittleO_sector {f : ℂ → E} {R θ θ' ν : ℝ} (hθ' : θ' < θ)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖ ∧ |arg z| < θ})
    (ho : f =o[cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}] fun z => ‖z‖ ^ ν) :
    deriv f =o[cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'}] fun z => ‖z‖ ^ (ν - 1) := by
  obtain ⟨K, hK, hb⟩ := exists_pos_eventually_norm_deriv_le_sector (E := E) hθ' ν
  refine IsLittleO.of_bound fun ε hε => ?_
  have h := hb f R (ε / K) hf (by
    filter_upwards [ho.bound (div_pos hε hK)] with z hz
    rwa [Real.norm_of_nonneg (by positivity)] at hz)
  filter_upwards [h] with z hz
  rw [Real.norm_of_nonneg (by positivity)]
  rwa [mul_div_cancel₀ _ hK.ne'] at hz

/-- **Termwise differentiation** (DLMF §2.1(ii)): if `f` is holomorphic on
`{R < ‖z‖, |arg z| < θ}` with the Poincaré expansion `f(z) ∼ ∑ aₙ z⁻ⁿ` as `z → ∞` in
`|arg z| < θ`, then `f'(z) ∼ ∑ (-n aₙ) z⁻ⁿ⁻¹` as `z → ∞` in every closed subsector
`|arg z| ≤ θ'` with `θ' < θ`. -/
theorem HasAsymptoticExpansion.deriv_sector {f : ℂ → E} {a : ℕ → E} {R θ θ' : ℝ}
    (he : HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}) (fun n z => (z ^ n)⁻¹)
      a f)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖ ∧ |arg z| < θ}) (hθ' : θ' < θ) :
    HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'})
      (fun n z => (z ^ (n + 1))⁻¹) (fun n => -(n : ℂ) • a n) (deriv f) := by
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  set P : ℂ → E := fun z => ∑ n ∈ range N, (z ^ n)⁻¹ • a n
  have hP (z : ℂ) (hz : z ≠ 0) :
      HasDerivAt P (∑ n ∈ range N, (-(n : ℂ) * (z ^ (n + 1))⁻¹) • a n) z := by
    refine HasDerivAt.fun_sum fun n _ => ?_
    have hexp : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    have h := (hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz)).smul_const (a n)
    simp only [hexp, zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast] at h
    exact h
  have hS : {z : ℂ | max R 0 < ‖z‖ ∧ |arg z| < θ} ⊆ {z | R < ‖z‖ ∧ |arg z| < θ} :=
    fun z hz => ⟨(le_max_left R 0).trans_lt hz.1, hz.2⟩
  have hdiff : DifferentiableOn ℂ (fun z => f z - P z) {z | max R 0 < ‖z‖ ∧ |arg z| < θ} :=
    fun z hz => ((hf z (hS hz)).mono hS).sub (hP z (norm_pos_iff.mp
      ((le_max_right R 0).trans_lt hz.1))).differentiableAt.differentiableWithinAt
  have hnorm (n : ℕ) (z : ℂ) : ‖(z ^ n)⁻¹‖ = ‖z‖ ^ (-(n : ℝ)) := by
    rw [norm_inv, norm_pow, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  have hrem : (fun z => f z - P z) =O[cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}]
      fun z => ‖z‖ ^ (-(N : ℝ)) :=
    (he.isBigO N).trans <| isBigO_of_le _ fun z => by
      rw [hnorm, Real.norm_of_nonneg (by positivity)]
  have hscale : (fun z : ℂ => ‖z‖ ^ (-(N : ℝ) - 1)) =O[cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'}]
      fun z => (z ^ (N + 1))⁻¹ := isBigO_of_le _ fun z => by
    have hexp : -(N : ℝ) - 1 = -((N + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [Real.norm_of_nonneg (by positivity), hexp, hnorm]
  refine ((isBigO_deriv_of_isBigO_sector hθ' hdiff hrem).trans hscale).congr' ?_ .rfl
  obtain ⟨c, hc, hc2, hball⟩ := exists_pos_forall_mem_closedBall_abs_arg_lt hθ'
  refine (hasBasis_cobounded_norm.inf_principal _).eventually_iff.mpr
    ⟨2 * max R 0 + 1, trivial, fun z ⟨hz, harg⟩ => ?_⟩
  have hz' : 2 * max R 0 + 1 ≤ ‖z‖ := hz
  have hzR : max R 0 < ‖z‖ := by linarith [le_max_right R 0]
  have hz0 : z ≠ 0 := norm_pos_iff.mp ((le_max_right R 0).trans_lt hzR)
  have hnhds : {z | R < ‖z‖ ∧ |arg z| < θ} ∈ 𝓝 z :=
    mem_of_superset (closedBall_mem_nhds z (mul_pos hc (norm_pos_iff.mpr hz0)))
      (closedBall_subset_setOf_lt_norm_and_abs_arg_lt (A := R) hc2
        (fun w hw => (hball z harg w hw).1)
        (by linarith [le_max_left R 0, le_max_right R 0]))
  rw [((hf.differentiableAt hnhds).hasDerivAt.fun_sub (hP z hz0)).deriv]
  refine congrArg (deriv f z - ·) (sum_congr rfl fun n _ => ?_)
  rw [smul_smul, mul_comm]

end Asymptotics
