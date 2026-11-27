/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.EndEstimate
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart.Output
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Patching
import TauCeti.Topology.Separation.Basic

/-!
# The semi-Fredholm estimate of the linearized Floer operator on spheres with moving input ends

The associativity of the pair-of-pants product is proved through a family of spheres with finitely
many moving input ends, with centers `c i` and nonzero scales `a i`, and an output end at `∞`,
carrying the Hamiltonian perturbations `K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`.
The input end `i` is read in the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))`, where `φ₀` is the
end lift of the input end at `0` of the pair of pants, and the output end in the positive end chart
`φ'_∞` of the pair of pants (`TauCeti.Floer.positiveEndChart`). Let `D_u` be the linearized Floer
operator (`TauCeti.SymplecticForm.floerLinearization`) along a map `u` into a finite-dimensional
symplectic vector space, and let `Σ_T` be the truncation of the sphere at height `T`
(`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation`). This file proves the semi-Fredholm
estimate

`∑_i ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²)`
`  + ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²)`
`  + ∫_{Σ_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{Σ_{T + 1}} ‖ξ‖²)`

for `C²` sections `ξ` with compact support in the sphere minus its input punctures, the plane minus
the centers `c i`. The left side is the `W^{1,2}` energy of `ξ` for a metric that is cylindrical on
the ends; the error term lives on the compact truncation `Σ_{T + 1}`. This is the estimate that
Peetre's argument turns into finite-dimensional kernel and closed range once `D_u` is realized on
Sobolev spaces, as for the pair of pants
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm`).

The discs `‖w - c i‖ < ‖a i‖ / 2` of the input ends are assumed pairwise disjoint and to lie in the
disc `‖w‖ ≤ 2 exp (2π)`, as along the associativity path (`TauCeti.Floer.associativityCenter`,
`TauCeti.Floer.associativityScale`).

* `exists_forall_sum_setIntegral_add_le_mul_integral_floerLinearization_add_of_movingEnds_of_ends`
  patches the estimate together from estimates of `D_u` on the ends and the `L²` estimate of
  `TauCeti.Geometry.Symplectic.Floer.InteriorEstimate` on compact parts of the domain, for any
  Floer data that are regular and compatible along `u`. The section is cut into end pieces
  `β_e ξ`, one for each input end and one for the output end, and the core piece
  `(1 - ∑_e β_e) ξ`, supported in `Σ_{R₀ + 1}`, where `β_e = ψ(2 (s_e - R₀) - 1)` for the smooth
  transition function `ψ` and the longitudinal coordinate `s_e` of the end `e`. The operator
  differentiates the cutoffs only in the compact collars `R₀ ≤ s_e ≤ R₀ + 1`. Beyond the height
  `1` the ends are disjoint, so at most one end cutoff is nonzero at each point.
* The estimate for the datum `TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, along a map
  that solves the Floer equation far out on the ends and converges there to nondegenerate orbits,
  with structures cylindrical on the ends, is
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds`
  . The end estimates come from
  `exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_movingEnds` and
  `exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization_of_movingEnds`
* `TauCeti.Floer.integrableOn_sobolevDensity_comp_realChart_of_movingEnds`,
  `TauCeti.Floer.integrableOn_sobolevDensity_comp_positiveEndChart_of_movingEnds`: a `C¹` section
  with compact support in the sphere has integrable `W^{1,2}` energy density in the chart `ψ_i` of
  every input end and in the chart `φ'_∞` of the output end.

The patching (the cutoffs, the end and core pieces and their estimates, and the patching at one
height) follows the proof for the pair of pants of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_ends` in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm`, adapted to moving ends. The steps
that do not depend on the domain are shared with it through
`TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Patching`.

The target is a symplectic vector space. The Sobolev realization of `D_u`, the estimate of its
formal adjoint and the Fredholm index are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and the associativity of
  the product through families of four-punctured spheres.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical
  ends.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology NNReal Manifold Real
open TauCeti.Complex (realChart contDiff_realChart equivRealProdCLM_symm_realChart)

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} {c a : ι → ℂ}

/-! ### The ends of a sphere with moving input ends -/

/-- The longitudinal coordinate `s` of the end `e` of a sphere with moving input ends: on the
input end `i` the first coordinate of the chart `z ↦ c i + a i φ₀(z)`, on the output end (`none`)
the first positive end coordinate of the end at `∞` of the pair of pants. -/
private noncomputable def movingEndCoord (c a : ι → ℂ) : Option ι → ℝ × ℝ → ℝ
  | none, z => (positiveEndCoord inf z).1
  | some i, z => (zero.endCoord ((Complex.equivRealProdCLM.symm z - c i) / a i)).re

/-- The chart of the end `e` of a sphere with moving input ends. -/
private noncomputable def movingEndChart (c a : ι → ℂ) : Option ι → ℝ × ℝ → ℝ × ℝ
  | none => positiveEndChart inf
  | some i => realChart fun z ↦ c i + a i * zero.cylindricalEndLift z

/-- The sphere with moving input ends, in real coordinates: the plane minus the centers. -/
private noncomputable def movingEndsDomain (c : ι → ℂ) : Set (ℝ × ℝ) :=
  {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}

private theorem isOpen_movingEndsDomain [Finite ι] (c : ι → ℂ) :
    IsOpen (movingEndsDomain c) :=
  isOpen_forall_ne Complex.equivRealProdCLM.symm.continuous

/-- The truncation `Σ_T` of a sphere with moving input ends, in real coordinates. -/
private noncomputable def movingEndsTruncation (c a : ι → ℂ) (T : ℝ) : Set (ℝ × ℝ) :=
  Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T

private theorem isCompact_movingEndsTruncation (c a : ι → ℂ) (T : ℝ) :
    IsCompact (movingEndsTruncation c a T) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_puncturedSphereTruncation c a T)

private theorem movingEndsTruncation_mono (c a : ι → ℂ) {T T' : ℝ} (h : T ≤ T') :
    movingEndsTruncation c a T ⊆ movingEndsTruncation c a T' :=
  preimage_mono (puncturedSphereTruncation_mono h)

/-- The longitudinal coordinate recovers the first coordinate of a point of the end chart. -/
private theorem movingEndCoord_movingEndChart (ha : ∀ i, a i ≠ 0) (e : Option ι) (ζ : ℝ × ℝ) :
    movingEndCoord c a e (movingEndChart c a e ζ) = ζ.1 := by
  cases e with
  | none => exact fst_positiveEndCoord_positiveEndChart inf ζ
  | some i =>
    simp only [movingEndCoord, movingEndChart, equivRealProdCLM_symm_realChart,
      add_sub_cancel_left, mul_div_cancel_left₀ _ (ha i), re_endCoord_cylindricalEndLift]
    simp [Complex.equivRealProdCLM_symm_apply]

/-- On the output end, the longitudinal coordinate of a point of the disc `‖w‖ ≤ 2 exp (2πr)`,
`r ≥ 0`, is at most `r`. -/
private theorem movingEndCoord_none_le {r : ℝ} (hr : 0 ≤ r) {z : ℝ × ℝ}
    (hz : ‖Complex.equivRealProdCLM.symm z‖ ≤ 2 * Real.exp (2 * π * r)) :
    movingEndCoord c a none z ≤ r := by
  simp only [movingEndCoord, fst_positiveEndCoord, endSign_inf, neg_one_mul]
  exact neg_re_endCoord_inf_le hr hz

/-- A point beyond the height `0` of the output end is not `0`. -/
private theorem equivRealProdCLM_symm_ne_zero_of_pos_movingEndCoord_none {z : ℝ × ℝ}
    (h : 0 < movingEndCoord c a none z) : Complex.equivRealProdCLM.symm z ≠ 0 := fun h0 ↦ by
  have := movingEndCoord_none_le (c := c) (a := a) (r := 0) le_rfl (z := z)
    (by rw [h0, norm_zero]; positivity)
  linarith

/-- A point beyond the height `0` of an end is not `0` if the end is the output end. -/
private theorem equivRealProdCLM_symm_ne_zero_of_pos_movingEndCoord {e : Option ι} {z : ℝ × ℝ}
    (h : 0 < movingEndCoord c a e z) : e = none → Complex.equivRealProdCLM.symm z ≠ 0 := by
  rintro rfl
  exact equivRealProdCLM_symm_ne_zero_of_pos_movingEndCoord_none h

/-- Away from the center `c i`, the point read in the input end `i` is not the center of the end
at `0` of the pair of pants. -/
private theorem sub_div_ne_endCenter_zero (ha : ∀ i, a i ≠ 0) {i : ι} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ c i) :
    (Complex.equivRealProdCLM.symm z - c i) / a i ≠ zero.endCenter := by
  rw [endCenter_zero]
  exact div_ne_zero (sub_ne_zero.2 hz) (ha i)

/-- Away from its center, the longitudinal coordinate of the input end `i` is at most `r` exactly
off the open disc `‖w - c i‖ < ‖a i‖ exp (-2πr) / 2`. -/
private theorem movingEndCoord_some_le_iff (ha : ∀ i, a i ≠ 0) {i : ι} {r : ℝ} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ c i) :
    movingEndCoord c a (some i) z ≤ r ↔
      ‖a i‖ * Real.exp (-(2 * π * r)) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - c i‖ := by
  have hapos := norm_pos_iff.2 (ha i)
  simp only [movingEndCoord]
  rw [re_endCoord_le_iff (by decide) (sub_div_ne_endCenter_zero ha hz), endCenter_zero, sub_zero,
    norm_div, le_div_iff₀ hapos]
  constructor <;> intro h <;> linarith

/-- The longitudinal coordinate of an end is smooth away from the center of the end. -/
private theorem contDiffAt_movingEndCoord {e : Option ι} {z : ℝ × ℝ}
    (hz : ∀ i, e = some i → Complex.equivRealProdCLM.symm z ≠ c i)
    (h₀ : e = none → Complex.equivRealProdCLM.symm z ≠ 0) (ha : ∀ i, a i ≠ 0)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (movingEndCoord c a e) z := by
  cases e with
  | none => exact contDiffAt_fst_positiveEndCoord inf (by rw [endCenter_inf]; exact h₀ rfl)
  | some i =>
    have haff : ContDiffAt ℝ n (fun w : ℝ × ℝ ↦ (Complex.equivRealProdCLM.symm w - c i) / a i) z :=
      ((Complex.equivRealProdCLM.symm.contDiff.contDiffAt).sub contDiffAt_const).div_const _
    exact (contDiffAt_re_endCoord zero (sub_div_ne_endCenter_zero ha (hz i rfl))).comp z haff

/-- The longitudinal coordinate of an input end is continuous away from its center. -/
private theorem continuousAt_movingEndCoord_some (ha : ∀ i, a i ≠ 0) {i : ι} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ c i) :
    ContinuousAt (movingEndCoord c a (some i)) z :=
  (contDiffAt_movingEndCoord (n := 0) (fun j hj ↦ by cases hj; exact hz) (by simp)
    ha).continuousAt

/-- **The ends are disjoint beyond the height `1`.** A point beyond the height `1` of one end has
longitudinal coordinate at most `1` on every other end. -/
private theorem movingEndCoord_le_one_of_ne (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {z : ℝ × ℝ}
    (hz : z ∈ movingEndsDomain c) {e e' : Option ι} (hee' : e ≠ e')
    (h : 1 < movingEndCoord c a e z) : movingEndCoord c a e' z ≤ 1 := by
  set w := Complex.equivRealProdCLM.symm z
  have hexp : Real.exp (-(2 * π * 1)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  -- An input coordinate is nonpositive off the disc of radius `‖a j‖ / 2` about the center.
  have hin (j : ι) (hj : ‖a j‖ / 2 ≤ ‖w - c j‖) : movingEndCoord c a (some j) z ≤ 1 := by
    refine (movingEndCoord_some_le_iff ha (hz j)).2 (le_trans ?_ hj)
    have := norm_nonneg (a j)
    nlinarith
  cases e with
  | none =>
    -- Beyond the height `1` of the output end, `‖w‖ > 2 exp (2π)`.
    have hw0 : w ≠ 0 := equivRealProdCLM_symm_ne_zero_of_pos_movingEndCoord_none (by linarith)
    have hw := (lt_fst_positiveEndCoord_inf_iff hw0).1 h
    rw [mul_one] at hw
    obtain _ | j := e'
    · exact absurd rfl hee'
    refine hin j ?_
    linarith [hout j, norm_sub_norm_le w (c j)]
  | some i =>
    -- Beyond the height `1` of the input end `i`, `‖w - c i‖ < ‖a i‖ / 2`.
    have hapos := norm_pos_iff.2 (ha i)
    have hi : ‖w - c i‖ < ‖a i‖ / 2 := by
      have h' := (not_congr (movingEndCoord_some_le_iff (r := 1) ha (hz i))).1 h.not_ge
      push Not at h'
      nlinarith
    obtain _ | j := e'
    · refine movingEndCoord_none_le zero_le_one ?_
      rw [mul_one]
      linarith [hout i, norm_le_norm_add_norm_sub' w (c i), norm_sub_rev w (c i)]
    · have hij : i ≠ j := fun h' ↦ hee' (by rw [h'])
      refine hin j ?_
      have := hsep hij
      linarith [norm_sub_le_norm_sub_add_norm_sub (c i) w (c j), norm_sub_rev (c i) w]

/-- A point of the truncation `Σ_T`, `T ≥ 0`, lies in the sphere and has longitudinal coordinate
at most `T` on every end, and conversely. -/
private theorem mem_movingEndsTruncation_iff (ha : ∀ i, a i ≠ 0) {T : ℝ} (hT : 0 ≤ T)
    {z : ℝ × ℝ} :
    z ∈ movingEndsTruncation c a T ↔
      z ∈ movingEndsDomain c ∧ ∀ e, movingEndCoord c a e z ≤ T := by
  set w := Complex.equivRealProdCLM.symm z
  constructor
  · intro hz
    have hU : z ∈ movingEndsDomain c := fun i ↦ ne_of_mem_puncturedSphereTruncation (ha i) hz
    have hz' := mem_puncturedSphereTruncation.1 hz
    refine ⟨hU, fun e ↦ ?_⟩
    cases e with
    | none => exact movingEndCoord_none_le hT hz'.2
    | some i => exact (movingEndCoord_some_le_iff ha (hU i)).2 (hz'.1 i)
  · rintro ⟨hU, he⟩
    refine mem_puncturedSphereTruncation.2
      ⟨fun i ↦ (movingEndCoord_some_le_iff ha (hU i)).1 (he (some i)), ?_⟩
    rcases eq_or_ne w 0 with h0 | h0
    · rw [show Complex.equivRealProdCLM.symm z = 0 from h0, norm_zero]
      positivity
    · exact not_lt.1 fun h ↦ (he none).not_gt ((lt_fst_positiveEndCoord_inf_iff h0).2 h)

/-- The truncation `Σ_T` lies in the sphere. -/
private theorem movingEndsTruncation_subset (ha : ∀ i, a i ≠ 0) (T : ℝ) :
    movingEndsTruncation c a T ⊆ movingEndsDomain c :=
  fun _ hz i ↦ ne_of_mem_puncturedSphereTruncation (ha i) hz

/-- The longitudinal coordinate of every end is bounded above on a compact subset of the sphere. -/
private theorem exists_forall_movingEndCoord_le (ha : ∀ i, a i ≠ 0) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ movingEndsDomain c) (e : Option ι) :
    ∃ N, ∀ z ∈ K, movingEndCoord c a e z ≤ N := by
  cases e with
  | none =>
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      (f := fun z ↦ Complex.equivRealProdCLM.symm z)
      Complex.equivRealProdCLM.symm.continuous.continuousOn
    refine ⟨max M 0, fun z hz ↦ movingEndCoord_none_le (le_max_right _ _) ?_⟩
    -- `max M 0 ≤ 2 exp (2π max M 0)`, from `exp x ≥ 1 + x`.
    have h₁ := Real.add_one_le_exp (2 * π * max M 0)
    have h₂ : 0 ≤ max M 0 := le_max_right _ _
    nlinarith [hM z hz, le_max_left M 0, Real.two_le_pi]
  | some i =>
    obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn (f := movingEndCoord c a (some i))
      fun z hz ↦ (continuousAt_movingEndCoord_some ha (hKU hz i)).continuousWithinAt
    exact ⟨N, fun z hz ↦ (le_abs_self _).trans (hN z hz)⟩

omit [FiniteDimensional ℝ V] in
/-- A `C¹` section with compact support in the sphere has integrable `W^{1,2}` energy density in
the chart of every end, over every half-cylinder `(b, ∞) × [0, 1]`: it vanishes far out on the
end. -/
private theorem integrableOn_sobolevDensity_comp_movingEndChart (ha : ∀ i, a i ≠ 0)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ movingEndsDomain c) (e : Option ι) (b : ℝ) :
    IntegrableOn (sobolevDensity (ξ ∘ movingEndChart c a e)) (Ioi b ×ˢ Icc 0 1) := by
  have hψ : ContDiff ℝ 1 (movingEndChart c a e) := by
    cases e with
    | none => exact contDiff_positiveEndChart inf 1
    | some i => exact contDiff_realChart (by fun_prop)
  obtain ⟨N, hN⟩ := exists_forall_movingEndCoord_le ha hξc.isCompact hξU e
  refine integrableOn_sobolevDensity_of_eventuallyEq_zero
    (continuous_sobolevDensity (hξ.comp hψ)) (N := N) (fun ζ hζ ↦ ?_) b
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ] with ζ' hζ'
  rw [Pi.zero_apply, Function.comp_apply]
  refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
  have := hN _ h
  rw [movingEndCoord_movingEndChart ha] at this
  exact (lt_irrefl _) (hζ'.trans_le this)

/-- A point of the sphere at height `σ` on the end `e` is the image of a point of first
coordinate `σ` under the chart of the end, if `σ > 0`. -/
private theorem exists_movingEndChart_eq (ha : ∀ i, a i ≠ 0) {e : Option ι} {z : ℝ × ℝ}
    (hz : z ∈ movingEndsDomain c) (h : 0 < movingEndCoord c a e z) :
    ∃ ζ : ℝ × ℝ, ζ.1 = movingEndCoord c a e z ∧ movingEndChart c a e ζ = z := by
  cases e with
  | none =>
    have h0 : Complex.equivRealProdCLM.symm z ≠ inf.endCenter := by
      rw [endCenter_inf]
      exact equivRealProdCLM_symm_ne_zero_of_pos_movingEndCoord_none h
    exact ⟨endBandCoord inf z, by simp [movingEndCoord, endBandCoord_apply],
      positiveEndChart_endBandCoord inf h0⟩
  | some i =>
    set v := (Complex.equivRealProdCLM.symm z - c i) / a i
    have hv : v ≠ zero.endCenter := sub_div_ne_endCenter_zero ha (hz i)
    refine ⟨Complex.equivRealProdCLM (zero.endCoord v), by simp [movingEndCoord, v], ?_⟩
    simp only [movingEndChart, TauCeti.Complex.realChart_apply,
      ContinuousLinearEquiv.symm_apply_apply, zero.cylindricalEndLift_endCoord hv, v,
      mul_div_cancel₀ _ (ha i), add_sub_cancel, ContinuousLinearEquiv.apply_symm_apply]

/-! ### Cutoffs on a sphere with moving input ends -/

/-- The cutoff `β_e = ψ(2 (s_e - R₀) - 1)` of the end `e`, for the smooth transition function
`ψ`. It vanishes to first order where `s_e ≤ R₀`, and it is `1` where `s_e ≥ R₀ + 1`. -/
private noncomputable def movingEndCutoff (c a : ι → ℂ) (R₀ : ℝ) (e : Option ι) (z : ℝ × ℝ) : ℝ :=
  Real.smoothTransition (2 * (movingEndCoord c a e z - R₀) - 1)

private theorem movingEndCutoff_eq_zero {R₀ : ℝ} {e : Option ι} {z : ℝ × ℝ}
    (h : movingEndCoord c a e z ≤ R₀) : movingEndCutoff c a R₀ e z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem movingEndCutoff_eq_one {R₀ : ℝ} {e : Option ι} {z : ℝ × ℝ}
    (h : R₀ + 1 ≤ movingEndCoord c a e z) : movingEndCutoff c a R₀ e z = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem movingEndCutoff_nonneg (R₀ : ℝ) (e : Option ι) (z : ℝ × ℝ) :
    0 ≤ movingEndCutoff c a R₀ e z :=
  Real.smoothTransition.nonneg _

private theorem movingEndCutoff_le_one (R₀ : ℝ) (e : Option ι) (z : ℝ × ℝ) :
    movingEndCutoff c a R₀ e z ≤ 1 :=
  Real.smoothTransition.le_one _

/-- For `R₀ ≥ 0` the cutoff of the output end vanishes near `0`, where the coordinate of the output
end is not smooth. -/
private theorem movingEndCutoff_none_eventuallyEq_zero {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {z : ℝ × ℝ}
    (h₀ : Complex.equivRealProdCLM.symm z = 0) : movingEndCutoff c a R₀ none =ᶠ[𝓝 z] 0 := by
  have hopen : IsOpen {w : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm w‖ < 2} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds (by simp [h₀])] with w hw
  refine movingEndCutoff_eq_zero ((movingEndCoord_none_le le_rfl ?_).trans hR₀)
  rw [mul_zero, Real.exp_zero, mul_one]
  exact hw.le

/-- For `R₀ ≥ 0`, near every point either the cutoff of the end `e` vanishes, or the point is not
`0` when `e` is the output end, so that the coordinate of the end is smooth there. -/
private theorem movingEndCutoff_eventuallyEq_zero_or_ne_zero {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (e : Option ι) (z : ℝ × ℝ) :
    movingEndCutoff c a R₀ e =ᶠ[𝓝 z] 0 ∨ (e = none → Complex.equivRealProdCLM.symm z ≠ 0) := by
  by_cases h₀ : e = none ∧ Complex.equivRealProdCLM.symm z = 0
  · obtain ⟨rfl, h₀⟩ := h₀
    exact .inl (movingEndCutoff_none_eventuallyEq_zero hR₀ h₀)
  · push Not at h₀
    exact .inr h₀

/-- The derivative of the cutoff of the end `e` at a point of the sphere, away from `0` if `e` is
the output end. -/
private theorem hasFDerivAt_movingEndCutoff (ha : ∀ i, a i ≠ 0) (R₀ : ℝ) {e : Option ι}
    {z : ℝ × ℝ} (hz : z ∈ movingEndsDomain c)
    (h₀ : e = none → Complex.equivRealProdCLM.symm z ≠ 0) :
    HasFDerivAt (movingEndCutoff c a R₀ e)
      (deriv Real.smoothTransition (2 * (movingEndCoord c a e z - R₀) - 1) •
        (2 : ℝ) • fderiv ℝ (movingEndCoord c a e) z) z :=
  ((((contDiffAt_movingEndCoord (n := 1) (fun i _ ↦ hz i) h₀ ha).differentiableAt
    one_ne_zero).hasFDerivAt.sub_const R₀).const_mul 2 |>.sub_const 1).smoothTransition

/-- The cutoff of an end is smooth on the sphere, for `R₀ ≥ 0`. At `0`, where the coordinate of
the output end is not smooth, the cutoff of the output end vanishes near the point. -/
private theorem contDiffAt_movingEndCutoff (ha : ∀ i, a i ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (e : Option ι) {z : ℝ × ℝ} (hz : z ∈ movingEndsDomain c) {n : ℕ∞} :
    ContDiffAt ℝ n (movingEndCutoff c a R₀ e) z := by
  rcases movingEndCutoff_eventuallyEq_zero_or_ne_zero hR₀ e z with h₀ | h₀
  · exact contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq h₀
  · exact Real.smoothTransition.contDiff.contDiffAt.comp z
      ((contDiffAt_const.mul ((contDiffAt_movingEndCoord (fun i _ ↦ hz i) h₀ ha).sub
        contDiffAt_const)).sub contDiffAt_const)

/-- Away from the collar `R₀ ≤ s_e ≤ R₀ + 1`, the cutoff of the end `e` is locally constant. -/
private theorem mem_Icc_of_fderiv_movingEndCutoff_ne_zero (ha : ∀ i, a i ≠ 0) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) {e : Option ι} {z : ℝ × ℝ} (hz : z ∈ movingEndsDomain c)
    (h : fderiv ℝ (movingEndCutoff c a R₀ e) z ≠ 0) :
    movingEndCoord c a e z ∈ Icc R₀ (R₀ + 1) := by
  rcases movingEndCutoff_eventuallyEq_zero_or_ne_zero hR₀ e z with h₀ | h₀
  · exact absurd (((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq h₀).fderiv) h
  rw [(hasFDerivAt_movingEndCutoff ha R₀ hz h₀).fderiv] at h
  refine ⟨?_, ?_⟩ <;> by_contra! h'
  · exact h (by rw [Real.smoothTransition.deriv_of_nonpos (by linarith), zero_smul])
  · exact h (by rw [Real.smoothTransition.deriv_of_one_le (by linarith), zero_smul])

variable [Fintype ι]

/-- The cutoff `1 - ∑_e β_e` of the core of a sphere with moving input ends. -/
private noncomputable def movingCoreCutoff (c a : ι → ℂ) (R₀ : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 - ∑ e, movingEndCutoff c a R₀ e z

private theorem contDiffAt_movingCoreCutoff (ha : ∀ i, a i ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {z : ℝ × ℝ} (hz : z ∈ movingEndsDomain c) {n : ℕ∞} :
    ContDiffAt ℝ n (movingCoreCutoff c a R₀) z :=
  contDiffAt_const.sub (ContDiffAt.sum fun e _ ↦ contDiffAt_movingEndCutoff ha hR₀ e hz)

private theorem fderiv_movingCoreCutoff (ha : ∀ i, a i ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {z : ℝ × ℝ} (hz : z ∈ movingEndsDomain c) :
    fderiv ℝ (movingCoreCutoff c a R₀) z = -∑ e, fderiv ℝ (movingEndCutoff c a R₀ e) z := by
  have hd (e : Option ι) : DifferentiableAt ℝ (movingEndCutoff c a R₀ e) z :=
    (contDiffAt_movingEndCutoff ha hR₀ e hz (n := 1)).differentiableAt one_ne_zero
  unfold movingCoreCutoff
  rw [fderiv_const_sub, fderiv_fun_sum fun e _ ↦ hd e]

section Geometry

variable (ha : ∀ i, a i ≠ 0) (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
  (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
include ha hsep hout

omit [Fintype ι] in
/-- At a point beyond `R₀ ≥ 1` on the end `e`, all other end cutoffs vanish. -/
private theorem movingEndCutoff_eq_zero_of_ne {R₀ : ℝ} (hR₀ : 1 ≤ R₀) {e e' : Option ι}
    (hee' : e ≠ e') {z : ℝ × ℝ} (hz : z ∈ movingEndsDomain c) (h : R₀ < movingEndCoord c a e z) :
    movingEndCutoff c a R₀ e' z = 0 :=
  movingEndCutoff_eq_zero
    ((movingEndCoord_le_one_of_ne ha hsep hout hz hee' (by linarith)).trans hR₀)

/-- At most one end cutoff is nonzero, so the core cutoff lies in `[0, 1]`. -/
private theorem movingCoreCutoff_mem_Icc {R₀ : ℝ} (hR₀ : 1 ≤ R₀) {z : ℝ × ℝ}
    (hz : z ∈ movingEndsDomain c) : movingCoreCutoff c a R₀ z ∈ Icc 0 1 := by
  by_cases h : ∃ e, R₀ < movingEndCoord c a e z
  · obtain ⟨e, he⟩ := h
    rw [movingCoreCutoff, Finset.sum_eq_single e (fun e' _ he' ↦
      movingEndCutoff_eq_zero_of_ne ha hsep hout hR₀ (Ne.symm he') hz he) (by simp)]
    exact ⟨by linarith [movingEndCutoff_le_one (c := c) (a := a) R₀ e z],
      by linarith [movingEndCutoff_nonneg (c := c) (a := a) R₀ e z]⟩
  · push Not at h
    simp [movingCoreCutoff, movingEndCutoff_eq_zero (h _)]

private theorem abs_movingCoreCutoff_le_one {R₀ : ℝ} (hR₀ : 1 ≤ R₀) {z : ℝ × ℝ}
    (hz : z ∈ movingEndsDomain c) : |movingCoreCutoff c a R₀ z| ≤ 1 :=
  abs_le.2 ⟨by linarith [(movingCoreCutoff_mem_Icc ha hsep hout hR₀ hz).1],
    (movingCoreCutoff_mem_Icc ha hsep hout hR₀ hz).2⟩

private theorem movingCoreCutoff_eq_zero {R₀ : ℝ} (hR₀ : 1 ≤ R₀) {e : Option ι} {z : ℝ × ℝ}
    (hz : z ∈ movingEndsDomain c) (h : R₀ + 1 ≤ movingEndCoord c a e z) :
    movingCoreCutoff c a R₀ z = 0 := by
  rw [movingCoreCutoff, Finset.sum_eq_single e (fun e' _ he' ↦
    movingEndCutoff_eq_zero_of_ne ha hsep hout hR₀ (Ne.symm he') hz (by linarith)) (by simp),
    movingEndCutoff_eq_one h, sub_self]

omit [Fintype ι] in
/-- Where the derivative of an end cutoff is nonzero, the point lies in `Σ_{R₀ + 1}`. -/
private theorem mem_movingEndsTruncation_of_fderiv_movingEndCutoff_ne_zero {R₀ : ℝ}
    (hR₀ : 1 < R₀) {e : Option ι} {z : ℝ × ℝ} (hz : z ∈ movingEndsDomain c)
    (h : fderiv ℝ (movingEndCutoff c a R₀ e) z ≠ 0) :
    z ∈ movingEndsTruncation c a (R₀ + 1) := by
  obtain ⟨h₁, h₂⟩ := mem_Icc_of_fderiv_movingEndCutoff_ne_zero ha (by linarith) hz h
  refine (mem_movingEndsTruncation_iff ha (by linarith)).2 ⟨hz, fun e' ↦ ?_⟩
  rcases eq_or_ne e e' with rfl | hee'
  · exact h₂
  · linarith [movingEndCoord_le_one_of_ne ha hsep hout hz hee' (by linarith)]

/-- Where the derivative of the core cutoff is nonzero, the point lies in `Σ_{R₀ + 1}`. -/
private theorem mem_movingEndsTruncation_of_fderiv_movingCoreCutoff_ne_zero {R₀ : ℝ}
    (hR₀ : 1 < R₀) {z : ℝ × ℝ} (hz : z ∈ movingEndsDomain c)
    (h : fderiv ℝ (movingCoreCutoff c a R₀) z ≠ 0) :
    z ∈ movingEndsTruncation c a (R₀ + 1) := by
  rw [fderiv_movingCoreCutoff ha (by linarith) hz, neg_ne_zero] at h
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact mem_movingEndsTruncation_of_fderiv_movingEndCutoff_ne_zero ha hsep hout hR₀ hz he

omit hsep hout in
/-- On `Σ_{R₀}` the core cutoff is `1` to first order. -/
private theorem movingCoreCutoff_eq_one_and_fderiv_eq_zero {R₀ : ℝ} (hR₀ : 1 ≤ R₀)
    {z : ℝ × ℝ} (hz : z ∈ movingEndsTruncation c a R₀) :
    movingCoreCutoff c a R₀ z = 1 ∧ fderiv ℝ (movingCoreCutoff c a R₀) z = 0 := by
  obtain ⟨hU, hle⟩ := (mem_movingEndsTruncation_iff ha (by linarith)).1 hz
  refine ⟨by simp [movingCoreCutoff, movingEndCutoff_eq_zero (hle _)], ?_⟩
  rw [fderiv_movingCoreCutoff ha (by linarith) hU, neg_eq_zero]
  refine Finset.sum_eq_zero fun e _ ↦ by_contra fun h ↦ ?_
  obtain ⟨h₁, -⟩ := mem_Icc_of_fderiv_movingEndCutoff_ne_zero ha (by linarith) hU h
  -- On the collar the cutoff has derivative `ψ'(2 (s - R₀) - 1) = ψ'(-1) = 0` at `s = R₀`.
  have hs : movingEndCoord c a e z = R₀ := le_antisymm (hle e) h₁
  have h₀ :=
    equivRealProdCLM_symm_ne_zero_of_pos_movingEndCoord ((by linarith : (0 : ℝ) < R₀).trans_le h₁)
  exact h (by rw [(hasFDerivAt_movingEndCutoff ha R₀ hU h₀).fderiv, hs,
    Real.smoothTransition.deriv_of_nonpos (by linarith), zero_smul])

omit [FiniteDimensional ℝ V] [Fintype ι] hsep hout in
/-- The cut-off section `β_e ξ` of the end `e` is supported in the chart of the end beyond any
height `R < R₀`. -/
private theorem tsupport_movingEndCutoff_smul_subset {R₀ R : ℝ} (hR₀ : 0 < R₀) (hR : R < R₀)
    {e : Option ι} {ξ : ℝ × ℝ → V} (hξU : tsupport ξ ⊆ movingEndsDomain c) :
    tsupport (fun z ↦ movingEndCutoff c a R₀ e z • ξ z) ⊆
      movingEndChart c a e '' (Ioi R ×ˢ univ) := by
  intro z hz
  have hzU : z ∈ movingEndsDomain c := hξU (tsupport_smul_subset_right _ _ hz)
  -- The cut-off section vanishes near every point where `s_e < R₀`.
  have hle : R₀ ≤ movingEndCoord c a e z := by
    refine le_of_not_gt fun h ↦ notMem_tsupport_iff_eventuallyEq.2 ?_ hz
    rcases movingEndCutoff_eventuallyEq_zero_or_ne_zero (c := c) (a := a) hR₀.le e z with h₀ | h₀
    · filter_upwards [h₀] with w hw
      simp [hw]
    filter_upwards [(contDiffAt_movingEndCoord (n := 0) (fun i _ ↦ hzU i) h₀
      ha).continuousAt.eventually (Iio_mem_nhds h)] with w hw
    simp [movingEndCutoff_eq_zero (le_of_lt hw)]
  obtain ⟨ζ, hζ, hζz⟩ := exists_movingEndChart_eq ha hzU (by linarith)
  exact ⟨ζ, ⟨by rw [mem_Ioi, hζ]; linarith, mem_univ _⟩, hζz⟩

omit [FiniteDimensional ℝ V] in
/-- The cut-off section `(1 - ∑_e β_e) ξ` of the core is supported in `Σ_{R₀ + 1}`. -/
private theorem tsupport_movingCoreCutoff_smul_subset {R₀ : ℝ} (hR₀ : 1 ≤ R₀) {ξ : ℝ × ℝ → V}
    (hξU : tsupport ξ ⊆ movingEndsDomain c) :
    tsupport (fun z ↦ movingCoreCutoff c a R₀ z • ξ z) ⊆ movingEndsTruncation c a (R₀ + 1) := by
  intro z hz
  have hzU : z ∈ movingEndsDomain c := hξU (tsupport_smul_subset_right _ _ hz)
  refine (mem_movingEndsTruncation_iff ha (by linarith)).2 ⟨hzU, fun e ↦ le_of_not_gt fun h ↦
    notMem_tsupport_iff_eventuallyEq.2 ?_ hz⟩
  -- Beyond `R₀ + 1 > 0` on the output end, the point is not `0`.
  have h₀ :=
    equivRealProdCLM_symm_ne_zero_of_pos_movingEndCoord ((by linarith : (0 : ℝ) < R₀ + 1).trans h)
  filter_upwards [(contDiffAt_movingEndCoord (n := 0) (fun i _ ↦ hzU i) h₀
      ha).continuousAt.eventually (Ioi_mem_nhds h),
    (isOpen_movingEndsDomain c).mem_nhds hzU] with w hw hwU
  simp [movingCoreCutoff_eq_zero ha hsep hout hR₀ hwU (le_of_lt hw)]

end Geometry

/-! ### The linearized operator on cut-off sections -/

omit [Fintype ι] [FiniteDimensional ℝ V] in
/-- The cut-off section `β_e ξ` of the end `e` of a `C²` section supported in the sphere is
`C²`. -/
private theorem contDiff_movingEndCutoff_smul [Finite ι] (ha : ∀ i, a i ≠ 0) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) (e : Option ι) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hξU : tsupport ξ ⊆ movingEndsDomain c) :
    ContDiff ℝ 2 fun z ↦ movingEndCutoff c a R₀ e z • ξ z :=
  (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
    (fun _ hz ↦ (contDiffAt_movingEndCutoff ha hR₀ e hz).contDiffWithinAt) hξ.contDiffOn
    (isOpen_movingEndsDomain c) hξU

omit [FiniteDimensional ℝ V] in
/-- The cut-off section `(1 - ∑_e β_e) ξ` of the core of a `C²` section supported in the sphere
is `C²`. -/
private theorem contDiff_movingCoreCutoff_smul (ha : ∀ i, a i ≠ 0) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξU : tsupport ξ ⊆ movingEndsDomain c) :
    ContDiff ℝ 2 fun z ↦ movingCoreCutoff c a R₀ z • ξ z :=
  (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
    (fun _ hz ↦ (contDiffAt_movingCoreCutoff ha hR₀ hz).contDiffWithinAt) hξ.contDiffOn
    (isOpen_movingEndsDomain c) hξU

omit [Fintype ι] [FiniteDimensional ℝ V] in
/-- **The end piece.** Beyond `R₀ + 1` on the end `e`, a section agrees with its cut-off `β_e ξ`,
so its energy there is at most the energy of `β_e ξ` on the end beyond `2`. -/
private theorem setIntegral_sobolevDensity_comp_movingEndChart_le [Finite ι] (ha : ∀ i, a i ≠ 0)
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (e : Option ι) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hξc : HasCompactSupport ξ) (hξU : tsupport ξ ⊆ movingEndsDomain c) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ movingEndChart c a e) ζ ≤
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity ((fun z ↦ movingEndCutoff c a R₀ e z • ξ z) ∘ movingEndChart c a e) ζ := by
  have hβξ := contDiff_movingEndCutoff_smul ha (R₀ := R₀) (by linarith) e hξ hξU
  calc _ = ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity ((fun z ↦ movingEndCutoff c a R₀ e z • ξ z) ∘ movingEndChart c a e) ζ := by
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
        refine (sobolevDensity_congr_of_eventuallyEq ?_).symm
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ.1] with ζ' hζ'
        rw [Function.comp_apply, Function.comp_apply, movingEndCutoff_eq_one
          (by rw [movingEndCoord_movingEndChart ha]; exact le_of_lt hζ'), one_smul]
    _ ≤ _ := setIntegral_mono_set (integrableOn_sobolevDensity_comp_movingEndChart ha
        (hβξ.of_le one_le_two) (hξc.mono (support_smul_subset_right _ ξ))
        ((tsupport_smul_subset_right _ _).trans hξU) e 2)
        (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)
        (.of_forall fun _ hζ ↦ prod_mono (Ioi_subset_Ioi (by linarith)) subset_rfl hζ)

omit [Fintype ι] in
/-- **The end estimate on a cut-off section.** If `D_u` controls the energy on the end `e` in its
chart for sections supported beyond the height `Re < R₀`, then the energy of a section beyond
`R₀ + 1` on that end is controlled by `D_u ξ` and by `ξ` on `Σ_{R₀ + 1}`, through the cut-off
section `β_e ξ`; here `M` bounds the derivative of `β_e` and `B` bounds `J` along `u` on
`Σ_{R₀ + 1}`. -/
private theorem setIntegral_sobolevDensity_comp_movingEndChart_le_of_end [Finite ι]
    (ω : SymplecticForm V) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ movingEndsDomain c, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ movingEndsDomain c, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ movingEndsDomain c, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ movingEndsDomain c, ContDiffAt ℝ 1 u z) {R₀ : ℝ} (hR₀ : 1 < R₀) (e : Option ι)
    {Ce Re : ℝ} (hRe : Re < R₀)
    (hend : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ movingEndChart c a e '' (Ioi Re ×ˢ univ) →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ movingEndChart c a e) ζ ≤
        Ce * ∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2)
    {M B : ℝ}
    (hM : ∀ z ∈ movingEndsTruncation c a (R₀ + 1), ‖fderiv ℝ (movingEndCutoff c a R₀ e) z‖ ≤ M)
    (hB : ∀ z ∈ movingEndsTruncation c a (R₀ + 1), ‖J z (u z)‖ ≤ B) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) (hξU : tsupport ξ ⊆ movingEndsDomain c) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ movingEndChart c a e) ζ ≤
      max Ce 0 * (2 * (∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * ∫ z in movingEndsTruncation c a (R₀ + 1), ‖ξ z‖ ^ 2) := by
  have hβξ := contDiff_movingEndCutoff_smul ha (R₀ := R₀) (by linarith) e hξ hξU
  have hD := ω.integral_norm_floerLinearization_fun_smul_sq_le (isOpen_movingEndsDomain c) hJ hKs
    hKt hu (isCompact_movingEndsTruncation c a _)
    (fun z hz ↦ contDiffAt_movingEndCutoff ha (by linarith) e hz)
    (fun z _ ↦ abs_le.2 ⟨by linarith [movingEndCutoff_nonneg (c := c) (a := a) R₀ e z],
      movingEndCutoff_le_one R₀ e z⟩)
    (fun z hz ↦ mem_movingEndsTruncation_of_fderiv_movingEndCutoff_ne_zero ha hsep hout hR₀ hz)
    hM hB hξ hξc hξU
  have hD₀ : 0 ≤ ∫ z, ‖ω.floerLinearization J Ks Kt u
      (fun w ↦ movingEndCutoff c a R₀ e w • ξ w) z‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  refine (setIntegral_sobolevDensity_comp_movingEndChart_le ha hR₀.le e hξ hξc hξU).trans <|
    (hend hβξ (hξc.mono (support_smul_subset_right _ ξ))
      (tsupport_movingEndCutoff_smul_subset ha (by linarith) hRe hξU)).trans ?_
  exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hD₀).trans
    (mul_le_mul_of_nonneg_left hD (le_max_right _ _))

/-- **Patching at one height.** If `D_u` controls the energy on every end `e` in its chart for
sections supported beyond the height `R e`, then for every height `R₀ > 1` above the `R e`, the
energy of a section beyond `R₀ + 1` on the ends and on the truncation `Σ_{R₀}` is controlled by
`D_u ξ` and by `ξ` on `Σ_{R₀ + 1}`. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_movingEnds_aux
    (ω : SymplecticForm V) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ movingEndsDomain c, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ movingEndsDomain c, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ movingEndsDomain c, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ movingEndsDomain c, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ movingEndsDomain c, ω.Compatible (J z (u z))) {C R : Option ι → ℝ}
    (hend : ∀ e ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ movingEndChart c a e '' (Ioi (R e) ×ˢ univ) →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ movingEndChart c a e) ζ ≤
        C e * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2)
    {R₀ : ℝ} (hR₀ : 1 < R₀) (hR : ∀ e, R e < R₀) :
    ∃ C', 0 ≤ C' ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ movingEndsDomain c →
      (∑ e, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (ξ ∘ movingEndChart c a e) ζ) +
          ∫ z in movingEndsTruncation c a R₀, sobolevDensity ξ z ≤
        C' * ((∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
          ∫ z in movingEndsTruncation c a (R₀ + 1), ‖ξ z‖ ^ 2) := by
  set K := movingEndsTruncation c a (R₀ + 1)
  have hK : IsCompact K := isCompact_movingEndsTruncation c a _
  have hKU : K ⊆ movingEndsDomain c := movingEndsTruncation_subset ha _
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  -- Bounds for `J` along `u` and for the derivatives of the cutoffs on `K`.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ J' z (u z))
    fun z hz ↦ ((hJ z (hKU hz)).continuousAt.comp₂ continuousAt_id
      (hu z (hKU hz)).continuousAt).continuousWithinAt
  obtain ⟨M, hMe, hMc⟩ := hK.exists_forall_norm_fderiv_le
    (fun e z hz ↦ contDiffAt_movingEndCutoff ha (by linarith) e (hKU hz))
    fun z hz ↦ fderiv_movingCoreCutoff ha (by linarith) (hKU hz)
  -- The estimate on the compact core `K`.
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨C₀, hC₀, hint⟩ :=
   exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset
      ω (μ := volume) hK (fun z hz ↦ hJ z (hKU hz)) (fun z hz ↦ hKs z (hKU hz))
      (fun z hz ↦ hKt z (hKU hz)) (fun z hz ↦ hu z (hKU hz)) (fun z hz ↦ hc z (hKU hz))
  set c' := M * (1 + B)
  refine ⟨∑ e, max (C e) 0 * (2 + 2 * c' ^ 2) + C₀ * (3 + 2 * c' ^ 2) + 1, by positivity,
    fun ξ hξ hξc hξU ↦ ?_⟩
  set X := ∫ z, ‖ω.floerLinearization J' Ks Kt u ξ z‖ ^ 2
  set Y := ∫ z in K, ‖ξ z‖ ^ 2
  have hX : 0 ≤ X := integral_nonneg fun _ ↦ sq_nonneg _
  have hY : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  -- The ends through the end cutoffs, and the core through the core cutoff.
  have hends (e : Option ι) := ω.setIntegral_sobolevDensity_comp_movingEndChart_le_of_end
    (J := J') ha hsep hout hJ hKs hKt hu hR₀ e (hR e) (hend e) (hMe e) hB hξ hξc hξU
  have hDc := ω.integral_norm_floerLinearization_fun_smul_sq_le (J := J')
    (isOpen_movingEndsDomain c) hJ hKs hKt hu hK
    (fun z hz ↦ contDiffAt_movingCoreCutoff ha (by linarith) hz)
    (fun z hz ↦ abs_movingCoreCutoff_le_one ha hsep hout hR₀.le hz)
    (fun z hz ↦ mem_movingEndsTruncation_of_fderiv_movingCoreCutoff_ne_zero ha hsep hout hR₀ hz)
    hMc hB hξ hξc hξU
  have hcore : ∫ z in movingEndsTruncation c a R₀, sobolevDensity ξ z ≤
      C₀ * (2 * X + 2 * c' ^ 2 * Y + Y) + Y :=
    (ω.setIntegral_sobolevDensity_le_mul_integral_floerLinearization_smul_add (J := J')
      (isOpen_movingEndsDomain c) hJ hKs hKt hu
      (isCompact_movingEndsTruncation c a R₀).measurableSet hK
      (movingEndsTruncation_mono c a (by linarith)) hKU
      (fun z hz ↦ contDiffAt_movingCoreCutoff ha (by linarith) hz)
      (fun z hz ↦ abs_movingCoreCutoff_le_one ha hsep hout hR₀.le (hKU hz))
      (fun z hz ↦ movingCoreCutoff_eq_one_and_fderiv_eq_zero ha hR₀.le hz) hC₀ hint hξ hξc hξU
      (tsupport_movingCoreCutoff_smul_subset ha hsep hout hR₀.le hξU)).trans (by gcongr)
  -- Summing the pieces.
  exact sum_add_le_mul_add (fun e ↦ le_max_right _ _) hC₀ hX hY hends hcore

/-! ### The semi-Fredholm estimate -/

/-- **Patching end estimates into the semi-Fredholm estimate on a sphere with moving input ends.**
Let the discs `‖w - c i‖ < ‖a i‖ / 2` of the input ends be pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, with nonzero scales. Let `J(z)` be compatible along `u` on the sphere minus
the centers `c i`, with `J` `C¹` and `K_s`, `K_t` `C²` at the points `(z, u z)`, and `u` `C¹` there.
Suppose that on each end the linearized Floer operator `D_u` controls the energy in the chart of
the end: on the input end `i`, read in the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))`, every
`C²` section `ξ` with compact support in `ψ_i ((R i, ∞) × ℝ)` satisfies
`∫_{(2, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²) ≤ C i ∫ ‖D_u ξ‖²`, and
likewise on the output end in the chart `φ'_∞` beyond `Rout`, with the constant `Cout`. Then there
are `C ≥ 0` and `T ≥ 2` such that every `C²` section `ξ` with compact support in the sphere minus
the centers satisfies

`∑_i ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²)`
`  + ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²)`
`  + ∫_{Σ_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{Σ_{T + 1}} ‖ξ‖²)`,

where `Σ_T` is the truncation `TauCeti.ThricePuncturedSphere.puncturedSphereTruncation c a T`. -/
theorem
    exists_forall_sum_setIntegral_add_le_mul_integral_floerLinearization_add_of_movingEnds_of_ends
    (ω : SymplecticForm V) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ω.Compatible (J z (u z)))
    {C R : ι → ℝ}
    (hend : ∀ i ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆
        realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) '' (Ioi (R i) ×ˢ univ) →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ ≤
        C i * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2)
    {Cout Rout : ℝ}
    (hendOut : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ positiveEndChart inf '' (Ioi Rout ×ˢ univ) →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ ≤
        Cout * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 2 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} →
      (∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) +
        (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
          sobolevDensity ξ z ≤
        C' * ((∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a (T + 1),
            ‖ξ z‖ ^ 2) := by
  -- Index the ends by `Option ι`, with `none` the output end.
  let Ce : Option ι → ℝ := fun e ↦ e.elim Cout C
  let Re : Option ι → ℝ := fun e ↦ e.elim Rout R
  have hend' (e : Option ι) ⦃ξ : ℝ × ℝ → V⦄ (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
      (hξR : tsupport ξ ⊆ movingEndChart c a e '' (Ioi (Re e) ×ˢ univ)) :
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ movingEndChart c a e) ζ ≤
        Ce e * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 := by
    cases e with
    | none => exact hendOut hξ hξc hξR
    | some i => exact hend i hξ hξc hξR
  obtain ⟨C', hC', T, hT, hest⟩ := exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_le
    (K := movingEndsTruncation c a) (isCompact_movingEndsTruncation c a)
    (fun _ _ h ↦ movingEndsTruncation_mono c a h) (r := 2) (S := movingEndsDomain c) (R := Re)
    (G := fun e ξ ↦ ξ ∘ movingEndChart c a e) fun _ hR₀ hR ↦
      ω.exists_forall_sum_setIntegral_add_setIntegral_le_of_movingEnds_aux ha hsep hout hJ hKs hKt
        hu hc hend' (by linarith) hR
  refine ⟨C', hC', T, hT, fun ξ hξ hξc hξU ↦ ?_⟩
  have h := hest hξ hξc hξU
  rw [Fintype.sum_option] at h
  simp only [movingEndChart, movingEndsTruncation] at h
  linarith

/-- **The semi-Fredholm estimate on a sphere with moving input ends.** Let the discs
`‖w - c i‖ < ‖a i‖ / 2` of the input ends be pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, with nonzero scales, and let the Hamiltonians `H i` and `Hout` be jointly `C²`
of period one. For each input end `i`, let `x i` be an orbit of `H i` starting at a nondegenerate
fixed point of its time-one map and let `J_e i` be a `C¹` family of almost complex structures
compatible along `x i`; for the output end, let `x_out` and `J_out` be the same data for the
Hamiltonian `H'(t, y) = -Hout(-t, y)` of the output end read in its positive end chart. Let `J`
be `J_e i (t)` beyond `s = 2` in the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))` of each input
end and `J_out (t)` beyond `s = 2` in the positive end chart `φ'_∞` of the output end. Let `u`
and `J` along `u` be `C¹` on the sphere minus the centers `c i`, with `J` compatible along `u`
there, let `u` solve the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` beyond `s = 2` on each end, and let its loops
in the end charts converge uniformly to the orbits while the slice defects tend uniformly to zero.
Then there are `C ≥ 0` and `T ≥ 2` such that every `C²` section `ξ` with compact support in the
sphere minus the centers satisfies

`∑_i ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²)`
`  + ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²)`
`  + ∫_{Σ_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{Σ_{T + 1}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of these data, where `Σ_T` is the truncation
`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation c a T`. -/
theorem
exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds
    (ω : SymplecticForm V) {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {L : ι → ℝ≥0}
    (hX : ∀ i, LipschitzWith (L i) (ω.timeDependentHamiltonianSuspension (H i)))
    {x : ι → ℝ → V} (hx : ∀ i t, HasDerivAt (x i) (ω.hamiltonianVectorField (H i t) (x i t)) t)
    (hnd : ∀ i, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (H i) (hX i) 0 1) (x i 0))
    {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ i t, ω.Compatible (Je i t (x i t))) {Lout : ℝ≥0}
    (hXout : LipschitzWith Lout (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {xout : ℝ → V}
    (hxout : ∀ t, HasDerivAt xout (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (xout t)) t)
    (hndout : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hXout 0 1) (xout 0))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJoutx : ∀ t, ω.Compatible (Jout t (xout t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ω.Compatible (J z (u z)))
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 2 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} →
      (∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) +
        (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
          sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a (T + 1),
            ‖ξ z‖ ^ 2) := by
  -- Beyond `s = 0` an input end avoids every center.
  have hin (i : ι) (ζ : ℝ × ℝ) (hζ : 0 < ζ.1) (j : ι) : Complex.equivRealProdCLM.symm
      (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) ≠ c j := by
    rw [equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simpa using hζ) j
  choose C R _ hend using fun i ↦
    exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_movingEnds
      ω hH hHs hHout hHouts ha hsep hout i (hX i) (hx i) (hnd i) (hJe i) (hJex i) (hJeq i)
      (fun ζ hζ ↦ hJ _ (hin i ζ (by linarith))) (fun ζ hζ ↦ hu _ (hin i ζ (by linarith)))
      (hF i) (hux i) (hδ i)
  obtain ⟨Cout, Rout, -, hendOut⟩ :=
    exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization_of_movingEnds
      ω hH hHs hHout hHouts ha hout hXout hxout hndout hJout hJoutx hJoutq
      (fun ζ hζ ↦ hJ _ (equivRealProdCLM_symm_positiveEndChart_inf_ne hout (by linarith)))
      (fun ζ hζ ↦ hu _ (equivRealProdCLM_symm_positiveEndChart_inf_ne hout (by linarith))) hFout
      huxout hδout
  exact
    exists_forall_sum_setIntegral_add_le_mul_integral_floerLinearization_add_of_movingEnds_of_ends
      ω ha hsep hout hJ
      (fun z hz ↦ contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz _ 1)
      (fun z hz ↦ contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz _
        Complex.I) hu hc hend hendOut

end TauCeti.SymplecticForm

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type*} {c a : ι → ℂ}

/-- A `C¹` section with compact support in the sphere with moving input ends, the plane minus the
centers `c i`, has integrable `W^{1,2}` energy density in the chart
`ψ_i = realChart (z ↦ c i + a i φ₀(z))` of the input end `i`, over every half-cylinder
`(b, ∞) × [0, 1]`: it vanishes far out on the end. -/
theorem integrableOn_sobolevDensity_comp_realChart_of_movingEnds (ha : ∀ i, a i ≠ 0)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (i : ι) (b : ℝ) :
    IntegrableOn
      (sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z))
      (Ioi b ×ˢ Icc 0 1) :=
  SymplecticForm.integrableOn_sobolevDensity_comp_movingEndChart ha hξ hξc hξU (some i) b

/-- A `C¹` section with compact support in the sphere with moving input ends, the plane minus the
centers `c i`, has integrable `W^{1,2}` energy density in the positive end chart `φ'_∞` of the
output end, over every half-cylinder `(b, ∞) × [0, 1]`: it vanishes far out on the end. -/
theorem integrableOn_sobolevDensity_comp_positiveEndChart_of_movingEnds (ha : ∀ i, a i ≠ 0)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (b : ℝ) :
    IntegrableOn (sobolevDensity (ξ ∘ positiveEndChart inf)) (Ioi b ×ˢ Icc 0 1) :=
  SymplecticForm.integrableOn_sobolevDensity_comp_movingEndChart ha hξ hξc hξU none b

end TauCeti.Floer
