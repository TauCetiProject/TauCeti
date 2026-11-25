/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Wirtinger
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Area.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.MeasureTheory.Integral.Circle.LIntegral
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The isoperimetric inequality in a symplectic vector space

Let `V` be a finite-dimensional real inner product space carrying a symplectic form `ω` and an
almost complex structure `J` whose metric `ω(·, J ·)` is the inner product of `V`, as for the
standard triple `(ω₀, J₀, ⟪·, ·⟫)` on `ℝ²ⁿ`. The symplectic area enclosed by a loop
`γ : [a, b] → V` is `a(γ) = ½ ∫ ω(γ, γ')`: it is `∫ γ^*λ` for the primitive
`λ_x(v) = ½ ω(x, v)` of `ω`, hence the symplectic area of any disc bounding `γ`. The
**isoperimetric inequality** bounds it by the energy of the loop,

`|∫ x in a..b, ω (γ x) (γ' x)| ≤ (b - a) / (2π) * ∫ x in a..b, ‖γ' x‖ ^ 2`
(`TauCeti.SymplecticForm.abs_integral_apply_le`),

that is `|a(γ)| ≤ (b - a) / (4π) * ∫ ‖γ'‖²`. For a loop on `[0, 1]` traversed at constant speed
the right side is `ℓ(γ)² / (4π)`, where `ℓ(γ)` is the length; the constant is attained by round
circles in a complex line. This is the estimate behind removal of singularities for holomorphic
curves: the energy of a holomorphic curve `u` on a disc is the symplectic area enclosed by the
boundary loop `θ ↦ u(r e^{iθ})`, so it is bounded by the energy of that loop.

The inequality comes from Wirtinger's inequality
(`ContinuousLinearMap.norm_integral_apply_apply_le`) and the Cauchy--Schwarz bound
`|ω(v, w)| ≤ ‖v‖ ‖w‖` of a compatible triple (`TauCeti.SymplecticForm.abs_apply_le_norm_mul_norm`,
in `CompatibleMetric.lean`).

An arc whose endpoints lie in a subspace `L` on which `ω` vanishes satisfies the same inequality
with `(b - a) / π` in place of `(b - a) / (2π)`
(`TauCeti.SymplecticForm.abs_integral_apply_le_of_mem`): the action `∫ γ^*λ` of the arc is the
symplectic area of a surface bounded by the arc and a path in `L`. Applied to the boundary
half-circles of a half-annulus whose diameter is mapped into `L`, it bounds the symplectic area of
the half-annulus by the energies of the half-circles; this is the estimate behind removal of
boundary punctures of holomorphic curves with Lagrangian boundary conditions.

## Main results

* `TauCeti.SymplecticForm.abs_integral_apply_le`: the isoperimetric inequality.
* `TauCeti.SymplecticForm.abs_integral_fderiv_apply_annulus_le`: the area of an annulus is
  bounded by half the sum of the energies of its two boundary loops.
* `TauCeti.SymplecticForm.abs_integral_apply_le_of_mem`: the isoperimetric inequality for arcs
  with endpoints in an isotropic subspace.
* `TauCeti.SymplecticForm.abs_integral_fderivWithin_apply_upperHalfAnnulus_le`: the area of an
  upper half-annulus with isotropic diameter is bounded by half the sum of the energies of its two
  boundary half-circles.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Sections 4.4 and 4.5.
-/

public section

open MeasureTheory Set TauCeti
open scoped Real Interval RealInnerProductSpace

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {a b : ℝ}

/-- When the inner product of `V` is the metric `ω(·, J ·)`, the continuous bilinear map of `ω`
has operator norm at most one, so a bound `‖∫ B (f x) (f' x)‖ ≤ ‖B‖ * C` for it gives
`|∫ ω (f x) (f' x)| ≤ C`. -/
private theorem abs_integral_apply_le_of_norm_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {f f' : ℝ → V} {C : ℝ} (hC : 0 ≤ C)
    (h : ‖∫ x in a..b, ω.toBilinForm.toContinuousBilinearMap (f x) (f' x)‖ ≤
      ‖ω.toBilinForm.toContinuousBilinearMap‖ * C) :
    |∫ x in a..b, ω (f x) (f' x)| ≤ C := by
  simp only [LinearMap.toContinuousBilinearMap_apply, Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_left hC (norm_toContinuousBilinearMap_le_one hg))

/-- **The isoperimetric inequality.** If the inner product of `V` is the metric `ω(·, J ·)`, then
for a loop `γ` on `[a, b]` with square-integrable derivative, twice the symplectic area
`∫ ω(γ, γ')` it encloses is bounded by `(b - a) / (2π)` times its energy `∫ ‖γ'‖²`. -/
theorem abs_integral_apply_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hab : a < b) {γ γ' : ℝ → V}
    (hγ : ∀ x ∈ [[a, b]], HasDerivAt γ (γ' x) x) (hγab : γ a = γ b)
    (hγ' : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    |∫ x in a..b, ω (γ x) (γ' x)| ≤ (b - a) / (2 * π) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by
  have hE : 0 ≤ ∫ x in a..b, ‖γ' x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => by positivity
  refine abs_integral_apply_le_of_norm_le hg
    (mul_nonneg (div_nonneg (sub_nonneg.2 hab.le) (by positivity)) hE) ?_
  simpa only [mul_assoc] using
    ω.toBilinForm.toContinuousBilinearMap.norm_integral_apply_apply_le hab hγ hγab hγ'

/-- The absolute symplectic area of a `C²` map on an annulus is at most half the sum of the
energies of its boundary loops parametrized on `[-π, π]`. The map need not extend over the
inner disc, and no holomorphicity assumption is imposed. -/
theorem abs_integral_fderiv_apply_annulus_le {u : ℂ → V} (z₀ : ℂ)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z) :
    |∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I)| ≤
      (1 / 2 : ℝ) * ((∫ θ in -π..π,
        ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) +
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ a θ)) θ‖ ^ 2) := by
  have hloop (r : ℝ) (hr : r ∈ Icc a b) :
      |∫ θ in -π..π, ω (u (circleMap z₀ r θ))
        (deriv (fun θ ↦ u (circleMap z₀ r θ)) θ)| ≤
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2 := by
    have hmem (θ : ℝ) :
        circleMap z₀ r θ ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} :=
      circleMap_mem_setOf_le_norm_sub_le ha hr θ
    have hE : 0 ≤ ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ ↦ sq_nonneg _
    exact abs_integral_apply_le_of_norm_le hg hE <|
      norm_integral_apply_apply_circleMap_le u z₀ r fun θ ↦ (hu _ (hmem θ)).of_le one_le_two
  rw [ω.integral_fderiv_apply_annulus z₀ ha hab hu, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  gcongr
  exact (abs_sub _ _).trans (add_le_add (hloop b ⟨hab, le_rfl⟩)
    (hloop a ⟨le_rfl, hab⟩))

/-- **The isoperimetric inequality for arcs with isotropic boundary.** If the inner product of `V`
is the metric `ω(·, J ·)`, then for an arc `γ` on `[a, b]` with square-integrable derivative and
both endpoints in a subspace `L` on which `ω` vanishes, `|∫ ω(γ, γ')|` is bounded by
`(b - a) / π` times the energy `∫ ‖γ'‖²` of the arc. -/
theorem abs_integral_apply_le_of_mem (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hab : a < b)
    {L : Submodule ℝ V} (hL : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0) {γ γ' : ℝ → V}
    (hγc : ContinuousOn γ (Icc a b)) (hγ : ∀ x ∈ Ioo a b, HasDerivAt γ (γ' x) x)
    (hγ' : MemLp γ' 2 (volume.restrict (Ioc a b))) (ha : γ a ∈ L) (hb : γ b ∈ L) :
    |∫ x in a..b, ω (γ x) (γ' x)| ≤ (b - a) / π * ∫ x in a..b, ‖γ' x‖ ^ 2 := by
  have hE : 0 ≤ ∫ x in a..b, ‖γ' x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => by positivity
  refine abs_integral_apply_le_of_norm_le hg
    (mul_nonneg (div_nonneg (sub_nonneg.2 hab.le) Real.pi_pos.le) hE) ?_
  simpa only [mul_assoc] using
    ω.toBilinForm.toContinuousBilinearMap.norm_integral_apply_apply_le_of_mem
      (fun v hv w hw ↦ by simpa using hL v hv w hw) hab hγc hγ hγ' ha hb

/-- The action of a boundary half-circle `θ ↦ u (z₀ + r e^{iθ})`, `0 ≤ θ ≤ π`, of a map that is
`C²` up to the line `z.im = z₀.im` and sends it into a subspace `L` on which `ω` vanishes,
is bounded by the energy of the half-circle: the half-circle is an arc with endpoints in `L`. -/
private theorem abs_integral_apply_fderivWithin_circleMap_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {u : ℂ → V} {z₀ : ℂ} {O : Set ℂ} (hO : IsOpen O) {r : ℝ} (hr : 0 ≤ r)
    (hrO : ∀ θ ∈ Icc 0 π, circleMap z₀ r θ ∈ O)
    (hu : ContDiffOn ℝ 2 u ({z : ℂ | z₀.im ≤ z.im} ∩ O)) {L : Submodule ℝ V}
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0) (huL : ∀ z ∈ O, z.im = z₀.im → u z ∈ L) :
    |∫ θ in 0..π, ω (u (circleMap z₀ r θ))
      (fderivWithin ℝ u {z | z₀.im ≤ z.im} (circleMap z₀ r θ) (circleMap 0 r θ * Complex.I))| ≤
      ∫ θ in 0..π, ‖fderivWithin ℝ u {z | z₀.im ≤ z.im} (circleMap z₀ r θ)
        (circleMap 0 r θ * Complex.I)‖ ^ 2 := by
  set H : Set ℂ := {z | z₀.im ≤ z.im}
  set Du := fderivWithin ℝ u H
  have hDu : ContinuousOn Du (H ∩ O) :=
    hu.continuousOn_fderivWithin_of_inter (uniqueDiffOn_setOfPred_le_im _) hO
      (by norm_num)
  have hmem (θ : ℝ) (hθ : θ ∈ Icc 0 π) : circleMap z₀ r θ ∈ H ∩ O :=
    ⟨(circleMap_mem_upperHalfAnnulus hr ⟨le_rfl, le_rfl⟩ hθ).1, hrO θ hθ⟩
  have hend (θ : ℝ) (hθ : θ ∈ Icc 0 π) (hs : Real.sin θ = 0) : u (circleMap z₀ r θ) ∈ L :=
    huL _ (hrO θ hθ) (by rw [circleMap_im, hs, mul_zero, add_zero])
  have hcm : Continuous fun θ ↦ circleMap z₀ r θ := continuous_circleMap z₀ r
  have hγ'c : ContinuousOn
      (fun θ ↦ Du (circleMap z₀ r θ) (circleMap 0 r θ * Complex.I)) (Icc 0 π) :=
    (hDu.comp hcm.continuousOn hmem).clm_apply
      ((continuous_circleMap 0 r).mul continuous_const).continuousOn
  -- Inside the half-plane the one-sided derivative is the derivative.
  have hγd (θ : ℝ) (hθ : θ ∈ Ioo 0 π) : HasDerivAt (fun θ ↦ u (circleMap z₀ r θ))
      (Du (circleMap z₀ r θ) (circleMap 0 r θ * Complex.I)) θ := by
    rcases hr.eq_or_lt with rfl | hpos
    · simpa using hasDerivAt_const θ (u z₀)
    have hH : H ∈ nhds (circleMap z₀ r θ) := setOfPred_le_im_mem_nhds <| by
      rw [circleMap_im, lt_add_iff_pos_right]
      exact mul_pos hpos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    have hdu : HasFDerivAt u (Du (circleMap z₀ r θ)) (circleMap z₀ r θ) := by
      rw [show Du (circleMap z₀ r θ) = fderiv ℝ u (circleMap z₀ r θ) from
        fderivWithin_of_mem_nhds hH]
      exact ((hu.contDiffAt (Filter.inter_mem hH (hO.mem_nhds
        (hrO θ (Ioo_subset_Icc_self hθ))))).differentiableAt (by norm_num)).hasFDerivAt
    exact hdu.comp_hasDerivAt θ (hasDerivAt_circleMap z₀ r θ)
  have h := abs_integral_apply_le_of_mem hg Real.pi_pos hLω
    (hu.continuousOn.comp hcm.continuousOn hmem) hγd
    (hγ'c.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioc
      Ioc_subset_Icc_self 2) (hend 0 ⟨le_rfl, Real.pi_pos.le⟩ Real.sin_zero)
    (hend π ⟨Real.pi_pos.le, le_rfl⟩ Real.sin_pi)
  rwa [sub_zero, div_self Real.pi_ne_zero, one_mul] at h

/-- The absolute symplectic area of a map `u` on the closed upper half `S` of the annulus of radii
`0 ≤ a ≤ b` about `z₀` is at most half the sum of the energies of its two boundary half-circles
parametrized on `[0, π]`, if `u` is `C²` on `{z | z₀.im ≤ z.im} ∩ O` for an open set `O`
containing `S`, with derivatives taken within the closed half-plane, and maps the points of `O` on
the line `z.im = z₀.im` into a subspace `L` on which `ω` vanishes. No holomorphicity
assumption is imposed. -/
theorem abs_integral_fderivWithin_apply_upperHalfAnnulus_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {u : ℂ → V} (z₀ : ℂ) {O : Set ℂ} (hO : IsOpen O) (ha : 0 ≤ a) (hab : a ≤ b)
    (hSO : {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} ⊆ O)
    (hu : ContDiffOn ℝ 2 u ({z : ℂ | z₀.im ≤ z.im} ∩ O)) {L : Submodule ℝ V}
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0)
    (huL : ∀ z ∈ O, z.im = z₀.im → u z ∈ L) :
    |∫ z in {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      ω (fderivWithin ℝ u {z | z₀.im ≤ z.im} z 1)
        (fderivWithin ℝ u {z | z₀.im ≤ z.im} z Complex.I)| ≤
      (1 / 2 : ℝ) * ((∫ θ in 0..π, ‖fderivWithin ℝ u {z | z₀.im ≤ z.im} (circleMap z₀ b θ)
          (circleMap 0 b θ * Complex.I)‖ ^ 2) +
        ∫ θ in 0..π, ‖fderivWithin ℝ u {z | z₀.im ≤ z.im} (circleMap z₀ a θ)
          (circleMap 0 a θ * Complex.I)‖ ^ 2) := by
  -- The boundary half-circles lie in `O`.
  have hrO (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) (hθ : θ ∈ Icc 0 π) : circleMap z₀ r θ ∈ O :=
    hSO (circleMap_mem_upperHalfAnnulus ha hr hθ)
  rw [ω.integral_fderivWithin_apply_upperHalfAnnulus z₀ hO ha hab hSO hu hLω huL, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  gcongr
  exact (abs_sub _ _).trans (add_le_add
    (abs_integral_apply_fderivWithin_circleMap_le hg hO (ha.trans hab) (hrO b ⟨hab, le_rfl⟩) hu
      hLω huL)
    (abs_integral_apply_fderivWithin_circleMap_le hg hO ha (hrO a ⟨le_rfl, hab⟩) hu hLω huL))

end SymplecticForm

end TauCeti
