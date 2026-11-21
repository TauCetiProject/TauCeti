/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Convex.Star
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Normed.Group.LocallyBounded
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral.Segment
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.Convex.Topology
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# The Poincaré lemma for differential forms on star-convex sets

Let `s` be an open subset of a real normed space `E`, star-convex with respect to a point `x₀`,
and let `ω` be a `C¹` differential `(n + 1)`-form on `s` with values in a Banach space `F`. The
*Poincaré homotopy operator* (`TauCeti.poincareHomotopy`) contracts `ω` along the rays from `x₀`:

`(K ω)(x)(v₁, …, vₙ) = ∫₀¹ tⁿ ω(x₀ + t (x - x₀))(x - x₀, v₁, …, vₙ) dt`.

It satisfies the homotopy formula `d (K ω) + K (d ω) = ω` on `s`
(`StarConvex.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv`). Consequently every closed
`C¹` form of positive degree on `s` is exact: if `d ω = 0` on `s`, then `K ω` is a primitive of `ω`
(`StarConvex.extDeriv_poincareHomotopy`). The primitive is as smooth as `ω`
(`StarConvex.contDiffOn_poincareHomotopy`) and vanishes at `x₀` (`TauCeti.poincareHomotopy_self`).

The same holds relative to a convex set `s` with unique derivatives that need not be open, such as
a closed half-ball, the image of a boundary chart of a manifold with boundary. There the
derivatives are taken within `s`, and the homotopy formula reads
`extDerivWithin (K ω) s + K (extDerivWithin ω s) = ω` on `s`
(`Convex.extDerivWithin_poincareHomotopy_add_poincareHomotopy_extDerivWithin`). Differentiating
`K ω` within `s` uses Mathlib's mean value inequality along the segments of `s`, which is why the
relative statements ask for convexity rather than star-convexity. For a family of forms `ω q`
depending jointly `C^r` on a parameter `q` ranging over a convex set with unique derivatives, the
operators `K (ω q)` depend jointly `C^r` on `q` and the point
(`Convex.contDiffOn_uncurry_poincareHomotopy`), so that a smooth family of closed forms has a
smooth family of primitives.

Mathlib proves the Poincaré lemma for `1`-forms on convex sets by integrating along segments
(`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`); this file treats forms of every
positive degree with Mathlib's exterior derivative `extDeriv`. A smooth primitive vanishing at the
centre of a ball is what Moser's deformation argument integrates, for instance in the proof of
Darboux's theorem.

The homotopy formula is the integral over `t ∈ [0, 1]` of the identity
`d/dt (tⁿ⁺¹ ω(x₀ + t (x - x₀))) = tⁿ⁺¹ Dω(…)(x - x₀) + (n + 1) tⁿ ω(…)`, after the derivative
term is split by the constant-coefficient Cartan formula
`ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft`.

## Main declarations

* `TauCeti.poincareHomotopy`: the Poincaré homotopy operator with centre `x₀`.
* `TauCeti.poincareHomotopy_pullback_apply`: it commutes with pullback along a continuous linear
  map, which moves the centre.
* `StarConvex.compContinuousLinearMap_poincareHomotopy_eq`: centred at a fixed point of a linear
  map, it preserves invariance of forms under that map.
* `TauCeti.poincareHomotopy_apply_vecCons_sub_center`: it vanishes on the radial direction
  `x - x₀`.
* `TauCeti.norm_poincareHomotopy_le`: the sharp radial bound
  `‖poincareHomotopy x₀ ω x‖ ≤ B * ‖x - x₀‖ / (n + 1)`.
* `TauCeti.curryLeft_poincareHomotopy_sub_eq_zero`: `K ω` vanishes on the radial vector `x - x₀`.
* `StarConvex.norm_poincareHomotopy_sub_le`: a Lipschitz bound for `K ω` from bounds on `ω` and
  its Lipschitz constant.
* `StarConvex.isLocallyBoundedOn_poincareHomotopy`,
  `StarConvex.isLocallyBoundedOn_fderiv_poincareHomotopy`: families of forms bounded, with their
  derivatives, on compact subsets of `s` have Poincaré homotopies bounded, with their derivatives,
  on compact subsets of `s`.
* `TauCeti.norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le`,
  `TauCeti.exists_norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le`,
  `TauCeti.exists_norm_iteratedFDeriv_intervalIntegral_pow_smul_clm_apply_lineMap_le`,
  `TauCeti.exists_norm_iteratedFDeriv_smul_poincareHomotopy_le`: bounds on the spatial iterated
  derivatives of radial bilinear integrands, their `[0, 1]` integrals, and
  `y ↦ χ y • poincareHomotopy x₀ ω y`.
* `TauCeti.poincareHomotopy_eventuallyEq_zero_of_disjoint`: vanishing on a neighbourhood of any
  set whose segments from `x₀` miss `tsupport ω`.
* `StarConvex.contDiffOn_poincareHomotopy`, `TauCeti.contDiff_poincareHomotopy`: it preserves
  `C^r` regularity.
* `TauCeti.contDiff_poincareHomotopy_apply_zero`: on a `1`-form it gives a function
  `x ↦ (K ω)(x) ()`, as smooth as the form.
* `StarConvex.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv`,
  `TauCeti.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv`: the homotopy formula.
* `StarConvex.poincareHomotopy_extDerivWithin_eq_sub`,
  `StarConvex.poincareHomotopy_extDeriv_eq_sub`, `TauCeti.poincareHomotopy_extDeriv_eq_sub`: the
  degree-zero homotopy formula `K (d f) x = f x - f x₀`.
* `StarConvex.extDeriv_poincareHomotopy` and `StarConvex.exists_contDiffOn_forall_extDeriv_eq`: the
  Poincaré lemma, and `StarConvex.extDeriv_poincareHomotopy_extDeriv`: `d (K (d ω)) = d ω`.
* `Convex.contDiffOn_uncurry_poincareHomotopy`: on convex sets with unique derivatives, it
  depends jointly smoothly on parameters.
* `Convex.contDiffOn_poincareHomotopy`,
  `Convex.extDerivWithin_poincareHomotopy_add_poincareHomotopy_extDerivWithin`,
  `Convex.extDerivWithin_poincareHomotopy` and `Convex.exists_contDiffOn_forall_extDerivWithin_eq`:
  the relative versions on convex sets with unique derivatives.

## References

* M. Spivak, *Calculus on Manifolds*, Theorem 4-11, whose proof uses this homotopy operator.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17 (the Poincaré lemma).
-/

public section

noncomputable section

open AffineMap Filter MeasureTheory Set
open scoped Topology unitInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

namespace TauCeti

/-- The **Poincaré homotopy operator** with centre `x₀`: the `n`-form
`x ↦ ∫₀¹ tⁿ ω(x₀ + t (x - x₀))(x - x₀, ·) dt` built from a differential `(n + 1)`-form `ω`.
When `ω` is `C¹` on an open set star-convex with respect to `x₀` and takes values in a Banach
space, it satisfies `d (K ω) + K (d ω) = ω` there. -/
def poincareHomotopy (x₀ : E) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    E [⋀^Fin n]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀)

theorem poincareHomotopy_apply (x₀ : E) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    poincareHomotopy x₀ ω x =
      ∫ t in (0 : ℝ)..1, t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀) :=
  (rfl)

/-- The Poincaré homotopy operator vanishes at its centre. -/
@[simp]
theorem poincareHomotopy_self (x₀ : E) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F) :
    poincareHomotopy x₀ ω x₀ = 0 := by
  simp [poincareHomotopy_apply]

/-- The Poincaré homotopy operator at `x` only depends on the form along the segment `[x₀, x]`. -/
theorem poincareHomotopy_congr {x₀ x : E} {ω₁ ω₂ : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (h : EqOn ω₁ ω₂ (segment ℝ x₀ x)) : poincareHomotopy x₀ ω₁ x = poincareHomotopy x₀ ω₂ x := by
  rw [poincareHomotopy_apply, poincareHomotopy_apply]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  simp only [h (lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht))]

/-- The Poincaré homotopy operator of the zero form is zero. -/
@[simp]
theorem poincareHomotopy_zero (x₀ : E) :
    poincareHomotopy x₀ (0 : E → E [⋀^Fin (n + 1)]→L[ℝ] F) = 0 := by
  funext x
  simp [poincareHomotopy_apply]

/-- The Poincaré homotopy operator commutes with real scalar multiplication of forms. -/
theorem poincareHomotopy_smul (x₀ : E) (c : ℝ) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F) :
    poincareHomotopy x₀ (c • ω) = c • poincareHomotopy x₀ ω := by
  funext x
  simp only [poincareHomotopy_apply, Pi.smul_apply, ContinuousAlternatingMap.curryLeft_smul,
    smul_apply, ← intervalIntegral.integral_smul, smul_comm c]

/-- The integrand of the homotopy operator at `x` is interval integrable on `[0, 1]` when the
form is continuous along the segment `[x₀, x]`. -/
private theorem intervalIntegrable_integrand {x₀ x : E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (hω : ContinuousOn ω (segment ℝ x₀ x)) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀))
      volume 0 1 := by
  have hmaps : MapsTo (lineMap x₀ x) (uIcc (0 : ℝ) 1) (segment ℝ x₀ x) := fun _ ht ↦
    lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht)
  exact ((continuousOn_pow n).smul (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E)
    (F := F) (n := n)).toContinuousLinearMap.flip (x - x₀)).continuous.comp_continuousOn
      (hω.comp lineMap_continuous.continuousOn hmaps))).intervalIntegrable

/-- The Poincaré homotopy operator is additive on forms that are continuous along the segment
`[x₀, x]`. -/
theorem poincareHomotopy_add_apply {x₀ x : E} {ω₁ ω₂ : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (h₁ : ContinuousOn ω₁ (segment ℝ x₀ x)) (h₂ : ContinuousOn ω₂ (segment ℝ x₀ x)) :
    poincareHomotopy x₀ (ω₁ + ω₂) x = poincareHomotopy x₀ ω₁ x + poincareHomotopy x₀ ω₂ x := by
  rw [poincareHomotopy_apply, poincareHomotopy_apply, poincareHomotopy_apply,
    ← intervalIntegral.integral_add (intervalIntegrable_integrand h₁)
      (intervalIntegrable_integrand h₂)]
  simp only [Pi.add_apply, ContinuousAlternatingMap.curryLeft_add, add_apply,
    smul_add]

/-- The Poincaré homotopy operator vanishes on the radial direction: `K ω` at `x`, contracted
with `x - x₀`, is zero. -/
theorem poincareHomotopy_apply_vecCons_sub_center [CompleteSpace F] (x₀ : E)
    (ω : E → E [⋀^Fin (n + 2)]→L[ℝ] F) (x : E) (v : Fin n → E) :
    poincareHomotopy x₀ ω x (Matrix.vecCons (x - x₀) v) = 0 := by
  rw [poincareHomotopy_apply]
  by_cases hint : IntervalIntegrable
      (fun t : ℝ ↦ t ^ (n + 1) • (ω (lineMap x₀ x t)).curryLeft (x - x₀)) volume 0 1
  · rw [← ContinuousAlternatingMap.apply_apply (𝕜 := ℝ),
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    simp only [ContinuousAlternatingMap.apply_apply, ContinuousAlternatingMap.smul_apply,
      ← ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.curryLeft_same,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, smul_zero, intervalIntegral.integral_zero]
  · rw [intervalIntegral.integral_undef hint, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- The Poincaré homotopy operator at `x` is bounded in norm by `B * ‖x - x₀‖ / (n + 1)` whenever
the form is bounded by `B` along the segment `[x₀, x]`. -/
theorem norm_poincareHomotopy_le {x₀ x : E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F} {B : ℝ}
    (h : ∀ y ∈ segment ℝ x₀ x, ‖ω y‖ ≤ B) :
    ‖poincareHomotopy x₀ ω x‖ ≤ B * ‖x - x₀‖ / (n + 1) := by
  rw [poincareHomotopy_apply]
  have hle : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀)‖ ≤ (B * ‖x - x₀‖) * t ^ n := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ht0 _), mul_comm (t ^ n)]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg ht0 _)
    calc ‖(ω (lineMap x₀ x t)).curryLeft (x - x₀)‖
        ≤ ‖(ω (lineMap x₀ x t)).curryLeft‖ * ‖x - x₀‖ :=
          (ω (lineMap x₀ x t)).curryLeft.le_opNorm _
      _ = ‖ω (lineMap x₀ x t)‖ * ‖x - x₀‖ := by simp [ContinuousAlternatingMap.norm_curryLeft]
      _ ≤ B * ‖x - x₀‖ :=
          mul_le_mul_of_nonneg_right (h _ (lineMap_mem_segment ℝ x₀ x (Ioc_subset_Icc_self ht)))
            (norm_nonneg _)
  have hint : IntervalIntegrable (fun t : ℝ ↦ (B * ‖x - x₀‖) * t ^ n) volume 0 1 :=
    (continuousOn_const.mul (continuousOn_pow n)).intervalIntegrable
  calc ‖∫ t in (0 : ℝ)..1, t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀)‖
      ≤ ∫ t in (0 : ℝ)..1, (B * ‖x - x₀‖) * t ^ n :=
        intervalIntegral.norm_integral_le_of_norm_le zero_le_one (ae_of_all _ hle) hint
    _ = (B * ‖x - x₀‖) * ∫ t in (0 : ℝ)..1, t ^ n := intervalIntegral.integral_const_mul _ _
    _ = B * ‖x - x₀‖ / (n + 1) := by simp [integral_pow, div_eq_mul_inv]

/-- **The Poincaré homotopy operator is radial.** Contracting the form `K ω` at `x` with the
radial vector `x - x₀` gives zero, since the integrand already contains `x - x₀` in its first
slot. -/
@[simp]
theorem curryLeft_poincareHomotopy_sub_eq_zero (x₀ : E)
    (ω : E → E [⋀^Fin (n + 2)]→L[ℝ] F) (x : E) :
    (poincareHomotopy x₀ ω x).curryLeft (x - x₀) = 0 := by
  rw [poincareHomotopy_apply]
  by_cases hG : CompleteSpace (E [⋀^Fin (n + 1)]→L[ℝ] F)
  swap
  · simp [intervalIntegral, integral_of_not_completeSpace hG]
  by_cases h : IntervalIntegrable
      (fun t : ℝ ↦ t ^ (n + 1) • (ω (lineMap x₀ x t)).curryLeft (x - x₀)) volume 0 1
  · let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
      (n := n)).toContinuousLinearMap.flip (x - x₀)
    have hL (f : E [⋀^Fin (n + 1)]→L[ℝ] F) : L f = f.curryLeft (x - x₀) := by simp [L]
    -- The codomain of `L` need not be complete, so commute the integral in its completion.
    have key := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
      (F := UniformSpace.Completion (E [⋀^Fin n]→L[ℝ] F))
      (UniformSpace.Completion.toComplL.comp L) h
    simp only [ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL, hL,
      ContinuousAlternatingMap.curryLeft_smul, smul_apply,
      ContinuousAlternatingMap.curryLeft_same, smul_zero, UniformSpace.Completion.coe_zero,
      intervalIntegral.integral_zero] at key
    exact UniformSpace.Completion.coe_injective _
      (key.symm.trans UniformSpace.Completion.coe_zero.symm)
  · rw [intervalIntegral.integral_undef h]
    simp

/-- Pointwise `m`-th spatial derivative bound for a radial bilinear integrand
`z ↦ t ^ k • L (f (lineMap x₀ z t)) (V z)` with `t ∈ [0, 1]`. -/
theorem norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le
    {G E' H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x₀ : E) (k : ℕ) (L : G →L[ℝ] E' →L[ℝ] H)
    {V : E → E'} {m : ℕ} (hV : ContDiff ℝ m V) {M : ℕ → ℝ} {y : E}
    (hM : ∀ j ≤ m, ‖iteratedFDeriv ℝ j V y‖ ≤ M j)
    {f : E → G} (hf : ContDiff ℝ m f) {D : ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hD : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (lineMap x₀ y t)‖ ≤ D) :
    ‖iteratedFDeriv ℝ m (fun z ↦ t ^ k • L (f (lineMap x₀ z t)) (V z)) y‖ ≤
      (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (‖L‖ * M (m - j))) * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (Nat.zero_le _))
  have ht_id : ‖t • ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_right ht.1 ContinuousLinearMap.norm_id_le).trans ht.2
  have htk_id : ‖(t ^ k) • ContinuousLinearMap.id ℝ H‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ht.1 _)]
    exact (mul_le_of_le_one_right (pow_nonneg ht.1 _) ContinuousLinearMap.norm_id_le).trans
      (pow_le_one₀ ht.1 ht.2)
  have hray_cont : ContDiff ℝ m (fun z ↦ f (lineMap x₀ z t)) := by
    simp only [lineMap_apply_module']
    exact hf.comp (((contDiff_id.sub contDiff_const).const_smul t).add contDiff_const)
  -- Bound the derivatives of `z ↦ L (f (lineMap x₀ z t))` using `0 ≤ t ≤ 1`.
  have hray_norm {j : ℕ} (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fun z ↦ L (f (lineMap x₀ z t))) y‖ ≤ ‖L‖ * D := by
    have hj' : (j : WithTop ℕ∞) ≤ m := by exact_mod_cast hj
    have hcompL : (fun z ↦ L (f (lineMap x₀ z t))) = L ∘ (fun z ↦ f (lineMap x₀ z t)) := rfl
    rw [hcompL]
    refine (L.norm_iteratedFDeriv_comp_left hray_cont.contDiffAt hj').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg L)
    have hshift : ContDiff ℝ m (fun z ↦ f (z + (1 - t) • x₀)) :=
      hf.comp (contDiff_id.add contDiff_const)
    have hline : (fun z ↦ f (lineMap x₀ z t)) =
        (fun z ↦ f (z + (1 - t) • x₀)) ∘ (t • ContinuousLinearMap.id ℝ E) := by
      funext z
      simp [lineMap_apply_module, add_comm]
    have hpt : (t • ContinuousLinearMap.id ℝ E) y + (1 - t) • x₀ = lineMap x₀ y t := by
      simp [lineMap_apply_module, add_comm]
    rw [hline, (t • ContinuousLinearMap.id ℝ E).iteratedFDeriv_comp_right hshift y hj',
      iteratedFDeriv_comp_add_right, hpt]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hD j hj)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) ht_id
  -- Apply the Leibniz bound to `z ↦ L (f (lineMap x₀ z t)) (V z)` and absorb `t ^ k`.
  have hu_eq : (fun z ↦ t ^ k • L (f (lineMap x₀ z t)) (V z)) =
      ((t ^ k) • ContinuousLinearMap.id ℝ H) ∘ fun z ↦ L (f (lineMap x₀ z t)) (V z) := by
    funext z
    simp
  have hclm_cont : ContDiff ℝ m (fun z ↦ L (f (lineMap x₀ z t)) (V z)) :=
    (L.contDiff.comp hray_cont).clm_apply hV
  rw [hu_eq]
  refine (((t ^ k) • ContinuousLinearMap.id ℝ H).norm_iteratedFDeriv_comp_left
    hclm_cont.contDiffAt le_rfl).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) htk_id).trans ?_
  refine (norm_iteratedFDeriv_clm_apply (L.contDiff.comp hray_cont) hV y le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  calc (m.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun z ↦ L (f (lineMap x₀ z t))) y‖ *
        ‖iteratedFDeriv ℝ (m - j) V y‖
      ≤ (m.choose j : ℝ) * (‖L‖ * D) * M (m - j) := by
        gcongr
        exacts [hray_norm hjm, hM (m - j) (Nat.sub_le m j)]
    _ = (m.choose j : ℝ) * (‖L‖ * M (m - j)) * D := by ring

/-- **Global derivative domination for a compactly supported radial bilinear integrand.** If `V`
is `C^i` with compact support and `f` is `C^i`, then the spatial derivatives of
`y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)` of order at most `i` are bounded uniformly in
`t ∈ [0, 1]` and `z : E`. -/
theorem exists_norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le
    {G E' H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x₀ : E) (k : ℕ) (L : G →L[ℝ] E' →L[ℝ] H)
    {V : E → E'} {i : ℕ} (hV : ContDiff ℝ i V) (hVc : HasCompactSupport V)
    {f : E → G} (hf : ContDiff ℝ i f) :
    ∃ C : ℝ, ∀ m ≤ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z,
      ‖iteratedFDeriv ℝ m (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) z‖ ≤ C := by
  -- Bound the derivatives of the compactly supported factor `V` globally on `E`.
  have hVbd : ∀ m ≤ i, ∃ M : ℝ, ∀ y, ‖iteratedFDeriv ℝ m V y‖ ≤ M := fun m hm ↦
    Continuous.bounded_above_of_compact_support
      (hV.continuous_iteratedFDeriv (by exact_mod_cast hm)) (hVc.iteratedFDeriv m)
  choose! M hM using hVbd
  have hM0 {m : ℕ} (hm : m ≤ i) : 0 ≤ M m := (norm_nonneg _).trans (hM m hm x₀)
  -- Bound the derivatives of `f` on the compact cone over `tsupport V`.
  let K' : Set E := ⋃ y ∈ tsupport V, segment ℝ x₀ y
  have hK' : IsCompact K' := hVc.biUnion_segment x₀
  have hfbd : ∀ j ≤ i, ∃ Cf : ℝ, ∀ z ∈ K', ‖iteratedFDeriv ℝ j f z‖ ≤ Cf := fun j hj ↦
    hK'.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn
  choose! Cf hCf using hfbd
  let Df : ℝ := ∑ j ∈ Finset.range (i + 1), |Cf j|
  have hDf0 : 0 ≤ Df := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hDf {j : ℕ} (hj : j ≤ i) {z : E} (hz : z ∈ K') : ‖iteratedFDeriv ℝ j f z‖ ≤ Df :=
    (hCf j hj z hz).trans <| (le_abs_self _).trans <|
      Finset.single_le_sum (f := fun j ↦ |Cf j|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  let A (m : ℕ) : ℝ := ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (‖L‖ * M (m - j))
  have hA0 {m : ℕ} (hm : m ≤ i) : 0 ≤ A m :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (norm_nonneg L) (hM0 ((Nat.sub_le m j).trans hm)))
  refine ⟨∑ m ∈ Finset.range (i + 1), A m * Df, fun m hm t ht z ↦ ?_⟩
  have hm_le : A m * Df ≤ ∑ n ∈ Finset.range (i + 1), A n * Df :=
    Finset.single_le_sum
      (fun n hn ↦ mul_nonneg (hA0 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))) hDf0)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
  by_cases hz : z ∈ tsupport V
  · exact (norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le x₀ k L
      (hV.of_le (by exact_mod_cast hm)) (fun j hj ↦ hM j (hj.trans hm) z)
      (hf.of_le (by exact_mod_cast hm)) ht
      (fun j hj ↦ hDf (hj.trans hm) (mem_biUnion hz (lineMap_mem_segment ℝ x₀ z ht)))).trans hm_le
  · -- Off `tsupport V`, the integrand vanishes in a neighbourhood of `z`, so its derivatives do.
    have hu_tsup : tsupport (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) ⊆ tsupport V :=
      closure_minimal (Function.support_subset_iff'.2 fun w hw ↦ by
        simp [image_eq_zero_of_notMem_tsupport hw]) (isClosed_tsupport V)
    have hu0 : iteratedFDeriv ℝ m (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) z = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem ↦
        hz (hu_tsup (tsupport_iteratedFDeriv_subset m hmem))
    rw [hu0, norm_zero]
    exact (mul_nonneg (hA0 hm) hDf0).trans hm_le

/-- **Spatial derivative bound for a compactly supported radial bilinear interval integral.**
If `V` is `C^i` with compact support, there exists `A ≥ 0` such that for every `C^i` map `f` whose
derivatives of order at most `i` are bounded by `B` along `[x₀, x]`, the `i`-th derivative of
`y ↦ ∫ t in 0..1, t ^ k • L (f (lineMap x₀ y t)) (V y)` at `x` has norm at most `A * B`. -/
theorem exists_norm_iteratedFDeriv_intervalIntegral_pow_smul_clm_apply_lineMap_le
    {G E' H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (x₀ : E) (k : ℕ) (L : G →L[ℝ] E' →L[ℝ] H)
    {V : E → E'} {i : ℕ} (hV : ContDiff ℝ i V) (hVc : HasCompactSupport V) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {f : E → G}, ContDiff ℝ i f →
        ∀ {x : E} {B : ℝ},
          (∀ j ≤ i, ∀ z ∈ segment ℝ x₀ x, ‖iteratedFDeriv ℝ j f z‖ ≤ B) →
          ‖iteratedFDeriv ℝ i
            (fun y ↦ ∫ t in (0 : ℝ)..1, t ^ k • L (f (lineMap x₀ y t)) (V y)) x‖ ≤
            A * B := by
  have hVbd : ∀ j ≤ i, ∃ M : ℝ, ∀ y, ‖iteratedFDeriv ℝ j V y‖ ≤ M := fun j hj ↦
    Continuous.bounded_above_of_compact_support
      (hV.continuous_iteratedFDeriv (by exact_mod_cast hj)) (hVc.iteratedFDeriv j)
  choose! M hM using hVbd
  have hM0 {j : ℕ} (hj : j ≤ i) : 0 ≤ M j := (norm_nonneg _).trans (hM j hj x₀)
  let A : ℝ := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (‖L‖ * M (i - j))
  have hA0 : 0 ≤ A :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (norm_nonneg L) (hM0 (Nat.sub_le i j)))
  refine ⟨A, hA0, fun {f} hf {x B} hB ↦ ?_⟩
  -- Joint smoothness and global derivative domination justify differentiating under the integral.
  have hG : ContDiff ℝ i (fun p : ℝ × E ↦ p.1 ^ k • L (f (lineMap x₀ p.2 p.1)) (V p.2)) := by
    have hline_p : ContDiff ℝ i (fun p : ℝ × E ↦ lineMap x₀ p.2 p.1) := by
      simp only [lineMap_apply_module']
      exact (contDiff_fst.smul (contDiff_snd.sub contDiff_const)).add contDiff_const
    exact (contDiff_fst.pow k).smul ((L.contDiff.comp (hf.comp hline_p)).clm_apply
      (hV.comp contDiff_snd))
  have hcont {m : ℕ} (hm : m ≤ i) (z : E) :
      Continuous fun t : ℝ ↦
        iteratedFDeriv ℝ m (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) z :=
    (_root_.ContDiff.continuous_iteratedFDeriv_prod_right hG m (by exact_mod_cast hm)).comp
      (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le x₀ k L hV hVc hf
  have hub (m : ℕ) (hm : m ≤ i) :
      ∀ᵐ t ∂volume.restrict (uIoc (0 : ℝ) 1), ∀ z,
        ‖iteratedFDeriv ℝ m (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) z‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_uIoc, uIoc_of_le zero_le_one]
    exact Eventually.of_forall fun t ht z ↦ hC m hm t (Ioc_subset_Icc_self ht) z
  rw [iteratedFDeriv_intervalIntegral (μ := volume) (a := 0) (b := 1)
    (u := fun t y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) (N := i)
    (Eventually.of_forall fun t ↦ hG.comp (contDiff_const.prodMk contDiff_id))
    (fun m hm z ↦ (hcont hm z).aestronglyMeasurable)
    (bound := fun _ _ ↦ C) (fun _ _ ↦ intervalIntegrable_const) hub le_rfl]
  -- Apply the sharp pointwise derivative bound at `x` along `[x₀, x]`.
  have hle : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ i (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) x‖ ≤ A * B :=
    fun t ht ↦ by
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
      exact norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le x₀ k L hV (fun j hj ↦ hM j hj x)
        hf ht' (fun j hj ↦ hB j hj _ (lineMap_mem_segment ℝ x₀ x ht'))
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hle

/-- For a compactly supported `C^i` scalar function `χ`, there exists a constant `A ≥ 0` such that
for every `C^i` differential `(k + 1)`-form `ω` whose derivatives of order at most `i` are bounded
by `B` along the segment `[x₀, x]`, the `i`-th derivative of `y ↦ χ y • poincareHomotopy x₀ ω y`
at `x` has norm at most `A * B`. -/
theorem exists_norm_iteratedFDeriv_smul_poincareHomotopy_le [CompleteSpace F]
    (x₀ : E) (k : ℕ) {χ : E → ℝ} {i : ℕ} (hχ : ContDiff ℝ i χ)
    (hχc : HasCompactSupport χ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] F}, ContDiff ℝ i ω →
        ∀ {x : E} {B : ℝ},
          (∀ j ≤ i, ∀ z ∈ segment ℝ x₀ x, ‖iteratedFDeriv ℝ j ω z‖ ≤ B) →
          ‖iteratedFDeriv ℝ i (fun y ↦ χ y • poincareHomotopy x₀ ω y) x‖ ≤ A * B := by
  let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := k)).toContinuousLinearMap
  obtain ⟨A, hA0, hA⟩ :=
    exists_norm_iteratedFDeriv_intervalIntegral_pow_smul_clm_apply_lineMap_le x₀ k L
      (V := fun y ↦ χ y • (y - x₀)) (hχ.smul (contDiff_id.sub contDiff_const)) hχc.smul_right
  refine ⟨A, hA0, fun {ω} hω {x B} hB ↦ ?_⟩
  have heq : (fun y ↦ χ y • poincareHomotopy x₀ ω y) =
      fun y ↦ ∫ t in (0 : ℝ)..1, t ^ k • L (ω (lineMap x₀ y t)) (χ y • (y - x₀)) := by
    funext y
    rw [poincareHomotopy_apply, ← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp [L, smul_comm (χ y)]
  rw [heq]
  exact hA hω hB

/-- If the topological support of `ω` is disjoint from every segment `[x₀, x]` for `x ∈ s`, then
`poincareHomotopy x₀ ω` vanishes on a neighbourhood of `s`, with no compactness assumption on `s`
or `tsupport ω`. -/
theorem poincareHomotopy_eventuallyEq_zero_of_disjoint {x₀ : E} {s : Set E}
    {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (h : Disjoint (tsupport ω) (⋃ x ∈ s, segment ℝ x₀ x)) :
    poincareHomotopy x₀ ω =ᶠ[𝓝ˢ s] 0 := by
  filter_upwards [(isClosed_tsupport ω).eventually_disjoint_segment h] with y hy
  rw [Pi.zero_apply, poincareHomotopy_congr (ω₂ := 0) fun z hz ↦
    image_eq_zero_of_notMem_tsupport (hy.notMem_of_mem_right hz), poincareHomotopy_zero,
    Pi.zero_apply]

/-- **Naturality of the Poincaré homotopy operator.** Contracting the pullback of a form along a
continuous linear map `A` along the rays from `y₀` is the same as pulling back the contraction of
the form along the rays from `A y₀`. In particular, if `A` fixes the centre, the operator commutes
with pullback along `A`. -/
theorem poincareHomotopy_pullback_apply {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [CompleteSpace (E [⋀^Fin n]→L[ℝ] F)] [CompleteSpace (E' [⋀^Fin n]→L[ℝ] F)]
    (A : E →L[ℝ] E') {y₀ x : E} {ω : E' → E' [⋀^Fin (n + 1)]→L[ℝ] F}
    (hω : ContinuousOn ω (segment ℝ (A y₀) (A x))) :
    poincareHomotopy y₀ (fun y ↦ (ω (A y)).compContinuousLinearMap A) x =
      (poincareHomotopy (A y₀) ω (A x)).compContinuousLinearMap A := by
  have hline (t : ℝ) : A (lineMap y₀ x t) = lineMap (A y₀) (A x) t := by
    simp [lineMap_apply_module']
  rw [poincareHomotopy_apply, poincareHomotopy_apply,
    ← ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (intervalIntegrable_integrand hω)]
  simp [hline]

/-- The integrand of the homotopy operator of a family of forms `ω q` is as smooth as the family,
jointly in the parameter `q`, the point `x` and the time `t`, on the set of triples with
`(q, x₀ + t (x - x₀)) ∈ W`. -/
private theorem contDiffOn_uncurry_integrand {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {x₀ : E} {W : Set (P × E)} {ω : P → E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    {r : WithTop ℕ∞} (hω : ContDiffOn ℝ r (Function.uncurry ω) W) :
    ContDiffOn ℝ r (fun p : (P × E) × ℝ ↦ (ω p.1.1 (lineMap x₀ p.1.2 p.2)).curryLeft (p.1.2 - x₀))
      {p : (P × E) × ℝ | (p.1.1, lineMap x₀ p.1.2 p.2) ∈ W} := by
  have hcomp : ContDiffOn ℝ r (fun p : (P × E) × ℝ ↦ ω p.1.1 (lineMap x₀ p.1.2 p.2))
      {p : (P × E) × ℝ | (p.1.1, lineMap x₀ p.1.2 p.2) ∈ W} :=
    hω.comp ((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_const.lineMap (contDiff_snd.comp contDiff_fst) contDiff_snd)).contDiffOn
      fun _ hp ↦ hp
  exact (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap.contDiff.comp_contDiffOn hcomp |>.clm_apply
      (((contDiff_snd.comp contDiff_fst).sub contDiff_const).contDiffOn)

/-- The integrand of the homotopy operator is as smooth as the form, on the set of pairs
`(x, t)` with `x₀ + t (x - x₀) ∈ s`. This is the constant family case of
`contDiffOn_uncurry_integrand`. -/
private theorem contDiffOn_integrand {x₀ : E} {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    {r : WithTop ℕ∞} (hω : ContDiffOn ℝ r ω s) :
    ContDiffOn ℝ r (fun p : E × ℝ ↦ (ω (lineMap x₀ p.1 p.2)).curryLeft (p.1 - x₀))
      {p : E × ℝ | lineMap x₀ p.1 p.2 ∈ s} := by
  have hω' : ContDiffOn ℝ r (Function.uncurry fun _ : ℝ ↦ ω) (univ ×ˢ s) :=
    hω.comp contDiff_snd.contDiffOn fun _ hp ↦ hp.2
  have hg : ContDiff ℝ r fun p : E × ℝ ↦ (((0 : ℝ), p.1), p.2) :=
    (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
  -- Elaborated before matching the goal: unifying the composite with the goal directly is slow.
  have h := (contDiffOn_uncurry_integrand (x₀ := x₀) hω').comp hg.contDiffOn
    (s := {p : E × ℝ | lineMap x₀ p.1 p.2 ∈ s}) fun _ hp ↦ ⟨mem_univ _, hp⟩
  exact h

/-- The partial derivative in `x` of the integrand of the homotopy operator at a parameter `t`,
within a set `u` that `x' ↦ x₀ + t (x' - x₀)` maps into a set `v` on which `ω` has derivative
`ω'` at `x₀ + t (x - x₀)`. -/
private theorem hasFDerivWithinAt_integrand {x₀ : E} {u v : Set E}
    {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F} {ω' : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] F} {x : E} {t : ℝ}
    (hω : HasFDerivWithinAt ω ω' v (lineMap x₀ x t))
    (huv : MapsTo (fun x' ↦ lineMap x₀ x' t) u v) :
    HasFDerivWithinAt (fun x' ↦ (ω (lineMap x₀ x' t)).curryLeft (x' - x₀))
      (t • ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
          (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L ω') +
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
          (n := n)).toContinuousLinearMap (ω (lineMap x₀ x t))) u x := by
  set L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap
  have hray : HasFDerivAt (fun x' ↦ lineMap x₀ x' t) (t • ContinuousLinearMap.id ℝ E) x := by
    simp only [lineMap_apply_module']
    exact (((hasFDerivAt_id x).sub_const x₀).const_smul t).add_const x₀
  refine (L.hasFDerivWithinAt_of_bilinear (hω.comp x hray.hasFDerivWithinAt huv)
    ((hasFDerivAt_id x).sub_const x₀).hasFDerivWithinAt).congr_fderiv ?_
  ext h v
  simp [L, add_comm]

end TauCeti

open TauCeti

namespace StarConvex

variable {x₀ : E} {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}

/-- **The Poincaré homotopy operator preserves invariance.** Let `A` be a continuous linear map
fixing `x₀` and mapping a set `s`, star-convex with respect to `x₀`, into itself. If a form `ω`,
continuous on `s`, satisfies `A^* ω = ω` on `s`, then so does its Poincaré homotopy operator
centred at `x₀`. -/
theorem compContinuousLinearMap_poincareHomotopy_eq (hs : StarConvex ℝ x₀ s)
    (hωc : ContinuousOn ω s) {A : E →L[ℝ] E} (hAx₀ : A x₀ = x₀) (hAs : MapsTo A s s)
    (hω : ∀ y ∈ s, (ω (A y)).compContinuousLinearMap A = ω y) {x : E} (hx : x ∈ s) :
    (poincareHomotopy x₀ ω (A x)).compContinuousLinearMap A = poincareHomotopy x₀ ω x := by
  have hseg : segment ℝ (A x₀) (A x) ⊆ s := by rw [hAx₀]; exact hs.segment_subset (hAs hx)
  by_cases hG : CompleteSpace (E [⋀^Fin n]→L[ℝ] F)
  swap
  · -- without completeness every integral vanishes by convention
    simp only [poincareHomotopy_apply, intervalIntegral.integral_of_le zero_le_one,
      integral_of_not_completeSpace hG]
    ext
    simp
  calc (poincareHomotopy x₀ ω (A x)).compContinuousLinearMap A
      = (poincareHomotopy (A x₀) ω (A x)).compContinuousLinearMap A := by rw [hAx₀]
    _ = poincareHomotopy x₀ (fun y ↦ (ω (A y)).compContinuousLinearMap A) x :=
        (poincareHomotopy_pullback_apply A (hωc.mono hseg)).symm
    _ = poincareHomotopy x₀ ω x :=
        poincareHomotopy_congr fun y hy ↦ hω y (hs.segment_subset hx hy)

/-- The Poincaré homotopy operator of a `C^r` form on an open star-convex set is `C^r` there. -/
theorem contDiffOn_poincareHomotopy (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {r : ℕ∞}
    (hω : ContDiffOn ℝ r ω s) : ContDiffOn ℝ r (poincareHomotopy x₀ ω) s := by
  have hpow : Integrable (fun t : I ↦ (t : ℝ) ^ n) volume :=
    (continuous_subtypeVal.pow n).integrable_of_hasCompactSupport (.of_compactSpace _)
  refine (contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    hpow continuous_subtypeVal
    (hso.preimage (by fun_prop : Continuous fun p : E × ℝ ↦ lineMap x₀ p.1 p.2))
    (contDiffOn_integrand hω) fun x hx t ↦
      hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x t.property)).congr
      fun x _ ↦ ?_
  rw [poincareHomotopy_apply, intervalIntegral_eq_integral_unitInterval]

/-- **Lipschitz bound for the Poincaré homotopy operator.** If `ω` is bounded by `B` and
`L`-Lipschitz on a set `s` star-convex with respect to `x₀`, then for `x, y ∈ s`

`‖K ω x - K ω y‖ ≤ (L ‖x - x₀‖ / (n + 2) + B / (n + 1)) ‖x - y‖`.

The points `x₀ + t (x - x₀)` and `x₀ + t (y - x₀)` at which the integrands are evaluated differ by
`t (x - y)`. -/
theorem norm_poincareHomotopy_sub_le (hs : StarConvex ℝ x₀ s) {B : ℝ} {L : NNReal}
    (hB : ∀ z ∈ s, ‖ω z‖ ≤ B) (hL : LipschitzOnWith L ω s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖poincareHomotopy x₀ ω x - poincareHomotopy x₀ ω y‖ ≤
      (L * ‖x - x₀‖ / (n + 2) + B / (n + 1)) * ‖x - y‖ := by
  have hseg {z : E} (hz : z ∈ s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : lineMap x₀ z t ∈ s :=
    hs.segment_subset hz (lineMap_mem_segment ℝ x₀ z ht)
  have hcont {z : E} (hz : z ∈ s) : ContinuousOn ω (segment ℝ x₀ z) :=
    hL.continuousOn.mono (hs.segment_subset hz)
  rw [poincareHomotopy_apply, poincareHomotopy_apply, ← intervalIntegral.integral_sub
    (intervalIntegrable_integrand (hcont hx)) (intervalIntegrable_integrand (hcont hy))]
  have hle : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖t ^ n • (ω (lineMap x₀ x t)).curryLeft (x - x₀) -
          t ^ n • (ω (lineMap x₀ y t)).curryLeft (y - x₀)‖ ≤
        (L * ‖x - x₀‖ * ‖x - y‖) * t ^ (n + 1) + (B * ‖x - y‖) * t ^ n := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hdist : ‖lineMap x₀ x t - lineMap x₀ y t‖ = t * ‖x - y‖ := by
      rw [lineMap_apply_module, lineMap_apply_module, add_sub_add_left_eq_sub, ← smul_sub,
        norm_smul, Real.norm_of_nonneg ht0]
    have hω : ‖ω (lineMap x₀ x t) - ω (lineMap x₀ y t)‖ ≤ L * (t * ‖x - y‖) := by
      rw [← dist_eq_norm, ← hdist, ← dist_eq_norm]
      exact hL.dist_le_mul _ (hseg hx htI) _ (hseg hy htI)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (pow_nonneg ht0 _)]
    calc t ^ n * ‖(ω (lineMap x₀ x t)).curryLeft (x - x₀) -
            (ω (lineMap x₀ y t)).curryLeft (y - x₀)‖
        ≤ t ^ n * (L * (t * ‖x - y‖) * ‖x - x₀‖ + B * ‖x - y‖) := by
          refine mul_le_mul_of_nonneg_left
            ((ContinuousAlternatingMap.norm_curryLeft_sub_curryLeft_le _ _ _ _).trans
              (add_le_add (mul_le_mul_of_nonneg_right hω (norm_nonneg _)) ?_)) (pow_nonneg ht0 _)
          rw [sub_sub_sub_cancel_right]
          exact mul_le_mul_of_nonneg_right (hB _ (hseg hy htI)) (norm_nonneg _)
      _ = (L * ‖x - x₀‖ * ‖x - y‖) * t ^ (n + 1) + (B * ‖x - y‖) * t ^ n := by ring
  have hpow (c : ℝ) (k : ℕ) : IntervalIntegrable (fun t : ℝ ↦ c * t ^ k) volume 0 1 :=
    (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one (ae_of_all _ hle)
    ((hpow _ _).add (hpow _ _))).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (hpow _ _) (hpow _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  push_cast
  field_simp
  ring

/-- **Local bounds for the Poincaré homotopy operator.** If a family of forms is bounded on each
compact subset of a set `s` star-convex with respect to `x₀`, uniformly in the index, then so is
the family of their Poincaré homotopies with centre `x₀`. -/
theorem isLocallyBoundedOn_poincareHomotopy (hs : StarConvex ℝ x₀ s) {ι : Type*}
    {f : ι → E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hf : IsLocallyBoundedOn f s) :
    IsLocallyBoundedOn (fun i ↦ poincareHomotopy x₀ (f i)) s := by
  refine isLocallyBoundedOn_def.2 fun K hKs hK ↦ ?_
  obtain ⟨B, hB⟩ := isLocallyBoundedOn_def.1 hf _ (hs.convexJoin_singleton_subset hKs)
    (isCompact_singleton.convexJoin hK)
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (continuous_id.sub continuous_const).norm.continuousOn
  refine ⟨max B 0 * R / (n + 1), fun i x hx ↦ ?_⟩
  have hR' : ‖x - x₀‖ ≤ R := by simpa using hR x hx
  refine (norm_poincareHomotopy_le fun y hy ↦ (hB i y
    (segment_subset_convexJoin (mem_singleton x₀) hx hy)).trans (le_max_left B 0)).trans ?_
  gcongr

open Metric in
/-- **Local derivative bounds for the Poincaré homotopy operator.** If a family of differentiable
forms on an open set `s` star-convex with respect to `x₀` is bounded, together with its
derivatives, on each compact subset of `s`, uniformly in the index, then so are the derivatives of
their Poincaré homotopies with centre `x₀`. Near a point `x` the homotopies are Lipschitz on the
cone over a small ball about `x` (`StarConvex.norm_poincareHomotopy_sub_le`). -/
theorem isLocallyBoundedOn_fderiv_poincareHomotopy [ProperSpace E] (hs : StarConvex ℝ x₀ s)
    (hso : IsOpen s) {ι : Type*} {f : ι → E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (hf : ∀ i, DifferentiableOn ℝ (f i) s) (hfb : IsLocallyBoundedOn f s)
    (hDf : IsLocallyBoundedOn (fun i ↦ fderiv ℝ (f i)) s) :
    IsLocallyBoundedOn (fun i ↦ fderiv ℝ (poincareHomotopy x₀ (f i))) s := by
  refine isLocallyBoundedOn_def.2 fun K hKs hK ↦ ?_
  obtain ⟨δ, hδ, hδs⟩ := hK.exists_cthickening_subset_open hso hKs
  set K' := convexJoin ℝ {x₀} (cthickening δ K)
  have hK's : K' ⊆ s := hs.convexJoin_singleton_subset hδs
  have hK' : IsCompact K' := isCompact_singleton.convexJoin hK.cthickening
  obtain ⟨B₁, hB₁⟩ := isLocallyBoundedOn_def.1 hfb K' hK's hK'
  obtain ⟨B₂, hB₂⟩ := isLocallyBoundedOn_def.1 hDf K' hK's hK'
  obtain ⟨R, hR⟩ := hK'.exists_bound_of_continuousOn
    (continuous_id.sub continuous_const).norm.continuousOn
  set L : NNReal := Real.toNNReal B₂
  refine ⟨Real.toNNReal (L * R / (n + 2) + B₁ / (n + 1)), fun i x hx ↦ ?_⟩
  -- The cone `S` over the closed ball of radius `δ` about `x` is a convex neighbourhood of `x`.
  set S := convexJoin ℝ {x₀} (closedBall x δ)
  have hSK' : S ⊆ K' := convexJoin_mono_right (closedBall_subset_cthickening hx δ)
  have hS : Convex ℝ S := (convex_singleton x₀).convexJoin (convex_closedBall x δ)
  have hlip : LipschitzOnWith L (f i) S := by
    refine hS.lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ) (fun z hz ↦ ?_) fun z hz ↦ ?_
    · exact (hf i z (hK's (hSK' hz))).differentiableAt (hso.mem_nhds (hK's (hSK' hz)))
    · rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal']
      exact (hB₂ i z (hSK' hz)).trans (le_max_left _ _)
  refine norm_fderiv_le_of_lipschitzOn ℝ (mem_of_superset (ball_mem_nhds x hδ)
    (ball_subset_closedBall.trans (subset_convexJoin_right (𝕜 := ℝ) (singleton_nonempty x₀))))
    (LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_)
  rw [dist_eq_norm, dist_eq_norm]
  refine ((hS.starConvex (subset_convexJoin_left (nonempty_closedBall.2 hδ.le)
    (mem_singleton x₀))).norm_poincareHomotopy_sub_le (fun z hz ↦ hB₁ i z (hSK' hz)) hlip hy
      hz).trans (mul_le_mul_of_nonneg_right (le_trans ?_ (Real.le_coe_toNNReal _))
        (norm_nonneg _))
  have : ‖y - x₀‖ ≤ R := by simpa using hR y (hSK' hy)
  gcongr

variable [CompleteSpace F]

/-- The exterior derivative of the Poincaré homotopy operator, as an integral over `[0, 1]`. -/
private theorem extDeriv_poincareHomotopy_eq (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ ω) x =
      ∫ t in (0 : ℝ)..1, t ^ n •
        (t • ContinuousAlternatingMap.alternatizeUncurryFin
            ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
              (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L
                fderivWithin ℝ ω s (lineMap x₀ x t)) +
          (n + 1) • ω (lineMap x₀ x t)) := by
  have hW : IsOpen {p : E × ℝ | lineMap x₀ p.1 p.2 ∈ s} :=
    hso.preimage (by fun_prop : Continuous fun p : E × ℝ ↦ lineMap x₀ p.1 p.2)
  have hpow : Integrable (fun t : I ↦ (t : ℝ) ^ n) volume :=
    (continuous_subtypeVal.pow n).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hF := contDiffOn_integrand (x₀ := x₀) hω
  have hmem (t : I) : (x, (t : ℝ)) ∈ {p : E × ℝ | lineMap x₀ p.1 p.2 ∈ s} :=
    hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x t.property)
  have h : HasFDerivAt
      (fun x ↦ ∫ t : I, (t : ℝ) ^ n • (ω (lineMap x₀ x (t : ℝ))).curryLeft (x - x₀))
      (∫ t : I, (t : ℝ) ^ n •
        fderiv ℝ (fun x' ↦ (ω (lineMap x₀ x' (t : ℝ))).curryLeft (x' - x₀)) x) x :=
    hasFDerivAt_integral_smul_of_contDiffOn (μ := (volume : Measure I))
      hpow continuous_subtypeVal hW hF hmem
  have h' := h.congr_of_eventuallyEq (f₁ := poincareHomotopy x₀ ω) <|
    Filter.Eventually.of_forall fun x ↦ by
      rw [poincareHomotopy_apply, intervalIntegral_eq_integral_unitInterval]
  -- the derivative of the integrand is integrable, so the alternatization commutes with `∫`
  have hint := integrable_smul_of_continuousOn (μ := (volume : Measure I))
    hpow continuous_subtypeVal
    ((hF.fderiv_partial_of_isOpen (m := 0) (by simpa using hW)).continuousOn) hmem
  calc extDeriv (poincareHomotopy x₀ ω) x
      = ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (∫ t : I, (t : ℝ) ^ n •
          fderiv ℝ (fun x' ↦ (ω (lineMap x₀ x' (t : ℝ))).curryLeft (x' - x₀)) x) := by
        rw [extDeriv, h'.fderiv, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    _ = ∫ t : I, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F ((t : ℝ) ^ n •
          fderiv ℝ (fun x' ↦ (ω (lineMap x₀ x' (t : ℝ))).curryLeft (x' - x₀)) x) :=
        (ContinuousLinearMap.integral_comp_comm _ hint).symm
    _ = _ := by
        rw [intervalIntegral_eq_integral_unitInterval]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        have hy := hmem t
        have hω' : HasFDerivAt ω (fderivWithin ℝ ω s (lineMap x₀ x (t : ℝ)))
            (lineMap x₀ x (t : ℝ)) :=
          (hω.differentiableOn one_ne_zero _ hy).hasFDerivWithinAt.hasFDerivAt
            (hso.mem_nhds hy)
        dsimp only
        rw [(hasFDerivWithinAt_univ.1 (hasFDerivWithinAt_integrand hω'.hasFDerivWithinAt
          (mapsTo_univ _ _))).fderiv]
        simp

/-- The fundamental theorem of calculus for `t ↦ tⁿ⁺¹ ω(x₀ + t (x - x₀))` on `[0, 1]`, for a
form `C¹` on a star-convex set with unique derivatives. -/
private theorem integral_pow_smul_fderivWithin_add_eq (hs : StarConvex ℝ x₀ s)
    (hsu : UniqueDiffOn ℝ s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    ∫ t in (0 : ℝ)..1, (t ^ (n + 1) • fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀) +
      ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) = ω x := by
  have hmaps : MapsTo (lineMap x₀ x) (Icc (0 : ℝ) 1) s := fun _ ht ↦
    hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x ht)
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ t ^ (n + 1) • ω (lineMap x₀ x t))
        (t ^ (n + 1) • fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀) +
          ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) t := by
    have hmem := hmaps (Ioo_subset_Icc_self ht)
    have hω' : HasDerivWithinAt (fun t : ℝ ↦ ω (lineMap x₀ x t))
        (fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀)) (Icc 0 1) t :=
      (hω.differentiableOn one_ne_zero _ hmem).hasFDerivWithinAt.comp_hasDerivWithinAt t
        hasDerivAt_lineMap.hasDerivWithinAt hmaps
    refine ((hasDerivAt_pow (n + 1) t).smul
      (hω'.hasDerivAt (Icc_mem_nhds ht.1 ht.2))).congr_deriv ?_
    simp
  have hcont : ContinuousOn (fun t : ℝ ↦ t ^ (n + 1) • ω (lineMap x₀ x t)) (Icc 0 1) :=
    (continuousOn_pow (n + 1)).smul (hω.continuousOn.comp lineMap_continuous.continuousOn hmaps)
  have hint : IntervalIntegrable (fun t : ℝ ↦
      t ^ (n + 1) • fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀) +
        ((n + 1 : ℝ) * t ^ n) • ω (lineMap x₀ x t)) volume 0 1 :=
    (((continuousOn_pow (n + 1)).smul
      ((ContinuousLinearMap.apply ℝ _ (x - x₀)).continuous.comp_continuousOn
        ((hω.continuousOn_fderivWithin hsu le_rfl).comp lineMap_continuous.continuousOn
          hmaps))).add
      ((continuousOn_const.mul (continuousOn_pow n)).smul
        (hω.continuousOn.comp lineMap_continuous.continuousOn hmaps))).intervalIntegrable_of_Icc
      zero_le_one
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  simp

/-- The homotopy formula with the exterior derivative of the homotopy operator replaced by its
integral expression, for a form `C¹` on a star-convex set with unique derivatives. -/
private theorem integral_add_poincareHomotopy_extDerivWithin_eq (hs : StarConvex ℝ x₀ s)
    (hsu : UniqueDiffOn ℝ s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    (∫ t in (0 : ℝ)..1, t ^ n •
        (t • ContinuousAlternatingMap.alternatizeUncurryFin
            ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
              (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L
                fderivWithin ℝ ω s (lineMap x₀ x t)) +
          (n + 1) • ω (lineMap x₀ x t))) + poincareHomotopy x₀ (extDerivWithin ω s) x = ω x := by
  set L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap
  set y := x - x₀
  have hmaps : MapsTo (lineMap x₀ x) (uIcc (0 : ℝ) 1) s := fun _ ht ↦
    hs.segment_subset hx (lineMap_mem_segment ℝ x₀ x (by rwa [uIcc_of_le zero_le_one] at ht))
  have hDω_cont := (hω.continuousOn_fderivWithin hsu le_rfl).comp
    lineMap_continuous.continuousOn hmaps
  have hD_int : IntervalIntegrable (fun t : ℝ ↦ t ^ n •
      (t • ContinuousAlternatingMap.alternatizeUncurryFin
          (L.flip y ∘L fderivWithin ℝ ω s (lineMap x₀ x t)) +
        (n + 1) • ω (lineMap x₀ x t))) volume 0 1 :=
    ContinuousOn.intervalIntegrable ((continuousOn_pow n).smul ((continuousOn_id.smul
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).continuous.comp_continuousOn
        ((ContinuousLinearMap.compL ℝ E _ _ (L.flip y)).continuous.comp_continuousOn
          hDω_cont))).add
        ((hω.continuousOn.comp lineMap_continuous.continuousOn hmaps).const_smul _)))
  have hcurry := (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n + 1)).toContinuousLinearMap.flip y).comp
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F)).continuous.comp_continuousOn
        hDω_cont
  have hdω_int : IntervalIntegrable (fun t : ℝ ↦ t ^ (n + 1) •
      (extDerivWithin ω s (lineMap x₀ x t)).curryLeft y) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ((continuousOn_pow (n + 1)).smul ?_)
    refine hcurry.congr fun t _ ↦ ?_
    simp [extDerivWithin]
  rw [poincareHomotopy_apply, ← intervalIntegral.integral_add hD_int hdω_int,
    ← integral_pow_smul_fderivWithin_add_eq hs hsu hω hx]
  -- pointwise, this is the constant-coefficient Cartan formula for `Dω` and `y = x - x₀`
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have key := ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft
    (fderivWithin ℝ ω s (lineMap x₀ x t)) y
  simp only [extDerivWithin, L]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  linear_combination (norm := module) t ^ (n + 1) • key

/-- **The homotopy formula** `d (K ω) + K (d ω) = ω` for the Poincaré homotopy operator `K` of a
`C¹` form on an open set star-convex with respect to the centre of `K`. -/
theorem extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv (hs : StarConvex ℝ x₀ s)
    (hso : IsOpen s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ ω) x + poincareHomotopy x₀ (extDeriv ω) x = ω x := by
  have hK : poincareHomotopy x₀ (extDeriv ω) x = poincareHomotopy x₀ (extDerivWithin ω s) x :=
    poincareHomotopy_congr fun y hy ↦ by
      rw [extDerivWithin_of_isOpen hso (hs.segment_subset hx hy)]
  rw [extDeriv_poincareHomotopy_eq hs hso hω hx, hK]
  exact integral_add_poincareHomotopy_extDerivWithin_eq hs hso.uniqueDiffOn hω hx

/-- **The Poincaré lemma.** On an open set star-convex with respect to `x₀`, the Poincaré
homotopy operator with centre `x₀` of a closed `C¹` form is a primitive of it. -/
theorem extDeriv_poincareHomotopy (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hω : ContDiffOn ℝ 1 ω s) (hclosed : ∀ y ∈ s, extDeriv ω y = 0) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ ω) x = ω x := by
  have h0 : poincareHomotopy x₀ (extDeriv ω) x = 0 := by
    rw [poincareHomotopy_congr (ω₂ := 0) fun y hy ↦ hclosed y (hs.segment_subset hx hy),
      poincareHomotopy_zero, Pi.zero_apply]
  simpa [h0] using hs.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv hso hω hx

/-- The Poincaré homotopy of an exact form `d ω`, for `ω` of class `C²` on an open star-convex set,
is a primitive of `d ω` there: `d (K (d ω)) = d ω`. So `ω - K (d ω)` is closed; in degree one it is
the gauge change `dθ` that puts an abelian connection `ω` into the radial gauge `K (d ω)`, with the
same curvature. -/
theorem extDeriv_poincareHomotopy_extDeriv (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    {ω : E → E [⋀^Fin n]→L[ℝ] F} (hω : ContDiffOn ℝ 2 ω s) {x : E} (hx : x ∈ s) :
    extDeriv (poincareHomotopy x₀ (extDeriv ω)) x = extDeriv ω x :=
  hs.extDeriv_poincareHomotopy hso (contDiffOn_extDeriv hω hso (by norm_num))
    (fun y hy ↦ extDeriv_extDeriv_apply (hω.contDiffAt (hso.mem_nhds hy)) (by simp)) hx

/-- **The Poincaré lemma.** A closed `C^r` form, `r ≥ 1`, on an open star-convex set is the
exterior derivative of a `C^r` form, which can be chosen to vanish at the centre. -/
theorem exists_contDiffOn_forall_extDeriv_eq (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {r : ℕ∞}
    (hr : 1 ≤ r) (hω : ContDiffOn ℝ r ω s) (hclosed : ∀ y ∈ s, extDeriv ω y = 0) :
    ∃ α : E → E [⋀^Fin n]→L[ℝ] F, ContDiffOn ℝ r α s ∧ α x₀ = 0 ∧
      ∀ x ∈ s, extDeriv α x = ω x :=
  ⟨poincareHomotopy x₀ ω, hs.contDiffOn_poincareHomotopy hso hω, poincareHomotopy_self x₀ ω,
    fun _ hx ↦ hs.extDeriv_poincareHomotopy hso (hω.of_le (by exact_mod_cast hr)) hclosed hx⟩

/-- **The homotopy formula in degree zero**, `K (d f) x = f x - f x₀` for a `0`-form `f` that is
`C¹` on a star-convex set `s` with unique derivatives, with exterior derivative within `s`. -/
theorem poincareHomotopy_extDerivWithin_eq_sub (hs : StarConvex ℝ x₀ s) (hsu : UniqueDiffOn ℝ s)
    {ω : E → E [⋀^Fin 0]→L[ℝ] F} (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    poincareHomotopy x₀ (extDerivWithin ω s) x = ω x - ω x₀ := by
  have hftc : ∫ t in (0 : ℝ)..1, fderivWithin ℝ ω s (lineMap x₀ x t) (x - x₀) = ω x - ω x₀ :=
    (hs.sub_eq_intervalIntegral_lineMap_apply (hω.continuousOn_fderivWithin hsu le_rfl)
      (fun z hz ↦ (hω.differentiableOn one_ne_zero z hz).hasFDerivWithinAt) hx).symm
  rw [← hftc, poincareHomotopy_apply]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  ext v
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

/-- **The homotopy formula in degree zero**, `K (d f) x = f x - f x₀` for a `0`-form `f` that is
`C¹` on an open set star-convex with respect to `x₀`. -/
theorem poincareHomotopy_extDeriv_eq_sub (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    {ω : E → E [⋀^Fin 0]→L[ℝ] F} (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    poincareHomotopy x₀ (extDeriv ω) x = ω x - ω x₀ := by
  rw [poincareHomotopy_congr (ω₂ := extDerivWithin ω s) fun y hy ↦ by
    rw [extDerivWithin_of_isOpen hso (hs.segment_subset hx hy)]]
  exact hs.poincareHomotopy_extDerivWithin_eq_sub hso.uniqueDiffOn hω hx

end StarConvex

/-! ### Convex sets that need not be open

On a convex set `s` with unique derivatives, such as a closed half-ball (the image of a boundary
chart), derivatives are taken within `s` and the exterior derivative is `extDerivWithin`. -/

namespace Convex

variable {x₀ : E} {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}

/-- **The Poincaré homotopy operator depends smoothly on parameters.** Let `ω q` be a family of
forms indexed by a convex set `t` with unique derivatives in a normed space `P`, jointly `C^r` on
`t ×ˢ s` for a convex set `s` with unique derivatives containing `x₀`. Then the Poincaré homotopy
operators `poincareHomotopy x₀ (ω q)` are jointly `C^r` in `(q, x)` on `t ×ˢ s`. -/
theorem contDiffOn_uncurry_poincareHomotopy {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {t : Set P} {ω : P → E → E [⋀^Fin (n + 1)]→L[ℝ] F} (ht : Convex ℝ t) (htu : UniqueDiffOn ℝ t)
    (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hx₀ : x₀ ∈ s) {r : ℕ∞}
    (hω : ContDiffOn ℝ r (Function.uncurry ω) (t ×ˢ s)) :
    ContDiffOn ℝ r (fun q : P × E ↦ poincareHomotopy x₀ (ω q.1) q.2) (t ×ˢ s) := by
  have hpow : Integrable (fun t : I ↦ (t : ℝ) ^ n) volume :=
    (continuous_subtypeVal.pow n).integrable_of_hasCompactSupport (.of_compactSpace _)
  -- The integrand, as a function of the parameter, the point and the time.
  have hint : ContDiffOn ℝ r
      (fun p : (P × E) × ℝ ↦ (ω p.1.1 (lineMap x₀ p.1.2 p.2)).curryLeft (p.1.2 - x₀))
      ((t ×ˢ s) ×ˢ Icc 0 1) := (contDiffOn_uncurry_integrand (x₀ := x₀) hω).mono fun p hp ↦
    ⟨hp.1.1, (hs.starConvex hx₀).segment_subset hp.1.2 (lineMap_mem_segment ℝ x₀ p.1.2 hp.2)⟩
  refine ((ht.prod hs).contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I)) hpow
    continuous_subtypeVal (htu.prod hsu) ((htu.prod hsu).prod uniqueDiffOn_Icc_zero_one) hint
    fun x hx τ ↦ ⟨hx, τ.property⟩).congr fun x _ ↦ ?_
  rw [poincareHomotopy_apply, intervalIntegral_eq_integral_unitInterval]

/-- The Poincaré homotopy operator of a `C^r` form on a convex set with unique derivatives, with
centre in that set, is `C^r` there. -/
theorem contDiffOn_poincareHomotopy (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hx₀ : x₀ ∈ s)
    {r : ℕ∞} (hω : ContDiffOn ℝ r ω s) : ContDiffOn ℝ r (poincareHomotopy x₀ ω) s := by
  -- The constant family over the parameter space `ℝ`, restricted to the parameter `0`.
  have h := contDiffOn_uncurry_poincareHomotopy (P := ℝ) (t := univ) (ω := fun _ ↦ ω)
    convex_univ uniqueDiffOn_univ hs hsu hx₀ (hω.comp contDiff_snd.contDiffOn fun p hp ↦ hp.2)
  refine (h.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun x hx ↦ ⟨mem_univ (0 : ℝ), hx⟩).congr fun x _ ↦ ?_
  simp only [Function.comp_apply, id_eq]

variable [CompleteSpace F]

/-- The exterior derivative within a convex set of the Poincaré homotopy operator, as an
integral over `[0, 1]`. -/
private theorem extDerivWithin_poincareHomotopy_eq (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hx₀ : x₀ ∈ s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDerivWithin (poincareHomotopy x₀ ω) s x =
      ∫ t in (0 : ℝ)..1, t ^ n •
        (t • ContinuousAlternatingMap.alternatizeUncurryFin
            ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
              (n := n)).toContinuousLinearMap.flip (x - x₀) ∘L
                fderivWithin ℝ ω s (lineMap x₀ x t)) +
          (n + 1) • ω (lineMap x₀ x t)) := by
  set L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
    (n := n)).toContinuousLinearMap
  have hstar := hs.starConvex hx₀
  have hpow : Integrable (fun t : I ↦ (t : ℝ) ^ n) volume :=
    (continuous_subtypeVal.pow n).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hmaps (t : I) : MapsTo (fun x' ↦ lineMap x₀ x' (t : ℝ)) s s := fun x' hx' ↦
    hstar.segment_subset hx' (lineMap_mem_segment ℝ x₀ x' t.property)
  have h := hs.hasFDerivWithinAt_integral_smul_of_contDiffOn (μ := (volume : Measure I)) hpow
    continuous_subtypeVal (hsu.prod uniqueDiffOn_Icc_zero_one)
    ((contDiffOn_integrand (x₀ := x₀) hω).mono fun p hp ↦
      hstar.segment_subset hp.1 (lineMap_mem_segment ℝ x₀ p.1 hp.2))
    (fun x hx t ↦ ⟨hx, t.property⟩) hx (hsu x hx)
  have hK : poincareHomotopy x₀ ω =
      fun x ↦ ∫ t : I, (t : ℝ) ^ n • (ω (lineMap x₀ x (t : ℝ))).curryLeft (x - x₀) :=
    funext fun x ↦ by rw [poincareHomotopy_apply, intervalIntegral_eq_integral_unitInterval]
  -- the partial derivative of the integrand, explicitly
  set D : ℝ → E →L[ℝ] E [⋀^Fin n]→L[ℝ] F := fun t ↦
    t • (L.flip (x - x₀) ∘L fderivWithin ℝ ω s (lineMap x₀ x t)) + L (ω (lineMap x₀ x t))
  have hD (t : I) : fderivWithin ℝ (fun x' ↦ (ω (lineMap x₀ x' (t : ℝ))).curryLeft (x' - x₀)) s x =
      D t :=
    (hasFDerivWithinAt_integrand ((hω.differentiableOn one_ne_zero _
      (hmaps t hx)).hasFDerivWithinAt) (hmaps t)).fderivWithin (hsu x hx)
  have hDc : ContinuousOn D (Icc 0 1) := by
    have hseg : MapsTo (lineMap x₀ x) (Icc (0 : ℝ) 1) s := fun t ht ↦ hmaps ⟨t, ht⟩ hx
    exact (continuousOn_id.smul ((ContinuousLinearMap.compL ℝ E _ _
      (L.flip (x - x₀))).continuous.comp_continuousOn
        ((hω.continuousOn_fderivWithin hsu le_rfl).comp lineMap_continuous.continuousOn
          hseg))).add (L.continuous.comp_continuousOn
            (hω.continuousOn.comp lineMap_continuous.continuousOn hseg))
  have hint := integrable_smul_of_continuousOn (μ := (volume : Measure I)) (x := x) hpow
    continuous_subtypeVal (F := fun p : E × ℝ ↦ D p.2) (W := {p | p.2 ∈ Icc 0 1})
    (hDc.comp continuous_snd.continuousOn fun _ hp ↦ hp) fun t ↦ t.property
  calc extDerivWithin (poincareHomotopy x₀ ω) s x
      = ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F
          (∫ t : I, (t : ℝ) ^ n • D t) := by
        rw [extDerivWithin, hK, h.fderivWithin (hsu x hx),
          ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
        simp only [hD]
    _ = ∫ t : I, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F ((t : ℝ) ^ n • D t) :=
        (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
          (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (n := n)) hint).symm
    _ = _ := by
        rw [intervalIntegral_eq_integral_unitInterval]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        simp [D, L]

/-- **The homotopy formula** `d (K ω) + K (d ω) = ω`, with exterior derivatives within `s`, for
the Poincaré homotopy operator `K` of a `C¹` form on a convex set `s` with unique derivatives,
whose centre lies in `s`. -/
theorem extDerivWithin_poincareHomotopy_add_poincareHomotopy_extDerivWithin (hs : Convex ℝ s)
    (hsu : UniqueDiffOn ℝ s) (hx₀ : x₀ ∈ s) (hω : ContDiffOn ℝ 1 ω s) {x : E} (hx : x ∈ s) :
    extDerivWithin (poincareHomotopy x₀ ω) s x + poincareHomotopy x₀ (extDerivWithin ω s) x =
      ω x := by
  rw [extDerivWithin_poincareHomotopy_eq hs hsu hx₀ hω hx]
  exact (hs.starConvex hx₀).integral_add_poincareHomotopy_extDerivWithin_eq hsu hω hx

/-- **The relative Poincaré lemma.** On a convex set with unique derivatives, the Poincaré
homotopy operator, centred in the set, of a form closed within the set is a primitive of it
within the set. -/
theorem extDerivWithin_poincareHomotopy (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hx₀ : x₀ ∈ s) (hω : ContDiffOn ℝ 1 ω s) (hclosed : ∀ y ∈ s, extDerivWithin ω s y = 0)
    {x : E} (hx : x ∈ s) : extDerivWithin (poincareHomotopy x₀ ω) s x = ω x := by
  have h0 : poincareHomotopy x₀ (extDerivWithin ω s) x = 0 := by
    rw [poincareHomotopy_congr (ω₂ := 0) fun y hy ↦
        hclosed y ((hs.starConvex hx₀).segment_subset hx hy),
      poincareHomotopy_zero, Pi.zero_apply]
  simpa [h0] using
    hs.extDerivWithin_poincareHomotopy_add_poincareHomotopy_extDerivWithin hsu hx₀ hω hx

/-- **The relative Poincaré lemma.** A `C^r` form, `r ≥ 1`, closed within a convex set with unique
derivatives is the exterior derivative within the set of a `C^r` form, which can be chosen to
vanish at any given point of the set. The set need not be open: a closed half-ball, the image of
a boundary chart, is allowed. -/
theorem exists_contDiffOn_forall_extDerivWithin_eq (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hx₀ : x₀ ∈ s) {r : ℕ∞} (hr : 1 ≤ r) (hω : ContDiffOn ℝ r ω s)
    (hclosed : ∀ y ∈ s, extDerivWithin ω s y = 0) :
    ∃ α : E → E [⋀^Fin n]→L[ℝ] F, ContDiffOn ℝ r α s ∧ α x₀ = 0 ∧
      ∀ x ∈ s, extDerivWithin α s x = ω x :=
  ⟨poincareHomotopy x₀ ω, hs.contDiffOn_poincareHomotopy hsu hx₀ hω, poincareHomotopy_self x₀ ω,
    fun _ hx ↦ hs.extDerivWithin_poincareHomotopy hsu hx₀ (hω.of_le (by exact_mod_cast hr))
      hclosed hx⟩

end Convex

namespace TauCeti

/-- The Poincaré homotopy operator of a form that is `C^r` on all of `E` is `C^r`. -/
theorem contDiff_poincareHomotopy {r : ℕ∞} (x₀ : E) {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (hω : ContDiff ℝ r ω) : ContDiff ℝ r (poincareHomotopy x₀ ω) :=
  contDiffOn_univ.1 ((starConvex_univ x₀).contDiffOn_poincareHomotopy isOpen_univ hω.contDiffOn)

/-- The function `x ↦ (K ω)(x) ()` given by the Poincaré homotopy operator of a `1`-form `ω` that
is `C^r` on all of `E` is `C^r`. -/
theorem contDiff_poincareHomotopy_apply_zero {r : ℕ∞} (x₀ : E) {ω : E → E [⋀^Fin 1]→L[ℝ] F}
    (hω : ContDiff ℝ r ω) : ContDiff ℝ r fun x ↦ poincareHomotopy x₀ ω x 0 :=
  (ContinuousAlternatingMap.apply ℝ E F (0 : Fin 0 → E)).contDiff.comp
    (contDiff_poincareHomotopy x₀ hω)

variable [CompleteSpace F]

/-- **The homotopy formula** `d (K ω) + K (d ω) = ω` for a form that is `C¹` on all of `E`. -/
theorem extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv (x₀ : E)
    {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hω : ContDiff ℝ 1 ω) (x : E) :
    extDeriv (poincareHomotopy x₀ ω) x + poincareHomotopy x₀ (extDeriv ω) x = ω x :=
  (starConvex_univ x₀).extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv isOpen_univ
    hω.contDiffOn (mem_univ x)

/-- **The homotopy formula in degree zero**, `K (d f) x = f x - f x₀` for a `0`-form `f` that is
`C¹` on all of `E`. -/
theorem poincareHomotopy_extDeriv_eq_sub (x₀ : E) {ω : E → E [⋀^Fin 0]→L[ℝ] F}
    (hω : ContDiff ℝ 1 ω) (x : E) :
    poincareHomotopy x₀ (extDeriv ω) x = ω x - ω x₀ :=
  (starConvex_univ x₀).poincareHomotopy_extDeriv_eq_sub isOpen_univ hω.contDiffOn (mem_univ x)

end TauCeti
