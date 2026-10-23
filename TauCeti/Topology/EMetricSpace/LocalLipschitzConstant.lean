/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.MulAction
public import TauCeti.Order.Filter.ENNReal
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The local Lipschitz constant

For a map `f : X → Y` between extended pseudometric spaces, the *local Lipschitz constant* (or
*slope*) of `f` at `x` is

`|Df|(x) = limsup_{y → x, y ≠ x} d(f y, f x) / d(y, x)`,

the largest rate at which `f` can move away from `f x` near `x`; at an isolated point it is `0`.
It is the metric replacement for the norm of the gradient that enters the Cheeger energy
`½ ∫ |Df|² dm` of a function on a metric-measure space. Unlike the descending slope
`TauCeti.descendingSlope` of an energy, it measures the variation of `f` in both directions.

A `K`-Lipschitz map has local Lipschitz constant at most `K` everywhere, constants have local
Lipschitz constant `0`, and for maps into a normed group the local Lipschitz constant is subadditive
and positively homogeneous. For a map that does not separate points at distance `0` (for instance a
continuous map), the local Lipschitz constant is the infimum over `n` of the suprema of the
difference quotients over the balls of radius `1 / (n + 1)`, and for a continuous map each of
these suprema is a lower semicontinuous function of the point. This is what makes the local
Lipschitz constant of a continuous map a Borel function, so that it can be integrated.

## Main definitions

* `TauCeti.localLipschitzConstant f x`: the local Lipschitz constant of `f` at `x`.

## Main results

* `LipschitzOnWith.localLipschitzConstant_le` and `LipschitzWith.localLipschitzConstant_le`: the
  local Lipschitz constant of a `K`-Lipschitz map is at most `K`.
* `TauCeti.localLipschitzConstant_add_le` and `TauCeti.localLipschitzConstant_const_smul`:
  subadditivity and homogeneity for maps into a normed space.
* `TauCeti.localLipschitzConstant_eq_iInf_iSup` and
  `Continuous.lowerSemicontinuous_iSup_edist_div`: the local Lipschitz constant of a continuous map
  is a countable infimum of lower semicontinuous functions.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Calculus and heat flow in metric measure spaces and
  applications to spaces with Ricci bounds from below*, Invent. Math. 195 (2014), 289--391,
  Section 2.2.
* J. Cheeger, *Differentiability of Lipschitz functions on metric measure spaces*, Geom. Funct.
  Anal. 9 (1999), 428--517.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [PseudoEMetricSpace X]

section PseudoEMetricSpace

variable [PseudoEMetricSpace Y] {f : X → Y} {x : X}

/-- The *local Lipschitz constant* (or *slope*) of `f` at `x`: the upper limit, as `y → x` with
`y ≠ x`, of the difference quotient `d(f y, f x) / d(y, x)`. At an isolated point it is `0`. -/
def localLipschitzConstant (f : X → Y) (x : X) : ℝ≥0∞ :=
  limsup (fun y ↦ edist (f y) (f x) / edist y x) (𝓝[≠] x)

/-- The defining formula of the local Lipschitz constant, as an upper limit of difference
quotients. -/
theorem localLipschitzConstant_def (f : X → Y) (x : X) :
    localLipschitzConstant f x = limsup (fun y ↦ edist (f y) (f x) / edist y x) (𝓝[≠] x) :=
  (rfl)

/-- If near `x` the map `f` moves at most like `C * d(y, x)`, then its local Lipschitz constant at
`x` is at most `C`. -/
theorem localLipschitzConstant_le_of_eventually_le {C : ℝ≥0∞}
    (h : ∀ᶠ y in 𝓝[≠] x, edist (f y) (f x) ≤ C * edist y x) : localLipschitzConstant f x ≤ C :=
  limsup_le_of_le (h := h.mono fun _ hy ↦ ENNReal.div_le_of_le_mul hy)

/-- The local Lipschitz constant at `x` of a map that is `K`-Lipschitz on a neighbourhood of `x` is
at most `K`. -/
theorem _root_.LipschitzOnWith.localLipschitzConstant_le {K : ℝ≥0} {s : Set X}
    (hf : LipschitzOnWith K f s) (hs : s ∈ 𝓝 x) : localLipschitzConstant f x ≤ K :=
  localLipschitzConstant_le_of_eventually_le <| by
    filter_upwards [nhdsWithin_le_nhds hs] with y hy using hf hy (mem_of_mem_nhds hs)

/-- The local Lipschitz constant of a `K`-Lipschitz map is at most `K` everywhere. -/
theorem _root_.LipschitzWith.localLipschitzConstant_le {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : X) : localLipschitzConstant f x ≤ K :=
  hf.lipschitzOnWith.localLipschitzConstant_le univ_mem

/-- A constant map has local Lipschitz constant `0`. -/
@[simp]
theorem localLipschitzConstant_const (c : Y) (x : X) :
    localLipschitzConstant (fun _ : X ↦ c) x = 0 :=
  nonpos_iff_eq_zero.1 <| localLipschitzConstant_le_of_eventually_le <| by simp

/-- If `f` does not separate from `x` the points at distance `0` from `x` (for instance, if `f`
is continuous), the local Lipschitz constant of `f` at `x` is the infimum over `n` of the suprema of
the difference quotients over the balls of radius `1 / (n + 1)`. The centre of the ball, and the
points at distance `0` from it, contribute the value `0 / 0 = 0`. -/
theorem localLipschitzConstant_eq_iInf_iSup
    (hf : ∀ y, edist y x = 0 → edist (f y) (f x) = 0) :
    localLipschitzConstant f x =
      ⨅ n : ℕ, ⨆ (y : X) (_ : edist y x < ((n : ℝ≥0∞) + 1)⁻¹), edist (f y) (f x) / edist y x := by
  have hb : (𝓝[≠] x).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ Metric.eball x ((n : ℝ≥0∞) + 1)⁻¹ ∩ {x}ᶜ := by
    refine (Metric.nhdsWithin_basis_eball (x := x) (s := {x}ᶜ)).to_hasBasis
      (fun ε hε ↦ ?_) fun n _ ↦ ⟨_, by simp, subset_rfl⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine ⟨n, trivial, inter_subset_inter_left _ (Metric.eball_subset_eball ?_)⟩
    exact (ENNReal.inv_le_inv.2 le_self_add).trans hn.le
  rw [localLipschitzConstant_def, hb.limsup_eq_iInf_iSup]
  refine iInf_congr fun n ↦ (iInf_pos trivial).trans <|
    le_antisymm (iSup₂_le fun y hy ↦ ?_) (iSup₂_le fun y hy ↦ ?_)
  · exact le_iSup₂_of_le (f := fun y (_ : edist y x < ((n : ℝ≥0∞) + 1)⁻¹) ↦
      edist (f y) (f x) / edist y x) y (Metric.mem_eball.1 hy.1) le_rfl
  · by_cases hyx : edist y x = 0
    · simp [hyx, hf y hyx]
    · refine le_iSup₂_of_le (f := fun y (_ : y ∈ Metric.eball x ((n : ℝ≥0∞) + 1)⁻¹ ∩ {x}ᶜ) ↦
        edist (f y) (f x) / edist y x) y ⟨hy, ?_⟩ le_rfl
      rintro rfl
      exact hyx (edist_self y)

/-- For a continuous map `f` and a radius `r`, the supremum of the difference quotients
`d(f y, f x) / d(y, x)` over the ball of radius `r` about `x` is a lower semicontinuous function of
`x`. -/
theorem _root_.Continuous.lowerSemicontinuous_iSup_edist_div (hf : Continuous f) (r : ℝ≥0∞) :
    LowerSemicontinuous fun x ↦ ⨆ (y : X) (_ : edist y x < r), edist (f y) (f x) / edist y x := by
  refine lowerSemicontinuous_iSup fun y x c hc ↦ ?_
  obtain ⟨hyx, hc⟩ := lt_iSup_iff.1 hc
  have hpos : edist y x ≠ 0 := by
    intro h0
    have hfyx : edist (f y) (f x) = 0 :=
      ((EMetric.inseparable_iff.2 h0).map hf).edist_eq_zero
    simp [h0, hfyx] at hc
  have htop : edist y x ≠ ∞ ∨ edist (f y) (f x) ≠ ∞ := by
    by_contra! h
    simp [h.1, h.2] at hc
  have hlim : Tendsto (fun x' ↦ edist (f y) (f x') / edist y x') (𝓝 x)
      (𝓝 (edist (f y) (f x) / edist y x)) :=
    ENNReal.Tendsto.div ((continuous_const.edist hf).tendsto x) (Or.inr hpos)
      ((continuous_const.edist continuous_id).tendsto x) htop
  filter_upwards [hlim.eventually (lt_mem_nhds hc),
    (continuous_const.edist continuous_id).isOpen_preimage _ isOpen_Iio |>.mem_nhds hyx]
    with x' hx' hyx'
  exact hx'.trans_le (le_iSup (fun _ : edist y x' < r ↦ edist (f y) (f x') / edist y x') hyx')

end PseudoEMetricSpace

section Normed

variable {E : Type*} [SeminormedAddCommGroup E] {f g : X → E} {x : X}

/-- The local Lipschitz constant of a sum is at most the sum of the local Lipschitz constants. -/
theorem localLipschitzConstant_add_le (f g : X → E) (x : X) :
    localLipschitzConstant (f + g) x ≤ localLipschitzConstant f x + localLipschitzConstant g x := by
  refine (limsup_le_limsup (Eventually.of_forall fun y ↦ ?_)).trans
    (ENNReal.limsup_add_le' _ _)
  simp only [Pi.add_apply, ← ENNReal.add_div]
  exact ENNReal.div_le_div_right (edist_add_add_le _ _ _ _) _

/-- The local Lipschitz constant is positively homogeneous: scaling a map by `c` scales its local
Lipschitz constant by `‖c‖ₑ`. -/
@[simp]
theorem localLipschitzConstant_const_smul {𝕜 : Type*} [SeminormedRing 𝕜] [Module 𝕜 E]
    [NormSMulClass 𝕜 E] (c : 𝕜) (f : X → E) (x : X) :
    localLipschitzConstant (c • f) x = ‖c‖ₑ * localLipschitzConstant f x := by
  simp only [localLipschitzConstant_def, Pi.smul_apply, edist_smul₀, ENNReal.smul_def, smul_eq_mul,
    mul_div_assoc]
  rw [enorm_eq_nnnorm, ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top]

end Normed

end TauCeti
