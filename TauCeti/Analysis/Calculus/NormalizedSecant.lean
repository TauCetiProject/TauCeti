/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Limits of normalized secants of a smooth equation

If two sequences of zeros of a strictly differentiable map approach the same point, a
convergent normalized difference lies in the kernel of its derivative. This is the
pointwise calculus step in passing from ordered minimal graph sheets to a Jacobi field.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A limit of normalized differences of zeros belongs to the kernel of the linearized
equation. Strict differentiability controls secants even when their length is much smaller
than their distance to the limiting zero. -/
theorem HasStrictFDerivAt.map_normalized_secant_eq_zero
    {P : E → F} {L : E →L[ℝ] F} {x : E} (hP : HasStrictFDerivAt P L x)
    {a b : ℕ → E} {c : ℕ → ℝ} {v : ℕ → E} {w : E}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 x))
    (hc : ∀ i, c i ≠ 0) (hgap : ∀ i, a i - b i = c i • v i)
    (hv : Tendsto v atTop (𝓝 w)) (hzero : ∀ i, P (a i) = P (b i)) :
    L w = 0 := by
  let err : ℕ → F := fun i ↦ P (a i) - P (b i) - L (a i - b i)
  have ho : err =o[atTop] (fun i ↦ a i - b i) := by
    simpa only [err, Function.comp_def] using
      hP.isLittleO.comp_tendsto (ha.prodMk_nhds hb)
  have hbound : (fun i ↦ a i - b i) =O[atTop] c := by
    have hvbound : v =O[atTop] (fun _ ↦ (1 : ℝ)) :=
      Asymptotics.isBigO_const_of_tendsto hv one_ne_zero
    have h := (Asymptotics.isBigO_refl c atTop).smul hvbound
    simpa only [smul_eq_mul, mul_one] using h.congr_left (fun i ↦ (hgap i).symm)
  have hlim : Tendsto (fun i ↦ (c i)⁻¹ • err i) atTop (𝓝 0) :=
    (ho.trans_isBigO hbound).tendsto_inv_smul_nhds_zero
  have heq (i : ℕ) : (c i)⁻¹ • err i = -L (v i) := by
    simp only [err, hzero i, sub_self, zero_sub, hgap i, map_smul, smul_smul,
      inv_mul_cancel₀ (hc i), one_smul, smul_neg, one_smul]
  have hlim' : Tendsto (fun i ↦ -L (v i)) atTop (𝓝 0) := by
    simpa only [heq] using hlim
  have hlimv : Tendsto (fun i ↦ -L (v i)) atTop (𝓝 (-L w)) :=
    L.continuous.tendsto w |>.comp hv |>.neg
  have hw : -L w = 0 := tendsto_nhds_unique hlimv hlim'
  exact neg_eq_zero.mp hw

end TauCeti
