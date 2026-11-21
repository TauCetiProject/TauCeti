/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Integrals of derivatives along segments, with a parameter

Let `s` be a convex subset of a real normed space `E` and `c ∈ s`. For a family
`D : E × G → (E →L[ℝ] V)` of linear maps depending on a point of `E` and a parameter in a normed
space `G`, this file studies the segment integral

`Q (y, q) = ∫₀¹ D (c + τ (y - c), q) (y - c) dτ`.

If `D` is `C^r` on `s ×ˢ u` for a convex set `u` of parameters, where both sets have unique
derivatives (for instance intersections of balls with the range of a model with corners), then
`Q` is `C^r` on `s ×ˢ u` (`Convex.contDiffOn_intervalIntegral_lineMap_apply`). Neither set needs to
be open, so the statement applies in boundary charts. If moreover `D (·, q)` is the derivative
within `s` of a function `g`, then `Q (y, q) = g y - g c` for every `y ∈ s`, by the fundamental
theorem of calculus along the segment from `c` to `y`
(`StarConvex.sub_eq_intervalIntegral_lineMap_apply`).

Together these say that the normalized primitives `y ↦ g y - g c` of a family of exact one-forms
on a convex set depend on the parameter as smoothly as the forms do. This is the local step in
the construction of smooth families of primitives on manifolds
(`TauCeti.exists_contMDiff_mvfderiv_eq_of_forall_exists`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 11.49 (line integrals of exact
  covector fields) and Chapter 17 (the Poincaré lemma, whose primitive this is in degree one).
-/

public section

noncomputable section

open AffineMap MeasureTheory Set
open scoped unitInterval

variable {E G V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace StarConvex

variable {s : Set E} {c : E}

/-- **The fundamental theorem of calculus along segments.** On a set `s` star-convex with respect
to `c`, a function `g` with derivative `D z` within `s` at every point `z ∈ s`, where `D` is
continuous on `s`, satisfies `g y - g c = ∫₀¹ D (c + τ (y - c)) (y - c) dτ` for every `y ∈ s`. -/
theorem sub_eq_intervalIntegral_lineMap_apply [CompleteSpace V] (hs : StarConvex ℝ c s)
    {g : E → V} {D : E → E →L[ℝ] V} (hD : ContinuousOn D s)
    (hg : ∀ z ∈ s, HasFDerivWithinAt g (D z) s z) {y : E} (hy : y ∈ s) :
    g y - g c = ∫ τ in (0 : ℝ)..1, D (lineMap c y τ) (y - c) := by
  have hmaps : MapsTo (lineMap c y) (Icc (0 : ℝ) 1) s := fun _ ht ↦
    hs.segment_subset hy (lineMap_mem_segment ℝ c y ht)
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ g (lineMap c y t)) (D (lineMap c y t) (y - c)) t := by
    have h : HasDerivWithinAt (fun t : ℝ ↦ g (lineMap c y t)) (D (lineMap c y t) (y - c))
        (Icc 0 1) t :=
      (hg _ (hmaps (Ioo_subset_Icc_self ht))).comp_hasDerivWithinAt t
        hasDerivAt_lineMap.hasDerivWithinAt hmaps
    exact h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hgc : ContinuousOn g s := fun z hz ↦ (hg z hz).continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ ↦ g (lineMap c y t)) (Icc 0 1) :=
    hgc.comp lineMap_continuous.continuousOn hmaps
  have hint : IntervalIntegrable (fun t : ℝ ↦ D (lineMap c y t) (y - c)) volume 0 1 :=
    ((ContinuousLinearMap.apply ℝ V (y - c)).continuous.comp_continuousOn
      (hD.comp lineMap_continuous.continuousOn hmaps)).intervalIntegrable_of_Icc zero_le_one
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  simp

end StarConvex

namespace Convex

variable {s : Set E} {c : E}

/-- **Smoothness of segment integrals in a parameter.** Let `s` and `u` be convex sets with unique
derivatives in `E` and `G`, with `c ∈ s`. If `D` is `C^r` on `s ×ˢ u`, then so is
`(y, q) ↦ ∫₀¹ D (c + τ (y - c), q) (y - c) dτ`. -/
theorem contDiffOn_intervalIntegral_lineMap_apply (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hc : c ∈ s) {u : Set G} (hu : Convex ℝ u) (huu : UniqueDiffOn ℝ u) {r : ℕ∞}
    {D : E × G → E →L[ℝ] V} (hD : ContDiffOn ℝ r D (s ×ˢ u)) :
    ContDiffOn ℝ r (fun z : E × G ↦ ∫ τ in (0 : ℝ)..1, D (lineMap c z.1 τ, z.2) (z.1 - c))
      (s ×ˢ u) := by
  have hmaps : MapsTo (fun p : (E × G) × ℝ ↦ (lineMap c p.1.1 p.2, p.1.2))
      ((s ×ˢ u) ×ˢ Icc (0 : ℝ) 1) (s ×ˢ u) := fun p hp ↦
    ⟨hs.segment_subset hc hp.1.1 (lineMap_mem_segment ℝ c p.1.1 hp.2), hp.1.2⟩
  have hF : ContDiffOn ℝ r (fun p : (E × G) × ℝ ↦ D (lineMap c p.1.1 p.2, p.1.2) (p.1.1 - c))
      ((s ×ˢ u) ×ˢ Icc (0 : ℝ) 1) :=
    (hD.comp ((contDiff_const.lineMap (contDiff_fst.comp contDiff_fst) contDiff_snd).prodMk
      (contDiff_snd.comp contDiff_fst)).contDiffOn hmaps).clm_apply
      ((contDiff_fst.comp contDiff_fst).sub contDiff_const).contDiffOn
  have hone : Integrable (fun _ : I ↦ (1 : ℝ)) volume :=
    continuous_const.integrable_of_hasCompactSupport (.of_compactSpace _)
  refine ((hs.prod hu).contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I)) hone
    continuous_subtypeVal (hsu.prod huu) ((hsu.prod huu).prod uniqueDiffOn_Icc_zero_one) hF
    fun z hz t ↦ ⟨hz, t.property⟩).congr fun z _ ↦ ?_
  simp only [one_smul]
  exact TauCeti.intervalIntegral_eq_integral_unitInterval _

end Convex
