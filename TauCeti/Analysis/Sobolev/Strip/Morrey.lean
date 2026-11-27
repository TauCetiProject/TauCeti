/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Strip.Jet
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Sobolev.Morrey.Basic
import TauCeti.MeasureTheory.Measure.Haar.Prod
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Morrey's estimate on the strip, up to the boundary

Let `V` be a real Banach space. Sections of the trivial bundle with fibre `V` over the strip
`ℝ × [0, 1]` are maps `ξ : ℝ × ℝ → V`, of which only the values on the closed strip
`univ ×ˢ Icc 0 1` matter, and the `W^{1,p}` norm of a `C¹` section is, up to a factor between `1`
and `3 ^ (1 / p)`, the `Lᵖ` norm on the strip of its jet
`TauCeti.StripSobolev.jet ξ = (ξ, ∂s ξ, ∂t ξ)`.

The strip has dimension two, so for `p > 2` Morrey's inequality bounds a section pointwise by its
`W^{1,p}` norm, up to the two boundary lines: there is a constant `C`, depending on `p`, with

`‖ξ z‖ ≤ C ‖jet ξ‖_{Lᵖ(ℝ × [0, 1])}`

for every point `z` of the closed strip and every `ξ` that is `C¹` on the open strip
`ℝ × (0, 1)` and continuous on the closed strip
(`TauCeti.StripSobolev.exists_enorm_le_mul_eLpNorm_jet`). No decay of `ξ` along the ends and no
boundary condition are assumed. Applied to differences, the same constant bounds `‖ξ z - η z‖` by
the `Lᵖ` norm of `jet (ξ - η)`, so sections whose jets converge in `Lᵖ` converge uniformly on the
closed strip.

The proof applies Morrey's bound for star-convex domains
(`TauCeti.exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv`) at a point `z = (s, t)` of the open
strip, on the open rectangle `(s - 1, s + 1) × (0, 1)`. This rectangle is convex, lies inside the
strip, and meets the unit ball about `z` for the sup norm in area at least `1` whatever `z`
(`TauCeti.ofReal_mul_ofReal_le_volume_Ioo_prod_Ioo_inter_ball`), so the constant does not depend
on `z`. Unlike on the cylinder (`TauCeti.CylinderSobolev.exists_enorm_le_mul_eLpNorm_jet`),
where every unit ball meets the fundamental domain in a full square by periodicity, the rectangle
stays on one side of each boundary line, which is why `z` is first taken in the open strip; the
bound then extends to the boundary lines by continuity.

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4 (Morrey's inequality).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.1,
  on the Sobolev embedding `W^{1,p} ⊂ C⁰` for `p > 2` on surfaces with boundary.
-/

public section

namespace TauCeti.StripSobolev

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Morrey's estimate on the strip, up to the boundary.** For `p > 2` there is a constant `C`
such that every `ξ` which is `C¹` on the open strip `ℝ × (0, 1)` and continuous on the closed strip
satisfies `‖ξ z‖ ≤ C ‖jet ξ‖_{Lᵖ(ℝ × [0, 1])}` at every point `z` of the closed strip. -/
theorem exists_enorm_le_mul_eLpNorm_jet [CompleteSpace V] {p : ℝ≥0} (hp : 2 < p) :
    ∃ C : ℝ≥0, ∀ {ξ : ℝ × ℝ → V}, ContDiffOn ℝ 1 ξ (univ ×ˢ Ioo 0 1) →
      ContinuousOn ξ (univ ×ˢ Icc 0 1) → ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1,
        ‖ξ z‖ₑ ≤ C * eLpNorm (jet ξ) p stripMeasure := by
  have hn : finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hp' : (finrank ℝ (ℝ × ℝ) : ℝ≥0) < p := by rw [hn]; exact_mod_cast hp
  have hp1 : 1 ≤ p := le_of_lt (lt_of_le_of_lt (by norm_num) hp)
  -- Morrey's bound for domains meeting the unit ball about the point in area at least `1`.
  obtain ⟨C, hC⟩ := exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv (μ := volume) (F := V) hp1 hp'
    1 (m := ENNReal.ofReal 1 * ENNReal.ofReal 1) (by norm_num)
  refine ⟨3 * C, fun {ξ} hξ hξc ↦ ?_⟩
  -- The bound at the points of the open strip, from the rectangle `(s - 1, s + 1) × (0, 1)`.
  have hint : ∀ z ∈ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1,
      ‖ξ z‖ₑ ≤ ↑(3 * C) * eLpNorm (jet ξ) p stripMeasure := by
    intro z hz
    set Ω := Ioo (z.1 - 1) (z.1 + 1) ×ˢ Ioo (0 : ℝ) 1
    have hΩo : IsOpen Ω := isOpen_Ioo.prod isOpen_Ioo
    have hzΩ : z ∈ Ω := ⟨⟨by linarith, by linarith⟩, hz.2⟩
    have hΩs : Ω ⊆ univ ×ˢ Ioo 0 1 := prod_mono (subset_univ _) subset_rfl
    have hξΩ : ContDiffOn ℝ 1 ξ Ω := hξ.mono hΩs
    have hΩm : ENNReal.ofReal 1 * ENNReal.ofReal 1 ≤ volume (Ω ∩ ball z 1) :=
      ofReal_mul_ofReal_le_volume_Ioo_prod_Ioo_inter_ball le_rfl (by linarith) le_rfl
        (by norm_num) ⟨⟨by linarith, by linarith⟩, Ioo_subset_Icc_self hz.2⟩
    -- The `Lᵖ` norms over the rectangle are controlled by the jet on the strip.
    have hμ : volume.restrict Ω ≤ stripMeasure :=
      Measure.restrict_mono (hΩs.trans (prod_mono subset_rfl Ioo_subset_Icc_self)) le_rfl
    have hval := eLpNorm_le_eLpNorm_jet (μ := volume.restrict Ω)
      (hξΩ.continuousOn.aestronglyMeasurable hΩo.measurableSet) p
    have hder := eLpNorm_fderiv_le_two_mul_eLpNorm_jet (μ := volume.restrict Ω)
      ((hξΩ.continuousOn_fderiv_of_isOpen hΩo le_rfl).aestronglyMeasurable hΩo.measurableSet) p
    have hjet := eLpNorm_mono_measure (jet ξ) (p := p) hμ
    set N := eLpNorm (jet ξ) p (volume.restrict Ω)
    calc ‖ξ z‖ₑ ≤ C * (eLpNorm ξ p (volume.restrict Ω) +
          eLpNorm (fderiv ℝ ξ) p (volume.restrict Ω)) :=
          hC Ω ξ z hΩo (((convex_Ioo _ _).prod (convex_Ioo _ _)).starConvex hzΩ) hξΩ hΩm
      _ ≤ C * (N + 2 * N) := by gcongr
      _ = ↑(3 * C) * N := by push_cast; ring
      _ ≤ ↑(3 * C) * eLpNorm (jet ξ) p stripMeasure := by gcongr
  -- The bound extends to the boundary lines by continuity.
  intro z hz
  have hcl : z ∈ closure ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) := by
    rwa [closure_prod_eq, closure_univ, closure_Ioo zero_ne_one]
  exact ContinuousWithinAt.closure_le hcl
    ((continuous_eNorm.continuousAt.comp_continuousWithinAt (hξc z hz)).mono
      (prod_mono subset_rfl Ioo_subset_Icc_self))
    continuousWithinAt_const hint

end TauCeti.StripSobolev
