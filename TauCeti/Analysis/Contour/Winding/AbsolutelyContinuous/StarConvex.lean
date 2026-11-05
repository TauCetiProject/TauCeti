/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
public import Mathlib.Analysis.Convex.Star
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Proximity
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Path
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Reparam
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Path
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Reparam

/-!
# Winding numbers of absolutely continuous curves in star-shaped sets

A closed absolutely continuous curve contained in a set `Ω` that is star-shaped about `x` has
winding number `0` about every point outside `Ω`, by straight-line contraction to the constant
curve at `x`. Consequently, two absolutely continuous paths in `Ω` sharing both endpoints have
the same winding number about every point outside `Ω`.

## References

* S. Lang, *Complex Analysis*, Ch. IV.
-/

public section

open Set

namespace TauCeti.Contour

variable {γ γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- **The winding number of a closed absolutely continuous curve vanishes outside any star-shaped
set containing its trace.** -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_starConvex
    {Ω : Set ℂ} {x : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hstar : StarConvex ℝ x Ω) (hclosed : γ a = γ b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hw : w ∉ Ω) :
    windingNumber γ a b w = 0 := by
  let c : ℝ → ℂ := Function.const ℝ x
  have hc : AbsolutelyContinuousOnInterval c a b :=
    (LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval
  have hseg : ∀ t ∈ uIcc a b, w ∉ segment ℝ (γ t) (c t) := by
    intro t ht hwt
    rw [segment_symm] at hwt
    exact hw (hstar.segment_subset (hγΩ t ht) hwt)
  rw [← hγ.windingNumber_eq_of_notMem_segment hc hclosed rfl hseg]
  exact windingNumber_const x a b w

/-- **A closed absolutely continuous curve in a star-shaped set is null-homologous there.** -/
theorem _root_.AbsolutelyContinuousOnInterval.isNullHomologous_of_starConvex
    {Ω : Set ℂ} {x : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hstar : StarConvex ℝ x Ω) (hclosed : γ a = γ b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) :
    IsNullHomologous γ a b Ω :=
  isNullHomologous_iff.mpr fun _ hw ↦
    hγ.windingNumber_eq_zero_of_starConvex hstar hclosed hγΩ hw

/-- Affine normalization of an absolutely continuous curve on `[a, b]` to a `Path` on `[0, 1]`. -/
private noncomputable def lineMapPath (hγ : AbsolutelyContinuousOnInterval γ a b) :
    Path (γ a) (γ b) where
  toFun t := γ (AffineMap.lineMap a b (t : ℝ))
  continuous_toFun := hγ.comp_lineMap.continuousOn.comp_continuous continuous_subtype_val
    fun t ↦ (uIcc_of_le (zero_le_one' ℝ)).symm ▸ t.2
  source' := by simp
  target' := by simp

/-- **Two absolutely continuous paths in a star-shaped set with common endpoints have equal
winding numbers outside that set.** -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_starConvex_of_eq_endpoints
    {Ω : Set ℂ} {x : ℂ} (h₀ : AbsolutelyContinuousOnInterval γ₀ a b)
    (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (hstar : StarConvex ℝ x Ω) (ha : γ₀ a = γ₁ a) (hb : γ₀ b = γ₁ b)
    (h₀Ω : ∀ t ∈ uIcc a b, γ₀ t ∈ Ω) (h₁Ω : ∀ t ∈ uIcc a b, γ₁ t ∈ Ω) (hw : w ∉ Ω) :
    windingNumber γ₀ a b w = windingNumber γ₁ a b w := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hmap : MapsTo (AffineMap.lineMap a b) (Icc (0 : ℝ) 1) (uIcc a b) := by
    rw [mapsTo_iff_image_subset, ← segment_eq_image_lineMap, segment_eq_uIcc]
  let p₀ : Path (γ₀ a) (γ₀ b) := lineMapPath h₀
  let p₁ : Path (γ₀ a) (γ₀ b) := (lineMapPath h₁).cast ha hb
  have hp₀ : AbsolutelyContinuousOnInterval p₀.extend 0 1 :=
    h₀.comp_lineMap.congr fun t ht ↦ (p₀.extend_apply (uIcc_of_le h01 ▸ ht)).symm
  have hp₁ : AbsolutelyContinuousOnInterval p₁.extend 0 1 :=
    h₁.comp_lineMap.congr fun t ht ↦ (p₁.extend_apply (uIcc_of_le h01 ▸ ht)).symm
  have hp₀Ω : ∀ t : Icc (0 : ℝ) 1, p₀ t ∈ Ω := fun t ↦ h₀Ω _ (hmap t.2)
  have hp₁Ω : ∀ t : Icc (0 : ℝ) 1, p₁ t ∈ Ω := fun t ↦ h₁Ω _ (hmap t.2)
  have hp₁symm : ∀ t : Icc (0 : ℝ) 1, p₁.symm t ≠ w := fun t ht ↦ by
    obtain ⟨u, rfl⟩ : w ∈ range p₁ := by rw [← Path.symm_range]; exact ⟨t, ht⟩
    exact hw (hp₁Ω u)
  have hloopΩ : ∀ t ∈ uIcc (0 : ℝ) 1, (p₀.trans p₁.symm).extend t ∈ Ω := fun t ht ↦ by
    have ht' : t ∈ Icc (0 : ℝ) 1 := uIcc_of_le h01 ▸ ht
    rw [(p₀.trans p₁.symm).extend_apply ht']
    have hmem : (p₀.trans p₁.symm) ⟨t, ht'⟩ ∈ range (p₀.trans p₁.symm) := mem_range_self _
    rw [Path.trans_range, Path.symm_range] at hmem
    exact hmem.elim (fun ⟨u, hu⟩ ↦ hu ▸ hp₀Ω u) (fun ⟨u, hu⟩ ↦ hu ▸ hp₁Ω u)
  have hzero : windingNumber (p₀.trans p₁.symm).extend 0 1 w = 0 :=
    (Path.absolutelyContinuousOnInterval_extend_trans hp₀
      (Path.absolutelyContinuousOnInterval_extend_symm hp₁)).windingNumber_eq_zero_of_starConvex
      hstar (by simp) hloopΩ hw
  rw [hp₀.windingNumber_path_trans (Path.absolutelyContinuousOnInterval_extend_symm hp₁)
      (fun t ht ↦ hw (by rw [← ht]; exact hp₀Ω t)) hp₁symm,
    hp₁.windingNumber_path_symm (fun t ht ↦ hw (by rw [← ht]; exact hp₁Ω t))] at hzero
  have hw₀ : windingNumber p₀.extend 0 1 w = windingNumber γ₀ a b w := by
    rw [windingNumber_congr_curve (γ₂ := γ₀ ∘ AffineMap.lineMap a b)
      (fun t ht ↦ p₀.extend_apply (Ioo_subset_Icc_self (uIoo_of_le h01 ▸ ht))),
      h₀.windingNumber_comp_lineMap fun ⟨t, ht, htw⟩ ↦ hw (htw ▸ h₀Ω t ht)]
  have hw₁ : windingNumber p₁.extend 0 1 w = windingNumber γ₁ a b w := by
    rw [windingNumber_congr_curve (γ₂ := γ₁ ∘ AffineMap.lineMap a b)
      (fun t ht ↦ p₁.extend_apply (Ioo_subset_Icc_self (uIoo_of_le h01 ▸ ht))),
      h₁.windingNumber_comp_lineMap fun ⟨t, ht, htw⟩ ↦ hw (htw ▸ h₁Ω t ht)]
  exact sub_eq_zero.mp (by linear_combination -hw₀ + hw₁ + hzero)

end TauCeti.Contour
