/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.Basic

/-!
# The transition between the two affine charts of the plane blow-up

In the upper chart, the overlap with the lower chart is the locus `v ≠ 0`. The change of
coordinates is `(u, v) ↦ (v⁻¹, u * v)`. In particular, the exceptional axes are glued by
inversion of their nonzero coordinates. The formulas hold on the exceptional fibre as well
as away from it: they are computed from monomials on the common diagonal-face chart.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open Multiplicative Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric

private abbrev upper : affinePlaneBlowUpFan.cones :=
  ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inr (.refl _))⟩

private abbrev lower : affinePlaneBlowUpFan.cones :=
  ⟨affinePlaneBlowUpLowerCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inl (.refl _))⟩

private abbrev diagonal : affinePlaneBlowUpFan.cones :=
  ⟨affinePlaneBlowUpDiagonalCone, affinePlaneBlowUpDiagonalCone_mem_affinePlaneBlowUpFan_cones⟩

private abbrev upperFace := affinePlaneBlowUpDiagonalCone_isFaceOf_affinePlaneBlowUpUpperCone
private abbrev lowerFace := affinePlaneBlowUpDiagonalCone_isFaceOf_affinePlaneBlowUpLowerCone

private theorem upper_realCharacter₂ :
    affinePlaneBlowUpFan.lattice.realCharacter affinePlaneBlowUpUpperCharacter₂ =
      (LinearMap.proj 0).comp (LinearMap.snd ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)) -
        (LinearMap.proj 0).comp (LinearMap.fst ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)) := by
  apply Eq.symm
  apply affinePlaneBlowUpFan.lattice.eq_realCharacter
  intro n
  simp

private theorem upper_inf_ker :
    affinePlaneBlowUpUpperCone ⊓ PointedCone.ofSubmodule
      (LinearMap.ker (affinePlaneBlowUpFan.lattice.realCharacter
        affinePlaneBlowUpUpperCharacter₂)) = affinePlaneBlowUpDiagonalCone := by
  ext x
  simp only [Submodule.mem_inf, PointedCone.mem_ofSubmodule_iff, LinearMap.mem_ker,
    upper_realCharacter₂, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.snd_apply, LinearMap.fst_apply, sub_eq_zero,
    mem_affinePlaneBlowUpUpperCone_iff, mem_affinePlaneBlowUpDiagonalCone_iff]
  grind

private theorem diagonal_coordinates
    (x : AffineSemigroupComplexPoint
      (dualSemigroup affinePlaneBlowUpFan.lattice affinePlaneBlowUpDiagonalCone)) :
    let u := affinePlaneBlowUpUpperPointHomeomorph
      (faceAffinePointMap affinePlaneBlowUpFan.lattice upperFace x)
    let v := affinePlaneBlowUpLowerPointHomeomorph
      (faceAffinePointMap affinePlaneBlowUpFan.lattice lowerFace x)
    u.2 ≠ 0 ∧ v = (u.2⁻¹, u.1 * u.2) := by
  let a : dualSemigroup affinePlaneBlowUpFan.lattice affinePlaneBlowUpDiagonalCone :=
    ⟨affinePlaneBlowUpUpperCharacter₁, dualSemigroup_anti _ upperFace.le
      affinePlaneBlowUpUpperCharacter₁.2⟩
  let b : dualSemigroup affinePlaneBlowUpFan.lattice affinePlaneBlowUpDiagonalCone :=
    ⟨affinePlaneBlowUpUpperCharacter₂, dualSemigroup_anti _ upperFace.le
      affinePlaneBlowUpUpperCharacter₂.2⟩
  let c : dualSemigroup affinePlaneBlowUpFan.lattice affinePlaneBlowUpDiagonalCone :=
    ⟨affinePlaneBlowUpLowerCharacter₁, dualSemigroup_anti _ lowerFace.le
      affinePlaneBlowUpLowerCharacter₁.2⟩
  let d : dualSemigroup affinePlaneBlowUpFan.lattice affinePlaneBlowUpDiagonalCone :=
    ⟨affinePlaneBlowUpLowerCharacter₂, dualSemigroup_anti _ lowerFace.le
      affinePlaneBlowUpLowerCharacter₂.2⟩
  have hbc : b + c = 0 := by ext n; simp [b, c]
  have hab : a + b = d := by ext n; simp [a, b, d]
  have hprod : x (MonoidAlgebra.single (ofAdd b) 1) *
      x (MonoidAlgebra.single (ofAdd c) 1) = 1 := by
    rw [← AffineSemigroupComplexPoint.apply_single_add, hbc, ofAdd_zero,
      ← MonoidAlgebra.one_def, map_one]
  have hsum := (AffineSemigroupComplexPoint.apply_single_add x a b).symm
  rw [hab] at hsum
  dsimp only
  simp only [affinePlaneBlowUpUpperPointHomeomorph_apply,
    affinePlaneBlowUpLowerPointHomeomorph_apply, faceAffinePointMap_apply_single]
  exact ⟨left_ne_zero_of_mul_eq_one hprod,
    Prod.ext (inv_eq_of_mul_eq_one_right hprod).symm hsum.symm⟩

/-- On the overlap of the two blow-up charts, the lower coordinates of an upper-chart point
`(u, v)` are `(v⁻¹, u * v)`. This includes points on the exceptional axis `u = 0`. -/
theorem affinePlaneBlowUpUpperChart_eq_lowerChart (z : ℂ × ℂ) (hz : z.2 ≠ 0) :
    affinePlaneBlowUpUpperChart z = affinePlaneBlowUpLowerChart (z.2⁻¹, z.1 * z.2) := by
  let x : AffineSemigroupComplexPoint
      (dualSemigroup affinePlaneBlowUpFan.lattice affinePlaneBlowUpUpperCone) :=
    affinePlaneBlowUpUpperPointHomeomorph.symm z
  have hu : affinePlaneBlowUpUpperPointHomeomorph x = z :=
    affinePlaneBlowUpUpperPointHomeomorph.apply_symm_apply z
  have hx : x (MonoidAlgebra.single (ofAdd affinePlaneBlowUpUpperCharacter₂) 1) ≠ 0 := by
    have h : x (MonoidAlgebra.single (ofAdd affinePlaneBlowUpUpperCharacter₂) 1) = z.2 := by
      simpa only [affinePlaneBlowUpUpperPointHomeomorph_apply] using congrArg Prod.snd hu
    rw [h]
    exact hz
  have hrange : x ∈ Set.range (faceAffinePointMap affinePlaneBlowUpFan.lattice upperFace) := by
    rw [range_faceAffinePointMap_of_inf_ker_eq affinePlaneBlowUpFan.lattice
      isRegularCone_affinePlaneBlowUpUpperCone.fg upperFace
      affinePlaneBlowUpUpperCharacter₂ upper_inf_ker]
    exact hx
  obtain ⟨p, hp⟩ := hrange
  have hupper : affinePlaneBlowUpUpperPointHomeomorph
      (faceAffinePointMap affinePlaneBlowUpFan.lattice upperFace p) = z := hp ▸ hu
  have hlower := (diagonal_coordinates p).2
  dsimp only at hlower
  rw [hupper] at hlower
  rw [affinePlaneBlowUpUpperChart_def, affinePlaneBlowUpLowerChart_def]
  rw [← hlower]
  -- The point homeomorphisms use bundled chart topologies; `erw` reads their underlying points.
  erw [Homeomorph.symm_apply_apply]
  exact (congrArg (affinePlaneBlowUpFan.analyticAffineChartι
    isRegular_affinePlaneBlowUpFan upper) hp.symm).trans
      (affinePlaneBlowUpFan.analyticAffineChartι_faceAffinePointMap_eq
        isRegular_affinePlaneBlowUpFan (υ := diagonal) upperFace.le lowerFace.le p)

/-- Two points in the upper and lower blow-up charts represent the same point exactly when
the upper point lies in the overlap and the lower coordinates are the prescribed transition. -/
@[simp]
theorem affinePlaneBlowUpUpperChart_eq_lowerChart_iff (z w : ℂ × ℂ) :
    affinePlaneBlowUpUpperChart z = affinePlaneBlowUpLowerChart w ↔
      z.2 ≠ 0 ∧ w = (z.2⁻¹, z.1 * z.2) := by
  constructor
  · intro h
    have hmeet : upper ⊓ lower = diagonal := by
      apply Subtype.ext
      exact inf_comm _ _ |>.trans affinePlaneBlowUpLowerCone_inf_affinePlaneBlowUpUpperCone
    have hm : affinePlaneBlowUpUpperChart z ∈
        Set.range (affinePlaneBlowUpFan.analyticAffineChartι
          isRegular_affinePlaneBlowUpFan upper) ∩
        Set.range (affinePlaneBlowUpFan.analyticAffineChartι
          isRegular_affinePlaneBlowUpFan lower) :=
      ⟨⟨_, (affinePlaneBlowUpUpperChart_def z).symm⟩,
        ⟨_, (affinePlaneBlowUpLowerChart_def w).symm.trans h.symm⟩⟩
    rw [Fan.range_analyticAffineChartι_inter_range_analyticAffineChartι, hmeet] at hm
    obtain ⟨p, hp⟩ := hm
    have hu := (affinePlaneBlowUpFan.isOpenEmbedding_analyticAffineChartι
      isRegular_affinePlaneBlowUpFan upper).injective
      ((affinePlaneBlowUpFan.analyticAffineChartι_faceAffinePointMap
        isRegular_affinePlaneBlowUpFan (τ := diagonal) upperFace.le p).trans
          (hp.trans (affinePlaneBlowUpUpperChart_def z)))
    have hl := (affinePlaneBlowUpFan.isOpenEmbedding_analyticAffineChartι
      isRegular_affinePlaneBlowUpFan lower).injective
      ((affinePlaneBlowUpFan.analyticAffineChartι_faceAffinePointMap
        isRegular_affinePlaneBlowUpFan (τ := diagonal) lowerFace.le p).trans
          (hp.trans (h.trans (affinePlaneBlowUpLowerChart_def w))))
    have hu' := congrArg affinePlaneBlowUpUpperPointHomeomorph hu
    have hl' := congrArg affinePlaneBlowUpLowerPointHomeomorph hl
    simp only [Homeomorph.apply_symm_apply] at hu' hl'
    simpa only [hu', hl'] using diagonal_coordinates p
  · rintro ⟨hz, rfl⟩
    exact affinePlaneBlowUpUpperChart_eq_lowerChart z hz

/-- In lower coordinates, the change to the upper chart is `(s, t) ↦ (s * t, s⁻¹)`. -/
theorem affinePlaneBlowUpLowerChart_eq_upperChart (w : ℂ × ℂ) (hw : w.1 ≠ 0) :
    affinePlaneBlowUpLowerChart w = affinePlaneBlowUpUpperChart (w.1 * w.2, w.1⁻¹) := by
  have h := affinePlaneBlowUpUpperChart_eq_lowerChart
    (w.1 * w.2, w.1⁻¹) (inv_ne_zero hw)
  have hmul : (w.1 * w.2) * w.1⁻¹ = w.2 := by
    field_simp
  simpa only [Prod.fst, Prod.snd, inv_inv, hmul, Prod.eta] using h.symm

/-- The overlap with the lower chart is exactly the nonzero second-coordinate locus in the
upper chart. -/
@[simp↓]
theorem affinePlaneBlowUpUpperChart_mem_range_lowerChart_iff (z : ℂ × ℂ) :
    affinePlaneBlowUpUpperChart z ∈ Set.range affinePlaneBlowUpLowerChart ↔ z.2 ≠ 0 := by
  constructor
  · rintro ⟨w, hw⟩
    exact ((affinePlaneBlowUpUpperChart_eq_lowerChart_iff z w).1 hw.symm).1
  · intro hz
    exact ⟨_, (affinePlaneBlowUpUpperChart_eq_lowerChart z hz).symm⟩

/-- The overlap with the upper chart is exactly the nonzero first-coordinate locus in the
lower chart. -/
@[simp↓]
theorem affinePlaneBlowUpLowerChart_mem_range_upperChart_iff (w : ℂ × ℂ) :
    affinePlaneBlowUpLowerChart w ∈ Set.range affinePlaneBlowUpUpperChart ↔ w.1 ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hz₂, rfl⟩ := (affinePlaneBlowUpUpperChart_eq_lowerChart_iff z w).1 hz
    exact inv_ne_zero hz₂
  · intro hw
    exact ⟨_, (affinePlaneBlowUpLowerChart_eq_upperChart w hw).symm⟩

/-- The biholomorphic change from upper to lower blow-up coordinates. Its source is `v ≠ 0`,
its target is `s ≠ 0`, and its inverse sends `(s, t)` to `(s * t, s⁻¹)`. -/
noncomputable def affinePlaneBlowUpTransition (n : ℕ∞ω) :
    PartialDiffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ) n where
  toFun z := (z.2⁻¹, z.1 * z.2)
  invFun w := (w.1 * w.2, w.1⁻¹)
  source := {z | z.2 ≠ 0}
  target := {w | w.1 ≠ 0}
  map_source' _ hz := inv_ne_zero hz
  map_target' _ hw := inv_ne_zero hw
  left_inv' z hz := by
    simp only [Set.mem_ofPred_eq] at hz
    apply Prod.ext <;> dsimp only <;> field_simp
  right_inv' w hw := by
    simp only [Set.mem_ofPred_eq] at hw
    apply Prod.ext <;> dsimp only <;> field_simp
  open_source := isOpen_ne_fun continuous_snd continuous_const
  open_target := isOpen_ne_fun continuous_fst continuous_const
  contMDiffOn_toFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (contDiff_snd.contDiffOn.inv fun _ hz ↦ hz).prodMk
      (contDiff_fst.mul contDiff_snd).contDiffOn
  contMDiffOn_invFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (contDiff_fst.mul contDiff_snd).contDiffOn.prodMk
      (contDiff_fst.contDiffOn.inv fun _ hw ↦ hw)

/-- The transition is defined precisely on the upper-chart overlap. -/
@[simp]
theorem affinePlaneBlowUpTransition_source (n : ℕ∞ω) :
    (affinePlaneBlowUpTransition n).source = {z | z.2 ≠ 0} := (rfl)

/-- The transition has the lower-chart overlap as its target. -/
@[simp]
theorem affinePlaneBlowUpTransition_target (n : ℕ∞ω) :
    (affinePlaneBlowUpTransition n).target = {w | w.1 ≠ 0} := (rfl)

/-- The forward transition formula. -/
@[simp]
theorem affinePlaneBlowUpTransition_apply (n : ℕ∞ω) (z : ℂ × ℂ) :
    affinePlaneBlowUpTransition n z = (z.2⁻¹, z.1 * z.2) := (rfl)

/-- The inverse transition formula. -/
@[simp]
theorem affinePlaneBlowUpTransition_invFun (n : ℕ∞ω) (w : ℂ × ℂ) :
    (affinePlaneBlowUpTransition n).invFun w = (w.1 * w.2, w.1⁻¹) := (rfl)

/-- Applying the forward transition on its source preserves the represented blow-up point. -/
theorem affinePlaneBlowUpLowerChart_transition (n : ℕ∞ω) (z : ℂ × ℂ)
    (hz : z ∈ (affinePlaneBlowUpTransition n).source) :
    affinePlaneBlowUpLowerChart (affinePlaneBlowUpTransition n z) =
      affinePlaneBlowUpUpperChart z := by
  simpa only [affinePlaneBlowUpTransition_apply] using
    (affinePlaneBlowUpUpperChart_eq_lowerChart z
      (by simpa only [affinePlaneBlowUpTransition_source, Set.mem_ofPred_eq] using hz)).symm

/-- Applying the inverse transition on its target preserves the represented blow-up point. -/
theorem affinePlaneBlowUpUpperChart_transition_invFun (n : ℕ∞ω) (w : ℂ × ℂ)
    (hw : w ∈ (affinePlaneBlowUpTransition n).target) :
    affinePlaneBlowUpUpperChart ((affinePlaneBlowUpTransition n).invFun w) =
      affinePlaneBlowUpLowerChart w := by
  simpa only [affinePlaneBlowUpTransition_invFun] using
    (affinePlaneBlowUpLowerChart_eq_upperChart w
      (by simpa only [affinePlaneBlowUpTransition_target, Set.mem_ofPred_eq] using hw)).symm

end TauCeti.Toric
