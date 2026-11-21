/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Area
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Topology.Algebra.Order.Floor
import TauCeti.Topology.Homotopy.Path

/-!
# Smooth representatives of raw caps

Let `M` be a Hausdorff boundaryless manifold modelled on a finite-dimensional space, and `γ` a loop
in `M` based at `x` whose `1`-periodic extension `g : ℝ → M` is smooth, as for a one-periodic
orbit of a Hamiltonian. This file proves that every raw cap of `γ`
(`TauCeti.Floer.RawCap γ`), a homotopy class of continuous discs bounding `γ`, is the homotopy
class of a smooth based cap (`TauCeti.Floer.IsSmoothBasedCap`)
(`TauCeti.Floer.RawCap.exists_isSmoothBasedCap_homotopyClass_eq`). Consequently a loop has a smooth
based cap exactly when it is null-homotopic and its periodic extension is smooth
(`TauCeti.Floer.exists_isSmoothBasedCap_iff`). This discharges the hypothesis of
`TauCeti.Floer.RawCap.area` for every smooth contractible loop, and the area of every raw cap of
such a loop is the integral of the form over a smooth based cap in its class
(`TauCeti.Floer.RawCap.exists_area_eq_rectangleIntegral`).

The proof smooths a disc relative to its boundary, keeping the boundary values exactly. A raw cap
is the class of a path `P` in the loop space from `γ` to the constant loop. It is first replaced
by a continuous map of the plane which is already smooth off a rectangle inside the unit square.
Fix a smooth map `c` of `[0, 1]` onto itself which is `0` near `0` and `1` near `1`
(`TauCeti.collaredSmoothTransition`), and its linear interpolation `τ_r = (1 - r) id + r c` with
the identity (`TauCeti.collaredSmoothTransitionLineMap`). Then:

* near the edge `s = 0` the map is `g ∘ τ_r`, with `r` rising smoothly from `0` to `1`;
* the rest of the disc is `P` precomposed with `c` in the loop direction, so it is constant
  equal to `x` near the seam `t ∈ ℤ` and near the edge `s = 1`.

Its class is that of `P`: it is the image of the diagonal of the square of loops
`(r, s) ↦ P s ∘ τ_r`, which is constant along its top edge. The relative Whitney approximation
theorem (`ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`) then makes it
smooth without changing it off the rectangle. The result is periodized in `t`; since the map is
periodic near the seam, the periodization is still smooth, and on the unit square it is the
smoothed map.

## Main results

* `TauCeti.Floer.RawCap.exists_isSmoothBasedCap_homotopyClass_eq`: every raw cap of a loop with a
  smooth periodic extension is the homotopy class of a smooth based cap.
* `TauCeti.Floer.exists_isSmoothBasedCap_iff`: a loop has a smooth based cap exactly when it is
  null-homotopic and its periodic extension is smooth.
* `TauCeti.Floer.RawCap.exists_area_eq_rectangleIntegral`: the area of every raw cap of such a loop
  is the integral of the form over a smooth based cap representing it.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 6 (the Whitney approximation
  theorem for maps into manifolds, relative to a closed set).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (capped periodic orbits and their action).
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti.Floer

/-! ### Reparametrizations -/

section Reparam

/-- A smooth map of the line which is `0` up to `1/6` and `1` from `1/4` on. -/
private def capRamp (s : ℝ) : ℝ :=
  Real.smoothTransition (12 * s - 2)

private theorem capRamp_of_le {s : ℝ} (hs : s ≤ 1 / 6) : capRamp s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem capRamp_of_ge {s : ℝ} (hs : 1 / 4 ≤ s) : capRamp s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem capRamp_mem (s : ℝ) : capRamp s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem contDiff_capRamp : ContDiff ℝ ∞ capRamp :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem contDiff_lineMap_capRamp :
    ContDiff ℝ ∞ fun z : ℝ × ℝ ↦ collaredSmoothTransitionLineMap (capRamp z.1) z.2 :=
  (contDiff_collaredSmoothTransitionLineMap le_rfl).comp
    ((contDiff_capRamp.comp contDiff_fst).prodMk contDiff_snd)

end Reparam

/-! ### A model of a cap which is smooth near the boundary of a rectangle -/

section Model

variable {M : Type*} [TopologicalSpace M] {x : M} {γ : Ω M x}

/-- The model of the raw cap of `P`, for a periodic extension `g` of `γ`: `g` precomposed with
`collaredSmoothTransitionLineMap (capRamp s)` for `s ≤ 1/3`, and `P` precomposed with
`collaredSmoothTransition` in the loop direction, run three times as fast, beyond. It is smooth
near the edge `s = 0` and equal to `x` near the seam and near the edge `s = 1`. -/
private def capModel (g : ℝ → M) (P : Path γ (Path.refl x)) (z : ℝ × ℝ) : M :=
  if z.1 ≤ 1 / 3 then g (collaredSmoothTransitionLineMap (capRamp z.1) z.2)
  else P (projIcc 0 1 zero_le_one (3 * z.1 - 1)) (collaredSmoothTransitionUnit z.2)

variable {g : ℝ → M} {P : Path γ (Path.refl x)}

private theorem capModel_of_le {z : ℝ × ℝ} (hz : z.1 ≤ 1 / 3) :
    capModel g P z = g (collaredSmoothTransitionLineMap (capRamp z.1) z.2) := by
  simp only [capModel, hz, ↓reduceIte]

private theorem capModel_of_lt {z : ℝ × ℝ} (hz : 1 / 3 < z.1) :
    capModel g P z =
      P (projIcc 0 1 zero_le_one (3 * z.1 - 1)) (collaredSmoothTransitionUnit z.2) := by
  simp only [capModel, hz.not_ge, ↓reduceIte]

private theorem continuous_uncurry_path (P : Path γ (Path.refl x)) :
    Continuous fun q : unitInterval × unitInterval ↦ P q.1 q.2 :=
  Path.continuous_uncurry_iff.2 P.continuous

private theorem capModel_zero (t : ℝ) : capModel g P (0, t) = g t := by
  rw [capModel_of_le (by norm_num), capRamp_of_le (by norm_num),
    collaredSmoothTransitionLineMap_zero_left]

variable (hgγ : ∀ t : unitInterval, g t = γ t)
include hgγ

private theorem apply_zero_eq_base : g 0 = x := by
  rw [← Icc.coe_zero, hgγ, γ.source]

private theorem apply_one_eq_base : g 1 = x := by
  rw [← Icc.coe_one, hgγ, γ.target]

private theorem capModel_eq_of_mem (s t : unitInterval) :
    capModel g P (s, t) = P (projIcc 0 1 zero_le_one (3 * s - 1))
      (collaredSmoothTransitionLineMapUnit (projIcc 0 1 zero_le_one (capRamp s)) t) := by
  rw [projIcc_of_mem _ (capRamp_mem s)]
  rcases le_or_gt (s : ℝ) (1 / 3) with hs | hs
  · simp [capModel_of_le (z := ((s : ℝ), (t : ℝ))) hs,
      projIcc_of_le_left _ (by linarith : 3 * (s : ℝ) - 1 ≤ 0), ← hgγ]
  · have hr : (⟨capRamp s, capRamp_mem s⟩ : unitInterval) = 1 :=
      Subtype.ext (capRamp_of_ge (by linarith))
    rw [capModel_of_lt hs, hr, collaredSmoothTransitionLineMapUnit_one_left]

private theorem continuous_capModel (hg : Continuous g) : Continuous (capModel g P) := by
  have hr : Continuous fun z : ℝ × ℝ ↦ collaredSmoothTransitionLineMap (capRamp z.1) z.2 :=
    continuous_collaredSmoothTransitionLineMap.comp
      ((contDiff_capRamp.continuous.comp continuous_fst).prodMk continuous_snd)
  have hs : Continuous fun z : ℝ × ℝ ↦ projIcc (0 : ℝ) 1 zero_le_one (3 * z.1 - 1) :=
    continuous_projIcc.comp ((continuous_const.mul continuous_fst).sub continuous_const)
  refine Continuous.if_le (hg.comp hr) ((continuous_uncurry_path P).comp
    (hs.prodMk (continuous_collaredSmoothTransitionUnit.comp continuous_snd)))
    continuous_fst continuous_const fun z hz ↦ ?_
  simp [capRamp_of_ge (by linarith : 1 / 4 ≤ z.1),
    projIcc_of_le_left _ (by linarith : 3 * z.1 - 1 ≤ 0), ← hgγ, collaredSmoothTransition_def]

/-- The model is `x` beyond `s = 2/3`, and near the seam beyond `s = 1/4`. -/
private theorem capModel_eq_base {z : ℝ × ℝ}
    (hz : 2 / 3 < z.1 ∨ 1 / 4 < z.1 ∧ (z.2 ≤ 1 / 4 ∨ 3 / 4 ≤ z.2)) : capModel g P z = x := by
  rcases le_or_gt z.1 (1 / 3) with hs | hs
  · have hz' : 1 / 4 < z.1 ∧ (z.2 ≤ 1 / 4 ∨ 3 / 4 ≤ z.2) := hz.resolve_left (by linarith)
    rcases hz'.2 with ht | ht
    · simp [capModel_of_le hs, capRamp_of_ge hz'.1.le, collaredSmoothTransition_eq_zero_of_le ht,
        apply_zero_eq_base hgγ]
    · simp [capModel_of_le hs, capRamp_of_ge hz'.1.le, collaredSmoothTransition_eq_one_of_ge ht,
        apply_one_eq_base hgγ]
  · rcases hz with hz | ⟨-, ht | ht⟩
    · simp [capModel_of_lt hs, projIcc_of_right_le _ (by linarith : 1 ≤ 3 * z.1 - 1)]
    · simp [capModel_of_lt hs, collaredSmoothTransitionUnit_eq_zero_of_le ht]
    · simp [capModel_of_lt hs, collaredSmoothTransitionUnit_eq_one_of_ge ht]

private theorem capModel_one (t : ℝ) : capModel g P (1, t) = x :=
  capModel_eq_base hgγ (Or.inl (by norm_num))

private theorem capModel_seam_zero (s : ℝ) : capModel g P (s, 0) = x := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [capModel_of_le hs, collaredSmoothTransitionLineMap_zero_right, apply_zero_eq_base hgγ]
  · rw [capModel_of_lt hs, collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num), Path.source]

private theorem capModel_seam_one (s : ℝ) : capModel g P (s, 1) = x := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [capModel_of_le hs, collaredSmoothTransitionLineMap_one_right, apply_one_eq_base hgγ]
  · rw [capModel_of_lt hs, collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num), Path.target]

/-- The model is periodic in `t` near the seam. -/
private theorem capModel_add_one (hgp : Periodic g 1) (s : ℝ) {t : ℝ} (ht₀ : -1 / 4 ≤ t)
    (ht₁ : t ≤ 1 / 4) : capModel g P (s, t + 1) = capModel g P (s, t) := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [capModel_of_le hs, capModel_of_le hs, collaredSmoothTransitionLineMap_add_one _ ht₀ ht₁,
      hgp]
  · rw [capModel_eq_base hgγ (Or.inr ⟨by linarith, Or.inr (by linarith)⟩),
      capModel_eq_base hgγ (Or.inr ⟨by linarith, Or.inl ht₁⟩)]

/-- The open set on which the model is constant equal to the base point. -/
private def capBaseSet : Set (ℝ × ℝ) :=
  {z | 2 / 3 < z.1} ∪ ({z | 1 / 4 < z.1} ∩ ({z | z.2 < 1 / 4} ∪ {z | 3 / 4 < z.2}))

omit hgγ in
private theorem isOpen_capBaseSet : IsOpen capBaseSet :=
  (isOpen_lt continuous_const continuous_fst).union <|
    (isOpen_lt continuous_const continuous_fst).inter <|
      (isOpen_lt continuous_snd continuous_const).union (isOpen_lt continuous_const continuous_snd)

private theorem capModel_of_mem_capBaseSet {z : ℝ × ℝ} (hz : z ∈ capBaseSet) :
    capModel g P z = x := by
  refine capModel_eq_base hgγ ?_
  rcases hz with hz | ⟨hz, ht | ht⟩
  exacts [Or.inl hz, Or.inr ⟨hz, Or.inl (le_of_lt ht)⟩, Or.inr ⟨hz, Or.inr (le_of_lt ht)⟩]

/-- The open set near which the model is smooth. -/
private def capSmoothSet : Set (ℝ × ℝ) :=
  {z | z.1 < 1 / 3} ∪ capBaseSet

omit hgγ in
private theorem isOpen_capSmoothSet : IsOpen capSmoothSet :=
  (isOpen_lt continuous_fst continuous_const).union isOpen_capBaseSet

private theorem contMDiffOn_capModel {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    (hg : ContMDiff 𝓘(ℝ) I ∞ g) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (capModel g P) capSmoothSet := by
  rintro z (hz | hz)
  · have h : capModel g P =ᶠ[𝓝 z] fun w : ℝ × ℝ ↦
        g (collaredSmoothTransitionLineMap (capRamp w.1) w.2) := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
      exact capModel_of_le (le_of_lt hw)
    exact ((hg.comp contDiff_lineMap_capRamp.contMDiff).contMDiffAt.congr_of_eventuallyEq
      h).contMDiffWithinAt
  · have h : capModel g P =ᶠ[𝓝 z] fun _ ↦ x := by
      filter_upwards [isOpen_capBaseSet.mem_nhds hz] with w hw
      exact capModel_of_mem_capBaseSet hgγ hw
    exact (contMDiffAt_const.congr_of_eventuallyEq h).contMDiffWithinAt

/-- The path in the loop space traced by the model on the unit square. -/
private def capModelPath (hg : Continuous g) : Path γ (Path.refl x) :=
  Path.ofContinuousFamily (fun s t : unitInterval ↦ capModel g P (s, t))
    ((continuous_capModel hgγ hg).comp (continuous_subtypeVal.prodMap continuous_subtypeVal))
    (fun s ↦ by rw [Icc.coe_zero, capModel_seam_zero hgγ])
    (fun s ↦ by rw [Icc.coe_one, capModel_seam_one hgγ])
    (fun t ↦ by rw [Icc.coe_zero, capModel_zero, hgγ])
    (fun t ↦ by rw [Icc.coe_one, capModel_one hgγ, Path.refl_apply])

private theorem capModelPath_apply (hg : Continuous g) (s t : unitInterval) :
    capModelPath (P := P) hgγ hg s t = capModel g P (s, t) :=
  Path.ofContinuousFamily_apply _ _ _ _ _ _ s t

/-- The model has the class of `P`: it is the image of the diagonal of the square of loops
`(r, s) ↦ P s ∘ τ_r`, which is constant along its top edge. -/
private theorem homotopic_capModelPath (hg : Continuous g) :
    P.Homotopic (capModelPath (P := P) hgγ hg) := by
  -- The square `(a, s) ↦ P (σ_a s) ∘ τ_{ρ_a s}`, with `(ρ_a, σ_a)` interpolating linearly between
  -- `(0, s)` and the parameters `(capRamp s, 3 s - 1)` of the model.
  set σ : unitInterval × unitInterval → unitInterval := fun q ↦
    projIcc 0 1 zero_le_one ((1 - q.1) * q.2 + q.1 * (3 * q.2 - 1))
  set ρ : unitInterval × unitInterval → unitInterval := fun q ↦
    projIcc 0 1 zero_le_one (q.1 * capRamp q.2)
  have hσ : Continuous σ := continuous_projIcc.comp (by fun_prop)
  have hρ : Continuous ρ := continuous_projIcc.comp
    ((continuous_subtypeVal.comp continuous_fst).mul
      (contDiff_capRamp.continuous.comp (continuous_subtypeVal.comp continuous_snd)))
  let K := Path.continuousFamily (x₀ := x) (x₁ := x)
    (fun (q : unitInterval × unitInterval) (t : unitInterval) ↦
      P (σ q) (collaredSmoothTransitionLineMapUnit (ρ q) t))
    ((continuous_uncurry_path P).comp ((hσ.comp continuous_fst).prodMk
      (continuous_collaredSmoothTransitionLineMapUnit.comp
        ((hρ.comp continuous_fst).prodMk continuous_snd))))
    (fun q ↦ by simp only [collaredSmoothTransitionLineMapUnit_zero_right, Path.source])
    (fun q ↦ by simp only [collaredSmoothTransitionLineMapUnit_one_right, Path.target])
  refine Path.homotopic_of_continuous_square K K.continuous (fun s ↦ ?_) (fun s ↦ ?_)
    (fun a ↦ ?_) (fun a ↦ ?_) <;> refine Path.ext (funext fun t ↦ ?_) <;>
    rw [Path.continuousFamily_apply]
  · have h₁ : σ (0, s) = s := by simp [σ]
    have h₂ : ρ (0, s) = 0 := by simp [ρ]
    rw [h₁, h₂, collaredSmoothTransitionLineMapUnit_zero_left]
  · have h₁ : σ (1, s) = projIcc 0 1 zero_le_one (3 * (s : ℝ) - 1) := by simp [σ]
    have h₂ : ρ (1, s) = projIcc 0 1 zero_le_one (capRamp s) := by simp [ρ]
    rw [h₁, h₂, capModelPath_apply, capModel_eq_of_mem hgγ]
  · have h₁ : σ (a, 0) = 0 := by
      simp only [σ, Icc.coe_zero, mul_zero, zero_add, zero_sub]
      rw [projIcc_of_le_left _ (by nlinarith [a.property.1]), Icc.mk_zero]
    have h₂ : ρ (a, 0) = 0 := by
      simp [ρ, capRamp_of_le (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    rw [h₁, h₂, collaredSmoothTransitionLineMapUnit_zero_left, P.source]
  · have h₁ : σ (a, 1) = 1 := by
      simp only [σ, Icc.coe_one]
      rw [projIcc_of_right_le _ (by nlinarith [a.property.1]), Icc.mk_one]
    rw [h₁, P.target, Path.refl_apply, Path.refl_apply]

end Model

/-! ### Smooth representatives -/

section Smoothing

/-- The complement of a rectangle inside the unit square: the closed set on which the smoothing
of the model keeps its values. -/
private def capFixedSet : Set (ℝ × ℝ) :=
  (Ioo (3 / 10 : ℝ) (7 / 10) ×ˢ Ioo (1 / 5 : ℝ) (4 / 5))ᶜ

private theorem isClosed_capFixedSet : IsClosed capFixedSet :=
  (isOpen_Ioo.prod isOpen_Ioo).isClosed_compl

private theorem mem_capFixedSet_of_fst {z : ℝ × ℝ} (h : z.1 ≤ 3 / 10 ∨ 7 / 10 ≤ z.1) :
    z ∈ capFixedSet := by
  rintro ⟨⟨h₁, h₂⟩, -⟩
  rcases h with h | h <;> linarith

private theorem mem_capFixedSet_of_snd {z : ℝ × ℝ} (h : z.2 ≤ 1 / 5 ∨ 4 / 5 ≤ z.2) :
    z ∈ capFixedSet := by
  rintro ⟨-, ⟨h₁, h₂⟩⟩
  rcases h with h | h <;> linarith

private theorem capFixedSet_subset : capFixedSet ⊆ capSmoothSet := by
  intro z hz
  rcases lt_or_ge z.1 (1 / 3) with h₁ | h₁
  · exact Or.inl h₁
  refine Or.inr ?_
  rcases le_or_gt (7 / 10) z.1 with h₂ | h₂
  · exact Or.inl (by linarith : (2 / 3 : ℝ) < z.1)
  refine Or.inr ⟨(by linarith : (1 / 4 : ℝ) < z.1), ?_⟩
  by_contra h
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at h
  exact hz ⟨⟨by linarith, h₂⟩, ⟨by linarith [h.1], by linarith [h.2]⟩⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {x : M} {γ : Ω M x}
  {g : ℝ → M} {P : Path γ (Path.refl x)}

/-- The periodization in `t` of a smooth map `G` which agrees with the model off a rectangle
inside the unit square is a smooth based cap. -/
private theorem isSmoothBasedCap_periodize (hgp : Periodic g 1)
    (hgγ : ∀ t : unitInterval, g t = γ t) {G : ℝ × ℝ → M} (hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ G)
    (hGf : ∀ z ∈ capFixedSet, G z = capModel g P z) :
    IsSmoothBasedCap I γ fun z ↦ G (z.1, Int.fract z.2) where
  contMDiff z := by
    refine ((hG.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)).contMDiff)
      z).congr_of_eventuallyEq
      (apply_fract_snd_eventuallyEq (ε := 1 / 5) (by norm_num) (fun s t ht₀ ht₁ ↦ ?_) z)
    rw [hGf _ (mem_capFixedSet_of_snd (Or.inr (by linarith))),
      hGf _ (mem_capFixedSet_of_snd (Or.inl (by linarith))),
      capModel_add_one hgγ hgp s (by linarith) (by linarith)]
  apply_add_one z := by simp only [Int.fract_add_one]
  apply_zero t := by
    rw [hGf _ (mem_capFixedSet_of_fst (Or.inl (by norm_num))), capModel_zero, hgp.apply_fract,
      hgγ]
  apply_one t := by
    rw [hGf _ (mem_capFixedSet_of_fst (Or.inr (by norm_num))), capModel_one hgγ, Path.refl_apply]
  apply_seam s := by
    rw [Int.fract_zero, hGf _ (mem_capFixedSet_of_snd (Or.inl (by norm_num))),
      capModel_seam_zero hgγ]

/-- A homotopy, relative to the complement of a rectangle inside the unit square, from the model
to a smooth map `G` gives a homotopy of paths in the loop space from the model path to the path
of the periodization of `G`. -/
private theorem homotopic_capModelPath_toPath (hgp : Periodic g 1)
    (hgγ : ∀ t : unitInterval, g t = γ t) (hg : Continuous g) {G : C(ℝ × ℝ, M)}
    (hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ G)
    (R : (⟨capModel g P, continuous_capModel hgγ hg⟩ : C(ℝ × ℝ, M)).HomotopyRel G capFixedSet) :
    (capModelPath (P := P) hgγ hg).Homotopic
      (isSmoothBasedCap_periodize hgp hgγ hG fun _ hz ↦ (R.fst_eq_snd hz).symm).toPath := by
  have hR : Continuous fun q : (unitInterval × unitInterval) × unitInterval ↦
      R (q.1.1, ((q.1.2 : ℝ), (q.2 : ℝ))) :=
    R.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_subtypeVal.comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_subtypeVal.comp continuous_snd)))
  let K := Path.continuousFamily (x₀ := x) (x₁ := x)
    (fun (q : unitInterval × unitInterval) (t : unitInterval) ↦ R (q.1, ((q.2 : ℝ), (t : ℝ)))) hR
    (fun q ↦ by
      rw [Icc.coe_zero]
      exact (R.eq_fst _ (mem_capFixedSet_of_snd (Or.inl (by norm_num)))).trans
        (capModel_seam_zero hgγ _))
    (fun q ↦ by
      rw [Icc.coe_one]
      exact (R.eq_fst _ (mem_capFixedSet_of_snd (Or.inr (by norm_num)))).trans
        (capModel_seam_one hgγ _))
  refine Path.homotopic_of_continuous_square K K.continuous (fun s ↦ ?_) (fun s ↦ ?_)
    (fun a ↦ ?_) (fun a ↦ ?_) <;> refine Path.ext (funext fun t ↦ ?_) <;>
    rw [Path.continuousFamily_apply]
  · rw [capModelPath_apply]
    exact R.apply_zero _
  · -- At `t = 1` the periodization reads `G` at `t = 0`, where both values are `x`.
    rw [R.apply_one, IsSmoothBasedHomotopy.toPath_apply]
    rcases eq_or_lt_of_le t.property.2 with h | h
    · rw [h, Int.fract_one,
        ← R.fst_eq_snd (x := ((s : ℝ), 1)) (mem_capFixedSet_of_snd (Or.inr (by norm_num))),
        ← R.fst_eq_snd (x := ((s : ℝ), 0)) (mem_capFixedSet_of_snd (Or.inl (by norm_num)))]
      exact (capModel_seam_one hgγ _).trans (capModel_seam_zero hgγ _).symm
    · rw [Int.fract_eq_self.2 ⟨t.property.1, h⟩]
  · rw [Icc.coe_zero]
    exact (R.eq_fst _ (mem_capFixedSet_of_fst (Or.inl (by norm_num)))).trans
      ((capModel_zero t).trans (hgγ t))
  · rw [Icc.coe_one]
    exact (R.eq_fst _ (mem_capFixedSet_of_fst (Or.inr (by norm_num)))).trans
      (capModel_one hgγ _)

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **Smooth representatives of raw caps.** If the `1`-periodic extension `g` of a loop `γ` is
smooth, every raw cap of `γ` is the homotopy class of a smooth based cap. -/
theorem RawCap.exists_isSmoothBasedCap_homotopyClass_eq (hg : ContMDiff 𝓘(ℝ) I ∞ g)
    (hgp : Periodic g 1) (hgγ : ∀ t : unitInterval, g t = γ t) (D : RawCap γ) :
    ∃ u, ∃ hu : IsSmoothBasedCap I γ u, hu.homotopyClass = D := by
  obtain ⟨P, rfl⟩ := Path.Homotopic.Quotient.mk_surjective D
  have hgc := hg.continuous
  let f : C(ℝ × ℝ, M) := ⟨capModel g P, continuous_capModel hgγ hgc⟩
  -- The model takes values in the images of `g` and of `P`, so its image is relatively compact.
  have hK : IsCompact (closure (range f)) := by
    refine ((hgp.compact_of_continuous one_ne_zero hgc).union
      (isCompact_range (continuous_uncurry_path P))).closure_of_subset ?_
    rintro _ ⟨z, rfl⟩
    rcases le_or_gt z.1 (1 / 3) with h | h
    · exact Or.inl ⟨_, (capModel_of_le h).symm⟩
    · exact Or.inr ⟨(_, _), (capModel_of_lt h).symm⟩
  -- Smooth the model relative to the complement of a rectangle inside the unit square.
  obtain ⟨G, hG, ⟨R⟩⟩ := f.exists_contMDiff_homotopicRel_of_isCompact_closure_range
    (I := 𝓘(ℝ, ℝ × ℝ)) (J := I) ⊤ hK isClosed_capFixedSet
    (isOpen_capSmoothSet.mem_nhdsSet.2 capFixedSet_subset) (contMDiffOn_capModel hgγ hg)
  refine ⟨_, isSmoothBasedCap_periodize hgp hgγ hG fun _ hz ↦ (R.fst_eq_snd hz).symm, ?_⟩
  rw [IsSmoothBasedHomotopy.homotopyClass_def]
  exact (Path.Homotopic.Quotient.eq.2 ((homotopic_capModelPath hgγ hgc).trans
    (homotopic_capModelPath_toPath hgp hgγ hgc hG R))).symm

/-- **Existence of smooth based caps.** A loop has a smooth based cap exactly when it is
null-homotopic and its `1`-periodic extension is smooth. -/
theorem exists_isSmoothBasedCap_iff :
    (∃ u, IsSmoothBasedCap I γ u) ↔ γ.Homotopic (Path.refl x) ∧
      ∃ g : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ g ∧ Periodic g 1 ∧ ∀ t : unitInterval, g t = γ t := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨RawCap.nonempty_iff.1 ⟨hu.homotopyClass⟩, fun t ↦ u (0, t),
      hu.contMDiff.comp (contDiff_const.prodMk contDiff_id).contMDiff,
      fun t ↦ hu.apply_add_one (0, t), hu.apply_zero⟩
  · rintro ⟨h, g, hg, hgp, hgγ⟩
    obtain ⟨D⟩ := RawCap.nonempty_iff.2 h
    obtain ⟨u, hu, -⟩ := RawCap.exists_isSmoothBasedCap_homotopyClass_eq hg hgp hgγ D
    exact ⟨u, hu⟩

/-- **The area of a raw cap is the integral over a smooth representative.** For a loop with a
smooth based cap and a closed `C¹` two-form, every raw cap is the raw cap of a smooth based cap
`u`, and its area is the integral of the form over `u` on the unit square. -/
theorem RawCap.exists_area_eq_rectangleIntegral [CompactSpace M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (h : ∃ u, IsSmoothBasedCap I γ u) (D : RawCap γ) :
    ∃ u, ∃ hu : IsSmoothBasedCap I γ u,
      hu.homotopyClass = D ∧ RawCap.area φ h D = rectangleIntegral φ u (0, 0) (1, 1) := by
  obtain ⟨-, g, hg, hgp, hgγ⟩ := exists_isSmoothBasedCap_iff.1 h
  obtain ⟨u, hu, rfl⟩ := RawCap.exists_isSmoothBasedCap_homotopyClass_eq hg hgp hgγ D
  exact ⟨u, hu, rfl, RawCap.area_homotopyClass hφ hdφ hu⟩

end Smoothing

end TauCeti.Floer
