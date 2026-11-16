/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Area
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Topology.Homotopy.Path

/-!
# Smooth representatives of raw caps

Let `M` be a Hausdorff boundaryless manifold modelled on a finite-dimensional space, and `γ` a loop
in `M` based at `x` whose `1`-periodic extension `g : ℝ → M` is smooth, as for a one-periodic
orbit of a Hamiltonian. This file proves that every raw cap of `γ`
(`TauCeti.Floer.RawCap γ`), a homotopy class of continuous discs bounding `γ`, is the raw cap of a
smooth based cap (`TauCeti.Floer.IsSmoothBasedCap`)
(`TauCeti.Floer.RawCap.exists_isSmoothBasedCap_rawCap_eq`). Consequently a loop has a smooth based
cap exactly when it is null-homotopic and its periodic extension is smooth
(`TauCeti.Floer.exists_isSmoothBasedCap_iff`). This discharges the hypothesis of
`TauCeti.Floer.RawCap.area` for every smooth contractible loop, and the area of every raw cap of
such a loop is the integral of the form over a smooth based cap in its class
(`TauCeti.Floer.RawCap.exists_area_eq_rectangleIntegral`).

The proof smooths a disc relative to its boundary, keeping the boundary values exactly. A raw cap
is the class of a path `P` in the loop space from `γ` to the constant loop. It is first replaced
by a continuous map of the plane which is already smooth off a rectangle inside the unit square.
Fix a smooth map `c` of `[0, 1]` onto itself which is `0` near `0` and `1` near `1`, and its linear
interpolation `τ_r = (1 - r) id + r c` with the identity. Then:

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

* `TauCeti.Floer.RawCap.exists_isSmoothBasedCap_rawCap_eq`: every raw cap of a loop with a smooth
  periodic extension is the raw cap of a smooth based cap.
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

/-- A smooth map of the line which is `0` up to `1/4` and `1` from `3/4` on. Precomposing a loop
with it makes the loop constant equal to its base point near the ends of the unit interval. -/
private def capCut (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * t - 1 / 2)

/-- A smooth map of the line which is `0` up to `1/6` and `1` from `1/4` on. -/
private def capRamp (s : ℝ) : ℝ :=
  Real.smoothTransition (12 * s - 2)

/-- The interpolation `t + r (capCut t - t)` between the identity (`r = 0`) and `capCut`
(`r = 1`). -/
private def capReparam (r t : ℝ) : ℝ :=
  t + r * (capCut t - t)

private theorem capCut_of_le {t : ℝ} (ht : t ≤ 1 / 4) : capCut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem capCut_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) : capCut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem capCut_mem (t : ℝ) : capCut t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem capRamp_of_le {s : ℝ} (hs : s ≤ 1 / 6) : capRamp s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem capRamp_of_ge {s : ℝ} (hs : 1 / 4 ≤ s) : capRamp s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem capRamp_mem (s : ℝ) : capRamp s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem capReparam_zero_left (t : ℝ) : capReparam 0 t = t := by
  simp [capReparam]

private theorem capReparam_one_left (t : ℝ) : capReparam 1 t = capCut t := by
  simp [capReparam]

private theorem capReparam_zero_right (r : ℝ) : capReparam r 0 = 0 := by
  simp [capReparam, capCut_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)]

private theorem capReparam_one_right (r : ℝ) : capReparam r 1 = 1 := by
  simp [capReparam, capCut_of_ge (by norm_num : (3 / 4 : ℝ) ≤ 1)]

/-- Near the base point the interpolation commutes with the translation by `1`. -/
private theorem capReparam_add_one (r : ℝ) {t : ℝ} (ht₀ : -1 / 4 ≤ t) (ht₁ : t ≤ 1 / 4) :
    capReparam r (t + 1) = capReparam r t + 1 := by
  rw [capReparam, capReparam, capCut_of_ge (by linarith), capCut_of_le ht₁]
  ring

private theorem capReparam_mem {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    capReparam r t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hr₀, hr₁⟩ := hr
  obtain ⟨ht₀, ht₁⟩ := ht
  obtain ⟨hc₀, hc₁⟩ := capCut_mem t
  have h : capReparam r t = (1 - r) * t + r * capCut t := by
    rw [capReparam]
    ring
  rw [h]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hr₁) ht₀, mul_nonneg hr₀ hc₀,
    mul_le_mul_of_nonneg_left ht₁ (sub_nonneg.2 hr₁), mul_le_mul_of_nonneg_left hc₁ hr₀]

private theorem contDiff_capCut : ContDiff ℝ ∞ capCut :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem contDiff_capRamp : ContDiff ℝ ∞ capRamp :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem contDiff_capReparam_capRamp :
    ContDiff ℝ ∞ fun z : ℝ × ℝ ↦ capReparam (capRamp z.1) z.2 :=
  contDiff_snd.add ((contDiff_capRamp.comp contDiff_fst).mul
    ((contDiff_capCut.comp contDiff_snd).sub contDiff_snd))

private theorem continuous_capReparam : Continuous fun z : ℝ × ℝ ↦ capReparam z.1 z.2 := by
  have hc : Continuous capCut := contDiff_capCut.continuous
  unfold capReparam
  fun_prop

/-- The interpolation `capReparam` as a map of the unit interval, for `r ∈ [0, 1]`. -/
private def capReparamI (r t : unitInterval) : unitInterval :=
  ⟨capReparam r t, capReparam_mem r.2 t.2⟩

private theorem coe_capReparamI (r t : unitInterval) :
    (capReparamI r t : ℝ) = capReparam r t :=
  (rfl)

private theorem continuous_capReparamI :
    Continuous fun q : unitInterval × unitInterval ↦ capReparamI q.1 q.2 :=
  (continuous_capReparam.comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _

private theorem capReparamI_zero_right (r : unitInterval) : capReparamI r 0 = 0 :=
  Subtype.ext (capReparam_zero_right r)

private theorem capReparamI_one_right (r : unitInterval) : capReparamI r 1 = 1 :=
  Subtype.ext (capReparam_one_right r)

private theorem capReparamI_zero_left (t : unitInterval) : capReparamI 0 t = t :=
  Subtype.ext (capReparam_zero_left t)

end Reparam

/-! ### Continuous families of loops -/

section Family

variable {M : Type*} [TopologicalSpace M] {x : M}

/-- The continuous family of loops at `x` given by a continuous map `F` on `Y × [0, 1]` sending
`Y × {0, 1}` to `x`. -/
private def loopFamily {Y : Type*} [TopologicalSpace Y] (F : Y → unitInterval → M)
    (hF : Continuous ↿F) (h₀ : ∀ y, F y 0 = x) (h₁ : ∀ y, F y 1 = x) : C(Y, Ω M x) where
  toFun y := ⟨⟨F y, hF.comp (continuous_const.prodMk continuous_id)⟩, h₀ y, h₁ y⟩
  continuous_toFun := Path.continuous_uncurry_iff.1 hF

private theorem loopFamily_apply {Y : Type*} [TopologicalSpace Y] (F : Y → unitInterval → M)
    (hF : Continuous ↿F) (h₀ : ∀ y, F y 0 = x) (h₁ : ∀ y, F y 1 = x) (y : Y) (t : unitInterval) :
    loopFamily F hF h₀ h₁ y t = F y t :=
  (rfl)

end Family

/-! ### A model of a cap which is smooth near the boundary of a rectangle -/

section Model

variable {M : Type*} [TopologicalSpace M] {x : M} {γ : Ω M x}

/-- The model of the raw cap of `P`, for a periodic extension `g` of `γ`: `g` precomposed with
`capReparam (capRamp s)` for `s ≤ 1/3`, and `P` precomposed with `capCut` in the loop direction,
run three times as fast, beyond. It is smooth near the edge `s = 0` and equal to `x` near the seam
and near the edge `s = 1`. -/
private def capModel (g : ℝ → M) (P : Path γ (Path.refl x)) (z : ℝ × ℝ) : M :=
  if z.1 ≤ 1 / 3 then g (capReparam (capRamp z.1) z.2)
  else P (projIcc 0 1 zero_le_one (3 * z.1 - 1)) (projIcc 0 1 zero_le_one (capCut z.2))

variable {g : ℝ → M} {P : Path γ (Path.refl x)}

private theorem capModel_of_le {z : ℝ × ℝ} (hz : z.1 ≤ 1 / 3) :
    capModel g P z = g (capReparam (capRamp z.1) z.2) := by
  simp only [capModel, hz, ↓reduceIte]

private theorem capModel_of_lt {z : ℝ × ℝ} (hz : 1 / 3 < z.1) :
    capModel g P z =
      P (projIcc 0 1 zero_le_one (3 * z.1 - 1)) (projIcc 0 1 zero_le_one (capCut z.2)) := by
  simp only [capModel, hz.not_ge, ↓reduceIte]

private theorem continuous_uncurry_path (P : Path γ (Path.refl x)) :
    Continuous fun q : unitInterval × unitInterval ↦ P q.1 q.2 :=
  Path.continuous_uncurry_iff.2 P.continuous

private theorem capModel_zero (t : ℝ) : capModel g P (0, t) = g t := by
  rw [capModel_of_le (by norm_num), capRamp_of_le (by norm_num), capReparam_zero_left]

variable (hgγ : ∀ t : unitInterval, g t = γ t)
include hgγ

private theorem capModel_eq_of_mem (s t : unitInterval) :
    capModel g P (s, t) = P (projIcc 0 1 zero_le_one (3 * s - 1))
      (capReparamI (projIcc 0 1 zero_le_one (capRamp s)) t) := by
  rw [projIcc_of_mem _ (capRamp_mem s)]
  rcases le_or_gt (s : ℝ) (1 / 3) with hs | hs
  · rw [capModel_of_le hs, projIcc_of_le_left _ (by linarith), Icc.mk_zero, P.source,
      ← hgγ, coe_capReparamI]
  · have hr : (⟨capRamp s, capRamp_mem s⟩ : unitInterval) = 1 :=
      Subtype.ext (capRamp_of_ge (by linarith))
    rw [capModel_of_lt hs, hr, projIcc_of_mem _ (capCut_mem t)]
    congr 1
    exact Subtype.ext (capReparam_one_left t).symm

private theorem continuous_capModel (hg : Continuous g) : Continuous (capModel g P) := by
  have hr : Continuous fun z : ℝ × ℝ ↦ capReparam (capRamp z.1) z.2 :=
    contDiff_capReparam_capRamp.continuous
  have hs : Continuous fun z : ℝ × ℝ ↦ projIcc (0 : ℝ) 1 zero_le_one (3 * z.1 - 1) :=
    continuous_projIcc.comp ((continuous_const.mul continuous_fst).sub continuous_const)
  have ht : Continuous fun z : ℝ × ℝ ↦ projIcc (0 : ℝ) 1 zero_le_one (capCut z.2) :=
    continuous_projIcc.comp (contDiff_capCut.continuous.comp continuous_snd)
  refine Continuous.if_le (hg.comp hr) ((continuous_uncurry_path P).comp (hs.prodMk ht))
    continuous_fst continuous_const fun z hz ↦ ?_
  rw [hz, capRamp_of_ge (by norm_num), capReparam_one_left,
    projIcc_of_le_left _ (by norm_num), Icc.mk_zero, P.source, projIcc_of_mem _ (capCut_mem _),
    ← hgγ]

/-- The model is `x` beyond `s = 2/3`, and near the seam beyond `s = 1/4`. -/
private theorem capModel_eq_base {z : ℝ × ℝ}
    (hz : 2 / 3 < z.1 ∨ 1 / 4 < z.1 ∧ (z.2 ≤ 1 / 4 ∨ 3 / 4 ≤ z.2)) : capModel g P z = x := by
  rcases le_or_gt z.1 (1 / 3) with hs | hs
  · have hz' : 1 / 4 < z.1 ∧ (z.2 ≤ 1 / 4 ∨ 3 / 4 ≤ z.2) := hz.resolve_left (by linarith)
    rw [capModel_of_le hs, capRamp_of_ge hz'.1.le, capReparam_one_left]
    rcases hz'.2 with ht | ht
    · rw [capCut_of_le ht, ← Icc.coe_zero, hgγ, γ.source]
    · rw [capCut_of_ge ht, ← Icc.coe_one, hgγ, γ.target]
  · rw [capModel_of_lt hs]
    rcases hz with hz | ⟨-, ht | ht⟩
    · rw [projIcc_of_right_le _ (by linarith), Icc.mk_one, P.target, Path.refl_apply]
    · rw [capCut_of_le ht, projIcc_left, Icc.mk_zero, Path.source]
    · rw [capCut_of_ge ht, projIcc_right, Icc.mk_one, Path.target]

private theorem capModel_one (t : ℝ) : capModel g P (1, t) = x :=
  capModel_eq_base hgγ (Or.inl (by norm_num))

private theorem capModel_seam_zero (s : ℝ) : capModel g P (s, 0) = x := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [capModel_of_le hs, capReparam_zero_right, ← Icc.coe_zero, hgγ, γ.source]
  · rw [capModel_of_lt hs, capCut_of_le (by norm_num), projIcc_left, Icc.mk_zero, Path.source]

private theorem capModel_seam_one (s : ℝ) : capModel g P (s, 1) = x := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [capModel_of_le hs, capReparam_one_right, ← Icc.coe_one, hgγ, γ.target]
  · rw [capModel_of_lt hs, capCut_of_ge (by norm_num), projIcc_right, Icc.mk_one, Path.target]

/-- The model is periodic in `t` near the seam. -/
private theorem capModel_add_one (hgp : Periodic g 1) (s : ℝ) {t : ℝ} (ht₀ : -1 / 4 ≤ t)
    (ht₁ : t ≤ 1 / 4) : capModel g P (s, t + 1) = capModel g P (s, t) := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [capModel_of_le hs, capModel_of_le hs, capReparam_add_one _ ht₀ ht₁, hgp]
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
  · have h : capModel g P =ᶠ[𝓝 z] fun w : ℝ × ℝ ↦ g (capReparam (capRamp w.1) w.2) := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
      exact capModel_of_le (le_of_lt hw)
    exact ((hg.comp contDiff_capReparam_capRamp.contMDiff).contMDiffAt.congr_of_eventuallyEq
      h).contMDiffWithinAt
  · have h : capModel g P =ᶠ[𝓝 z] fun _ ↦ x := by
      filter_upwards [isOpen_capBaseSet.mem_nhds hz] with w hw
      exact capModel_of_mem_capBaseSet hgγ hw
    exact (contMDiffAt_const.congr_of_eventuallyEq h).contMDiffWithinAt

/-- The path in the loop space traced by the model on the unit square. -/
private def capModelPath (hg : Continuous g) : Path γ (Path.refl x) where
  toContinuousMap := loopFamily (fun s t : unitInterval ↦ capModel g P (s, t))
    ((continuous_capModel hgγ hg).comp (continuous_subtype_val.prodMap continuous_subtype_val))
    (fun s ↦ capModel_seam_zero hgγ s) (fun s ↦ capModel_seam_one hgγ s)
  source' := Path.ext (funext fun t ↦ (capModel_zero t).trans (hgγ t))
  target' := Path.ext (funext fun t ↦ capModel_one hgγ t)

private theorem capModelPath_apply (hg : Continuous g) (s t : unitInterval) :
    capModelPath (P := P) hgγ hg s t = capModel g P (s, t) :=
  (rfl)

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
    ((continuous_subtype_val.comp continuous_fst).mul
      (contDiff_capRamp.continuous.comp (continuous_subtype_val.comp continuous_snd)))
  let K := loopFamily (x := x) (fun (q : unitInterval × unitInterval) (t : unitInterval) ↦
      P (σ q) (capReparamI (ρ q) t))
    ((continuous_uncurry_path P).comp ((hσ.comp continuous_fst).prodMk
      (continuous_capReparamI.comp ((hρ.comp continuous_fst).prodMk continuous_snd))))
    (fun q ↦ by simp only [capReparamI_zero_right, Path.source])
    (fun q ↦ by simp only [capReparamI_one_right, Path.target])
  refine Path.homotopic_of_continuous_square K K.continuous (fun s ↦ ?_) (fun s ↦ ?_)
    (fun a ↦ ?_) (fun a ↦ ?_) <;> refine Path.ext (funext fun t ↦ ?_) <;>
    rw [loopFamily_apply]
  · have h₁ : σ (0, s) = s := by simp [σ]
    have h₂ : ρ (0, s) = 0 := by simp [ρ]
    rw [h₁, h₂, capReparamI_zero_left]
  · have h₁ : σ (1, s) = projIcc 0 1 zero_le_one (3 * (s : ℝ) - 1) := by simp [σ]
    have h₂ : ρ (1, s) = projIcc 0 1 zero_le_one (capRamp s) := by simp [ρ]
    rw [h₁, h₂, capModelPath_apply, capModel_eq_of_mem hgγ]
  · have h₁ : σ (a, 0) = 0 := by
      simp only [σ, Icc.coe_zero, mul_zero, zero_add, zero_sub]
      rw [projIcc_of_le_left _ (by nlinarith [a.2.1]), Icc.mk_zero]
    have h₂ : ρ (a, 0) = 0 := by
      simp [ρ, capRamp_of_le (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    rw [h₁, h₂, capReparamI_zero_left, P.source]
  · have h₁ : σ (a, 1) = 1 := by
      simp only [σ, Icc.coe_one]
      rw [projIcc_of_right_le _ (by nlinarith [a.2.1]), Icc.mk_one]
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

/-- Near every point, the periodization `(s, t) ↦ G (s, fract t)` of a map `G` of the plane which
is periodic in `t` near the seam is a translate of `G`. -/
private theorem periodize_eventuallyEq {M : Type*} {G : ℝ × ℝ → M}
    (hG : ∀ s {t : ℝ}, -1 / 5 < t → t < 0 → G (s, t + 1) = G (s, t)) (z : ℝ × ℝ) :
    (fun w : ℝ × ℝ ↦ G (w.1, Int.fract w.2)) =ᶠ[𝓝 z] fun w ↦ G (w.1, w.2 - ⌊z.2⌋) := by
  have hz₁ : z.2 < ⌊z.2⌋ + 1 := Int.lt_floor_add_one _
  have hz₀ : (⌊z.2⌋ : ℝ) ≤ z.2 := Int.floor_le _
  by_cases h : Int.fract z.2 = 0
  · -- At the seam, `fract` jumps by `1`, across which `G` is periodic.
    rw [← Int.self_sub_floor, sub_eq_zero] at h
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds
        (by linarith : (⌊z.2⌋ : ℝ) - 1 / 5 < z.2),
      (isOpen_lt continuous_snd continuous_const).mem_nhds
        (by linarith : z.2 < ⌊z.2⌋ + 1 / 5)] with w hw₀ hw₁
    rcases le_or_gt (⌊z.2⌋ : ℝ) w.2 with hw | hw
    · have h' : Int.fract w.2 = w.2 - ⌊z.2⌋ :=
        Int.fract_eq_iff.2 ⟨by linarith, by linarith, ⌊z.2⌋, by ring⟩
      rw [h']
    · have h' : Int.fract w.2 = w.2 - ⌊z.2⌋ + 1 :=
        Int.fract_eq_iff.2 ⟨by linarith, by linarith, ⌊z.2⌋ - 1, by push_cast; ring⟩
      rw [h']
      exact hG _ (by linarith) (by linarith)
  · -- Off the seam, `fract` is a translation near `z`.
    have hz : (⌊z.2⌋ : ℝ) < z.2 :=
      lt_of_le_of_ne hz₀ fun h' ↦ h (by rw [← Int.self_sub_floor]; linarith)
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz,
      (isOpen_lt continuous_snd continuous_const).mem_nhds hz₁] with w hw₀ hw₁
    have h' : Int.fract w.2 = w.2 - ⌊z.2⌋ :=
      Int.fract_eq_iff.2 ⟨by linarith, by linarith, ⌊z.2⌋, by ring⟩
    rw [h']

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
      z).congr_of_eventuallyEq (periodize_eventuallyEq (fun s t ht₀ ht₁ ↦ ?_) z)
    rw [hGf _ (mem_capFixedSet_of_snd (Or.inr (by linarith))),
      hGf _ (mem_capFixedSet_of_snd (Or.inl (by linarith))),
      capModel_add_one hgγ hgp s (by linarith) (by linarith)]
  apply_add_one z := by simp only [Int.fract_add_one]
  apply_zero t := by
    have h := hgp.sub_int_mul_eq (x := (t : ℝ)) ⌊(t : ℝ)⌋
    rw [mul_one, Int.self_sub_floor] at h
    rw [hGf _ (mem_capFixedSet_of_fst (Or.inl (by norm_num))), capModel_zero, h, hgγ]
  apply_one t := by
    rw [hGf _ (mem_capFixedSet_of_fst (Or.inr (by norm_num))), capModel_one hgγ]
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
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd)))
  let K := loopFamily (x := x)
    (fun (q : unitInterval × unitInterval) (t : unitInterval) ↦ R (q.1, ((q.2 : ℝ), (t : ℝ)))) hR
    (fun q ↦ (R.eq_fst _ (mem_capFixedSet_of_snd (Or.inl (by norm_num)))).trans
      (capModel_seam_zero hgγ _))
    (fun q ↦ (R.eq_fst _ (mem_capFixedSet_of_snd (Or.inr (by norm_num)))).trans
      (capModel_seam_one hgγ _))
  refine Path.homotopic_of_continuous_square K K.continuous (fun s ↦ ?_) (fun s ↦ ?_)
    (fun a ↦ ?_) (fun a ↦ ?_) <;> refine Path.ext (funext fun t ↦ ?_) <;>
    rw [loopFamily_apply]
  · exact R.apply_zero _
  · -- At `t = 1` the periodization reads `G` at `t = 0`, where both values are `x`.
    rw [R.apply_one, IsSmoothBasedCap.toPath_apply]
    rcases eq_or_lt_of_le t.2.2 with h | h
    · rw [h, Int.fract_one,
        ← R.fst_eq_snd (x := ((s : ℝ), 1)) (mem_capFixedSet_of_snd (Or.inr (by norm_num))),
        ← R.fst_eq_snd (x := ((s : ℝ), 0)) (mem_capFixedSet_of_snd (Or.inl (by norm_num)))]
      exact (capModel_seam_one hgγ _).trans (capModel_seam_zero hgγ _).symm
    · rw [Int.fract_eq_self.2 ⟨t.2.1, h⟩]
  · exact (R.eq_fst _ (mem_capFixedSet_of_fst (Or.inl (by norm_num)))).trans
      ((capModel_zero t).trans (hgγ t))
  · exact (R.eq_fst _ (mem_capFixedSet_of_fst (Or.inr (by norm_num)))).trans
      (capModel_one hgγ _)

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **Smooth representatives of raw caps.** If the `1`-periodic extension `g` of a loop `γ` is
smooth, every raw cap of `γ` is the raw cap of a smooth based cap. -/
theorem RawCap.exists_isSmoothBasedCap_rawCap_eq (hg : ContMDiff 𝓘(ℝ) I ∞ g)
    (hgp : Periodic g 1) (hgγ : ∀ t : unitInterval, g t = γ t) (D : RawCap γ) :
    ∃ u, ∃ hu : IsSmoothBasedCap I γ u, hu.rawCap = D := by
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
  rw [IsSmoothBasedCap.rawCap_def]
  exact (Path.Homotopic.Quotient.eq.2 ((homotopic_capModelPath hgγ hgc).trans
    (homotopic_capModelPath_toPath hgp hgγ hgc hG R))).symm

/-- **Existence of smooth based caps.** A loop has a smooth based cap exactly when it is
null-homotopic and its `1`-periodic extension is smooth. -/
theorem exists_isSmoothBasedCap_iff :
    (∃ u, IsSmoothBasedCap I γ u) ↔ γ.Homotopic (Path.refl x) ∧
      ∃ g : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ g ∧ Periodic g 1 ∧ ∀ t : unitInterval, g t = γ t := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨RawCap.nonempty_iff.1 ⟨hu.rawCap⟩, fun t ↦ u (0, t),
      hu.contMDiff.comp (contDiff_const.prodMk contDiff_id).contMDiff,
      fun t ↦ hu.apply_add_one (0, t), hu.apply_zero⟩
  · rintro ⟨h, g, hg, hgp, hgγ⟩
    obtain ⟨D⟩ := RawCap.nonempty_iff.2 h
    obtain ⟨u, hu, -⟩ := RawCap.exists_isSmoothBasedCap_rawCap_eq hg hgp hgγ D
    exact ⟨u, hu⟩

/-- **The area of a raw cap is the integral over a smooth representative.** For a loop with a
smooth based cap and a closed `C¹` two-form, every raw cap is the raw cap of a smooth based cap
`u`, and its area is the integral of the form over `u` on the unit square. -/
theorem RawCap.exists_area_eq_rectangleIntegral [CompactSpace M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (h : ∃ u, IsSmoothBasedCap I γ u) (D : RawCap γ) :
    ∃ u, ∃ hu : IsSmoothBasedCap I γ u,
      hu.rawCap = D ∧ RawCap.area φ h D = rectangleIntegral φ u (0, 0) (1, 1) := by
  obtain ⟨-, g, hg, hgp, hgγ⟩ := exists_isSmoothBasedCap_iff.1 h
  obtain ⟨u, hu, rfl⟩ := RawCap.exists_isSmoothBasedCap_rawCap_eq hg hgp hgγ D
  exact ⟨u, hu, rfl, RawCap.area_rawCap hφ hdφ hu⟩

end Smoothing

end TauCeti.Floer
