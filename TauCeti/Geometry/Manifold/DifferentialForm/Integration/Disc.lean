/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Topology.Homotopy.GenLoop.Homotopic

/-!
# Integrals of closed two-forms over two discs bounding the same loop

Let `γ` be a loop in a manifold `M` based at `x`. A **smooth disc** bounding `γ`
(`TauCeti.IsSmoothDisc`) is a smooth map `D : ℝ × ℝ → M`, `1`-periodic in its second
coordinate, which is the constant loop at `x` along `s = 0`, the loop `γ` along `s = 1`, and
sends the seam `t = 0` of the unit square to `x`. These are the discs `(s, t) ↦ D (s, t)` of
the capped action `TauCeti.cappedLoopAction`, with centre `x`, whose seam stays at the base
point. Read from `s = 1` to `s = 0`, such a disc is a path in the loop space `Ω M x` from `γ`
to the constant loop (`TauCeti.IsSmoothDisc.loopPath`).

Two discs `D` and `D'` bounding `γ` differ by a sphere: the double loop which runs `D` from its
centre to `γ` and then `D'` back to its centre, `D.loopPath⁻¹ ⬝ D'.loopPath`, represents an
element of `π₂(M, x)` through `HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv`. The main result
of this file computes the integral `TauCeti.sphereIntegral` of a closed `C¹` two-form `φ` over
this element on a compact boundaryless manifold:

`∫_{D⁻¹ ⬝ D'} φ = ∫_D φ - ∫_{D'} φ`

(`TauCeti.IsSmoothDisc.sphereIntegral_loopPath_symm_trans`), the integrals of `D` and `D'` being
taken over the unit square (`TauCeti.rectangleIntegral`).

The double loop is only continuous, so the integral over its class is computed on a smooth
sphere representing it. Gluing `D` to `D'` run backwards along their common edge `γ`
(`TauCeti.rectangleTrans`) gives a smooth map whose integral is `∫_D φ - ∫_{D'} φ`
(`TauCeti.rectangleIntegral_rectangleTrans`). Reparametrizing both of its coordinates by a
smooth profile `τ` that is `0` on `(-∞, 1/4]` and `1` on `[3/4, ∞)` makes it constant equal to
`x` off `[1/4, 3/4]²`, so a smooth sphere in the sense of `TauCeti.IsSmoothSphere`. The
reparametrization does not change the integral, by homotopy invariance along the straight-line
homotopy of parameters (`TauCeti.rectangleIntegral_eq_of_homotopy`); and the generalized loop of
the sphere is that of the double loop with its two cube coordinates reparametrized by self-maps
of the unit interval fixing `0` and `1`, which does not change its class
(`GenLoop.homotopic_of_forall_apply_eq_comp`).

## Main definitions

* `TauCeti.IsSmoothDisc I γ D`: `D` is a smooth disc bounding the based loop `γ`.
* `TauCeti.IsSmoothDisc.loopPath`: a smooth disc as a path in the loop space, from `γ` to the
  constant loop.

## Main results

* `TauCeti.IsSmoothDisc.apply_zero_eq`, `TauCeti.IsSmoothDisc.apply_one_eq`: a disc is constant
  along the whole line `s = 0`, and two discs bounding the same loop agree along the whole line
  `s = 1`.
* `TauCeti.IsSmoothDisc.sphereIntegral_loopPath_symm_trans`: the integral of a closed form over
  the sphere by which two smooth discs differ is the difference of their integrals.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Springer, 1982, §4
  (homotopy invariance of integrals of closed forms).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and capped loops).
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff Topology Interval

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : M}

variable (I) in
/-- A **smooth disc** bounding a loop `γ` based at `x`: a smooth map `D` of the plane,
`1`-periodic in its second coordinate, which is the constant loop at `x` along `s = 0` (its
centre), the loop `γ` along `s = 1`, and sends the seam `t = 0` of the unit square to `x`. -/
structure IsSmoothDisc (γ : Path x x) (D : ℝ × ℝ → M) : Prop where
  /-- The disc is smooth. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ D
  /-- The disc is `1`-periodic in its second coordinate. -/
  apply_add_one : ∀ z : ℝ × ℝ, D (z.1, z.2 + 1) = D z
  /-- The disc is the constant loop at `x` along `s = 0`. -/
  apply_zero : ∀ t : unitInterval, D (0, t) = x
  /-- The disc is the loop `γ` along `s = 1`. -/
  apply_one : ∀ t : unitInterval, D (1, t) = γ t
  /-- The seam `t = 0` of the unit square stays at `x`. -/
  apply_seam : ∀ s : unitInterval, D (s, 0) = x

namespace IsSmoothDisc

variable {γ : Path x x} {D D' : ℝ × ℝ → M}

/-- The other edge `t = 1` of the unit square stays at `x` too. -/
theorem apply_seam_one (hD : IsSmoothDisc I γ D) (s : unitInterval) : D (s, 1) = x := by
  simpa using (hD.apply_add_one (s, 0)).trans (hD.apply_seam s)

/-- A disc only depends on the fractional part of its second coordinate. -/
theorem apply_fract (hD : IsSmoothDisc I γ D) (s t : ℝ) : D (s, Int.fract t) = D (s, t) := by
  simpa using Function.Periodic.sub_int_mul_eq (f := fun t ↦ D (s, t)) (c := 1) (x := t)
    (fun t ↦ hD.apply_add_one (s, t)) ⌊t⌋

private theorem fract_mem (t : ℝ) : Int.fract t ∈ unitInterval :=
  ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-- A disc is the constant loop at `x` along the whole line `s = 0`. -/
theorem apply_zero_eq (hD : IsSmoothDisc I γ D) (t : ℝ) : D (0, t) = x := by
  rw [← hD.apply_fract, hD.apply_zero ⟨_, fract_mem t⟩]

/-- Two discs bounding the same loop agree along the whole line `s = 1`: both are `γ` on the unit
interval and `1`-periodic. -/
theorem apply_one_eq (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') (t : ℝ) :
    D (1, t) = D' (1, t) := by
  rw [← hD.apply_fract, ← hD'.apply_fract, hD.apply_one ⟨_, fract_mem t⟩,
    hD'.apply_one ⟨_, fract_mem t⟩]

/-- A smooth disc as a path in the loop space `Ω M x`: at time `s` it is the loop
`t ↦ D (1 - s, t)`, running from the loop `γ` that `D` bounds to the constant loop at its
centre. -/
def loopPath (hD : IsSmoothDisc I γ D) : Path γ (Path.refl x) where
  toFun s :=
    { toFun t := D (unitInterval.symm s, t)
      continuous_toFun := hD.contMDiff.continuous.comp (by fun_prop)
      source' := by simpa using hD.apply_seam (unitInterval.symm s)
      target' := by simpa using hD.apply_seam_one (unitInterval.symm s) }
  continuous_toFun := Path.continuous_uncurry_iff.mp (hD.contMDiff.continuous.comp (by fun_prop))
  source' := Path.ext (funext fun t ↦ by simpa using hD.apply_one t)
  target' := Path.ext (funext fun t ↦ by simpa using hD.apply_zero t)

@[simp]
theorem loopPath_apply_apply (hD : IsSmoothDisc I γ D) (s t : unitInterval) :
    hD.loopPath s t = D (unitInterval.symm s, t) :=
  (rfl)

end IsSmoothDisc

/-! ### The sphere glued from two discs -/

section Glue

/-- The smooth profile `τ(r) = β(2 r - 1/2)`, for `β = Real.smoothTransition`: it is `0` on
`(-∞, 1/4]`, `1` on `[3/4, ∞)`, and takes values in the unit interval. -/
private def flat (r : ℝ) : ℝ :=
  Real.smoothTransition (2 * r - 1 / 2)

private theorem contDiff_flat : ContDiff ℝ ∞ flat :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)

private theorem flat_of_le {r : ℝ} (hr : r ≤ 1 / 4) : flat r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem flat_of_ge {r : ℝ} (hr : 3 / 4 ≤ r) : flat r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem flat_zero : flat 0 = 0 :=
  flat_of_le (by norm_num)

private theorem flat_one : flat 1 = 1 :=
  flat_of_ge (by norm_num)

private theorem flat_mem (r : ℝ) : flat r ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- A convex combination of two points of the unit interval lies in the unit interval. -/
private theorem sub_mul_add_mul_mem {a b c : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) : (1 - c) * a + c * b ∈ Icc (0 : ℝ) 1 :=
  ⟨by nlinarith [ha.1, hb.1, hc.1, hc.2], by nlinarith [ha.2, hb.2, hc.1, hc.2]⟩

/-- The reversal `(s, t) ↦ (1 - s, t)` of the first coordinate. -/
private def rev : ℝ × ℝ → ℝ × ℝ :=
  Prod.map (fun s ↦ 1 - s) id

variable {γ : Path x x} {D D' : ℝ × ℝ → M}

/-- `D` followed by `D'` run backwards, glued along their common edge `γ`. -/
private def discGlue (D D' : ℝ × ℝ → M) : ℝ × ℝ → M :=
  rectangleTrans D (D' ∘ rev)

private theorem discGlue_hyp (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') (t : ℝ) :
    D (1, t) = (D' ∘ rev) (0, t) := by
  simpa [rev] using hD.apply_one_eq hD' t

private theorem contMDiff_discGlue (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (discGlue D D') :=
  contMDiff_rectangleTrans (n := ⊤) hD.contMDiff
    (hD'.contMDiff.comp ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff)
    (discGlue_hyp hD hD')

/-- The glued map sends both edges `t = 0` and `t = 1` of the strip to `x`. -/
private theorem discGlue_apply_seam (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D')
    (s : ℝ) {t : ℝ} (ht : t = 0 ∨ t = 1) : discGlue D D' (s, t) = x := by
  have hβ (r : ℝ) : Real.smoothTransition r ∈ unitInterval :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have h1β (r : ℝ) : 1 - Real.smoothTransition r ∈ unitInterval :=
    Icc.mem_iff_one_sub_mem.mp (hβ r)
  rcases lt_or_ge s (2 / 3) with hs | hs
  · rw [discGlue, rectangleTrans_eq_left (discGlue_hyp hD hD') (z := (s, t)) hs]
    rcases ht with rfl | rfl
    · exact hD.apply_seam ⟨_, hβ _⟩
    · exact hD.apply_seam_one ⟨_, hβ _⟩
  · rw [discGlue, rectangleTrans_eq_right (discGlue_hyp hD hD') (z := (s, t)) (by linarith)]
    rcases ht with rfl | rfl
    · exact hD'.apply_seam ⟨_, h1β _⟩
    · exact hD'.apply_seam_one ⟨_, h1β _⟩

/-- The glued map is the constant loop at `x` along `s = 0` and `s = 1`, on the unit interval. -/
private theorem discGlue_apply_end (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D')
    {s : ℝ} (hs : s = 0 ∨ s = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : discGlue D D' (s, t) = x := by
  rcases hs with rfl | rfl
  · simpa [discGlue] using hD.apply_zero ⟨t, ht⟩
  · simpa [discGlue, rev] using hD'.apply_zero ⟨t, ht⟩

/-- The sphere glued from two discs: the glued map with both coordinates reparametrized by the
profile `τ`, constant equal to `x` off `[1/4, 3/4]²`. -/
private def discSphere (D D' : ℝ × ℝ → M) (z : ℝ × ℝ) : M :=
  discGlue D D' (flat z.1, flat z.2)

private theorem isSmoothSphere_discSphere (hD : IsSmoothDisc I γ D)
    (hD' : IsSmoothDisc I γ D') : IsSmoothSphere I x (discSphere D D') := by
  refine ⟨(contMDiff_discGlue hD hD').comp (contDiff_flat.prodMap contDiff_flat).contMDiff,
    1 / 4, by norm_num, fun z hz ↦ ?_⟩
  have hvert {r : ℝ} (hr : r ∉ Icc (1 / 4 : ℝ) (1 - 1 / 4)) : flat r = 0 ∨ flat r = 1 := by
    simp only [mem_Icc, not_and_or, not_le] at hr
    rcases hr with hr | hr
    · exact Or.inl (flat_of_le hr.le)
    · exact Or.inr (flat_of_ge (by linarith))
  simp only [mem_prod, not_and_or] at hz
  rcases hz with hz | hz
  · exact discGlue_apply_end hD hD' (hvert hz) (flat_mem _)
  · exact discGlue_apply_seam hD hD' _ (hvert hz)

/-- Reparametrizing the glued map by the profile `τ` does not change its integral. -/
private theorem rectangleIntegral_discSphere [IsManifold I 2 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') :
    rectangleIntegral φ (discSphere D D') (0, 0) (1, 1) =
      rectangleIntegral φ (discGlue D D') (0, 0) (1, 1) := by
  -- The straight-line homotopy from the identity to `τ`, in both coordinates.
  let Φ : (ℝ × ℝ) × ℝ → M := fun q ↦ discGlue D D'
    ((1 - q.2) * q.1.1 + q.2 * flat q.1.1, (1 - q.2) * q.1.2 + q.2 * flat q.1.2)
  have hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ :=
    ((contMDiff_discGlue hD hD').comp (ContDiff.contMDiff (by
      have := contDiff_flat
      fun_prop))).of_le (by norm_cast)
  have hmem {r c : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
      (1 - c) * r + c * flat r ∈ Icc (0 : ℝ) 1 :=
    sub_mul_add_mul_mem hr (flat_mem r) hc
  have h0 (c : ℝ) : (1 - c) * 0 + c * flat 0 = 0 := by simp [flat_of_le]
  have h1 (c : ℝ) : (1 - c) * 1 + c * flat 1 = 1 := by rw [flat_of_ge (by norm_num)]; ring
  have key := rectangleIntegral_eq_of_homotopy hφ hdφ hΦ (a := (0, 0)) (b := (1, 1))
    (Or.inr fun t ht c hc ↦ by
      simp only [Φ, h0]
      rw [discGlue_apply_end hD hD' (Or.inl rfl) (hmem (by simpa using ht) hc),
        discGlue_apply_end hD hD' (Or.inl rfl) ⟨le_rfl, zero_le_one⟩])
    (Or.inr fun t ht c hc ↦ by
      simp only [Φ, h1]
      rw [discGlue_apply_end hD hD' (Or.inr rfl) (hmem (by simpa using ht) hc),
        discGlue_apply_end hD hD' (Or.inr rfl) ⟨zero_le_one, le_rfl⟩])
    (fun s _ c _ ↦ by
      simp only [Φ, h0, h1]
      rw [discGlue_apply_seam hD hD' _ (Or.inr rfl), discGlue_apply_seam hD hD' _ (Or.inl rfl)])
  have hΦ₁ : (fun z ↦ Φ (z, 1)) = discSphere D D' := funext fun z ↦ by simp [Φ, discSphere]
  have hΦ₀ : (fun z ↦ Φ (z, 0)) = discGlue D D' := funext fun z ↦ by simp [Φ]
  rwa [hΦ₁, hΦ₀] at key

/-- The integral over the glued map is the integral over `D` minus the integral over `D'`. -/
private theorem rectangleIntegral_discGlue [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') :
    rectangleIntegral φ (discGlue D D') (0, 0) (1, 1) =
      rectangleIntegral φ D (0, 0) (1, 1) - rectangleIntegral φ D' (0, 0) (1, 1) := by
  have hD1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D := hD.contMDiff.of_le (by simp)
  have hD'1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D' := hD'.contMDiff.of_le (by simp)
  have hrev : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) 1 rev :=
    ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff
  rw [discGlue, rectangleIntegral_rectangleTrans hφ hD1 (hD'1.comp hrev) (discGlue_hyp hD hD'),
    rev, rectangleIntegral_comp_prodMap_one_sub hφ hD'1, sub_eq_add_neg]

end Glue

namespace IsSmoothDisc

variable {γ : Path x x} {D D' : ℝ × ℝ → M}

/-- The parameter of the double loop `D⁻¹ ⬝ D'` at which the glued map `discGlue D D'` reads its
value at `w ∈ [0, 1]`: `(β(3 w) + β(3 w - 2)) / 2` for `β = Real.smoothTransition`. -/
private def glueParam (w : ℝ) : ℝ :=
  (Real.smoothTransition (3 * w) + Real.smoothTransition (3 * w - 2)) / 2

private theorem glueParam_mem (w : ℝ) : glueParam w ∈ Icc (0 : ℝ) 1 := by
  have := Real.smoothTransition.nonneg (3 * w)
  have := Real.smoothTransition.nonneg (3 * w - 2)
  have := Real.smoothTransition.le_one (3 * w)
  have := Real.smoothTransition.le_one (3 * w - 2)
  exact ⟨by unfold glueParam; linarith, by unfold glueParam; linarith⟩

private theorem glueParam_zero : glueParam 0 = 0 := by
  simp [glueParam, Real.smoothTransition.zero_of_nonpos]

private theorem glueParam_one : glueParam 1 = 1 := by
  norm_num [glueParam, Real.smoothTransition.one_of_one_le]

/-- The self-map `w ↦ glueParam (τ w)` of the unit interval. -/
private def sphereParam₁ : C(unitInterval, unitInterval) :=
  ⟨fun w ↦ ⟨glueParam (flat w), glueParam_mem _⟩, by
    refine Continuous.subtype_mk ?_ _
    unfold glueParam flat
    fun_prop⟩

/-- The self-map `τ` of the unit interval. -/
private def sphereParam₂ : C(unitInterval, unitInterval) :=
  ⟨fun w ↦ ⟨flat w, flat_mem _⟩, by
    refine Continuous.subtype_mk ?_ _
    unfold flat
    fun_prop⟩

/-- The glued sphere is the double loop `D⁻¹ ⬝ D'` with its cube coordinates reparametrized. -/
private theorem discSphere_eq (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D')
    (z : Fin 2 → unitInterval) :
    discSphere D D' ((z 0 : ℝ), (z 1 : ℝ)) =
      GenLoop.fromDoubleLoop (hD.loopPath.symm.trans hD'.loopPath)
        (fun i ↦ (![sphereParam₁, sphereParam₂] : Fin 2 → C(unitInterval, unitInterval)) i
          (z i)) := by
  set w := flat (z 0)
  set t : unitInterval := ⟨flat (z 1), flat_mem _⟩
  have hβ₀ := Real.smoothTransition.nonneg (3 * w - 2)
  have hβ₁ := Real.smoothTransition.le_one (3 * w)
  simp only [GenLoop.fromDoubleLoop_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  change discGlue D D' (w, (t : ℝ)) =
    (hD.loopPath.symm.trans hD'.loopPath) ⟨glueParam w, glueParam_mem _⟩ t
  rw [Path.trans_apply]
  rcases le_or_gt w (1 / 2) with hw | hw
  · -- `w ≤ 1/2`: both sides run through `D` at the parameter `β(3 w)`.
    have h2 : Real.smoothTransition (3 * w - 2) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [discGlue, rectangleTrans_eq_left (discGlue_hyp hD hD') (z := (w, t)) (by linarith)]
    split_ifs with hp
    · simp only [Path.symm_apply, loopPath_apply_apply, unitInterval.symm_symm,
        Function.comp_apply, Prod.map_apply, id_eq]
      congr 2
      simp only [glueParam, h2]
      ring
    · exact absurd (by simp only [glueParam, h2]; linarith) hp
  · -- `w > 1/2`: both sides run backwards through `D'` at the parameter `1 - β(3 w - 2)`.
    have h1 : Real.smoothTransition (3 * w) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    rw [discGlue, rectangleTrans_eq_right (discGlue_hyp hD hD') (z := (w, t)) (by linarith)]
    simp only [Function.comp_apply, Prod.map_apply, id_eq, rev]
    split_ifs with hp
    · -- The parameter is `1/2`, so both sides lie on the common edge `γ`.
      have h2 : Real.smoothTransition (3 * w - 2) = 0 := by
        simp only [glueParam, h1] at hp
        linarith
      simp only [Path.symm_apply, h2, sub_zero]
      rw [← hD.apply_one_eq hD']
      congr 2
      simp [glueParam, h1, h2]
    · simp only [loopPath_apply_apply, unitInterval.coe_symm_eq]
      congr 2
      simp only [glueParam, h1]
      ring

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M]

/-- **The integral over the sphere by which two discs differ.** For a closed `C¹` two-form `φ` on
a compact manifold and two smooth discs `D` and `D'` bounding the same loop `γ`, the integral of
`φ` over the class in `π₂(M, x)` of the double loop `D⁻¹ ⬝ D'`, which runs from the centre of `D`
to `γ` and then back to the centre of `D'`, is the integral of `φ` over `D` minus its integral
over `D'`. -/
theorem sphereIntegral_loopPath_symm_trans {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') :
    sphereIntegral φ x (HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv
      (FundamentalGroup.fromPath (.mk (hD.loopPath.symm.trans hD'.loopPath)))) =
      rectangleIntegral φ D (0, 0) (1, 1) - rectangleIntegral φ D' (0, 0) (1, 1) := by
  have hv := isSmoothSphere_discSphere hD hD'
  have hloop : GenLoop.Homotopic (GenLoop.fromDoubleLoop (hD.loopPath.symm.trans hD'.loopPath))
      hv.genLoop :=
    GenLoop.homotopic_of_forall_apply_eq_comp ![sphereParam₁, sphereParam₂]
      (fun i ↦ by
        fin_cases i <;> ext <;> simp [sphereParam₁, sphereParam₂, flat_zero, glueParam_zero])
      (fun i ↦ by
        fin_cases i <;> ext <;> simp [sphereParam₁, sphereParam₂, flat_one, glueParam_one])
      fun z ↦ by rw [IsSmoothSphere.genLoop_apply]; exact discSphere_eq hD hD' z
  rw [HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_fromPath_mk, Quotient.sound hloop,
    sphereIntegral_mk hφ hdφ hv, rectangleIntegral_discSphere hφ hdφ hD hD',
    rectangleIntegral_discGlue (hφ.of_le (by simp)) hD hD']

end IsSmoothDisc

end TauCeti
