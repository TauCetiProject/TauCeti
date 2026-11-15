/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped

/-!
# The symplectic area of raw caps

Let `M` be a compact boundaryless manifold, `φ` a closed `C¹` two-form on `M`, for instance the
symplectic form of a closed symplectic manifold, and `γ` a loop in `M` based at `x`. The raw caps
of `γ` (`TauCeti.Floer.RawCap γ`) are homotopy classes of continuous discs bounding `γ`, and they
form a torsor under `π₂(M, x)` (`TauCeti.Floer.RawCap.instAddTorsor`). The integral of `φ` over
the classes of `π₂(M, x)` is the homomorphism `TauCeti.sphereIntegralHom`. This file defines the
integral of `φ` over a raw cap and proves that it obeys the recapping law for this homomorphism.

A **smooth based cylinder** from a loop `γ₁` to a loop `γ₂`, both based at `x`
(`TauCeti.Floer.IsSmoothBasedCylinder`), is a smooth map `w : ℝ × ℝ → M`, `1`-periodic in `t`,
with `w (0, t) = γ₁ t`, `w (1, t) = γ₂ t` and `w (s, 0) = x` for `s, t ∈ [0, 1]`: a cylinder swept
out from `γ₁` to `γ₂` through loops based at `x`. Its homotopy of based loops
`IsSmoothBasedCylinder.hom` is the class of the path `s ↦ w (s, ·)` in the loop space, a morphism
from `γ₁` to `γ₂` in the fundamental groupoid of the loop space. A **smooth based cap** of `γ`
(`TauCeti.Floer.IsSmoothBasedCap`) is a smooth based cylinder from `γ` to the constant loop: a disc
bounding `γ`, swept out from `γ` at `s = 0` to its centre at `s = 1`. Its homotopy of based loops is
a raw cap of `γ`. Periodicity makes two smooth based cylinders meeting along a loop agree along the
whole common edge, so that they glue smoothly: the concatenation `TauCeti.rectangleTrans w w'` is a
smooth based cylinder (`TauCeti.Floer.IsSmoothBasedCylinder.trans`) whose homotopy of loops is the
composite `w.hom ≫ w'.hom` (`TauCeti.Floer.IsSmoothBasedCylinder.hom_trans`), and the cylinder run
backwards is a smooth based cylinder (`TauCeti.Floer.IsSmoothBasedCylinder.symm`) whose homotopy
of loops is the inverse (`TauCeti.Floer.IsSmoothBasedCylinder.hom_symm`).

* **Two smooth caps differ by the sphere they bound.** For two smooth based caps `u` and `u'` of
  `γ`, the sphere `u'.hom -ᵥ u.hom` is represented by the concatenation of `u` run backwards and
  `u'` (`TauCeti.Floer.IsSmoothBasedCap.hom_vsub_hom_toMul`), a smooth based cylinder from the
  constant loop to itself. So the integral of `φ` over this sphere is `∫ u'^* φ - ∫ u^* φ`, the
  integrals being over the unit square
  (`TauCeti.Floer.IsSmoothBasedCap.sphereIntegral_hom_vsub_hom`), by
  `TauCeti.sphereIntegral_mk_of_contMDiff`.
* **The area of a raw cap.** If `γ` has a smooth based cap `u₀` (witnessing `h`), the area of a
  raw cap `D` is `RawCap.area φ h D = ∫ u₀^* φ + ∫_{D -ᵥ u₀.hom} φ`. The area is only defined
  for loops with a smooth based cap. It does not depend on `u₀`: the area of the raw cap of every
  smooth based cap `u` is `∫ u^* φ` (`TauCeti.Floer.RawCap.area_hom`).
* **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap adds the integral of `φ` over
  `a` to its area, `area (a +ᵥ D) = ∫_a φ + area D` (`TauCeti.Floer.RawCap.area_vadd`), and the
  areas of two raw caps differ by the integral over the sphere by which they differ
  (`TauCeti.Floer.RawCap.area_sub_area`).
* **Gluing a cylinder adds its area.** For a smooth based cylinder `w` from `γ₁` to `γ₂` and a raw
  cap `D` of `γ₂`, the raw cap `w.hom ≫ D` of `γ₁` has area `∫ w^* φ + area D`
  (`TauCeti.Floer.RawCap.area_hom_comp`), and gluing the cylinder run backwards to a raw cap of
  `γ₁` subtracts `∫ w^* φ` (`TauCeti.Floer.RawCap.area_inv_hom_comp`). Gluing a homotopy of loops to
  caps is the cap transport of `TauCeti.Floer.SphericalCapClass.glue`; these laws compute the area
  of the glued caps when the homotopy is represented by a smooth based cylinder.

The recapping law is the hypothesis of `TauCeti.Floer.CapClass.lift`, with the area homomorphism
`TauCeti.sphereIntegralHom` on the group `π₂(M, x)` of spheres. The area is measured with the cap
oriented from `γ` to its centre, as for `TauCeti.capArea`; the capped action
`TauCeti.cappedLoopAction` uses the disc oriented from its centre to `γ`, so for a smooth based cap
`hu : IsSmoothBasedCap I γ u` its area term is `-RawCap.area φ ⟨u, hu⟩ hu.hom`
(`TauCeti.Floer.IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub`).

## Main definitions

* `TauCeti.Floer.IsSmoothBasedCylinder I γ₁ γ₂ w`: `w` is a smooth based cylinder from `γ₁` to
  `γ₂`, and `TauCeti.Floer.IsSmoothBasedCylinder.hom` its homotopy of based loops.
* `TauCeti.Floer.IsSmoothBasedCap I γ u`: `u` is a smooth based cap of `γ`.
* `TauCeti.Floer.RawCap.area φ h D`: the integral of `φ` over a raw cap `D` of a loop with a
  smooth based cap (`h`).

## Main results

* `TauCeti.Floer.IsSmoothBasedCylinder.hom_trans`, `TauCeti.Floer.IsSmoothBasedCylinder.hom_symm`:
  gluing and reversing smooth based cylinders compose and invert their homotopies of loops.
* `TauCeti.Floer.IsSmoothBasedCap.hom_vsub_hom_toMul`: two smooth based caps differ by the
  sphere represented by their concatenation.
* `TauCeti.Floer.IsSmoothBasedCap.sphereIntegral_hom_vsub_hom`: two smooth based caps differ
  by a sphere whose integral is the difference of their integrals.
* `TauCeti.Floer.RawCap.area_hom`: the area of the raw cap of a smooth based cap is its integral.
* `TauCeti.Floer.RawCap.area_vadd`: the recapping law.
* `TauCeti.Floer.RawCap.area_sub_area`: two raw caps have areas differing by the integral over the
  sphere by which they differ.
* `TauCeti.Floer.RawCap.area_hom_comp`, `TauCeti.Floer.RawCap.area_inv_hom_comp`: gluing a smooth
  based cylinder to a raw cap adds the integral over the cylinder to its area, and gluing it run
  backwards subtracts this integral.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the action of capped loops and its recapping law.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and capped loops).
-/

public section

noncomputable section

open Set CategoryTheory HomotopyGroup
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti.Floer

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : M} {γ : Ω M x}

/-! ### Smooth based cylinders and caps -/

omit [TopologicalSpace M] in
/-- Two maps which are `1`-periodic in their second coordinate along the lines `s` and `s'`, and
agree there for `t` in the unit interval, agree along the whole lines. -/
private theorem apply_eq_apply_of_forall_unitInterval {u v : ℝ × ℝ → M} {s s' : ℝ}
    (hu : ∀ t, u (s, t + 1) = u (s, t)) (hv : ∀ t, v (s', t + 1) = v (s', t))
    (h : ∀ t : unitInterval, u (s, t) = v (s', t)) (t : ℝ) : u (s, t) = v (s', t) := by
  have hp : Function.Periodic (fun t ↦ u (s, t)) 1 := hu
  have hp' : Function.Periodic (fun t ↦ v (s', t)) 1 := hv
  have ht : t - ⌊t⌋ * 1 ∈ unitInterval := by
    rw [mul_one, ← Int.fract]
    exact ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  rw [← hp.sub_int_mul_eq ⌊t⌋, ← hp'.sub_int_mul_eq ⌊t⌋]
  exact h ⟨_, ht⟩

variable (I) in
/-- A **smooth based cylinder** from a loop `γ₁` to a loop `γ₂`, both based at `x`: a smooth map
`w : ℝ × ℝ → M`, `1`-periodic in its second coordinate, which runs along `γ₁` for `s = 0` and
along `γ₂` for `s = 1`, and sends the edge `t = 0` of the unit square to `x`. The loops
`w (s, ·)` are based at `x`, so `s ↦ w (s, ·)` is a path in the loop space from `γ₁` to `γ₂`, a
homotopy of based loops (`TauCeti.Floer.IsSmoothBasedCylinder.hom`). Periodicity makes `w (0, ·)`
and `w (1, ·)` the periodic extensions of `γ₁` and `γ₂`, so that two cylinders meeting along a
loop glue smoothly (`TauCeti.Floer.IsSmoothBasedCylinder.trans`). -/
structure IsSmoothBasedCylinder (γ₁ γ₂ : Ω M x) (w : ℝ × ℝ → M) : Prop where
  /-- A smooth based cylinder is smooth. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w
  /-- A smooth based cylinder is `1`-periodic in its second coordinate. -/
  apply_add_one : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z
  /-- A smooth based cylinder starts at its first loop. -/
  apply_zero : ∀ t : unitInterval, w (0, t) = γ₁ t
  /-- A smooth based cylinder ends at its second loop. -/
  apply_one : ∀ t : unitInterval, w (1, t) = γ₂ t
  /-- The seam `t = 0` stays at the base point. -/
  apply_seam : ∀ s : unitInterval, w (s, 0) = x

variable (I) in
/-- A **smooth based cap** of a loop `γ` based at `x`: a smooth based cylinder from `γ` to the
constant loop. That is, a smooth map `u : ℝ × ℝ → M`, `1`-periodic in its second coordinate, which
starts at `γ` for `s = 0`, ends at `x` for `s = 1`, and sends the edge `t = 0` of the unit square
to `x`: a disc bounding `γ`, with its centre at `s = 1`. Periodicity makes `u (0, ·)` the periodic
extension of `γ`, which is how the one-periodic orbits of a Hamiltonian are parametrized. -/
abbrev IsSmoothBasedCap (γ : Ω M x) (u : ℝ × ℝ → M) : Prop :=
  IsSmoothBasedCylinder I γ (Path.refl x) u

/-- The constant map is a smooth based cap of the constant loop. -/
theorem isSmoothBasedCap_refl (x : M) : IsSmoothBasedCap I (Path.refl x) fun _ ↦ x :=
  ⟨contMDiff_const, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

namespace IsSmoothBasedCylinder

variable {γ₁ γ₂ γ₃ : Ω M x} {w w' : ℝ × ℝ → M}

/-- The edge `t = 1` of a smooth based cylinder stays at the base point. -/
theorem apply_seam_one (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) (s : unitInterval) :
    w (s, 1) = x := by
  simpa using (hw.apply_add_one (s, 0)).trans (hw.apply_seam s)

/-- Two smooth based cylinders from the same loop agree along the whole line `s = 0`, where both
are the periodic extension of the loop. -/
theorem apply_zero_eq_apply_zero (hw : IsSmoothBasedCylinder I γ₁ γ₂ w)
    (hw' : IsSmoothBasedCylinder I γ₁ γ₃ w') (t : ℝ) : w (0, t) = w' (0, t) :=
  apply_eq_apply_of_forall_unitInterval (fun t ↦ hw.apply_add_one (0, t))
    (fun t ↦ hw'.apply_add_one (0, t)) (fun t ↦ (hw.apply_zero t).trans (hw'.apply_zero t).symm) t

/-- A smooth based cylinder ending at a loop and a smooth based cylinder starting at it agree along
the whole common edge, where both are the periodic extension of the loop. -/
theorem apply_one_eq_apply_zero (hw : IsSmoothBasedCylinder I γ₁ γ₂ w)
    (hw' : IsSmoothBasedCylinder I γ₂ γ₃ w') (t : ℝ) : w (1, t) = w' (0, t) :=
  apply_eq_apply_of_forall_unitInterval (fun t ↦ hw.apply_add_one (1, t))
    (fun t ↦ hw'.apply_add_one (0, t)) (fun t ↦ (hw.apply_one t).trans (hw'.apply_zero t).symm) t

/-- The path `s ↦ w (s, ·)` in the loop space of a smooth based cylinder `w`, from `γ₁` to
`γ₂`. -/
def toPath (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) : Path γ₁ γ₂ where
  toFun s := ⟨⟨fun t ↦ w (s, t),
    hw.contMDiff.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩,
    hw.apply_seam s, hw.apply_seam_one s⟩
  continuous_toFun := Path.continuous_uncurry_iff.1 <|
    hw.contMDiff.continuous.comp (by fun_prop)
  source' := Path.ext <| funext hw.apply_zero
  target' := Path.ext <| funext hw.apply_one

@[simp]
theorem toPath_apply (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) (s t : unitInterval) :
    hw.toPath s t = w (s, t) :=
  (rfl)

/-- The homotopy of based loops of a smooth based cylinder from `γ₁` to `γ₂`: the homotopy class of
its path in the loop space, a morphism from `γ₁` to `γ₂` in the fundamental groupoid of the loop
space. For a smooth based cap of `γ` it is a raw cap of `γ`. -/
def hom (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) : (⟨γ₁⟩ : FundamentalGroupoid (Ω M x)) ⟶ ⟨γ₂⟩ :=
  Path.Homotopic.Quotient.mk hw.toPath

theorem hom_def (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) :
    hw.hom = Path.Homotopic.Quotient.mk hw.toPath :=
  (rfl)

/-- **Gluing smooth based cylinders.** The concatenation `TauCeti.rectangleTrans w w'` of a smooth
based cylinder `w` from `γ₁` to `γ₂` and a smooth based cylinder `w'` from `γ₂` to `γ₃` is a smooth
based cylinder from `γ₁` to `γ₃`. -/
theorem trans (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) (hw' : IsSmoothBasedCylinder I γ₂ γ₃ w') :
    IsSmoothBasedCylinder I γ₁ γ₃ (rectangleTrans w w') where
  contMDiff := _root_.TauCeti.contMDiff_rectangleTrans hw.contMDiff hw'.contMDiff
    (hw.apply_one_eq_apply_zero hw')
  apply_add_one := rectangleTrans_apply_add_snd hw.apply_add_one hw'.apply_add_one
  apply_zero t := (rectangleTrans_apply_zero w w' t).trans (hw.apply_zero t)
  apply_one t := (rectangleTrans_apply_one w w' t).trans (hw'.apply_one t)
  apply_seam s := by
    have h := hw.apply_one_eq_apply_zero hw'
    have hβ (r : ℝ) : Real.smoothTransition r ∈ unitInterval :=
      ⟨Real.smoothTransition.nonneg r, Real.smoothTransition.le_one r⟩
    rcases lt_or_ge (s : ℝ) (2 / 3) with hs | hs
    · rw [rectangleTrans_eq_left h (z := ((s : ℝ), 0)) hs]
      exact hw.apply_seam ⟨Real.smoothTransition (3 * s), hβ _⟩
    · rw [rectangleTrans_eq_right h (z := ((s : ℝ), 0)) (by simp only; linarith)]
      exact hw'.apply_seam ⟨Real.smoothTransition (3 * s - 2), hβ _⟩

/-- **Reversing a smooth based cylinder.** A smooth based cylinder `w` from `γ₁` to `γ₂`, run
backwards in `s`, is a smooth based cylinder from `γ₂` to `γ₁`. -/
theorem symm (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) :
    IsSmoothBasedCylinder I γ₂ γ₁ (w ∘ Prod.map (fun s ↦ 1 - s) id) where
  contMDiff := hw.contMDiff.comp ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff
  apply_add_one z := hw.apply_add_one (1 - z.1, z.2)
  apply_zero t := by simpa using hw.apply_one t
  apply_one t := by simpa using hw.apply_zero t
  apply_seam s := by simpa using hw.apply_seam (unitInterval.symm s)

/-- The path in the loop space of a reversed cylinder is the reversed path. -/
@[simp]
theorem toPath_symm (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) : hw.symm.toPath = hw.toPath.symm := by
  ext s t
  simp

/-- The homotopy of loops of a reversed cylinder is the inverse homotopy of loops. -/
theorem hom_symm (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) : hw.symm.hom = inv hw.hom := by
  rw [← Groupoid.inv_eq_inv, hom_def, toPath_symm]
  rfl

/-- The reparametrization of the unit interval under which the concatenation of the paths in the
loop space of two cylinders becomes the path of their concatenation `TauCeti.rectangleTrans`. -/
private def concatReparam (s : ℝ) : ℝ :=
  if s ≤ 1 / 2 then Real.smoothTransition (3 * s) / 2
  else (1 + Real.smoothTransition (3 * s - 2)) / 2

private theorem concatReparam_of_le {s : ℝ} (hs : s ≤ 1 / 2) :
    concatReparam s = Real.smoothTransition (3 * s) / 2 := by
  simp only [concatReparam, hs, ↓reduceIte]

private theorem concatReparam_of_lt {s : ℝ} (hs : 1 / 2 < s) :
    concatReparam s = (1 + Real.smoothTransition (3 * s - 2)) / 2 := by
  simp only [concatReparam, hs.not_ge, ↓reduceIte]

private theorem continuous_concatReparam : Continuous concatReparam := by
  refine Continuous.if_le (by fun_prop (disch := exact Real.smoothTransition.continuous))
    (by fun_prop (disch := exact Real.smoothTransition.continuous)) continuous_id
    continuous_const fun s hs ↦ ?_
  rw [hs, Real.smoothTransition.one_of_one_le (by norm_num),
    Real.smoothTransition.zero_of_nonpos (by norm_num)]
  norm_num

private theorem concatReparam_mem (s : ℝ) : concatReparam s ∈ unitInterval := by
  have h₀ := Real.smoothTransition.nonneg (3 * s)
  have h₁ := Real.smoothTransition.le_one (3 * s)
  have h₂ := Real.smoothTransition.nonneg (3 * s - 2)
  have h₃ := Real.smoothTransition.le_one (3 * s - 2)
  rcases le_or_gt s (1 / 2) with hs | hs
  · rw [concatReparam_of_le hs]
    constructor <;> linarith
  · rw [concatReparam_of_lt hs]
    constructor <;> linarith

/-- The reparametrization of the unit interval as a map of the unit interval. -/
private def concatReparamI (s : unitInterval) : unitInterval :=
  ⟨concatReparam s, concatReparam_mem s⟩

private theorem coe_concatReparamI (s : unitInterval) :
    (concatReparamI s : ℝ) = concatReparam s :=
  (rfl)

private theorem continuous_concatReparamI : Continuous concatReparamI :=
  (continuous_concatReparam.comp continuous_subtype_val).subtype_mk _

private theorem concatReparamI_zero : concatReparamI 0 = 0 :=
  Subtype.ext <| by
    rw [coe_concatReparamI, Icc.coe_zero, concatReparam_of_le (by norm_num), mul_zero,
      Real.smoothTransition.zero, zero_div]

private theorem concatReparamI_one : concatReparamI 1 = 1 :=
  Subtype.ext <| by
    rw [coe_concatReparamI, Icc.coe_one, concatReparam_of_lt (by norm_num),
      Real.smoothTransition.one_of_one_le (by norm_num)]
    norm_num

/-- The path in the loop space of two glued cylinders is the concatenation of their paths,
reparametrized by `concatReparamI`. -/
private theorem toPath_trans (hw : IsSmoothBasedCylinder I γ₁ γ₂ w)
    (hw' : IsSmoothBasedCylinder I γ₂ γ₃ w') :
    (hw.trans hw').toPath = (hw.toPath.trans hw'.toPath).reparam concatReparamI
      continuous_concatReparamI concatReparamI_zero concatReparamI_one := by
  have h := hw.apply_one_eq_apply_zero hw'
  ext s t
  have hβ₀ := Real.smoothTransition.nonneg (3 * (s : ℝ) - 2)
  have hβ₁ := Real.smoothTransition.le_one (3 * (s : ℝ))
  rw [toPath_apply, Path.coe_reparam, Function.comp_apply, Path.trans_apply]
  rcases le_or_gt (s : ℝ) (1 / 2) with hs | hs
  · -- First half: `w`.
    have hc : (concatReparamI s : ℝ) ≤ 1 / 2 := by
      rw [coe_concatReparamI, concatReparam_of_le hs]
      linarith
    rw [dite_eq_left hc, rectangleTrans_eq_left h (by simp only; linarith)]
    simp only [Function.comp_apply, toPath_apply, coe_concatReparamI, concatReparam_of_le hs,
      Prod.map_apply, id_eq]
    congr 2
    ring
  · rw [rectangleTrans_eq_right h (by simp only; linarith)]
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    split_ifs with hc
    · -- Second half, while the concatenated path rests at `γ₂`.
      rw [coe_concatReparamI, concatReparam_of_lt hs] at hc
      have hz : Real.smoothTransition (3 * (s : ℝ) - 2) = 0 := by linarith
      simp only [toPath_apply, coe_concatReparamI, concatReparam_of_lt hs, hz]
      norm_num [h t]
    · -- Second half: `w'`.
      simp only [toPath_apply, coe_concatReparamI, concatReparam_of_lt hs]
      congr 2
      ring

/-- The homotopy of loops of two glued cylinders is the composite of their homotopies of loops. -/
theorem hom_trans (hw : IsSmoothBasedCylinder I γ₁ γ₂ w)
    (hw' : IsSmoothBasedCylinder I γ₂ γ₃ w') : (hw.trans hw').hom = hw.hom ≫ hw'.hom := by
  have hrep : Path.Homotopic.Quotient.mk (hw.toPath.trans hw'.toPath) =
      Path.Homotopic.Quotient.mk ((hw.toPath.trans hw'.toPath).reparam concatReparamI
        continuous_concatReparamI concatReparamI_zero concatReparamI_one) :=
    Quotient.sound ⟨Path.Homotopy.reparam _ _ _ _ _⟩
  rw [hom_def, toPath_trans hw hw', ← hrep]
  rfl

/-- A loop joined by a smooth based cylinder to a loop with a smooth based cap has a smooth based
cap, the glued cylinder. -/
theorem exists_isSmoothBasedCap (hw : IsSmoothBasedCylinder I γ₁ γ₂ w)
    (h : ∃ u, IsSmoothBasedCap I γ₂ u) : ∃ u, IsSmoothBasedCap I γ₁ u :=
  ⟨_, hw.trans h.choose_spec⟩

end IsSmoothBasedCylinder

namespace IsSmoothBasedCap

variable {γ : Ω M x} {u u' : ℝ × ℝ → M}

open IsSmoothBasedCylinder in
/-- **The sphere bounded by two smooth caps.** For smooth based caps `u` and `u'` of the same loop,
the sphere by which their raw caps differ is the class of any generalized loop restricting their
concatenation `rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`, `u` run backwards followed
by `u'`, to the unit square. This concatenation is the smooth based cylinder
`hu.symm.trans hu'` from the constant loop to itself. -/
theorem hom_vsub_hom_toMul (hu : IsSmoothBasedCap I γ u) (hu' : IsSmoothBasedCap I γ u')
    {p : Ω^ (Fin 2) M x}
    (hp : ∀ y, p y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ))) :
    (hu'.hom -ᵥ hu.hom).toMul = ⟦p⟧ := by
  -- The sphere is the class of the double loop `u` run backwards, then `u'`, which is the class of
  -- the path in the loop space of the glued cylinder.
  have hβ : (hu.symm.trans hu').hom =
      Path.Homotopic.Quotient.mk (hu.toPath.symm.trans hu'.toPath) := by
    rw [hom_trans hu.symm hu', hom_def, hom_def, toPath_symm]
    rfl
  have hv : hu'.hom -ᵥ hu.hom =
      .ofMul (fundamentalGroupLoopSpaceMulEquiv (FundamentalGroup.fromPath (hu.symm.trans hu').hom))
      := by
    -- In the fundamental groupoid, `inv ⟦P⟧ ≫ ⟦P'⟧` is `⟦P.symm.trans P'⟧` by definition of its
    -- inverse and composition.
    rw [hβ, RawCap.vsub_def]
    rfl
  rw [hv, toMul_ofMul, hom_def, fundamentalGroupLoopSpaceMulEquiv_fromPath_mk]
  exact congrArg _ <| GenLoop.ext _ _ fun y ↦ (GenLoop.fromDoubleLoop_apply _ _).trans (hp y).symm

/-- **Two smooth caps differ by the sphere they bound.** For smooth based caps `u` and `u'` of the
same loop, the integral of a closed `C¹` two-form over the sphere by which their raw caps differ
is the difference of their integrals over the unit square. -/
theorem sphereIntegral_hom_vsub_hom [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [CompactSpace M] [T2Space M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u') :
    sphereIntegral φ x (hu'.hom -ᵥ hu.hom).toMul =
      rectangleIntegral φ u' (0, 0) (1, 1) - rectangleIntegral φ u (0, 0) (1, 1) := by
  have hp (y : Fin 2 → unitInterval) : GenLoop.fromDoubleLoop (hu.symm.trans hu').toPath y =
      rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)) :=
    GenLoop.fromDoubleLoop_apply _ _
  rw [hu.hom_vsub_hom_toMul hu' hp,
    sphereIntegral_mk_of_contMDiff hφ hdφ (hu.symm.trans hu').contMDiff hp,
    rectangleIntegral_rectangleTrans_comp_prodMap_one_sub (hφ.of_le (by simp))
      (hu.contMDiff.of_le (by simp)) (hu'.contMDiff.of_le (by simp))
      (hu.apply_zero_eq_apply_zero hu')]

end IsSmoothBasedCap

/-! ### The area of a raw cap -/

section Area

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  {φ : RoughForm I M F 2}

/-- The **area** of a raw cap `D` of a loop `γ` with a smooth based cap `u₀`, for a two-form `φ`:
the integral of `φ` over `u₀` plus its integral over the sphere `D -ᵥ u₀.hom` by which `D`
differs from the raw cap of `u₀`. It is defined only for loops that have a smooth based cap. For a
closed `C¹` form it is the integral over the raw cap of any smooth based cap
(`TauCeti.Floer.RawCap.area_hom`), so it does not depend on `u₀`. The cap is oriented from `γ`
to its centre. -/
def RawCap.area (φ : RoughForm I M F 2) (h : ∃ u, IsSmoothBasedCap I γ u) (D : RawCap γ) : F :=
  rectangleIntegral φ h.choose (0, 0) (1, 1) +
    sphereIntegral φ x (D -ᵥ h.choose_spec.hom).toMul

/-- The defining equation of `TauCeti.Floer.RawCap.area`, for an arbitrary two-form. -/
theorem RawCap.area_def (φ : RoughForm I M F 2) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D : RawCap γ) :
    RawCap.area φ h D = rectangleIntegral φ h.choose (0, 0) (1, 1) +
      sphereIntegral φ x (D -ᵥ h.choose_spec.hom).toMul :=
  (rfl)

/-- **The area of a smooth cap.** For a closed `C¹` two-form, the area of the raw cap of a smooth
based cap `u` is the integral of the form over `u` on the unit square. -/
theorem RawCap.area_hom (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {u : ℝ × ℝ → M}
    (hu : IsSmoothBasedCap I γ u) :
    RawCap.area φ ⟨u, hu⟩ hu.hom = rectangleIntegral φ u (0, 0) (1, 1) := by
  have h : ∃ u, IsSmoothBasedCap I γ u := ⟨u, hu⟩
  rw [RawCap.area_def, h.choose_spec.sphereIntegral_hom_vsub_hom hφ hdφ hu, add_sub_cancel]

/-- **The recapping law.** If `γ` has a smooth based cap, gluing a sphere `a ∈ π₂(M, x)` to a raw
cap of `γ` adds the integral of a closed `C¹` two-form over `a` to the area. -/
theorem RawCap.area_vadd (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (h : ∃ u, IsSmoothBasedCap I γ u) (a : Additive (π_ 2 M x)) (D : RawCap γ) :
    RawCap.area φ h (a +ᵥ D) = sphereIntegralHom x hφ hdφ a + RawCap.area φ h D := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  rw [RawCap.area_def, RawCap.area_def, vadd_vsub_assoc,
    ← sphereIntegralHom_apply hφ hdφ, ← sphereIntegralHom_apply hφ hdφ, map_add]
  abel

/-- **Two raw caps differ by a sphere.** If `γ` has a smooth based cap, the areas of two raw caps
of `γ` differ by the integral of a closed `C¹` two-form over the sphere by which they differ. -/
theorem RawCap.area_sub_area (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (h : ∃ u, IsSmoothBasedCap I γ u) (D' D : RawCap γ) :
    RawCap.area φ h D' - RawCap.area φ h D = sphereIntegralHom x hφ hdφ (D' -ᵥ D) := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  conv_lhs => rw [← vsub_vadd D' D, RawCap.area_vadd hφ hdφ h]
  exact add_sub_cancel_right _ _

/-- **Gluing a cylinder adds its area.** Let `w` be a smooth based cylinder from `γ₁` to `γ₂`, and
suppose that `γ₂` has a smooth based cap (`h₂`), so that `γ₁` has one too (`h₁`, for instance
`TauCeti.Floer.IsSmoothBasedCylinder.exists_isSmoothBasedCap`). For a closed `C¹` two-form, the
area of the raw cap `w ≫ D` of `γ₁`, obtained by gluing the cylinder to a raw cap `D` of `γ₂`, is
the integral of the form over the cylinder plus the area of `D`. -/
theorem RawCap.area_hom_comp (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {γ₁ γ₂ : Ω M x}
    {w : ℝ × ℝ → M} (hw : IsSmoothBasedCylinder I γ₁ γ₂ w) (h₁ : ∃ u, IsSmoothBasedCap I γ₁ u)
    (h₂ : ∃ u, IsSmoothBasedCap I γ₂ u) (D : RawCap γ₂) :
    RawCap.area φ h₁ (hw.hom ≫ D) = rectangleIntegral φ w (0, 0) (1, 1) + RawCap.area φ h₂ D := by
  obtain ⟨u, hu⟩ := h₂
  have : Nonempty (RawCap γ₂) := ⟨D⟩
  -- Write `D` as a sphere glued to the raw cap of `u`; gluing `w` to the raw cap of `u` is the raw
  -- cap of the smooth based cap `w` followed by `u`.
  rw [← vsub_vadd D hu.hom, RawCap.comp_vadd, ← hw.hom_trans hu, RawCap.area_vadd hφ hdφ,
    RawCap.area_vadd hφ hdφ, RawCap.area_hom hφ hdφ (hw.trans hu), RawCap.area_hom hφ hdφ hu,
    rectangleIntegral_rectangleTrans (hφ.of_le (by simp)) (hw.contMDiff.of_le (by simp))
      (hu.contMDiff.of_le (by simp)) (hw.apply_one_eq_apply_zero hu)]
  abel

/-- **Gluing a reversed cylinder subtracts its area.** Under the hypotheses of
`TauCeti.Floer.RawCap.area_hom_comp`, the area of the raw cap of `γ₂` obtained by gluing the
cylinder `w` run backwards to a raw cap `D` of `γ₁` is the area of `D` minus the integral of the
form over the cylinder. -/
theorem RawCap.area_inv_hom_comp (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    {γ₁ γ₂ : Ω M x} {w : ℝ × ℝ → M} (hw : IsSmoothBasedCylinder I γ₁ γ₂ w)
    (h₁ : ∃ u, IsSmoothBasedCap I γ₁ u) (h₂ : ∃ u, IsSmoothBasedCap I γ₂ u) (D : RawCap γ₁) :
    RawCap.area φ h₂ (inv hw.hom ≫ D) =
      RawCap.area φ h₁ D - rectangleIntegral φ w (0, 0) (1, 1) := by
  rw [← hw.hom_symm, RawCap.area_hom_comp hφ hdφ hw.symm h₂ h₁,
    rectangleIntegral_comp_prodMap_one_sub (hφ.of_le (by simp)) (hw.contMDiff.of_le (by simp))]
  abel

/-- **The capped action of a smooth cap.** For a smooth based cap `u` of `γ` and a closed real
`C¹` two-form `σ`, the capped action of `γ` with the disc `u` run backwards, from its centre to
`γ`, is minus the area of the raw cap of `u` plus the Hamiltonian term. -/
theorem IsSmoothBasedCap.cappedLoopAction_comp_prodMap_one_sub {σ : RoughForm I M ℝ 2}
    (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ) {u : ℝ × ℝ → M}
    (hu : IsSmoothBasedCap I γ u) :
    cappedLoopAction σ Ham (fun t ↦ u (0, t)) (u ∘ Prod.map (fun s ↦ 1 - s) id) =
      -RawCap.area σ ⟨u, hu⟩ hu.hom + ∫ t in 0..1, Ham t (u (0, t)) := by
  rw [cappedLoopAction_def, rectangleIntegral_comp_prodMap_one_sub (hσ.of_le (by simp))
    (hu.contMDiff.of_le (by simp)), RawCap.area_hom hσ hdσ hu]

end Area

end TauCeti.Floer
