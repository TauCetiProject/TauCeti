/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Radial coordinates in a seminormed space

The positive-norm locus of a real seminormed space is homeomorphic to any sphere of positive radius
times the positive real numbers. The inverse map is scalar multiplication, so these coordinates give
product neighbourhoods of the sphere even when the seminorm has a nonzero kernel.

`TauCeti.homeomorphSphereProdOfNormPos` and its unit-sphere specialization
`TauCeti.homeomorphUnitSphereProdOfNormPos` generalize Mathlib's `homeomorphSphereProd` and
`homeomorphUnitSphereProd`: the positive-norm locus replaces the complement of the origin. The
construction follows those homeomorphisms, with the domain and the proof that the inverse lands in
it adapted to seminorms.

Reparametrizing the radius by an open embedding `ρ : Y → ℝ` with positive values gives an open
embedding `(u, y) ↦ ρ y • u` of `sphere (0 : E) 1 × Y` into `E`
(`Topology.IsOpenEmbedding.smul_coe_sphere`). With `Y = ℝ` and `ρ` an increasing homeomorphism
onto an interval of radii, such as `t ↦ r * exp t` or the logistic sigmoid, this is a product
neighbourhood of a round sphere: a bicollar whose zero slice is the sphere of radius `ρ 0`.
`TauCeti.polar` uses the exponential radius `exp (t - 1)`, so that time `1` corresponds to the
unit sphere and times at most `1` parametrize the punctured closed unit ball.
-/

public section

namespace TauCeti

open Metric Set Topology

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial coordinates on the positive-norm locus of a real seminormed space, using the sphere
of radius `r > 0`. The forward map sends `x` to `(r • ‖x‖⁻¹ • x, ‖x‖ / r)` and the inverse
sends `(u, d)` to `d • u`. -/
noncomputable def homeomorphSphereProdOfNormPos (r : ℝ) (hr : 0 < r) :
    {x : E | 0 < ‖x‖} ≃ₜ (sphere (0 : E) r × Ioi (0 : ℝ)) where
  toFun x :=
    have hx : 0 < ‖x.1‖ := x.2
    (⟨r • ‖x.1‖⁻¹ • x.1, by simp [norm_smul, abs_of_pos hr, hx.ne']⟩,
      ⟨‖x.1‖ / r, mem_Ioi.mpr (div_pos hx hr)⟩)
  invFun p := ⟨p.2.1 • p.1.1, by
    have hd : 0 < (p.2 : ℝ) := mem_Ioi.mp p.2.2
    simpa only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere p.1,
      abs_of_pos hd] using mul_pos hd hr⟩
  left_inv x := by
    have hx : 0 < ‖x.1‖ := x.2
    ext
    calc
      (‖x.1‖ / r) • (r • ‖x.1‖⁻¹ • x.1) =
          ‖x.1‖ • ‖x.1‖⁻¹ • x.1 := by rw [smul_smul, div_mul_cancel₀ _ hr.ne']
      _ = x.1 := smul_inv_smul₀ hx.ne' x.1
  right_inv p := by
    obtain ⟨⟨u, hu⟩, ⟨d, hd⟩⟩ := p
    rw [mem_Ioi] at hd
    rw [mem_sphere_zero_iff_norm] at hu
    simp [norm_smul, smul_smul, abs_of_pos hd, hu, hr.ne', hd.ne']
  continuous_toFun := by
    have hnorm : Continuous (fun x : {x : E | 0 < ‖x‖} => ‖x.1‖) :=
      continuous_subtype_val.norm
    have hdir := ((hnorm.inv₀ fun x => ne_of_gt x.2).smul continuous_subtype_val).const_smul r
    exact (hdir.subtype_mk _).prodMk ((hnorm.div_const r).subtype_mk _)
  continuous_invFun := by fun_prop

@[simp]
theorem homeomorphSphereProdOfNormPos_apply_fst_coe (r : ℝ) (hr : 0 < r)
    (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphSphereProdOfNormPos E r hr x).1 : E) = r • ‖x.1‖⁻¹ • x.1 :=
  (rfl)

@[simp]
theorem homeomorphSphereProdOfNormPos_apply_snd_coe (r : ℝ) (hr : 0 < r)
    (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphSphereProdOfNormPos E r hr x).2 : ℝ) = ‖x.1‖ / r :=
  (rfl)

@[simp]
theorem homeomorphSphereProdOfNormPos_symm_apply_coe (r : ℝ) (hr : 0 < r)
    (p : sphere (0 : E) r × Ioi (0 : ℝ)) :
    ((homeomorphSphereProdOfNormPos E r hr).symm p : E) = (p.2 : ℝ) • (p.1 : E) :=
  (rfl)

/-- Radial coordinates on the positive-norm locus of a real seminormed space, using the unit
sphere. The forward map sends `x` to `(‖x‖⁻¹ • x, ‖x‖)` and the inverse sends `(u, r)` to
`r • u`. -/
noncomputable def homeomorphUnitSphereProdOfNormPos :
    {x : E | 0 < ‖x‖} ≃ₜ (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
  homeomorphSphereProdOfNormPos E 1 one_pos

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_apply_fst_coe (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphUnitSphereProdOfNormPos E x).1 : E) = ‖x.1‖⁻¹ • x.1 := by
  simp [homeomorphUnitSphereProdOfNormPos]

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_apply_snd_coe (x : {x : E | 0 < ‖x‖}) :
    ((homeomorphUnitSphereProdOfNormPos E x).2 : ℝ) = ‖x.1‖ := by
  simp [homeomorphUnitSphereProdOfNormPos]

@[simp]
theorem homeomorphUnitSphereProdOfNormPos_symm_apply_coe
    (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
    ((homeomorphUnitSphereProdOfNormPos E).symm p : E) = (p.2 : ℝ) • (p.1 : E) := by
  simp [homeomorphUnitSphereProdOfNormPos]

variable {E} in
/-- **Polar coordinates with a reparametrized radius.** If `ρ : Y → ℝ` is an open embedding with
positive values, then `(u, y) ↦ ρ y • u` is an open embedding of `sphere (0 : E) 1 × Y` into
`E`, onto the vectors whose norm lies in the range of `ρ`. -/
theorem _root_.Topology.IsOpenEmbedding.smul_coe_sphere {Y : Type*} [TopologicalSpace Y]
    {ρ : Y → ℝ} (hρ : Topology.IsOpenEmbedding ρ) (hpos : ∀ y, 0 < ρ y) :
    Topology.IsOpenEmbedding fun q : sphere (0 : E) 1 × Y => ρ q.2 • (q.1 : E) := by
  have hρ' : Topology.IsOpenEmbedding (codRestrict ρ (Ioi 0) fun y ↦ mem_Ioi.2 (hpos y)) := by
    refine ⟨hρ.isEmbedding.codRestrict _ _, ?_⟩
    rw [range_codRestrict]
    exact hρ.isOpen_range.preimage continuous_subtype_val
  exact (isOpen_lt continuous_const continuous_norm).isOpenEmbedding_subtypeVal.comp
    ((homeomorphUnitSphereProdOfNormPos E).symm.isOpenEmbedding.comp
      (Topology.IsOpenEmbedding.id.prodMap hρ'))

/-! ### Exponential polar coordinates -/

section Exponential

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Polar coordinates on the complement of the origin, with time `t` on the sphere of radius
`exp (t - 1)`: time `1` is the unit sphere, and the times `t ≤ 1` fill the punctured closed unit
ball. -/
noncomputable def polar (q : sphere (0 : V) 1 × ℝ) : V :=
  Real.exp (q.2 - 1) • (q.1 : V)

/-- The value of the exponential polar-coordinate map. -/
theorem polar_apply (q : sphere (0 : V) 1 × ℝ) :
    polar q = Real.exp (q.2 - 1) • (q.1 : V) :=
  (rfl)

/-- The radius in exponential polar coordinates. -/
@[simp]
theorem norm_polar (q : sphere (0 : V) 1 × ℝ) : ‖polar q‖ = Real.exp (q.2 - 1) := by
  rw [polar_apply, norm_smul, norm_eq_of_mem_sphere q.1, mul_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Exponential polar coordinates avoid the origin. -/
theorem polar_ne_zero (q : sphere (0 : V) 1 × ℝ) : polar q ≠ 0 := by
  rw [← norm_pos_iff, norm_polar]
  exact Real.exp_pos _

/-- Exponential polar coordinates embed the sphere times the real line openly. -/
theorem isOpenEmbedding_polar : IsOpenEmbedding (polar (V := V)) :=
  (Real.isOpenEmbedding_exp.comp (Homeomorph.subRight (1 : ℝ)).isOpenEmbedding).smul_coe_sphere
    fun _ => Real.exp_pos _

/-- Every nonzero vector has exponential polar coordinates. -/
theorem mem_range_polar {v : V} (hv : v ≠ 0) : v ∈ range (polar (V := V)) := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine ⟨(⟨‖v‖⁻¹ • v, by simp [norm_smul, hv'.ne']⟩, 1 + Real.log ‖v‖), ?_⟩
  simp [polar_apply, Real.exp_log hv', smul_smul, hv'.ne']

end Exponential

end TauCeti
