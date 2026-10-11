/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
-- Read the inherited global model-space charts in the coordinate calculation.
import all TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic

/-!
# Isometries of `SL₂ℝ~` over the identity of the hyperbolic plane

An isometry of the Sasaki model `SL₂ℝ~` fixing both hyperbolic-base coordinates is exactly a
constant translation of the fibre. Consequently two lifts of the same base map differ by a
unique fibre translation. This identifies the kernel needed to recover the full isometry group
from its action on the hyperbolic plane.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4, pp. 464–465 (the isometry group of `SL₂ℝ~`).
-/

public section

noncomputable section

open Manifold Real
open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)

private def coordinateMap (Φ : Isom J SL2Tilde) : P → P :=
  toProd ∘ Φ ∘ toProd.symm

private theorem differentiable_coordinateMap (Φ : Isom J SL2Tilde) :
    Differentiable ℝ (coordinateMap Φ) := by
  -- SL2Tilde has exactly the charts of P; its coordinate equivalence is the identity.
  exact Φ.toDiffeomorph.contMDiff.contDiff.differentiable (by simp)

-- This coordinate calculation follows the inherited-chart method of
-- TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Connection.
private theorem coordinate_derivative (Φ : Isom J SL2Tilde) (p u : P) :
    tangentSpaceCastModel J (Φ (toProd.symm p))
      (mfderiv J J Φ (toProd.symm p)
        ((tangentSpaceCastModel J (toProd.symm p)).symm u)) =
      fderiv ℝ (coordinateMap Φ) p u := by
  have h := DFunLike.congr_fun (mfderiv_eq_fderiv (𝕜 := ℝ) (f := coordinateMap Φ) (x := p)) u
  -- The inherited atlas makes both tangent identifications the identity on coordinates.
  convert h using 1 <;> rfl

private theorem metric_coordinateMap (Φ : Isom J SL2Tilde) (p u v : P) :
    exp (-2 * (coordinateMap Φ p).2.1) * (fderiv ℝ (coordinateMap Φ) p u).1 *
        (fderiv ℝ (coordinateMap Φ) p v).1 +
      (fderiv ℝ (coordinateMap Φ) p u).2.1 * (fderiv ℝ (coordinateMap Φ) p v).2.1 +
      ((fderiv ℝ (coordinateMap Φ) p u).2.2 +
          exp (-(coordinateMap Φ p).2.1) * (fderiv ℝ (coordinateMap Φ) p u).1) *
        ((fderiv ℝ (coordinateMap Φ) p v).2.2 +
          exp (-(coordinateMap Φ p).2.1) * (fderiv ℝ (coordinateMap Φ) p v).1) =
      exp (-2 * p.2.1) * u.1 * v.1 + u.2.1 * v.2.1 +
        (u.2.2 + exp (-p.2.1) * u.1) * (v.2.2 + exp (-p.2.1) * v.1) := by
  have h := Φ.inner_mfderiv (toProd.symm p)
    ((tangentSpaceCastModel J (toProd.symm p)).symm u)
    ((tangentSpaceCastModel J (toProd.symm p)).symm v)
  rw [inner_def, inner_def] at h
  -- The model-space atlas identifies the manifold derivative and the coordinate derivative.
  rw [coordinate_derivative, coordinate_derivative] at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply, y_toProd_symm,
    coordinateMap, Function.comp_apply, fst_snd_toProd] using h

private theorem coordinate_derivative_base (Φ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = p.x) (hy : ∀ p, (Φ p).y = p.y) (p u : P) :
    (fderiv ℝ (coordinateMap Φ) p u).1 = u.1 ∧
      (fderiv ℝ (coordinateMap Φ) p u).2.1 = u.2.1 := by
  have hdx := ((differentiable_coordinateMap Φ p).hasFDerivAt.fst)
  have hdy := ((differentiable_coordinateMap Φ p).hasFDerivAt.snd.fst)
  have hfx : (fun q => (coordinateMap Φ q).1) = fun q => q.1 :=
    funext fun q => hx (toProd.symm q)
  have hfy : (fun q => (coordinateMap Φ q).2.1) = fun q => q.2.1 :=
    funext fun q => hy (toProd.symm q)
  rw [hfx] at hdx
  rw [hfy] at hdy
  exact ⟨DFunLike.congr_fun (hdx.unique hasFDerivAt_fst) u,
    DFunLike.congr_fun
      (hdy.unique (hasFDerivAt_fst (𝕜 := ℝ) (p := p.2) |>.comp p hasFDerivAt_snd)) u⟩

private theorem coordinate_derivative_y (Φ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = p.x) (hy : ∀ p, (Φ p).y = p.y) (p : P) :
    (fderiv ℝ (coordinateMap Φ) p (0, 1, 0)).2.2 = 0 := by
  have h := metric_coordinateMap Φ p (0, 1, 0) (0, 1, 0)
  obtain ⟨h₁, h₂⟩ := coordinate_derivative_base Φ hx hy p (0, 1, 0)
  simp only [h₁, h₂, mul_zero, zero_add, mul_one, add_zero] at h
  nlinarith [sq_nonneg ((fderiv ℝ (coordinateMap Φ) p (0, 1, 0)).2.2)]

private theorem coordinateMap_z_independent_y (Φ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = p.x) (hy : ∀ p, (Φ p).y = p.y) (a b c : ℝ) :
    (coordinateMap Φ (a, b, c)).2.2 = (coordinateMap Φ (a, 0, c)).2.2 := by
  have hd (t : ℝ) : HasDerivAt (fun t => (coordinateMap Φ (a, t, c)).2.2) 0 t := by
    have h := ((differentiable_coordinateMap Φ (a, t, c)).hasFDerivAt.snd.snd).comp_hasDerivAt t
      ((hasDerivAt_const t a).prodMk ((hasDerivAt_id t).prodMk (hasDerivAt_const t c)))
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', coordinate_derivative_y Φ hx hy] using h
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) b 0

private theorem coordinate_derivative_x_independent_y (Φ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = p.x) (hy : ∀ p, (Φ p).y = p.y) (a b c : ℝ) :
    (fderiv ℝ (coordinateMap Φ) (a, b, c) (1, 0, 0)).2.2 =
      (fderiv ℝ (coordinateMap Φ) (a, 0, c) (1, 0, 0)).2.2 := by
  have hd (b t : ℝ) : HasDerivAt (fun t => (coordinateMap Φ (t, b, c)).2.2)
      (fderiv ℝ (coordinateMap Φ) (t, b, c) (1, 0, 0)).2.2 t := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd'] using
      ((differentiable_coordinateMap Φ (t, b, c)).hasFDerivAt.snd.snd).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk ((hasDerivAt_const t b).prodMk (hasDerivAt_const t c)))
  have heq : (fun t => (coordinateMap Φ (t, b, c)).2.2) =
      (fun t => (coordinateMap Φ (t, 0, c)).2.2) :=
    funext fun t => coordinateMap_z_independent_y Φ hx hy t b c
  exact ((heq ▸ hd b a).unique (hd 0 a))

private theorem coordinate_derivative_x (Φ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = p.x) (hy : ∀ p, (Φ p).y = p.y) (p : P) :
    (fderiv ℝ (coordinateMap Φ) p (1, 0, 0)).2.2 = 0 := by
  have hnorm (b : ℝ) := metric_coordinateMap Φ (p.1, b, p.2.2) (1, 0, 0) (1, 0, 0)
  have hbase (b : ℝ) := coordinate_derivative_base Φ hx hy (p.1, b, p.2.2) (1, 0, 0)
  have hheight (b : ℝ) : (coordinateMap Φ (p.1, b, p.2.2)).2.1 = b :=
    hy (toProd.symm (p.1, b, p.2.2))
  have hsq (b : ℝ) :
      (fderiv ℝ (coordinateMap Φ) (p.1, 0, p.2.2) (1, 0, 0)).2.2 ^ 2 +
        2 * exp (-b) * (fderiv ℝ (coordinateMap Φ) (p.1, 0, p.2.2) (1, 0, 0)).2.2 = 0 := by
    have h := hnorm b
    rw [hheight b, (hbase b).1, (hbase b).2,
      coordinate_derivative_x_independent_y Φ hx hy] at h
    dsimp only at h
    nlinarith
  have h₀ := hsq 0
  have h₂ := hsq (-log 2)
  simp only [neg_zero, exp_zero] at h₀
  simp only [neg_neg, exp_log (by norm_num : (0 : ℝ) < 2)] at h₂
  rcases p with ⟨a, b, c⟩
  rw [coordinate_derivative_x_independent_y Φ hx hy]
  linarith

private theorem coordinate_derivative_z (Φ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = p.x) (hy : ∀ p, (Φ p).y = p.y) (p : P) :
    (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2 = 1 := by
  have h := metric_coordinateMap Φ p (1, 0, 0) (0, 0, 1)
  have hy' : (coordinateMap Φ p).2.1 = p.2.1 := hy (toProd.symm p)
  rw [hy', (coordinate_derivative_base Φ hx hy p (1, 0, 0)).1,
    (coordinate_derivative_base Φ hx hy p (1, 0, 0)).2,
    (coordinate_derivative_base Φ hx hy p (0, 0, 1)).1,
    (coordinate_derivative_base Φ hx hy p (0, 0, 1)).2,
    coordinate_derivative_x Φ hx hy] at h
  simp only [mul_zero, zero_add, add_zero, mul_one] at h
  exact (mul_eq_left₀ (exp_ne_zero _)).mp h

private theorem coordinate_derivative_eq_id (Φ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = p.x) (hy : ∀ p, (Φ p).y = p.y) (p : P) :
    fderiv ℝ (coordinateMap Φ) p = ContinuousLinearMap.id ℝ P := by
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext (coordinate_derivative_base Φ hx hy p u).1
  apply Prod.ext (coordinate_derivative_base Φ hx hy p u).2
  have hu : u = u.1 • (1, 0, 0) + u.2.1 • (0, 1, 0) + u.2.2 • (0, 0, 1) := by
    ext <;> simp
  conv_lhs => rw [hu]
  simp only [map_add, map_smul, Prod.snd_add, Prod.smul_snd,
    coordinate_derivative_x Φ hx hy, coordinate_derivative_y Φ hx hy,
    coordinate_derivative_z Φ hx hy, smul_eq_mul, mul_zero, mul_one, zero_add]

/-- An isometry fixing both hyperbolic-base coordinates is the constant fibre translation
by its fibre coordinate at the origin. No orientation or fibre-preservation hypothesis is needed. -/
theorem eq_translate_of_base_eq (Φ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = p.x) (hy : ∀ p, (Φ p).y = p.y) :
    Φ = translate 0 0 (Φ (mk 0 0 0)).z := by
  let c := (Φ (mk 0 0 0)).z
  have hg : Differentiable ℝ (fun p : P => p + (0, 0, c)) := by fun_prop
  have hzero : coordinateMap Φ (0, 0, 0) = (0, 0, 0) + (0, 0, c) := by
    apply Prod.ext
    · simpa [coordinateMap, mk] using hx (mk 0 0 0)
    · apply Prod.ext
      · simpa [coordinateMap, mk] using hy (mk 0 0 0)
      · simp [coordinateMap, c, mk]
  have heq := eq_of_fderiv_eq (differentiable_coordinateMap Φ) hg (fun p => by
    simp only [coordinate_derivative_eq_id Φ hx hy,
      fderiv_add_const, fderiv_fun_id]) (0, 0, 0) hzero
  apply RiemannianIsometry.ext
  intro p
  apply SL2Tilde.ext
  · simp [hx]
  · simp [hy]
  · have h := congrArg (fun q : P => q.2.2) (congrFun heq (toProd p))
    simpa only [coordinateMap, Function.comp_apply, Equiv.symm_apply_apply,
      snd_snd_toProd, Prod.snd_add, c, z_translate] using h

/-- The isometries over the identity of the hyperbolic plane are exactly the fibre translations,
with a unique translation parameter. -/
theorem existsUnique_eq_translate_iff (Φ : Isom J SL2Tilde) :
    (∃! c : ℝ, Φ = translate 0 0 c) ↔
      (∀ p, (Φ p).x = p.x) ∧ (∀ p, (Φ p).y = p.y) := by
  constructor
  · rintro ⟨c, rfl, -⟩
    exact ⟨fun p => by simp, fun p => by simp⟩
  · rintro ⟨hx, hy⟩
    refine ⟨(Φ (mk 0 0 0)).z, eq_translate_of_base_eq Φ hx hy, ?_⟩
    intro c hc
    have h := hc.symm.trans (eq_translate_of_base_eq Φ hx hy)
    exact (translate_inj.mp h).2.2

/-- Two isometries inducing the same map on the hyperbolic base differ by a unique fibre
translation on the target. This is uniqueness of a lift, up to the kernel of the base action. -/
theorem existsUnique_translate_mul_of_base_eq (Φ Ψ : Isom J SL2Tilde)
    (hx : ∀ p, (Φ p).x = (Ψ p).x) (hy : ∀ p, (Φ p).y = (Ψ p).y) :
    ∃! c : ℝ, Φ = translate 0 0 c * Ψ := by
  obtain ⟨c, hc, hunique⟩ := (existsUnique_eq_translate_iff (Φ * Ψ⁻¹)).mpr
    ⟨fun p => by simpa only [RiemannianIsometry.mul_apply,
      RiemannianIsometry.inv_apply, RiemannianIsometry.apply_symm_apply] using hx (Ψ⁻¹ p),
     fun p => by simpa only [RiemannianIsometry.mul_apply,
      RiemannianIsometry.inv_apply, RiemannianIsometry.apply_symm_apply] using hy (Ψ⁻¹ p)⟩
  refine ⟨c, ?_, ?_⟩
  · exact (eq_mul_inv_iff_mul_eq.mp hc.symm).symm
  · intro d hd
    apply hunique d
    rw [hd, mul_inv_cancel_right]

end TauCeti.SL2Tilde
