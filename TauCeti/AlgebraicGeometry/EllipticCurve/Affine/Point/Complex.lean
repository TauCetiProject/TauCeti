/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Real points inside complex points

A complex point of a real Weierstrass curve descends to a real point precisely when complex
conjugation fixes it. In particular, the sum of a point and its conjugate descends. This is the
point-level norm argument used to control cokernels of isogenies on real points.
-/

public section

namespace WeierstrassCurve.Affine.Point

variable {W : WeierstrassCurve ℝ}

/-- A complex point of a real Weierstrass curve comes from a real point exactly when it is fixed
by complex conjugation. No nonsingularity hypothesis on the curve is needed. -/
theorem exists_map_eq_iff_map_conj_eq_self (P : (W⁄ℂ).toAffine.Point) :
    (∃ Q : W.toAffine.Point, map (W' := W) (Algebra.ofId ℝ ℂ) Q = P) ↔
      map Complex.conjAe.toAlgHom P = P := by
  refine (exists_map_eq_iff (W := W) P (Algebra.ofId ℝ ℂ)).trans ?_
  rw [map_eq_self_iff]
  have h (z : ℂ) : z ∈ Set.range (Algebra.ofId ℝ ℂ) ↔ starRingEnd ℂ z = z := by
    exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ Complex.conj_ofReal r,
      fun hz ↦ ⟨z.re, Complex.conj_eq_iff_re.mp hz⟩⟩
  exact and_congr (h _) (h _)

/-- The sum of a complex point and its conjugate descends to a real point. -/
theorem exists_map_eq_add_conj (P : (W⁄ℂ).toAffine.Point) :
    ∃ Q : W.toAffine.Point,
      map (W' := W) (Algebra.ofId ℝ ℂ) Q = P + map Complex.conjAe.toAlgHom P := by
  apply (exists_map_eq_iff_map_conj_eq_self _).mpr
  rw [map_add, map_map]
  have h : Complex.conjAe.toAlgHom.comp Complex.conjAe.toAlgHom = AlgHom.id ℝ ℂ := by
    exact AlgHom.ext fun z ↦ Complex.conj_conj z
  rw [h]
  have hid : map (AlgHom.id ℝ ℂ) P = P := by
    cases P <;> rfl
  rw [hid, add_comm]

end WeierstrassCurve.Affine.Point
