/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.ComputeDegree

/-!
# Hensel's lemma for Weierstrass equations

Let `R` be a Henselian local ring with residue field `k`, and let `W` be a Weierstrass curve over
`R`. Every nonsingular point of the reduced curve `W_k = W ⊗ k` is the residue of a nonsingular
point of `W`. This is Hensel's lemma applied to the Weierstrass equation in whichever variable has
a nonvanishing partial derivative at the point of `W_k`.

## Main results

* `WeierstrassCurve.Affine.exists_nonsingular_residue_eq`: over a Henselian local ring, every
  nonsingular point of the reduced curve is the residue of a nonsingular point.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.1.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [HenselianLocalRing R] {W : Affine R}

/-- **Nonsingular points lift along a Henselian local ring.** Over a Henselian local ring `R`, every
nonsingular point of the reduction of a Weierstrass curve `W` to the residue field is the residue
of a nonsingular point of `W`. -/
theorem exists_nonsingular_residue_eq {x₀ y₀ : R}
    (h : (W.map (residue R)).Nonsingular (residue R x₀) (residue R y₀)) :
    ∃ x y : R, W.Nonsingular x y ∧ residue R x = residue R x₀ ∧ residue R y = residue R y₀ := by
  -- a solution over `R` whose residues are `(res x₀, res y₀)` is nonsingular over `R`, since one
  -- of its partial derivatives has nonzero residue
  have hns {x y : R} (he : W.Equation x y) (hx : residue R x = residue R x₀)
      (hy : residue R y = residue R y₀) : W.Nonsingular x y := by
    rw [← hx, ← hy] at h
    simp only [Nonsingular, map_polynomialX, map_polynomialY, map_mapRingHom_evalEval] at h
    exact ⟨he, h.2.imp (fun hr h0 ↦ hr (by rw [h0, map_zero]))
      (fun hr h0 ↦ hr (by rw [h0, map_zero]))⟩
  rw [nonsingular_iff'] at h
  obtain ⟨he, hX | hY⟩ := h
  · -- lift the `x`-coordinate as a simple root of the monic cubic `W(X, y₀)`, up to sign
    rw [equation_iff'] at he
    set g : R[X] := X ^ 3 + C W.a₂ * X ^ 2 + C (W.a₄ - W.a₁ * y₀) * X +
      C (W.a₆ - y₀ ^ 2 - W.a₃ * y₀) with hg
    have hgm : g.Monic := by rw [hg]; monicity!
    obtain ⟨x, hx, hxx₀⟩ := HenselianLocalRing.is_henselian g hgm x₀
      (by
        rw [← residue_eq_zero_iff, ← neg_eq_zero, ← he]
        simp [hg]
        ring)
      (by
        rw [← residue_ne_zero_iff_isUnit, ← neg_ne_zero]
        convert hX using 1
        simp [hg, derivative_pow, map_ofNat]
        ring)
    have hres : residue R x = residue R x₀ := by
      rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine ⟨x, y₀, hns ?_ hres rfl, hres, rfl⟩
    rw [equation_iff', ← neg_eq_zero, ← hx.eq_zero]
    simp [hg]
    ring
  · -- lift the `y`-coordinate as a simple root of the monic quadratic `W(x₀, Y)`
    rw [equation_iff'] at he
    set f : R[X] := X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X -
      C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hf
    have hfm : f.Monic := by rw [hf]; monicity!
    obtain ⟨y, hy, hyy₀⟩ := HenselianLocalRing.is_henselian f hfm y₀
      (by
        rw [← residue_eq_zero_iff, ← he]
        simp [hf]
        ring)
      (by
        rw [← residue_ne_zero_iff_isUnit]
        convert hY using 1
        simp [hf, derivative_pow, map_ofNat]
        ring)
    have hres : residue R y = residue R y₀ := by
      rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine ⟨x₀, y, hns ?_ rfl hres, rfl, hres⟩
    rw [equation_iff', ← hy.eq_zero]
    simp [hf]
    ring

end WeierstrassCurve.Affine

end
