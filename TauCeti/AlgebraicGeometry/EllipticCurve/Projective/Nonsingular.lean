/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Nonsingularity of projective points on an elliptic curve

Over a field, every nonzero point representative `[X : Y : Z]` satisfying the projective
Weierstrass equation of an elliptic curve is nonsingular. This is the projective counterpart of
Mathlib's `WeierstrassCurve.Affine.equation_iff_nonsingular`. The hypothesis that the
representative is nonzero is necessary: `(0, 0, 0)` satisfies the homogeneous equation but all
three partial derivatives vanish there. Conversely, over any commutative ring, a nonsingular point
representative is nonzero.

Over a local ring `R`, nonsingularity is detected by the residue field: if a solution reduces to a
nonsingular point of the reduced curve, then one of its three partial derivatives is a unit of `R`,
and its image under every ring homomorphism to a nontrivial ring is again nonsingular.

## Main results

* `WeierstrassCurve.Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero`: over a field,
  if the discriminant is nonzero, a nonzero point representative satisfies the equation if and
  only if it is nonsingular.
* `WeierstrassCurve.Projective.equation_iff_nonsingular_of_ne_zero`: on an elliptic curve over a
  field, a nonzero point representative satisfies the equation if and only if it is nonsingular.
* `WeierstrassCurve.Projective.ne_zero_of_nonsingular`: over any commutative ring, a nonsingular
  point representative is nonzero.
* `WeierstrassCurve.Projective.nonsingular_map_of_nonsingular_map_residue`: over a local ring, a
  solution with nonsingular reduction has nonsingular image under every ring homomorphism to a
  nontrivial ring.
-/

public section

namespace WeierstrassCurve.Projective

variable {F : Type*} [Field F] {W : Projective F}

/-- Over a field, if the discriminant is nonzero, then a nonzero point representative satisfies
the projective Weierstrass equation if and only if it is nonsingular. If `Z ≠ 0`, this is the
affine statement; if `Z = 0`, the equation forces `X = 0`, and then `Y ≠ 0` makes `W_Z = Y²`
nonzero. -/
theorem equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero (hΔ : W.Δ ≠ 0) {P : Fin 3 → F}
    (hP : P ≠ 0) : W.Equation P ↔ W.Nonsingular P := by
  refine ⟨fun h ↦ ?_, And.left⟩
  by_cases hz : P 2 = 0
  · have hx : P 0 = 0 := X_eq_zero_of_Z_eq_zero h hz
    have hy : P 1 ≠ 0 := fun hy ↦ hP (funext fun k ↦ by fin_cases k <;> assumption)
    rw [nonsingular_of_Z_eq_zero hz]
    exact ⟨h, Or.inr (by simpa [hx] using hy)⟩
  · rw [nonsingular_of_Z_ne_zero hz, ← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ,
      ← equation_of_Z_ne_zero hz]
    exact h

/-- On an elliptic curve over a field, a nonzero point representative satisfies the projective
Weierstrass equation if and only if it is nonsingular. -/
theorem equation_iff_nonsingular_of_ne_zero [W.IsElliptic] {P : Fin 3 → F} (hP : P ≠ 0) :
    W.Equation P ↔ W.Nonsingular P :=
  equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero (W.coe_Δ' ▸ W.Δ'.ne_zero) hP

/-- Over any commutative ring, a nonsingular point representative is nonzero. -/
theorem ne_zero_of_nonsingular {R : Type*} [CommRing R] {W' : Projective R} {P : Fin 3 → R}
    (hP : W'.Nonsingular P) : P ≠ 0 :=
  fun h ↦ by simp [h, nonsingular_iff] at hP

section LocalRing

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {W' : Projective R}

/-- **Nonsingularity spreads out from the residue field.** Over a local ring `R`, a solution `P` of
the projective Weierstrass equation whose reduction is a nonsingular point of the reduced curve has
nonsingular image under every ring homomorphism `f : R →+* S` to a nontrivial ring: a partial
derivative not vanishing at the reduction of `P` is a unit of `R`. -/
theorem nonsingular_map_of_nonsingular_map_residue {P : Fin 3 → R} (hP : W'.Equation P)
    (h : (W'.map (residue R)).Nonsingular (residue R ∘ P)) {S : Type*} [CommRing S]
    [Nontrivial S] (f : R →+* S) : (W'.map f).Nonsingular (f ∘ P) := by
  -- a polynomial whose value at `P` is nonzero modulo the maximal ideal has a unit value at `P`
  have key (p : MvPolynomial (Fin 3) R)
      (hp : MvPolynomial.eval (residue R ∘ P) (p.map (residue R)) ≠ 0) :
      MvPolynomial.eval (f ∘ P) (p.map f) ≠ 0 := by
    rw [MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp] at hp ⊢
    exact (((residue_ne_zero_iff_isUnit _).mp hp).map f).ne_zero
  refine ⟨hP.map f, ?_⟩
  have h := h.right
  simp only [map_polynomialX, map_polynomialY, map_polynomialZ] at h ⊢
  exact h.imp (key _) (Or.imp (key _) (key _))

end LocalRing

end WeierstrassCurve.Projective
