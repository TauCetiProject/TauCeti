/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.ShortWeierstrass
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# Algebraic independence of the universal Weierstrass invariants

The invariants `c₄` and `c₆` of the universal five-coefficient Weierstrass equation are
algebraically independent over `ℤ`. Thus the subalgebra they generate is a polynomial algebra
on two generators. This is the independence input for determining the relations among
`c₄`, `c₆` and the discriminant, whose known relation is `c₄³ - c₆² = 1728Δ`.

The argument specializes the universal equation to the short equation with prescribed
invariants over the rational function field `ℚ(C₄, C₆)`. It uses the existing
`WeierstrassCurve.ofCInvariants` and its invariant formulas; no integrality assertion about
that short equation is needed. The resulting independence is integral, even though its
specialization is rational.
-/

public section

noncomputable section

namespace WeierstrassCurve.Universal

open MvPolynomial

/-- The two `c`-invariants of the universal Weierstrass equation satisfy no nonzero polynomial
relation with integer coefficients. In particular, the relation involving the discriminant
does not impose a relation on `c₄` and `c₆` alone. -/
theorem algebraicIndependent_c₄_c₆ :
    AlgebraicIndependent ℤ ![curve.c₄, curve.c₆] := by
  let K := FractionRing (MvPolynomial (Fin 2) ℚ)
  let x : Fin 2 → K := fun i ↦ algebraMap (MvPolynomial (Fin 2) ℚ) K (X i)
  let : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  let : Invertible (3 : K) := invertibleOfNonzero (by norm_num)
  have hxQ : AlgebraicIndependent ℚ x :=
    (algebraicIndependent_X (Fin 2) ℚ).map'
      (f := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 2) ℚ) K)
      (IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) K)
  let W := ofCInvariants (x 0) (x 1)
  have h₄ : W.specialize curve.c₄ = x 0 := by
    simpa only [map_c₄, W, ofCInvariants_c₄] using
      congrArg WeierstrassCurve.c₄ (map_specialize W)
  have h₆ : W.specialize curve.c₆ = x 1 := by
    simpa only [map_c₆, W, ofCInvariants_c₆] using
      congrArg WeierstrassCurve.c₆ (map_specialize W)
  have h : W.specialize ∘ ![curve.c₄, curve.c₆] = x := by
    funext i
    fin_cases i <;> simp [h₄, h₆]
  have hW : AlgebraicIndependent ℚ (W.specialize ∘ ![curve.c₄, curve.c₆]) := h ▸ hxQ
  exact hW.of_ringHom_of_comp_eq (Int.castRingHom ℚ) W.specialize
    Int.cast_injective (RingHom.ext_int _ _)

end WeierstrassCurve.Universal
