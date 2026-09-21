/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree

/-!
# Factoring multiplication through an isogeny whose kernel counts its degree

The kernel form of the factorisation theorem
`TauCeti.Isogeny.existsUnique_comp_eq_iff_ker_le` applies to `[n]` with `n = deg φ`: every point
of `ker φ` is killed by the order of `ker φ`, which is `n`, so `[n]` factors through `φ`, uniquely.
The factor
`χ : W₂ → W₁` with `χ ∘ φ = [deg φ]` is the dual of `φ` (Silverman III.6.1), and its degree is
`deg φ`, by the tower formula and `deg [n] = n²`.

## Main results

* `TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree`: when `#ker φ = deg φ`,
  there is a unique `χ` with `χ ∘ φ = [deg φ]`.
* `TauCeti.Isogeny.degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree`: any such `χ` has degree
  `deg φ`.

## Provenance

Not ported. The factorisation of `[deg φ]` and the degree of its factor are the opening
construction of the dual isogeny in Silverman III.6.1.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.11 and III.6.1.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic]

/-- **`[deg φ]` factors through `φ` when the kernel of `φ` has `deg φ` points.** The factor
`χ : W₂ → W₁` with `χ ∘ φ = [deg φ]` is unique; it is the dual isogeny of `φ` (Silverman III.6.1).
The kernel of `φ` is a group of order `deg φ`, so `[deg φ]` kills it, and the kernel form of the
factorisation theorem applies. -/
theorem existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree {φ : Isogeny W₁ W₂}
    (hφ : Nat.card φ.ker = φ.degree) :
    ∃! χ : Isogeny W₂ W₁,
      χ.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_pos.ne') := by
  refine (existsUnique_comp_eq_iff_ker_le hφ _).2 fun P hP ↦ ?_
  rw [mem_ker_mulByIntIsogenyOfNeZero_iff, natCast_zsmul, ← hφ]
  exact congrArg Subtype.val (card_nsmul_eq_zero' (G := φ.ker) (x := ⟨P, hP⟩))

omit [DecidableEq F] in
/-- **A factor of `[deg φ]` through `φ` has the degree of `φ`**: `deg χ · deg φ = deg [deg φ]`,
which is `(deg φ)²`. No hypothesis on the kernel of `φ` is needed. -/
theorem degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree {φ : Isogeny W₁ W₂}
    {χ : Isogeny W₂ W₁} {hn : (φ.degree : ℤ) ≠ 0}
    (h : χ.comp φ = mulByIntIsogenyOfNeZero W₁ hn) : χ.degree = φ.degree := by
  have hdeg := congrArg degree h
  rw [degree_comp, degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast, sq] at hdeg
  exact Nat.eq_of_mul_eq_mul_right φ.degree_pos hdeg

end TauCeti.Isogeny

end
