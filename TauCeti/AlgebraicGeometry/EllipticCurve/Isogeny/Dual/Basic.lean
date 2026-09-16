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
# Factoring through an isogeny whose kernel counts its degree

The factorisation theorem `TauCeti.Isogeny.existsUnique_comp_eq_iff_fieldRange_le` decides whether
an isogeny `ψ : W₁ → W₃` factors through `φ : W₁ → W₂` by comparing pulled-back function fields.
Classically (Silverman III.4.11) the test is on kernels instead, `ker φ ⊆ ker ψ`, and that form is
correct exactly when the kernel of `φ` cuts out its pulled-back field: when `F(W₁)` is Galois over
`φ^*F(W₂)` with the translations by `ker φ` as its automorphisms. In this development `Isogeny.ker`
consists of base-field points, and that condition is `#ker φ = deg φ`
(`TauCeti.Isogeny.card_ker_eq_degree_iff`). Over a separably closed field it is the condition a
separable isogeny is expected to satisfy.

Under that hypothesis the kernel test applies to `[n]` with `n = deg φ`: every point of `ker φ` is
killed by the order of `ker φ`, which is `n`, so `[n]` factors through `φ`, uniquely. The factor
`χ : W₂ → W₁` with `χ ∘ φ = [deg φ]` is the dual of `φ` (Silverman III.6.1), and its degree is
`deg φ`, by the tower formula and `deg [n] = n²`.

The hypothesis is not a formality. Over `ℚ`, on a curve with no rational `2`-torsion, `[2]` has
trivial rational kernel but degree `4`, and the identity, whose kernel contains that of `[2]`,
does not factor through `[2]`. Frobenius has trivial kernel and degree `q`.

## Main results

* `TauCeti.Isogeny.existsUnique_comp_eq_iff_ker_le`: when `#ker φ = deg φ`, `ψ` factors through
  `φ` by a unique isogeny exactly when `ker φ ≤ ker ψ`.
* `TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree`: when `#ker φ = deg φ`,
  there is a unique `χ` with `χ ∘ φ = [deg φ]`.
* `TauCeti.Isogeny.degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree`: any such `χ` has degree
  `deg φ`.

## Provenance

Not ported. The kernel form of the factorisation theorem is Silverman III.4.11. There the
isogenies are separable, the base field is algebraically closed, and the proof uses Galois theory
of the function-field extension. Here that Galois theory is the translation-action
correspondence of `Affine/FunctionField/Translation/FixedField.lean`, and the pointedness of the
factor comes from the subfield form of the theorem.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.11 and III.6.1.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic]

/-- **The kernel form of the factorisation theorem** (Silverman III.4.11). When the kernel of
`φ : W₁ → W₂` has `deg φ` points, an isogeny `ψ : W₁ → W₃` factors through `φ`, by a unique
isogeny, exactly when `ker φ ≤ ker ψ`.

Without the hypothesis only the forward implication holds (`TauCeti.Isogeny.ker_le_ker_comp`).
The subfield criterion `TauCeti.Isogeny.existsUnique_comp_eq_iff_fieldRange_le` needs no
hypothesis. -/
theorem existsUnique_comp_eq_iff_ker_le {φ : Isogeny W₁ W₂} (hφ : Nat.card φ.ker = φ.degree)
    (ψ : Isogeny W₁ W₃) : (∃! χ : Isogeny W₂ W₃, χ.comp φ = ψ) ↔ φ.ker ≤ ψ.ker := by
  rw [existsUnique_comp_eq_iff_fieldRange_le]
  refine ⟨fun h ↦ by rw [ker_def, ker_def]; exact translationFixingSubgroup_antitone W₁ h,
    fun h ↦ ?_⟩
  -- `ψ^*F(W₃)` is fixed by `ker ψ`, hence by `ker φ`, and `hφ` says that `ker φ` fixes nothing
  -- beyond `φ^*F(W₂)`.
  calc ψ.fieldPullback.fieldRange ≤ translationFixedField W₁ ψ.ker :=
        by rw [ker_def]; exact le_translationFixedField_translationFixingSubgroup W₁ _
    _ ≤ translationFixedField W₁ φ.ker := translationFixedField_antitone W₁ h
    _ ≤ φ.fieldPullback.fieldRange := (card_ker_eq_degree_iff φ).1 hφ

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
