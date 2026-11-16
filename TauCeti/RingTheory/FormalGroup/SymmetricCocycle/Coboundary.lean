/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
import TauCeti.RingTheory.FormalGroup.AddInv
import TauCeti.RingTheory.FormalGroup.Obstruction

/-!
# Symmetric 2-cocycles of a formal group law

Let `F` be a formal group law over a commutative ring `R`. A power series `Φ(X, Y)` is a
**symmetric 2-cocycle** of `F` (`FormalGroup.IsSymmetricCocycle`) if `Φ(Y, X) = Φ(X, Y)` and

  `Φ(X, Y) + Φ(F(X, Y), Z) = Φ(X, F(Y, Z)) + Φ(Y, Z)`.

These are the symmetric 2-cocycles of the formal group `F` with coefficients in the additive group
`R`, as in Lubin and Tate. The cocycle identity is that of Lazard's additive 2-cocycles
(`MvPolynomial.IsAddCocycle₂`), with the additive law `X + Y` replaced by `F` and polynomials by
power series. They are closed under sums and scalar multiples.

The **coboundary** of a power series `g` is its additivity defect `g(F(X, Y)) - g(X) - g(Y)`, the
homomorphism defect `FormalGroup.homDefect F 𝔾ₐ g` towards the additive law
(`FormalGroup.homDefect_𝔾ₐ`). For commutative `F` every coboundary is a symmetric 2-cocycle
(`FormalGroup.isSymmetricCocycle_homDefect_𝔾ₐ`), and the leading term of any symmetric 2-cocycle
without constant term is a multiple of the Lazard cocycle `C_n`
(`FormalGroup.IsSymmetricCocycle.exists_homogeneousComponent_eq_smul_lazardCocycle`).

Lubin and Tate describe the first-order deformations of `F` by symmetric 2-cocycles modulo
coboundaries. For a law of finite height in characteristic `p`, the degrees in which a symmetric
2-cocycle can fail to be a coboundary are determined in
`TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Height`.

## Main definitions

* `FormalGroup.IsSymmetricCocycle`: symmetric 2-cocycles of a formal group law.

## Main results

* `FormalGroup.IsSymmetricCocycle.add`, `FormalGroup.IsSymmetricCocycle.smul`, and their
  consequences: symmetric 2-cocycles are closed under sums and scalar multiples, and `-Φ` is a
  symmetric 2-cocycle exactly when `Φ` is (`FormalGroup.IsSymmetricCocycle.neg_iff`).
* `FormalGroup.isSymmetricCocycle_homDefect_𝔾ₐ`: coboundaries of a commutative formal group law are
  symmetric 2-cocycles.
* `FormalGroup.IsSymmetricCocycle.exists_homogeneousComponent_eq_smul_lazardCocycle`: the degree-`n`
  part of a symmetric 2-cocycle vanishing below degree `n ≠ 0` is a multiple of `C_n`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1.
* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-- A **symmetric 2-cocycle** of the formal group law `F`, with coefficients in the additive
group: a power series `Φ(X, Y)` with `Φ(Y, X) = Φ(X, Y)` and
`Φ(X, Y) + Φ(F(X, Y), Z) = Φ(X, F(Y, Z)) + Φ(Y, Z)`. -/
structure IsSymmetricCocycle (Φ : MvPowerSeries (Fin 2) R) : Prop where
  /-- Symmetry: `Φ(Y, X) = Φ(X, Y)`. -/
  subst_swap : Φ.subst ![X 1, X 0] = Φ
  /-- The 2-cocycle identity `Φ(X, Y) + Φ(F(X, Y), Z) = Φ(X, F(Y, Z)) + Φ(Y, Z)`. -/
  subst_add_subst_eq : Φ.subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1] +
      Φ.subst ![F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1], X 2] =
    Φ.subst ![X 0, F.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2]] +
      Φ.subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2]

namespace IsSymmetricCocycle

variable {F} {Φ Ψ : MvPowerSeries (Fin 2) R}

/-- Zero is a symmetric 2-cocycle. -/
@[simp]
theorem zero : F.IsSymmetricCocycle 0 := by
  have h0 {τ : Type} (a : Fin 2 → MvPowerSeries τ R) :
      (0 : MvPowerSeries (Fin 2) R).subst a = 0 := by
    rw [← MvPolynomial.coe_zero, subst_coe, map_zero]
  exact ⟨h0 _, by rw [h0, h0, h0, h0]⟩

/-- The sum of symmetric 2-cocycles is a symmetric 2-cocycle. -/
theorem add (hΦ : F.IsSymmetricCocycle Φ) (hΨ : F.IsSymmetricCocycle Ψ) :
    F.IsSymmetricCocycle (Φ + Ψ) where
  subst_swap := by
    rw [subst_add .X_X, hΦ.subst_swap, hΨ.subst_swap]
  subst_add_subst_eq := by
    rw [subst_add .X_X, subst_add (.cons_subst_zero_left 0 1 2 F.zero_constantCoeff),
      subst_add (.cons_subst_zero_right 0 1 2 F.zero_constantCoeff), subst_add .X_X]
    linear_combination hΦ.subst_add_subst_eq + hΨ.subst_add_subst_eq

/-- A scalar multiple of a symmetric 2-cocycle is a symmetric 2-cocycle. -/
theorem smul (hΦ : F.IsSymmetricCocycle Φ) (c : R) : F.IsSymmetricCocycle (c • Φ) where
  subst_swap := by
    rw [subst_smul .X_X, hΦ.subst_swap]
  subst_add_subst_eq := by
    rw [subst_smul .X_X, subst_smul (.cons_subst_zero_left 0 1 2 F.zero_constantCoeff),
      subst_smul (.cons_subst_zero_right 0 1 2 F.zero_constantCoeff), subst_smul .X_X,
      ← smul_add, ← smul_add,
      hΦ.subst_add_subst_eq]

/-- The negative of a symmetric 2-cocycle is a symmetric 2-cocycle. -/
theorem neg (hΦ : F.IsSymmetricCocycle Φ) : F.IsSymmetricCocycle (-Φ) := by
  simpa using hΦ.smul (-1)

/-- `-Φ` is a symmetric 2-cocycle exactly when `Φ` is. -/
@[simp]
theorem neg_iff : F.IsSymmetricCocycle (-Φ) ↔ F.IsSymmetricCocycle Φ :=
  ⟨fun h ↦ by simpa using h.neg, neg⟩

/-- The difference of symmetric 2-cocycles is a symmetric 2-cocycle. -/
theorem sub (hΦ : F.IsSymmetricCocycle Φ) (hΨ : F.IsSymmetricCocycle Ψ) :
    F.IsSymmetricCocycle (Φ - Ψ) := by
  simpa only [sub_eq_add_neg] using hΦ.add hΨ.neg

/-- **Leading terms of symmetric 2-cocycles.** If a symmetric 2-cocycle `Φ` vanishes below degree
`n ≠ 0`, its degree-`n` part is a multiple `c C_n` of the Lazard cocycle. -/
theorem exists_homogeneousComponent_eq_smul_lazardCocycle (hΦ : F.IsSymmetricCocycle Φ) {n : ℕ}
    (hn : n ≠ 0) (hΦn : n ≤ Φ.order) :
    ∃ c : R, homogeneousComponent n Φ = ↑(c • TauCeti.lazardCocycle n R) := by
  refine F.exists_homogeneousComponent_eq_smul_lazardCocycle hn hΦn hΦ.subst_swap ?_
  rw [hΦ.subst_add_subst_eq, add_sub_cancel_left, sub_self, order_zero]
  exact le_top

end IsSymmetricCocycle

/-- **Coboundaries are cocycles.** For a commutative formal group law `F`, the coboundary
`g(F(X, Y)) - g(X) - g(Y)` of any power series `g` is a symmetric 2-cocycle of `F`. -/
theorem isSymmetricCocycle_homDefect_𝔾ₐ [F.IsComm] (g : PowerSeries R) :
    F.IsSymmetricCocycle (F.homDefect 𝔾ₐ g) where
  subst_swap := by
    have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
    rw [subst_homDefect_𝔾ₐ F g (hX 1) (hX 0), F.comm' (hX 1) (hX 0), finTwo_X_eq_X, subst_self,
      homDefect_𝔾ₐ]
    simp only [id]
    ring
  subst_add_subst_eq := by
    have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
    rw [subst_homDefect_𝔾ₐ F g (hX 0) (hX 1),
      subst_homDefect_𝔾ₐ F g (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2),
      subst_homDefect_𝔾ₐ F g (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2)),
      subst_homDefect_𝔾ₐ F g (hX 1) (hX 2), F.assoc' (hX 0) (hX 1) (hX 2)]
    ring

end FormalGroup
