/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Basic
public import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan

/-!
# The diagonal Cartan subalgebra of the symplectic Lie algebra

The diagonal matrices in the symplectic Lie algebra `𝔰𝔭(2n, R)` = `LieAlgebra.Symplectic.sp l R`
are the matrices `diag(D, -D)`. They form an abelian Lie subalgebra `𝔞`
(`LieAlgebra.Symplectic.diagonalSubalgebra`), the diagonal Cartan subalgebra of `gl` pulled back
along the inclusion. For `H ∈ 𝔞` the bracket `[H, X]` has `(a, b)` entry `(H a a - H b b) X a b`,
and over a field of characteristic other than two the elements
`H_i = E_(i, i) - E_(n + i, n + i)` of `𝔞` separate the indices of `l ⊕ l`. Hence `𝔞` is
self-normalizing, and so a Cartan subalgebra of `𝔰𝔭(2n, K)`.

## Main results

* `LieAlgebra.Symplectic.diagonalSubalgebra`: the diagonal matrices in `sp l R`.
* `LieAlgebra.Symplectic.lie_apply_of_mem_diagonalSubalgebra`: the entries of `[H, X]`.
* `LieAlgebra.Symplectic.diagonalSubalgebraElement`: the elements `H_i` of `𝔞`.
* `LieAlgebra.Symplectic.diagonalSubalgebra_normalizer_eq_self`: `𝔞` is self-normalizing.
* `LieAlgebra.Symplectic.instIsCartanSubalgebraDiagonalSubalgebra`: `𝔞` is a Cartan subalgebra.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebra.Symplectic

variable {l : Type*} [Fintype l] [DecidableEq l]

section CommRing

variable (l) (R : Type*) [CommRing R]

/-- The diagonal matrices in the symplectic Lie algebra `sp l R`, that is, the matrices
`diag(D, -D)`: the diagonal matrices of `gl` (`TauCeti.diagonalCartan`) pulled back along the
inclusion. They form an abelian Lie subalgebra. -/
def diagonalSubalgebra : LieSubalgebra R (sp l R) :=
  (TauCeti.diagonalCartan R (l ⊕ l)).comap (sp l R).incl

variable {l R}

/-- Membership in `LieAlgebra.Symplectic.diagonalSubalgebra`. -/
@[simp]
theorem mem_diagonalSubalgebra {X : sp l R} :
    X ∈ diagonalSubalgebra l R ↔ (X : Matrix (l ⊕ l) (l ⊕ l) R).IsDiag :=
  TauCeti.mem_diagonalCartan_iff_isDiag

/-- Diagonal symplectic Lie matrices commute. -/
theorem lie_eq_zero_of_mem_diagonalSubalgebra {X Y : sp l R} (hX : X ∈ diagonalSubalgebra l R)
    (hY : Y ∈ diagonalSubalgebra l R) : ⁅X, Y⁆ = 0 :=
  Subtype.ext <| by
    rw [LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero]
    exact TauCeti.lie_eq_zero_of_isDiag (mem_diagonalSubalgebra.mp hX)
      (mem_diagonalSubalgebra.mp hY)

instance : IsLieAbelian (diagonalSubalgebra l R) where
  trivial X Y := Subtype.ext (lie_eq_zero_of_mem_diagonalSubalgebra X.property Y.property)

/-- The entries of `[H, X]` for a diagonal `H`: `[H, X] a b = (H a a - H b b) X a b`. -/
theorem lie_apply_of_mem_diagonalSubalgebra {H : sp l R} (hH : H ∈ diagonalSubalgebra l R)
    (X : sp l R) (a b : l ⊕ l) :
    (⁅H, X⁆ : sp l R).val a b =
      ((H : Matrix (l ⊕ l) (l ⊕ l) R) a a - (H : Matrix (l ⊕ l) (l ⊕ l) R) b b) *
        (X : Matrix (l ⊕ l) (l ⊕ l) R) a b := by
  rw [LieSubalgebra.coe_bracket]
  exact TauCeti.lie_apply_of_mem_diagonalCartan
    (TauCeti.mem_diagonalCartan_iff_isDiag.mpr (mem_diagonalSubalgebra.mp hH)) _ a b

/-- The element `H_i = E_(i, i) - E_(n + i, n + i)` of `𝔞`. -/
def diagonalSubalgebraElement (i : l) : diagonalSubalgebra l R :=
  ⟨⟨single (.inl i) (.inl i) 1 - single (.inr i) (.inr i) 1,
    single_inl_inl_sub_single_inr_inr_mem_sp i i⟩, by
      simp only [mem_diagonalSubalgebra]
      intro a b hab
      simp only [Matrix.sub_apply, single_apply]
      grind⟩

/-- The matrix of `H_i = E_(i, i) - E_(n + i, n + i)`. -/
@[simp]
theorem coe_diagonalSubalgebraElement (i : l) :
    ((diagonalSubalgebraElement (R := R) i : sp l R) : Matrix (l ⊕ l) (l ⊕ l) R) =
      single (.inl i) (.inl i) 1 - single (.inr i) (.inr i) 1 :=
  (rfl)

/-- The diagonal entries of `H_i = E_(i, i) - E_(n + i, n + i)`. -/
theorem diagonalSubalgebraElement_apply (i : l) (a : l ⊕ l) :
    (((diagonalSubalgebraElement (R := R) i : sp l R) : Matrix (l ⊕ l) (l ⊕ l) R) a a) =
      (if a = .inl i then 1 else 0) - if a = .inr i then 1 else 0 := by
  simp [diagonalSubalgebraElement, Matrix.sub_apply, single_apply, eq_comm]

end CommRing

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The elements `H_i = E_(i, i) - E_(n + i, n + i)` of `𝔞` separate the indices of `l ⊕ l`:
for `a ≠ b` some `H_i` has different diagonal entries at `a` and `b`. -/
theorem exists_diagonalSubalgebraElement_apply_ne {a b : l ⊕ l} (hab : a ≠ b) :
    ∃ i : l, ((diagonalSubalgebraElement (R := K) i : sp l K) : Matrix (l ⊕ l) (l ⊕ l) K) a a ≠
      ((diagonalSubalgebraElement (R := K) i : sp l K) : Matrix (l ⊕ l) (l ⊕ l) K) b b := by
  have h2 : (1 : K) ≠ -1 := fun h ↦ two_ne_zero (α := K) (by linear_combination h)
  rcases a with i | i
  · refine ⟨i, ?_⟩
    rcases b with j | j
    · simp_all [diagonalSubalgebraElement_apply, eq_comm]
    · by_cases hij : j = i
      · subst hij; simpa [diagonalSubalgebraElement_apply] using h2
      · simp [diagonalSubalgebraElement_apply, hij]
  · refine ⟨i, ?_⟩
    rcases b with j | j
    · by_cases hij : j = i
      · subst hij; simpa [diagonalSubalgebraElement_apply] using h2.symm
      · simp [diagonalSubalgebraElement_apply, hij]
    · simp_all [diagonalSubalgebraElement_apply, eq_comm]

variable (l K)

/-- **The diagonal matrices are self-normalizing in `𝔰𝔭(2n, K)`**, over any field of
characteristic other than two: if `[H_i, X]` is diagonal for every `H_i`, then `X` is diagonal. -/
@[simp]
theorem diagonalSubalgebra_normalizer_eq_self :
    (diagonalSubalgebra l K).normalizer = diagonalSubalgebra l K := by
  refine le_antisymm (fun X hX ↦ ?_) (diagonalSubalgebra l K).le_normalizer
  rw [mem_diagonalSubalgebra]
  intro a b hab
  obtain ⟨i, hi⟩ := exists_diagonalSubalgebraElement_apply_ne (K := K) hab
  have h : (⁅_, X⁆ : sp l K).val a b = 0 := mem_diagonalSubalgebra.mp
    (((diagonalSubalgebra l K).mem_normalizer_iff' X).mp hX _
      (diagonalSubalgebraElement i).property) hab
  rw [lie_apply_of_mem_diagonalSubalgebra (diagonalSubalgebraElement i).property] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hi)

/-- The diagonal matrices form a Cartan subalgebra of `𝔰𝔭(2n, K)`: they are abelian and
self-normalizing. -/
instance instIsCartanSubalgebraDiagonalSubalgebra :
    (diagonalSubalgebra l K).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := diagonalSubalgebra_normalizer_eq_self l K

end Field

end LieAlgebra.Symplectic
