/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Subgroup.index`, `Subgroup.relIndex` and `Subgroup.normalizer` occur in the statements below,
-- and this module re-exports the `GL` notation.
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `QuadraticAlgebra.periodMatrixGroup`, the nonsplit Cartan subgroup, occurs in the statements
-- below.
public import TauCeti.Algebra.QuadraticAlgebra.UnitMatrix
-- `TauCeti.index_eq_of_natCard_eq_mul`: an index from the orders of a subgroup and its group.
import TauCeti.GroupTheory.Index.Basic
-- `TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul`: the order of `GL₂` over a finite field.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- `TauCeti.FiniteField.ne_zero_or_two_ne_zero_of_forall_sq_ne`: over a finite field an
-- irreducible quadratic is separable.
import TauCeti.FieldTheory.Finite.Card
-- `TauCeti.sq_add_mul_mul_sub_mul_sq_eq_zero_iff`: the norm form of `F[ω]` has no nontrivial zero.
import TauCeti.Algebra.QuadraticAlgebra.Basic

/-!
# The nonsplit Cartan subgroup of `GL₂` and its normalizer

Let `R` be a commutative ring and `a b : R`. Multiplication by `x + y ω` on
`QuadraticAlgebra R a b = R[ω] / (ω² - b ω - a)`, in row coordinates ordered as `(ω, 1)`, is the
matrix `!![x + b y, a y; y, x]`, and the invertible matrices of this shape form the subgroup
`QuadraticAlgebra.periodMatrixGroup a b` of `GL₂(R)`, the image of the unit group. When `R = F` is a
field and `X² - b X - a` has no root in `F`, the algebra is a field of degree `2` over `F` and this
subgroup is a **nonsplit Cartan subgroup** `C_ns` of `GL₂(F)`. Its normalizer is
`TauCeti.GL2NonSplitCartanNormalizer a b`, written `C_ns⁺`.

For an odd prime `ℓ` and a nonsquare `ε ∈ 𝔽_ℓ` the choice `a = ε`, `b = 0` gives the standard
`C_ns(ℓ) = {!![x, ε y; y, x]}`; over `𝔽₂` the choice `a = b = 1` gives the cyclic subgroup of
order `3` of `GL₂(𝔽₂)`. These are the levels of the modular curves `X_ns(ℓ)` and `X_ns⁺(ℓ)`.

Over a field `F` in which `X² - b X - a` has no root, `C_ns` is the unit group of a field with
`#F ^ 2` elements, so over a finite field with `q` elements it has `q² - 1` elements and index
`q (q - 1)`. When this irreducible quadratic is moreover separable, that is `b ≠ 0` or `2 ≠ 0`,
the Cartan subgroup has index `2` in its normalizer: an element `g` of the normalizer sends `ω` to
a root of `X² - b X - a` in `F[ω]`, which is `ω` or its conjugate `b - ω`. In the first case `g`
commutes with `ω` and lies in the Cartan subgroup
(`QuadraticAlgebra.mem_periodMatrixGroup_iff_commute`); in the second, so does `σ g`, where
`σ = !![1, -b; 0, -1]` is the matrix of the conjugation `ω ↦ b - ω`. Over a finite field an
irreducible quadratic is automatically separable.

`TauCeti.GL2NonSplitTorus F E` is the same construction for an abstract quadratic extension `E/F`
with a chosen basis, hence conjugate to this subgroup when `E ≅ F[ω]`; the explicit entries here
are those of the standard level `C_ns(ℓ)`, and they also make sense over `ℤ / N`.

## Main definitions

* `TauCeti.GL2NonSplitCartanNormalizer a b`: the normalizer of
  `QuadraticAlgebra.periodMatrixGroup a b`.

## Main results

* `QuadraticAlgebra.card_periodMatrixGroup_of_forall_sq_ne`,
  `QuadraticAlgebra.index_periodMatrixGroup_of_forall_sq_ne`: `|C_ns| = q² - 1` and
  `[GL₂(𝔽_q) : C_ns] = q (q - 1)` when `X² - b X - a` has no root in `𝔽_q`.
* `TauCeti.relIndex_periodMatrixGroup_GL2NonSplitCartanNormalizer`: `[C_ns⁺ : C_ns] = 2` when
  `X² - b X - a` is irreducible and separable.
* `TauCeti.GL2NonSplitCartanNormalizer.natCard`,
  `TauCeti.GL2NonSplitCartanNormalizer.two_mul_index`: `|C_ns⁺| = 2 (q² - 1)` and
  `2 [GL₂(𝔽_q) : C_ns⁺] = q (q - 1)` when `X² - b X - a` has no root in `𝔽_q`.

## References

* D. Zywina, *On the possible images of the mod `ℓ` representations associated to elliptic curves
  over `ℚ`*, arXiv:1508.07660, §1 (Notation) and §3.2.
-/

public section

open Matrix

namespace QuadraticAlgebra

variable {F : Type*} [Field F] {a b : F}

/-- **`|C_ns| = q² - 1`** over a field with `q` elements in which `X² - b X - a` has no root: the
nonsplit Cartan subgroup is the unit group of the field `QuadraticAlgebra F a b`. -/
theorem card_periodMatrixGroup_of_forall_sq_ne (hirr : ∀ r : F, r ^ 2 ≠ a + b * r) :
    Nat.card (periodMatrixGroup a b) = Nat.card F ^ 2 - 1 := by
  have : Fact (∀ r : F, r ^ 2 ≠ a + b * r) := ⟨hirr⟩
  rw [card_periodMatrixGroup, Nat.card_units, Nat.card_congr (equivProd a b), Nat.card_prod, sq]

/-- **`[GL₂(𝔽_q) : C_ns] = q (q - 1)`**, the degree of `X_ns(ℓ)` over the `j`-line for `q = ℓ`. -/
theorem index_periodMatrixGroup_of_forall_sq_ne [Finite F] (hirr : ∀ r : F, r ^ 2 ≠ a + b * r) :
    (periodMatrixGroup a b).index = Nat.card F * (Nat.card F - 1) := by
  have hpos : 0 < Nat.card F ^ 2 - 1 := by
    have := Finite.one_lt_card (α := F)
    have : 1 < Nat.card F ^ 2 := by nlinarith
    omega
  exact TauCeti.index_eq_of_natCard_eq_mul hpos (card_periodMatrixGroup_of_forall_sq_ne hirr)
    (TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul F)

end QuadraticAlgebra

namespace TauCeti

open QuadraticAlgebra

universe u

section CommRing

variable {R : Type u} [CommRing R]

/-- **The normalizer of the nonsplit Cartan subgroup** `QuadraticAlgebra.periodMatrixGroup a b`,
written `C_ns⁺`. -/
noncomputable def GL2NonSplitCartanNormalizer (a b : R) : Subgroup (GL (Fin 2) R) :=
  Subgroup.normalizer (periodMatrixGroup a b : Set (GL (Fin 2) R))

theorem GL2NonSplitCartanNormalizer_def (a b : R) :
    GL2NonSplitCartanNormalizer a b =
      Subgroup.normalizer (periodMatrixGroup a b : Set (GL (Fin 2) R)) :=
  (rfl)

theorem GL2NonSplitCartanNormalizer.periodMatrixGroup_le {a b : R} :
    periodMatrixGroup a b ≤ GL2NonSplitCartanNormalizer a b :=
  Subgroup.le_normalizer

end CommRing

section Field

variable {F : Type u} [Field F] {a b : F}

namespace GL2NonSplitCartanNormalizer

/-- The companion matrix `!![b, a; 1, 0]`, the matrix of multiplication by `ω`. -/
private noncomputable def omega (b : F) (ha : a ≠ 0) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![b, a; 1, 0] (by simpa [det_fin_two_of] using ha)

@[simp]
private theorem coe_omega (ha : a ≠ 0) :
    ((omega b ha : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![b, a; 1, 0] :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- The matrix `!![1, -b; 0, -1]` of the conjugation `ω ↦ b - ω` of `F[ω]`. -/
private noncomputable def conjMatrix (b : F) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1, -b; 0, -1] (by simp [det_fin_two_of])

@[simp]
private theorem coe_conjMatrix :
    ((conjMatrix b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -b; 0, -1] :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem conjMatrix_mul_self : conjMatrix b * conjMatrix b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem conjMatrix_inv : (conjMatrix b)⁻¹ = conjMatrix b :=
  inv_eq_of_mul_eq_one_right conjMatrix_mul_self

private theorem conjMatrix_mul_mul_mem {h : GL (Fin 2) F} (hh : h ∈ periodMatrixGroup a b) :
    conjMatrix b * h * conjMatrix b ∈ periodMatrixGroup a b := by
  obtain ⟨h₁, h₂⟩ := mem_periodMatrixGroup_iff.mp hh
  simp only [mem_periodMatrixGroup_iff, Units.val_mul, coe_conjMatrix, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Fin.isValue, one_mul,
    zero_mul, zero_add, neg_mul]
  constructor
  · linear_combination h₁
  · linear_combination -b * h₁ - h₂

private theorem conjMatrix_mem :
    conjMatrix b ∈ GL2NonSplitCartanNormalizer a b := by
  refine Subgroup.mem_normalizer_iff.mpr fun h ↦ ⟨fun hh ↦ ?_, fun hh ↦ ?_⟩
  · rw [conjMatrix_inv]
    exact conjMatrix_mul_mul_mem hh
  rw [conjMatrix_inv] at hh
  have := conjMatrix_mul_mul_mem hh
  rwa [← mul_assoc, ← mul_assoc, conjMatrix_mul_self, one_mul, mul_assoc, conjMatrix_mul_self,
    mul_one] at this

private theorem conjMatrix_notMem (hsep : b ≠ 0 ∨ (2 : F) ≠ 0) :
    conjMatrix b ∉ periodMatrixGroup a b := by
  intro h
  obtain ⟨h₁, h₂⟩ := mem_periodMatrixGroup_iff.mp h
  rcases hsep with h | h
  · exact h (by simpa using h₂)
  · have h₁' : (1 : F) = -1 := by simpa using h₁
    exact h (by linear_combination h₁')

/-- An element of the normalizer conjugates `ω` to `ω` or to its conjugate `b - ω`. -/
private theorem conj_omega_eq (hirr : ∀ r : F, r ^ 2 ≠ a + b * r) (ha : a ≠ 0)
    {g : GL (Fin 2) F} (hg : g ∈ GL2NonSplitCartanNormalizer a b) :
    g * omega b ha * g⁻¹ = omega b ha ∨
      g * omega b ha * g⁻¹ = conjMatrix b * omega b ha * conjMatrix b := by
  have hω : omega b ha ∈ periodMatrixGroup a b := by
    simp
  set y := g * omega b ha * g⁻¹ with hy
  obtain ⟨h₁, h₂⟩ := mem_periodMatrixGroup_iff.mp
    (show y ∈ periodMatrixGroup a b from (Subgroup.mem_normalizer_iff.mp hg _).mp hω)
  have htr : (y : Matrix (Fin 2) (Fin 2) F).trace = b := by
    rw [hy, Units.val_mul, Units.val_mul, Matrix.trace_units_conj]
    simp [trace_fin_two]
  have hdet : (y : Matrix (Fin 2) (Fin 2) F).det = -a := by
    rw [hy, Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    simp [det_fin_two]
  rw [trace_fin_two, h₁] at htr
  rw [det_fin_two, h₁, h₂] at hdet
  set x := (y : Matrix (Fin 2) (Fin 2) F) 1 1
  set s := (y : Matrix (Fin 2) (Fin 2) F) 1 0
  have hs : b * s = b - 2 * x := by linear_combination htr
  have hsq : x ^ 2 - b * x = a * (1 - s ^ 2) := by linear_combination -hdet + x * hs
  have hdisc : (b ^ 2 + 4 * a) * (1 - s ^ 2) = 0 := by
    linear_combination -4 * hsq - (b * s + b - 2 * x) * hs
  -- `(y - ω) (y - (b - ω)) = 0` in `F[ω]`, so one of the two factors has norm zero.
  have key : (x ^ 2 + b * x * (s - 1) - a * (s - 1) ^ 2) *
      ((x - b) ^ 2 + b * (x - b) * (s + 1) - a * (s + 1) ^ 2) = 0 := by
    linear_combination
      (x ^ 2 + b * s * x - a * s ^ 2 + a + (-b * x + 2 * a * s - 2 * a) +
          (b * x - b ^ 2 - 2 * a * s - 2 * a) - b * (b * s - b + 2 * x) + 8 * a + b ^ 2) * hdet +
        (-(-b * x + 2 * a * s - 2 * a) * b - 2 * a * b - (b ^ 2 + 4 * a) * x) * hs - a * hdisc
  rcases mul_eq_zero.mp key with h | h
  · obtain ⟨hx, hs'⟩ := (sq_add_mul_mul_sub_mul_sq_eq_zero_iff hirr).mp h
    have hs₁ : s = 1 := sub_eq_zero.mp hs'
    refine Or.inl (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h₁, h₂, x, s, hx, hs₁]
  · obtain ⟨hx, hs'⟩ := (sq_add_mul_mul_sub_mul_sq_eq_zero_iff hirr).mp h
    have hx' : x = b := sub_eq_zero.mp hx
    have hs₁ : s = -1 := eq_neg_of_add_eq_zero_left hs'
    refine Or.inr (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h₁, h₂, x, s, hx', hs₁]

end GL2NonSplitCartanNormalizer

open GL2NonSplitCartanNormalizer in
/-- **`[C_ns⁺ : C_ns] = 2`** when `X² - b X - a` has no root in `F` and is separable, that is
`b ≠ 0` or `2 ≠ 0`. Over a finite field separability is automatic
(`TauCeti.GL2NonSplitCartanNormalizer.two_mul_index`); for an inseparable `X² - a` the
conjugation `!![1, 0; 0, -1]` is the identity. -/
theorem relIndex_periodMatrixGroup_GL2NonSplitCartanNormalizer
    (hirr : ∀ r : F, r ^ 2 ≠ a + b * r) (hsep : b ≠ 0 ∨ (2 : F) ≠ 0) :
    (periodMatrixGroup a b).relIndex (GL2NonSplitCartanNormalizer a b) = 2 := by
  have ha : a ≠ 0 := fun h ↦ hirr 0 (by simp [h])
  refine Subgroup.relIndex_eq_two_iff'.mpr ⟨conjMatrix b, conjMatrix_mem, fun g hg ↦ ?_⟩
  by_cases hgC : g ∈ periodMatrixGroup a b
  · refine Or.inr ⟨hgC, fun h ↦ conjMatrix_notMem (a := a) hsep ?_⟩
    simpa using mul_mem h (inv_mem hgC)
  · refine Or.inl ⟨?_, hgC⟩
    rcases conj_omega_eq hirr ha hg with h | h
    · exact absurd (mem_periodMatrixGroup_iff_commute.mpr
        (congrArg Units.val (mul_inv_eq_iff_eq_mul.mp h))) hgC
    · apply mem_periodMatrixGroup_iff_commute.mpr
      have : conjMatrix b * g * omega b ha * (conjMatrix b * g)⁻¹ = omega b ha := by
        rw [_root_.mul_inv_rev, conjMatrix_inv]
        calc conjMatrix b * g * omega b ha * (g⁻¹ * conjMatrix b)
            = conjMatrix b * (g * omega b ha * g⁻¹) * conjMatrix b := by simp only [mul_assoc]
          _ = omega b ha := by
            rw [h]
            simp only [← mul_assoc, conjMatrix_mul_self, one_mul]
            simp only [mul_assoc, conjMatrix_mul_self, mul_one]
      exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp this)

namespace GL2NonSplitCartanNormalizer

/-- **`|C_ns⁺| = 2 (q² - 1)`** over a field with `q` elements. -/
theorem natCard (hirr : ∀ r : F, r ^ 2 ≠ a + b * r) :
    Nat.card (GL2NonSplitCartanNormalizer a b) = 2 * (Nat.card F ^ 2 - 1) := by
  have h := (periodMatrixGroup a b).relIndex_mul_card (GL2NonSplitCartanNormalizer a b)
  rw [inf_of_le_left periodMatrixGroup_le, card_periodMatrixGroup_of_forall_sq_ne hirr] at h
  rcases finite_or_infinite F with _ | _
  · rwa [relIndex_periodMatrixGroup_GL2NonSplitCartanNormalizer hirr
      (FiniteField.ne_zero_or_two_ne_zero_of_forall_sq_ne hirr), eq_comm] at h
  · rw [Nat.card_eq_zero_of_infinite (α := F)] at h ⊢
    simpa using h.symm

/-- **`2 [GL₂(𝔽_q) : C_ns⁺] = q (q - 1)`**: the degree of `X_ns⁺(ℓ)` over the `j`-line is
`ℓ (ℓ - 1) / 2`. -/
theorem two_mul_index [Finite F] (hirr : ∀ r : F, r ^ 2 ≠ a + b * r) :
    2 * (GL2NonSplitCartanNormalizer a b).index = Nat.card F * (Nat.card F - 1) := by
  rw [← index_periodMatrixGroup_of_forall_sq_ne hirr,
    ← Subgroup.relIndex_mul_index periodMatrixGroup_le,
    relIndex_periodMatrixGroup_GL2NonSplitCartanNormalizer hirr
      (FiniteField.ne_zero_or_two_ne_zero_of_forall_sq_ne hirr)]

end GL2NonSplitCartanNormalizer

end Field

end TauCeti
