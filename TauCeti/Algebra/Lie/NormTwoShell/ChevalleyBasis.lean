/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.SMul
public import TauCeti.Algebra.Lie.NormTwoShell.Serre

/-!
# The Chevalley basis of the signed Lie algebra of a simply laced Cartan matrix

Let `B : Matrix I I ℤ` be positive definite with even diagonal and nonpositive off-diagonal
entries, for instance the Cartan matrix of a simply laced Dynkin diagram with its vertices linearly
ordered, and let `Φ = B.normTwoShell` be its roots. In `Matrix.ShellLieAlgebra B` the root vector
`x_a` is indexed by the section `a ↦ ⟨1, a⟩` of the ordered sign cover `Matrix.SignCover B`, and
the opposite bracket is `⁅x_a, x_(-a)⁆ = ε(a, -a) H_a`, where `ε` is the ordered sign; the sign
`ε(a, -a) = ε(a, a)` need not be `1`.

This file rescales the root vectors of the negative roots by the signs of inverse lifts. In the
cover, `⟨1, a⟩⁻¹ = ε(a, a) ⟨1, -a⟩` (`Matrix.SignCover.inv_canonicalSection`), so for a positive
root `a` the normalized root vector of `-a` is `e_(-a) = ε(a, a) x_(-a)`, the sign being that of
the inverse lift of `⟨1, a⟩`
(`Matrix.ShellLieAlgebra.inv_canonicalSection_eq_inl_normalizationSign_mul`), while the positive
root vectors are kept: `e_a = s(a) x_a` with `s(a) = 1` for `a ≥ 0` and `s(a) = ε(a, a)` otherwise
(`Matrix.ShellLieAlgebra.normalizationSign`). Every root is positive or negative, and in the
normalized basis (`Matrix.ShellLieAlgebra.normalizedBasis`) the bracket takes the form of a
Chevalley basis:

* `⁅H_h, e_a⁆ = ⟪h, a⟫ e_a`;
* `⁅e_a, e_(-a)⁆ = H_a` for every root `a`;
* `⁅e_a, e_b⁆ = N(a, b) e_(a + b)` if `a + b ∈ Φ`, with a unit `N(a, b) = ±1`
  (`Matrix.ShellLieAlgebra.structureConstant`), and `0` if `a + b` is neither a root nor zero;
* `N(-a, -b) = -N(a, b)`.

For a simple root `αᵢ` the ordered sign `ε(αᵢ, αᵢ)` is `1`, so the normalization does not change
the Chevalley generators: `e_(αᵢ) = Eᵢ` and `e_(-αᵢ) = Fᵢ`, the images of the generators of the
Serre presentation in `TauCeti.Algebra.Lie.NormTwoShell.Serre`.

## Main definitions

* `Matrix.ShellLieAlgebra.normalizationSign`: the sign `s(a)`.
* `Matrix.ShellLieAlgebra.normalizedRoot`: the normalized root vector `e_a = s(a) x_a`.
* `Matrix.ShellLieAlgebra.structureConstant`: the structure constant `N(a, b)`.
* `Matrix.ShellLieAlgebra.normalizedBasis`: the integral basis of Cartan vectors `H_(αᵢ)` and
  normalized root vectors.

## Main results

* `Matrix.ShellLieAlgebra.inv_canonicalSection_eq_inl_normalizationSign_mul`: for a positive root
  `a`, the sign `s(-a)` is the sign of the inverse lift `⟨1, a⟩⁻¹` over `-a`.
* `Matrix.ShellLieAlgebra.normalizedRoot_lie_normalizedRoot_of_add_eq_zero`:
  `⁅e_a, e_(-a)⁆ = H_a`.
* `Matrix.ShellLieAlgebra.normalizedRoot_lie_normalizedRoot_of_mem`:
  `⁅e_a, e_b⁆ = N(a, b) e_(a + b)` when `a + b` is a root.
* `Matrix.ShellLieAlgebra.structureConstant_neg_neg`: `N(-a, -b) = -N(a, b)`.
* `Matrix.ShellLieAlgebra.normalizedRoot_single` and
  `Matrix.ShellLieAlgebra.normalizedRoot_neg_single`: the normalized simple root vectors are the
  Chevalley generators.

## References

* C. Chevalley, *Sur certains groupes simples*, Tôhoku Math. J. **7** (1955), 14--66.
* R. Steinberg, *Lectures on Chevalley groups*, University Lecture Series **66**, AMS (2016),
  §1, Theorem 1.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] (B : Matrix I I ℤ)

/-- **The normalization sign** `s(a)` of a lattice vector `a`: `1` if `a` is nonnegative, and the
ordered sign `ε(a, a) = (B.orderedSignForm a a).negOnePow` otherwise. On a negative root `a` it is
the sign of the inverse lift `⟨1, -a⟩⁻¹ = ε(a, a) ⟨1, a⟩` in `Matrix.SignCover B`, see
`Matrix.SignCover.inv_canonicalSection`. -/
noncomputable def normalizationSign (a : I → ℤ) : ℤˣ := by
  classical
  exact if 0 ≤ a then 1 else (B.orderedSignForm a a).negOnePow

/-- **The normalized root vector** `e_a = s(a) x_a` of a vector `a` of the norm-two shell: the
root vector `x_a` itself for a nonnegative root, and `ε(a, a) x_a` otherwise. -/
noncomputable def normalizedRoot (a : B.normTwoShell) : ShellLieAlgebra B :=
  normalizationSign B a • root B a

/-- **The structure constant** `N(a, b) = s(a) s(b) s(a + b) ε(a, b)` of a pair of lattice vectors.
When `a`, `b` and `a + b` are roots it is the coefficient of `e_(a + b)` in `⁅e_a, e_b⁆`, see
`Matrix.ShellLieAlgebra.normalizedRoot_lie_normalizedRoot_of_mem`. -/
noncomputable def structureConstant (a b : I → ℤ) : ℤˣ :=
  normalizationSign B a * normalizationSign B b * normalizationSign B (a + b) *
    (B.orderedSignForm a b).negOnePow

/-- **The normalized basis** of `Matrix.ShellLieAlgebra B`: the Cartan vectors `H_(αᵢ)` of the
coordinate vectors `αᵢ = Pi.single i 1`, followed by the normalized root vectors `e_a`. -/
noncomputable def normalizedBasis :
    Module.Basis (I ⊕ B.normTwoShell) ℤ (ShellLieAlgebra B) :=
  (basis B).unitsSMul (Sum.elim 1 fun a ↦ normalizationSign B a)

variable {B}

theorem normalizedRoot_def (a : B.normTwoShell) :
    normalizedRoot B a = normalizationSign B a • root B a :=
  (rfl)

theorem structureConstant_def (a b : I → ℤ) :
    structureConstant B a b = normalizationSign B a * normalizationSign B b *
      normalizationSign B (a + b) * (B.orderedSignForm a b).negOnePow :=
  (rfl)

/-! ### The normalization sign -/

@[simp]
theorem normalizationSign_of_nonneg {a : I → ℤ} (ha : 0 ≤ a) : normalizationSign B a = 1 := by
  rw [normalizationSign, ite_eq_left ha]

@[simp]
theorem normalizationSign_of_not_nonneg {a : I → ℤ} (ha : ¬0 ≤ a) :
    normalizationSign B a = (B.orderedSignForm a a).negOnePow := by
  rw [normalizationSign, ite_eq_right ha]

/-- The normalization sign of the negative of a nonnegative vector `a` is `ε(a, a)`. -/
theorem normalizationSign_neg_of_nonneg {a : I → ℤ} (ha : 0 ≤ a) :
    normalizationSign B (-a) = (B.orderedSignForm a a).negOnePow := by
  rcases eq_or_ne a 0 with rfl | ha'
  · simp
  have h : ¬0 ≤ -a := fun h ↦ ha' (le_antisymm (neg_nonneg.mp h) ha)
  rw [normalizationSign_of_not_nonneg h, LinearMap.map_neg₂, map_neg, neg_neg]

section Cover

attribute [local instance] TauCeti.trivialMulDistribMulAction

/-- **The normalization sign is the sign of the inverse lift**: for a nonnegative vector `a`, the
inverse of the section value `⟨1, a⟩` in `Matrix.SignCover B` is `s(-a) ⟨1, -a⟩`. -/
theorem inv_canonicalSection_eq_inl_normalizationSign_mul {a : I → ℤ} (ha : 0 ≤ a) :
    ((signFactorSet B).canonicalSection (Multiplicative.ofAdd a))⁻¹ =
      TauCeti.FactorSet.inl (signFactorSet B) (normalizationSign B (-a)) *
        (signFactorSet B).canonicalSection (Multiplicative.ofAdd (-a)) := by
  rw [SignCover.inv_canonicalSection, normalizationSign_neg_of_nonneg ha, orderedSign_apply,
    toAdd_ofAdd, ofAdd_neg]

end Cover

/-- **The normalization signs of opposite roots** multiply to `ε(a, a)`, for a positive definite
`B` with even diagonal and nonpositive off-diagonal entries: of `a` and `-a`, exactly one is
nonnegative. -/
theorem normalizationSign_mul_normalizationSign_neg (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) {a : I → ℤ} (ha : a ∈ B.normTwoShell) :
    normalizationSign B a * normalizationSign B (-a) = (B.orderedSignForm a a).negOnePow := by
  have hne := ne_zero_of_mem_normTwoShell ha
  rcases hB.nonneg_or_nonpos_of_mem_normTwoShell hev hoff ha with h | h
  · rw [normalizationSign_of_nonneg h, normalizationSign_neg_of_nonneg h, one_mul]
  · have h' : ¬0 ≤ a := fun h' ↦ hne (le_antisymm h h')
    rw [normalizationSign_of_not_nonneg h', normalizationSign_of_nonneg (neg_nonneg.mpr h),
      mul_one]

/-! ### Normalized root vectors -/

@[simp]
theorem normalizedRoot_of_nonneg {a : B.normTwoShell} (ha : 0 ≤ (a : I → ℤ)) :
    normalizedRoot B a = root B a := by
  rw [normalizedRoot_def, normalizationSign_of_nonneg ha, one_smul]

@[simp]
theorem normalizedRoot_of_not_nonneg {a : B.normTwoShell} (ha : ¬0 ≤ (a : I → ℤ)) :
    normalizedRoot B a = (B.orderedSignForm a a).negOnePow • root B a := by
  rw [normalizedRoot_def, normalizationSign_of_not_nonneg ha]

/-- The normalized root vector of a simple root `αᵢ` is the Chevalley generator `Eᵢ`. -/
theorem normalizedRoot_single (hdiag : ∀ i, B i i = 2) (i : I) :
    normalizedRoot B ⟨Pi.single i 1, single_mem_normTwoShell (hdiag i)⟩ =
      chevalleyE B hdiag i := by
  rw [normalizedRoot_of_nonneg (Pi.single_nonneg.mpr zero_le_one), chevalleyE_def]

/-- The normalized root vector of a negative simple root `-αᵢ` is the Chevalley generator `Fᵢ`:
the ordered sign `ε(αᵢ, αᵢ)` is `1`, since the ordered form only sees the strictly lower triangular
entries of `B`. -/
theorem normalizedRoot_neg_single (hdiag : ∀ i, B i i = 2) (i : I) :
    normalizedRoot B
        ⟨-Pi.single i 1, neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag i))⟩ =
      chevalleyF B hdiag i := by
  have h : ¬0 ≤ (-Pi.single i 1 : I → ℤ) := fun h ↦ by simpa using h i
  rw [normalizedRoot_of_not_nonneg h, chevalleyF_def]
  simp

/-! ### The bracket in the normalized basis -/

/-- The Cartan vector `H_h` acts on the normalized root vector `e_a` by the pairing `⟪h, a⟫`. -/
@[simp]
theorem cartan_lie_normalizedRoot (h : I → ℤ) (a : B.normTwoShell) :
    ⁅cartan B h, normalizedRoot B a⁆ = (h ⬝ᵥ B *ᵥ (a : I → ℤ)) • normalizedRoot B a := by
  rw [normalizedRoot_def, ShellLieAlgebra.lie_units_smul, cartan_lie_root, smul_comm]

/-- The bracket `⁅e_a, e_b⁆` of two normalized root vectors is the root bracket of `x_a` and `x_b`,
rescaled by the product `s(a) s(b)` of their normalization signs. -/
theorem normalizedRoot_lie_normalizedRoot (a b : B.normTwoShell) :
    ⁅normalizedRoot B a, normalizedRoot B b⁆ =
      (normalizationSign B a * normalizationSign B b) • rootBracket B a b := by
  rw [normalizedRoot_def, normalizedRoot_def, ShellLieAlgebra.units_smul_lie,
    ShellLieAlgebra.lie_units_smul, root_lie_root, smul_smul]

/-- **Opposite normalized root vectors bracket to the coroot**: `⁅e_a, e_(-a)⁆ = H_a`, for a
positive definite `B` with even diagonal and nonpositive off-diagonal entries. -/
@[simp]
theorem normalizedRoot_lie_normalizedRoot_of_add_eq_zero (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) (hoff : ∀ i j, i ≠ j → B i j ≤ 0) {a b : B.normTwoShell}
    (h : (a : I → ℤ) + b = 0) :
    ⁅normalizedRoot B a, normalizedRoot B b⁆ = cartan B a := by
  have hb : (b : I → ℤ) = -a := eq_neg_of_add_eq_zero_right h
  have key : normalizationSign B a * normalizationSign B (-a) *
      (B.orderedSignForm a (-a)).negOnePow = 1 := by
    rw [normalizationSign_mul_normalizationSign_neg hB hev hoff a.2, map_neg, Int.negOnePow_neg,
      Int.units_mul_self]
  rw [normalizedRoot_lie_normalizedRoot, rootBracket_of_add_eq_zero h, smul_smul, hb, key,
    one_smul]

/-- **The structure constants of the normalized basis**: if `a + b` is a root, then
`⁅e_a, e_b⁆ = N(a, b) e_(a + b)`. -/
@[simp]
theorem normalizedRoot_lie_normalizedRoot_of_mem {a b : B.normTwoShell}
    (h : (a : I → ℤ) + b ∈ B.normTwoShell) :
    ⁅normalizedRoot B a, normalizedRoot B b⁆ =
      structureConstant B a b • normalizedRoot B ⟨_, h⟩ := by
  rw [normalizedRoot_lie_normalizedRoot, rootBracket_of_mem h, normalizedRoot_def, smul_smul,
    smul_smul, structureConstant_def]
  congr 1
  -- The sign `s(a + b)` occurs twice on the right and squares to `1`.
  simp only [mul_assoc, mul_left_comm _ (B.orderedSignForm _ _).negOnePow, Int.units_mul_self,
    mul_one]

/-- Two normalized root vectors whose roots sum to neither a root nor zero commute. -/
@[simp]
theorem normalizedRoot_lie_normalizedRoot_of_notMem_of_add_ne_zero {a b : B.normTwoShell}
    (h : (a : I → ℤ) + b ∉ B.normTwoShell) (h' : (a : I → ℤ) + b ≠ 0) :
    ⁅normalizedRoot B a, normalizedRoot B b⁆ = 0 := by
  rw [normalizedRoot_lie_normalizedRoot, rootBracket_of_notMem_of_add_ne_zero h h', smul_zero]

/-- **The Chevalley sign rule** `N(-a, -b) = -N(a, b)`, for roots `a`, `b` with `a + b` a root, and
a positive definite `B` with even diagonal and nonpositive off-diagonal entries. -/
theorem structureConstant_neg_neg (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) {a b : I → ℤ} (ha : a ∈ B.normTwoShell)
    (hb : b ∈ B.normTwoShell) (hab : a + b ∈ B.normTwoShell) :
    structureConstant B (-a) (-b) = -structureConstant B a b := by
  have hS := hB.isHermitian.isSymm
  have hpair : a ⬝ᵥ B *ᵥ b = -1 := (hS.add_mem_normTwoShell_iff ha hb).1 hab
  have hpar := B.even_orderedSignForm_add_orderedSignForm_swap_sub hS hev a b
  -- The product `N(a, b) N(-a, -b)` collects into `s(c) s(-c) = ε(c, c)` for `c = a, b, a + b`.
  have key : structureConstant B a b * structureConstant B (-a) (-b) = -1 := by
    have e : structureConstant B a b * structureConstant B (-a) (-b) =
        normalizationSign B a * normalizationSign B (-a) *
          (normalizationSign B b * normalizationSign B (-b)) *
          (normalizationSign B (a + b) * normalizationSign B (-(a + b))) *
          ((B.orderedSignForm a b).negOnePow * (B.orderedSignForm (-a) (-b)).negOnePow) := by
      rw [structureConstant_def, structureConstant_def, neg_add]
      simp only [mul_left_comm, mul_assoc]
    rw [e, normalizationSign_mul_normalizationSign_neg hB hev hoff ha,
      normalizationSign_mul_normalizationSign_neg hB hev hoff hb,
      normalizationSign_mul_normalizationSign_neg hB hev hoff hab]
    simp only [← Int.negOnePow_add, Int.negOnePow_eq_neg_one_iff, Int.odd_iff]
    rw [Int.even_iff] at hpar
    simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, neg_neg]
    omega
  calc structureConstant B (-a) (-b)
      = structureConstant B a b * structureConstant B a b * structureConstant B (-a) (-b) := by
        rw [Int.units_mul_self, one_mul]
    _ = -structureConstant B a b := by rw [mul_assoc, key, mul_neg_one]

/-! ### The normalized basis -/

@[simp]
theorem normalizedBasis_inl (i : I) : normalizedBasis B (.inl i) = cartan B (Pi.single i 1) := by
  rw [normalizedBasis, Module.Basis.unitsSMul_apply, Sum.elim_inl, Pi.one_apply, one_smul,
    basis_inl]

@[simp]
theorem normalizedBasis_inr (a : B.normTwoShell) :
    normalizedBasis B (.inr a) = normalizedRoot B a := by
  rw [normalizedBasis, Module.Basis.unitsSMul_apply, Sum.elim_inr, basis_inr, normalizedRoot_def]

end Matrix.ShellLieAlgebra
