/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.GeneralLinear.BlockDiagonal
public import TauCeti.Algebra.Lie.GeneralLinear.Oscillator.Basic
public import TauCeti.Algebra.Lie.GeneralLinear.Twist
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import TauCeti.Algebra.MvPolynomial.Coeff

/-!
# The Fock module of the dual pair `(U(p, q), U(r, s))`

Let `I = I₊ ⊔ I₋` and `I' = I'₊ ⊔ I'₋` be finite sets of sizes `n = p + q` and `n' = r + s`, the
blocks being recorded by sign functions `ε : I → Bool` and `ε' : I' → Bool` (`true` for the
positive block). A pair `(a, c) ∈ I × I'` is *even* when `a` and `c` have the same sign, and *odd*
otherwise (`TauCeti.IsEvenPair`). The **Fock module** of the pair is the polynomial ring
`MvPolynomial (I × I') K` in the variables `z a c`, with the oscillator operators `R a c`, `L a c`
of `TauCeti/Algebra/Lie/GeneralLinear/Oscillator/Basic.lean` for this parity: `R = z ·`,
`L = ∂ / ∂ z` on even variables and `R = -∂ / ∂ z`, `L = z ·` on odd ones. It carries the two
commuting actions

* `E a b ↦ ∑ c, R a c L b c + (n' / 2) δ a b` of `gl I` (`TauCeti.fockRowHom`), and
* `E c d ↦ ∑ a, R a c L a d + (n / 2) δ c d` of `gl I'` (`TauCeti.fockColHom`),

which together form the action `TauCeti.fockHom` of `gl I × gl I'`. These are the derivatives
of the oscillator representation of the double cover of `U(p, q) × U(r, s)` on its polynomial Fock
vectors, normalised so that each matrix unit acts by a sum of products `R L` plus a half-integral
multiple of the identity on the diagonal, with no further sign or shift. Both actions are the
oscillator representation of `gl (I × I')` restricted along the embeddings `A ↦ A ⊗ 1`
(`TauCeti.glBlockDiagonal`) and `B ↦ 1 ⊗ B` (`TauCeti.glOneKronecker`), which commute, and twisted
by a multiple of the trace (`TauCeti.glTraceTwistHom`); these half-integral shifts are what give
the vacuum its weight.

The situation is symmetric: renaming `z a c` as `z c a` exchanges the two actions
(`TauCeti.rename_swap_fockColHom`).

The compact Lie algebra `𝔨 = gl I₊ × gl I₋` is spanned by the matrix units `E a b` with
`ε a = ε b`. These preserve the degree (`TauCeti.fockRowHom_single_mem_homogeneousSubmodule`),
and the vacuum `1` is a weight vector for them, of weight `(r - s) / 2` on `I₊` and `(s - r) / 2`
on `I₋` (`TauCeti.fockRowHom_single_self_one`); every monomial is a weight vector
(`TauCeti.fockRowHom_single_self_monomial`). The noncompact part `𝔭` is spanned by the `E a b`
with `ε a ≠ ε b`, and each of them is the sum of a degree-raising part, multiplication by the
quadratic polynomial `TauCeti.fockRowRaise a b`, and a degree-lowering part, minus the second-order
operator `TauCeti.fockRowLower a b` (`TauCeti.fockRowHom_single_of_ne`). The same holds for the
columns. Since every monomial is a weight vector, the weight of a nonzero weight vector bounds its
degree from below (`TauCeti.sum_abs_le_of_fockRowHom_single_self`).

## Main definitions

* `TauCeti.IsEvenPair ε ε'`: the even variables.
* `TauCeti.fockRowHom`, `TauCeti.fockColHom`: the actions of `gl I` and `gl I'`.
* `TauCeti.fockHom`: the joint action of `gl I × gl I'`.
* `TauCeti.fockRowRaise`, `TauCeti.fockRowLower`, `TauCeti.fockColRaise`, `TauCeti.fockColLower`:
  the degree-raising and degree-lowering components of the noncompact matrix units.

## Main results

* `TauCeti.fockRowHom_single`, `TauCeti.fockColHom_single`: the images of matrix units.
* `TauCeti.commute_fockRowHom_fockColHom`: the two actions commute.
* `TauCeti.fockRowHom_single_self_one`, `TauCeti.fockColHom_single_self_one`: the weight of the
  vacuum.
* `TauCeti.fockRowHom_single_self_monomial`, `TauCeti.fockColHom_single_self_monomial`: the
  weights of monomials.
* `TauCeti.fockRowHom_single_mem_homogeneousSubmodule`,
  `TauCeti.fockColHom_single_mem_homogeneousSubmodule`: `𝔨` and `𝔨'` preserve the degree.
* `TauCeti.fockRowHom_single_of_ne`, `TauCeti.fockColHom_single_of_ne`: the decomposition of the
  noncompact matrix units into a degree-raising and a degree-lowering part.
* `TauCeti.sum_abs_le_of_fockRowHom_single_self`, `TauCeti.sum_abs_le_of_fockColHom_single_self`:
  a weight vector of degree `d` whose weight differs from that of the vacuum by `ν` has
  `∑ |ν| ≤ d`; so a `K`-type of highest weight `μ` occurs only in degrees at least
  `∑_{a ∈ I₊} |μ a - (r - s) / 2| + ∑_{a ∈ I₋} |μ a + (r - s) / 2|`.
* `TauCeti.rename_swap_fockColHom`, `TauCeti.rename_swap_fockRowHom`: exchanging the two members
  of the pair, by renaming `z a c` as `z c a`, exchanges the two actions.

## References

* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535--552.
* M. Kashiwara and M. Vergne, *On the Segal–Shale–Weil representations and harmonic
  polynomials*, Invent. Math. 44 (1978), 1--47.
* The oscillator actions are adapted from `New.FockDualPair.oscRows` and
  `New.FockDualPair.swap_oscRows_E`, the vacuum weights (`TauCeti.fockRowHom_single_self_one`)
  from `New.FockDualPair.vacuumWeight`, and the degree-lowering operators
  (`TauCeti.fockRowLower`, `TauCeti.fockColLower`) from `New.FockDualPair.fockLaplacian`, all in
  `src/Lib/DiscreteSeries/Theta/FockDualPair.lean` of grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), and the
  oscillator operators from `New.Fock.raiseOp` and `New.Fock.lowerOp` in
  `src/Lib/Weil/Fock/Basic.lean`; there the column action is the contragredient of the one here
  and the pair carries a free global sign and free shifts.
-/

public section

namespace TauCeti

open MvPolynomial Finset Matrix

open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I I' : Type*}

/-- The variable `z a c` of the Fock module is *even* when `a` and `c` have the same sign. -/
def IsEvenPair (ε : I → Bool) (ε' : I' → Bool) (x : I × I') : Prop :=
  ε x.1 = ε' x.2

theorem isEvenPair_iff {ε : I → Bool} {ε' : I' → Bool} {x : I × I'} :
    IsEvenPair ε ε' x ↔ ε x.1 = ε' x.2 :=
  Iff.rfl

instance (ε : I → Bool) (ε' : I' → Bool) : DecidablePred (IsEvenPair ε ε') :=
  fun _ ↦ decidable_of_iff _ isEvenPair_iff.symm

/-- The variables `z a c` and `z b c` have the same parity when `a` and `b` have the same sign. -/
theorem isEvenPair_iff_of_eq {ε : I → Bool} {ε' : I' → Bool} {a b : I} (h : ε a = ε b) (c : I') :
    IsEvenPair ε ε' (a, c) ↔ IsEvenPair ε ε' (b, c) := by
  simp [isEvenPair_iff, h]

/-- The variables `z a c` and `z a d` have the same parity when `c` and `d` have the same sign. -/
theorem isEvenPair_iff_of_eq' {ε : I → Bool} {ε' : I' → Bool} {c d : I'} (h : ε' c = ε' d)
    (a : I) : IsEvenPair ε ε' (a, c) ↔ IsEvenPair ε ε' (a, d) := by
  simp [isEvenPair_iff, h]

/-- The variables `z a c` and `z b c` have opposite parities when `a` and `b` have opposite
signs. -/
theorem not_isEvenPair_iff_of_ne {ε : I → Bool} {ε' : I' → Bool} {a b : I} (h : ε a ≠ ε b)
    (c : I') : ¬(IsEvenPair ε ε' (a, c) ↔ IsEvenPair ε ε' (b, c)) := by
  simp only [isEvenPair_iff]
  revert h
  cases ε a <;> cases ε b <;> cases ε' c <;> simp

/-- The variables `z a c` and `z a d` have opposite parities when `c` and `d` have opposite
signs. -/
theorem not_isEvenPair_iff_of_ne' {ε : I → Bool} {ε' : I' → Bool} {c d : I'} (h : ε' c ≠ ε' d)
    (a : I) : ¬(IsEvenPair ε ε' (a, c) ↔ IsEvenPair ε ε' (a, d)) := by
  simp only [isEvenPair_iff]
  revert h
  cases ε' c <;> cases ε' d <;> cases ε a <;> simp

/-- Renaming `z a c` as `z c a` preserves the parity of the variables. -/
@[simp]
theorem isEvenPair_swap {ε : I → Bool} {ε' : I' → Bool} (x : I × I') :
    IsEvenPair ε' ε x.swap ↔ IsEvenPair ε ε' x := by
  simp [isEvenPair_iff, eq_comm]

/-! ### The raising and lowering operators of the noncompact parts -/

section RaiseLower

variable (K : Type*) [CommRing K] (ε : I → Bool) (ε' : I' → Bool)

/-- The degree-raising component of the noncompact matrix unit `E a b` of the rows
(`ε a ≠ ε b`): the quadratic polynomial `∑ z a c z b c` over the columns `c` of the sign of `a`,
by which it multiplies. -/
noncomputable def fockRowRaise [Fintype I'] (a b : I) : MvPolynomial (I × I') K :=
  ∑ c with ε a = ε' c, X (a, c) * X (b, c)

/-- The degree-lowering component of the noncompact matrix unit `E a b` of the rows
(`ε a ≠ ε b`), up to sign: the operator `∑ ∂ ∂ / ∂ z a c ∂ z b c` over the columns `c` of the
sign of `b`. -/
noncomputable def fockRowLower [Fintype I'] (a b : I) : Module.End K (MvPolynomial (I × I') K) :=
  ∑ c with ε a ≠ ε' c, (pderiv (a, c)).toLinearMap * (pderiv (b, c)).toLinearMap

/-- The degree-raising component of the noncompact matrix unit `E c d` of the columns
(`ε' c ≠ ε' d`): the quadratic polynomial `∑ z a c z a d` over the rows `a` of the sign of `c`,
by which it multiplies. -/
noncomputable def fockColRaise [Fintype I] (c d : I') : MvPolynomial (I × I') K :=
  ∑ a with ε a = ε' c, X (a, c) * X (a, d)

/-- The degree-lowering component of the noncompact matrix unit `E c d` of the columns
(`ε' c ≠ ε' d`), up to sign: the operator `∑ ∂ ∂ / ∂ z a c ∂ z a d` over the rows `a` of the sign
of `d`. -/
noncomputable def fockColLower [Fintype I] (c d : I') : Module.End K (MvPolynomial (I × I') K) :=
  ∑ a with ε a ≠ ε' c, (pderiv (a, c)).toLinearMap * (pderiv (a, d)).toLinearMap

variable {K ε ε'}

theorem fockRowRaise_def [Fintype I'] (a b : I) :
    fockRowRaise K ε ε' a b = ∑ c with ε a = ε' c, X (a, c) * X (b, c) :=
  (rfl)

theorem fockRowLower_apply [Fintype I'] (a b : I) (P : MvPolynomial (I × I') K) :
    fockRowLower K ε ε' a b P = ∑ c with ε a ≠ ε' c, pderiv (a, c) (pderiv (b, c) P) := by
  simp [fockRowLower, LinearMap.sum_apply]

theorem fockColRaise_def [Fintype I] (c d : I') :
    fockColRaise K ε ε' c d = ∑ a with ε a = ε' c, X (a, c) * X (a, d) :=
  (rfl)

theorem fockColLower_apply [Fintype I] (c d : I') (P : MvPolynomial (I × I') K) :
    fockColLower K ε ε' c d P = ∑ a with ε a ≠ ε' c, pderiv (a, c) (pderiv (a, d) P) := by
  simp [fockColLower, LinearMap.sum_apply]

/-- The degree-raising component of a noncompact matrix unit of the rows is homogeneous of
degree two. -/
theorem isHomogeneous_fockRowRaise [Fintype I'] (a b : I) :
    (fockRowRaise K ε ε' a b).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ (isHomogeneous_X K _).mul (isHomogeneous_X K _)

/-- The degree-raising component of a noncompact matrix unit of the columns is homogeneous of
degree two. -/
theorem isHomogeneous_fockColRaise [Fintype I] (c d : I') :
    (fockColRaise K ε ε' c d).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ (isHomogeneous_X K _).mul (isHomogeneous_X K _)

/-- The degree-lowering component of a noncompact matrix unit of the rows lowers the degree by
two. -/
theorem fockRowLower_mem_homogeneousSubmodule [Fintype I'] (a b : I) {d : ℕ}
    {P : MvPolynomial (I × I') K}
    (hP : P ∈ homogeneousSubmodule (I × I') K d) :
    fockRowLower K ε ε' a b P ∈ homogeneousSubmodule (I × I') K (d - 2) := by
  rw [fockRowLower_apply]
  exact sum_mem fun c _ ↦ by
    simpa [Nat.sub_sub] using
      (IsHomogeneous.pderiv (IsHomogeneous.pderiv ((mem_homogeneousSubmodule _ _).1 hP)))

/-- The degree-lowering component of a noncompact matrix unit of the columns lowers the degree
by two. -/
theorem fockColLower_mem_homogeneousSubmodule [Fintype I] (c d : I') {e : ℕ}
    {P : MvPolynomial (I × I') K}
    (hP : P ∈ homogeneousSubmodule (I × I') K e) :
    fockColLower K ε ε' c d P ∈ homogeneousSubmodule (I × I') K (e - 2) := by
  rw [fockColLower_apply]
  exact sum_mem fun a _ ↦ by
    simpa [Nat.sub_sub] using
      (IsHomogeneous.pderiv (IsHomogeneous.pderiv ((mem_homogeneousSubmodule _ _).1 hP)))

end RaiseLower

variable (K : Type*) [Field K] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  (ε : I → Bool) (ε' : I' → Bool)

/-! ### The two actions -/

/-- **The action of `gl I` on the Fock module**: the matrix unit `E a b` acts by
`∑ c, R a c L b c + (n' / 2) δ a b`, where `n'` is the number of elements of `I'`. -/
noncomputable def fockRowHom : Matrix I I K →ₗ⁅K⁆ Module.End K (MvPolynomial (I × I') K) :=
  glTraceTwistHom ((oscillatorHom K (IsEvenPair ε ε')).comp (glBlockDiagonal K I I'))
    (Fintype.card I' / 2)

/-- **The action of `gl I'` on the Fock module**: the matrix unit `E c d` acts by
`∑ a, R a c L a d + (n / 2) δ c d`, where `n` is the number of elements of `I`. -/
noncomputable def fockColHom : Matrix I' I' K →ₗ⁅K⁆ Module.End K (MvPolynomial (I × I') K) :=
  glTraceTwistHom ((oscillatorHom K (IsEvenPair ε ε')).comp (glOneKronecker K I I'))
    (Fintype.card I / 2)

variable {K ε ε'}

/-- The matrix unit `E a b` of `gl I` acts on the Fock module by
`∑ c, R a c L b c + (n' / 2) δ a b`. -/
theorem fockRowHom_single (a b : I) :
    fockRowHom K ε ε' (single a b 1) =
      ∑ c : I', oscRaise K (IsEvenPair ε ε') (a, c) * oscLower K (IsEvenPair ε ε') (b, c) +
        if a = b then (Fintype.card I' / 2 : K) • 1 else 0 := by
  rw [fockRowHom, glTraceTwistHom_apply, LieHom.comp_apply, glBlockDiagonal_single, map_sum]
  simp only [oscillatorHom_single, one_smul]
  split_ifs with hab
  · simp [hab]
  · simp [hab]

/-- The matrix unit `E c d` of `gl I'` acts on the Fock module by
`∑ a, R a c L a d + (n / 2) δ c d`. -/
theorem fockColHom_single (c d : I') :
    fockColHom K ε ε' (single c d 1) =
      ∑ a : I, oscRaise K (IsEvenPair ε ε') (a, c) * oscLower K (IsEvenPair ε ε') (a, d) +
        if c = d then (Fintype.card I / 2 : K) • 1 else 0 := by
  rw [fockColHom, glTraceTwistHom_apply, LieHom.comp_apply, glOneKronecker_single, map_sum]
  simp only [oscillatorHom_single, one_smul]
  split_ifs with hcd
  · simp [hcd]
  · simp [hcd]

/-- **The actions of `gl I` and `gl I'` on the Fock module commute.** Both come from the
oscillator representation of `gl (I × I')`, along the embeddings `A ↦ A ⊗ 1` and `B ↦ 1 ⊗ B`,
whose images commute. -/
theorem commute_fockRowHom_fockColHom (A : Matrix I I K) (B : Matrix I' I' K) :
    Commute (fockRowHom K ε ε' A) (fockColHom K ε ε' B) := by
  have h' : Commute (oscillatorHom K (IsEvenPair ε ε') (glBlockDiagonal K I I' A))
      (oscillatorHom K (IsEvenPair ε ε') (glOneKronecker K I I' B)) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie,
      (commute_iff_lie_eq).1 (commute_glBlockDiagonal_glOneKronecker A B), map_zero]
  simp only [fockRowHom, fockColHom, glTraceTwistHom_apply, LieHom.comp_apply]
  exact (h'.add_right (Commute.smul_right (Commute.one_right _) _)).add_left
    (Commute.smul_left (Commute.one_left _) _)

/-! ### Exchanging the two members of the pair -/

/-- **Exchanging the two members of the pair, columns to rows.** Renaming each variable `z a c`
as `z c a` carries the action of `gl I'` on the Fock module of `(ε, ε')` to the action of `gl I'`
on the rows of the Fock module of `(ε', ε)`. -/
theorem rename_swap_fockColHom (B : Matrix I' I' K) (P : MvPolynomial (I × I') K) :
    rename Prod.swap (fockColHom K ε ε' B P) = fockRowHom K ε' ε B (rename Prod.swap P) := by
  induction B using Matrix.induction_on' with
  | h_zero => simp
  | h_add B B' hB hB' => simp only [map_add, LinearMap.add_apply, hB, hB']
  | h_std_basis c d x =>
    -- Write `E c d x` as `x • E c d 1` (`Matrix.smul_single`) to use the matrix unit formulas.
    rw [← mul_one x, ← smul_eq_mul, ← smul_single, map_smul, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, map_smul, fockColHom_single, fockRowHom_single]
    congr 1
    simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum, mul_apply_eq_comp,
      rename_oscRaise Prod.swap_injective isEvenPair_swap,
      rename_oscLower Prod.swap_injective isEvenPair_swap, Prod.swap_prod_mk]
    split_ifs <;> simp

/-- **Exchanging the two members of the pair, rows to columns.** Renaming each variable `z a c`
as `z c a` carries the action of `gl I` on the Fock module of `(ε, ε')` to the action of `gl I`
on the columns of the Fock module of `(ε', ε)`. -/
theorem rename_swap_fockRowHom (A : Matrix I I K) (P : MvPolynomial (I × I') K) :
    rename Prod.swap (fockRowHom K ε ε' A P) = fockColHom K ε' ε A (rename Prod.swap P) := by
  -- Apply `TauCeti.rename_swap_fockColHom` to the exchanged pair; renaming twice is the identity.
  have h := rename_swap_fockColHom (ε := ε') (ε' := ε) A (rename Prod.swap P)
  rw [rename_rename, Prod.swap_swap_eq, rename_id_apply] at h
  rw [← h, rename_rename, Prod.swap_swap_eq, rename_id_apply]

/-! ### The compact parts: weights and degrees -/

/-- **The weight of the vacuum for the rows.** The diagonal matrix unit `E a a` multiplies `1`
by half the number of columns of the sign of `a` minus half the number of the other sign: by
`(r - s) / 2` for `a ∈ I₊` and by `(s - r) / 2` for `a ∈ I₋`. -/
theorem fockRowHom_single_self_one [NeZero (2 : K)] (a : I) :
    fockRowHom K ε ε' (single a a 1) 1 =
      (((#{c | ε a = ε' c} : K) - #{c | ε a ≠ ε' c}) / 2) • 1 := by
  have h (c : I') : (if IsEvenPair ε ε' (a, c) then (0 : MvPolynomial (I × I') K) else -1) =
      (if ε a = ε' c then (0 : K) else -1) • 1 := by
    split_ifs <;> simp_all [isEvenPair_iff]
  rw [fockRowHom_single]
  simp only [↓reduceIte, LinearMap.add_apply, LinearMap.sum_apply,
    oscRaise_mul_oscLower_self_one, LinearMap.smul_apply, one_apply_eq_self, h, ← sum_smul,
    ← add_smul]
  -- `n' / 2` and `-1` for each column of the other sign give half the difference of the counts.
  congr 1
  have h_card := card_filter_add_card_filter_not (s := univ) (fun c ↦ ε a = ε' c)
  rw [card_univ] at h_card
  simp only [sum_ite, sum_const_zero, sum_const, zero_add, nsmul_eq_mul, mul_neg, mul_one]
  rw [← h_card]
  push_cast
  field_simp
  ring

/-- **The vacuum is killed by the compact off-diagonal matrix units of the rows.** -/
theorem fockRowHom_single_one_of_ne {a b : I} (hab : a ≠ b) (h : ε a = ε b) :
    fockRowHom K ε ε' (single a b 1) 1 = 0 := by
  rw [fockRowHom_single]
  simp only [hab, ↓reduceIte, add_zero, LinearMap.sum_apply]
  exact sum_eq_zero fun c _ ↦ oscRaise_mul_oscLower_one_of_ne (by simp [hab])
    (isEvenPair_iff_of_eq h c)

/-- **Monomials are weight vectors for the rows.** The diagonal matrix unit `E a a` multiplies a
monomial `z ^ m` by `n' / 2 + ∑ c, ±m a c`, where an odd variable contributes
`-(m a c + 1)` in place of `m a c`. -/
theorem fockRowHom_single_self_monomial (a : I) (m : I × I' →₀ ℕ) (r : K) :
    fockRowHom K ε ε' (single a a 1) (monomial m r) =
      ((Fintype.card I' / 2 : K) +
        ∑ c, if ε a = ε' c then (m (a, c) : K) else -((m (a, c) : K) + 1)) • monomial m r := by
  rw [fockRowHom_single]
  simp only [↓reduceIte, LinearMap.add_apply, LinearMap.sum_apply,
    oscRaise_mul_oscLower_monomial, isEvenPair_iff, LinearMap.smul_apply, one_apply_eq_self,
    add_smul, sum_smul]
  rw [add_comm]

/-- **The compact matrix units of the rows preserve the degree.** -/
theorem fockRowHom_single_mem_homogeneousSubmodule {a b : I} (h : ε a = ε b) {d : ℕ}
    {P : MvPolynomial (I × I') K} (hP : P ∈ homogeneousSubmodule (I × I') K d) :
    fockRowHom K ε ε' (single a b 1) P ∈ homogeneousSubmodule (I × I') K d := by
  rw [fockRowHom_single, LinearMap.add_apply, LinearMap.sum_apply]
  refine add_mem (sum_mem fun c _ ↦
    oscRaise_mul_oscLower_mem_homogeneousSubmodule (isEvenPair_iff_of_eq h c) hP) ?_
  split_ifs
  · exact Submodule.smul_mem _ _ hP
  · exact zero_mem _

/-- **The weight of the vacuum for the columns.** The diagonal matrix unit `E c c` multiplies
`1` by half the number of rows of the sign of `c` minus half the number of the other sign: by
`(p - q) / 2` for `c ∈ I'₊` and by `(q - p) / 2` for `c ∈ I'₋`. -/
theorem fockColHom_single_self_one [NeZero (2 : K)] (c : I') :
    fockColHom K ε ε' (single c c 1) 1 =
      (((#{a | ε a = ε' c} : K) - #{a | ε a ≠ ε' c}) / 2) • 1 := by
  -- Exchange the two members of the pair and use the weight of the vacuum for the rows.
  apply rename_injective _ Prod.swap_injective
  rw [rename_swap_fockColHom, map_one, fockRowHom_single_self_one, map_smul, map_one]
  simp_rw [@eq_comm _ (ε' c), @ne_comm _ (ε' c)]

/-- **The vacuum is killed by the compact off-diagonal matrix units of the columns.** -/
theorem fockColHom_single_one_of_ne {c d : I'} (hcd : c ≠ d) (h : ε' c = ε' d) :
    fockColHom K ε ε' (single c d 1) 1 = 0 := by
  rw [fockColHom_single]
  simp only [hcd, ↓reduceIte, add_zero, LinearMap.sum_apply]
  exact sum_eq_zero fun a _ ↦ oscRaise_mul_oscLower_one_of_ne (by simp [hcd])
    (isEvenPair_iff_of_eq' h a)

/-- **Monomials are weight vectors for the columns.** The diagonal matrix unit `E c c` multiplies
a monomial `z ^ m` by `n / 2 + ∑ a, ±m a c`, where an odd variable contributes `-(m a c + 1)` in
place of `m a c`. -/
theorem fockColHom_single_self_monomial (c : I') (m : I × I' →₀ ℕ) (r : K) :
    fockColHom K ε ε' (single c c 1) (monomial m r) =
      ((Fintype.card I / 2 : K) +
        ∑ a, if ε a = ε' c then (m (a, c) : K) else -((m (a, c) : K) + 1)) • monomial m r := by
  rw [fockColHom_single]
  simp only [↓reduceIte, LinearMap.add_apply, LinearMap.sum_apply,
    oscRaise_mul_oscLower_monomial, isEvenPair_iff, LinearMap.smul_apply, one_apply_eq_self,
    add_smul, sum_smul]
  rw [add_comm]

/-- **The compact matrix units of the columns preserve the degree.** -/
theorem fockColHom_single_mem_homogeneousSubmodule {c d : I'} (h : ε' c = ε' d) {e : ℕ}
    {P : MvPolynomial (I × I') K} (hP : P ∈ homogeneousSubmodule (I × I') K e) :
    fockColHom K ε ε' (single c d 1) P ∈ homogeneousSubmodule (I × I') K e := by
  rw [fockColHom_single, LinearMap.add_apply, LinearMap.sum_apply]
  refine add_mem (sum_mem fun a _ ↦
    oscRaise_mul_oscLower_mem_homogeneousSubmodule (isEvenPair_iff_of_eq' h a) hP) ?_
  split_ifs
  · exact Submodule.smul_mem _ _ hP
  · exact zero_mem _

/-! ### Weights bound the degree -/

/-- **Weights bound the degree, for the rows.** Let `P ≠ 0` be homogeneous of degree `d` and a
weight vector for the diagonal matrix units of `gl I`, of weight `ν a` relative to the weight of
the vacuum. Then `∑ |ν a| ≤ d`. So a `K`-type of highest weight `μ` occurs only in degrees at
least `∑_{a ∈ I₊} |μ a - (r - s) / 2| + ∑_{a ∈ I₋} |μ a + (r - s) / 2|`. -/
theorem sum_abs_le_of_fockRowHom_single_self [CharZero K] {d : ℕ} {P : MvPolynomial (I × I') K}
    (hP : P ∈ homogeneousSubmodule (I × I') K d) (hP₀ : P ≠ 0) (ν : I → ℤ)
    (hν : ∀ a, fockRowHom K ε ε' (single a a 1) P =
      (((#{c | ε a = ε' c} : K) - #{c | ε a ≠ ε' c}) / 2 + ν a) • P) :
    ∑ a, |ν a| ≤ d := by
  obtain ⟨m, hm⟩ := ne_zero_iff.1 hP₀
  -- On the monomial `z ^ m` of `P`, the weight relative to the vacuum is `∑ c, ±m a c`.
  have h_weight (a : I) :
      ∑ c, (if ε a = ε' c then (m (a, c) : ℤ) else -(m (a, c) : ℤ)) = ν a := by
    -- The weight of the vacuum, read off the monomial `z ^ 0 = 1`.
    have h_vac : (Fintype.card I' / 2 : K) + ∑ c, (if ε a = ε' c then 0 else -1 : K) =
        ((#{c | ε a = ε' c} : K) - #{c | ε a ≠ ε' c}) / 2 := by
      have h := fockRowHom_single_self_monomial (ε := ε) (ε' := ε') a 0 (1 : K)
      rw [← C_apply, map_one, fockRowHom_single_self_one] at h
      have h' := smul_left_injective K one_ne_zero h
      simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add] at h'
      exact h'.symm
    have h := coeff_apply_eq_mul_of_apply_monomial
      (fockRowHom_single_self_monomial (ε := ε) (ε' := ε') a) P m
    rw [hν, smul_eq_C_mul, coeff_C_mul] at h
    have h' := mul_right_cancel₀ hm h
    rw [← h_vac] at h'
    have h_split : ∑ c, (if ε a = ε' c then (m (a, c) : K) else -((m (a, c) : K) + 1)) =
        ∑ c, (if ε a = ε' c then (m (a, c) : K) else -(m (a, c) : K)) +
          ∑ c, (if ε a = ε' c then 0 else -1 : K) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun c _ ↦ by split_ifs <;> ring
    rw [h_split] at h'
    exact_mod_cast (by linear_combination -h' :
      ∑ c, (if ε a = ε' c then (m (a, c) : K) else -(m (a, c) : K)) = ν a)
  have h_le (a : I) : |ν a| ≤ ∑ c, (m (a, c) : ℤ) := by
    rw [← h_weight a]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ ↦ ?_)
    split_ifs <;> simp
  have h_deg : ∑ a, ∑ c, m (a, c) = d := by
    rw [← (mem_homogeneousSubmodule _ _).1 hP hm]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_prod_type]
  calc ∑ a, |ν a| ≤ ∑ a, ∑ c, (m (a, c) : ℤ) := sum_le_sum fun a _ ↦ h_le a
    _ = d := by exact_mod_cast h_deg

/-- **Weights bound the degree, for the columns.** Let `P ≠ 0` be homogeneous of degree `d` and
a weight vector for the diagonal matrix units of `gl I'`, of weight `ν c` relative to the weight
of the vacuum. Then `∑ |ν c| ≤ d`. -/
theorem sum_abs_le_of_fockColHom_single_self [CharZero K] {d : ℕ} {P : MvPolynomial (I × I') K}
    (hP : P ∈ homogeneousSubmodule (I × I') K d) (hP₀ : P ≠ 0) (ν : I' → ℤ)
    (hν : ∀ c, fockColHom K ε ε' (single c c 1) P =
      (((#{a | ε a = ε' c} : K) - #{a | ε a ≠ ε' c}) / 2 + ν c) • P) :
    ∑ c, |ν c| ≤ d := by
  -- Exchange the two members of the pair and use the bound for the rows.
  refine sum_abs_le_of_fockRowHom_single_self (ε := ε') (ε' := ε) (P := rename Prod.swap P)
    ((mem_homogeneousSubmodule _ _).2 ((mem_homogeneousSubmodule _ _).1 hP).rename_isHomogeneous)
    ((map_ne_zero_iff _ (rename_injective _ Prod.swap_injective)).2 hP₀) ν fun c ↦ ?_
  rw [← rename_swap_fockColHom, hν, map_smul]
  simp_rw [@eq_comm _ (ε' c), @ne_comm _ (ε' c)]

/-! ### The noncompact parts -/

/-- **The noncompact matrix units of the rows split into a degree-raising and a degree-lowering
part.** For `ε a ≠ ε b`, `E a b` acts by multiplication by `TauCeti.fockRowRaise a b` minus
`TauCeti.fockRowLower a b`. -/
theorem fockRowHom_single_of_ne {a b : I} (h : ε a ≠ ε b) (P : MvPolynomial (I × I') K) :
    fockRowHom K ε ε' (single a b 1) P =
      fockRowRaise K ε ε' a b * P - fockRowLower K ε ε' a b P := by
  have hab : a ≠ b := fun hab ↦ h (hab ▸ rfl)
  rw [fockRowHom_single]
  simp only [hab, ↓reduceIte, add_zero]
  rw [LinearMap.sum_apply, fockRowRaise_def, fockRowLower_apply, sum_mul, sum_filter, sum_filter,
    ← sum_sub_distrib]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [oscRaise_mul_oscLower_of_not_iff (not_isEvenPair_iff_of_ne h c)]
  simp [isEvenPair_iff]

/-- **The noncompact matrix units of the columns split into a degree-raising and a
degree-lowering part.** For `ε' c ≠ ε' d`, `E c d` acts by multiplication by
`TauCeti.fockColRaise c d` minus `TauCeti.fockColLower c d`. -/
theorem fockColHom_single_of_ne {c d : I'} (h : ε' c ≠ ε' d) (P : MvPolynomial (I × I') K) :
    fockColHom K ε ε' (single c d 1) P =
      fockColRaise K ε ε' c d * P - fockColLower K ε ε' c d P := by
  have hcd : c ≠ d := fun hcd ↦ h (hcd ▸ rfl)
  rw [fockColHom_single]
  simp only [hcd, ↓reduceIte, add_zero]
  rw [LinearMap.sum_apply, fockColRaise_def, fockColLower_apply, sum_mul, sum_filter, sum_filter,
    ← sum_sub_distrib]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [oscRaise_mul_oscLower_of_not_iff (not_isEvenPair_iff_of_ne' h a)]
  simp [isEvenPair_iff]

variable (K ε ε') in
/-- **The action of `gl I × gl I'` on the Fock module**: `(A, B)` acts by the sum of the two
commuting actions `TauCeti.fockRowHom` and `TauCeti.fockColHom`. -/
noncomputable def fockHom :
    Matrix I I K × Matrix I' I' K →ₗ⁅K⁆ Module.End K (MvPolynomial (I × I') K) where
  __ := (fockRowHom K ε ε').toLinearMap.coprod (fockColHom K ε ε').toLinearMap
  map_lie' {x y} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coprod_apply,
      LieHom.coe_toLinearMap, LieAlgebra.Prod.bracket_apply, LieHom.map_lie, lie_add, add_lie,
      (commute_iff_lie_eq).1 (commute_fockRowHom_fockColHom _ _),
      (commute_iff_lie_eq).1 (commute_fockRowHom_fockColHom _ _).symm, add_zero, zero_add]

@[simp]
theorem fockHom_apply (x : Matrix I I K × Matrix I' I' K) :
    fockHom K ε ε' x = fockRowHom K ε ε' x.1 + fockColHom K ε ε' x.2 :=
  (rfl)

end TauCeti
