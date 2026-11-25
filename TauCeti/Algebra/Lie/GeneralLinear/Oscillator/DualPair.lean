/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.GeneralLinear.BlockDiagonal
public import TauCeti.Algebra.Lie.GeneralLinear.Oscillator.Basic
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

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
vectors, in the normalisation of the roadmap target below. Both actions are the oscillator
representation of `gl (I × I')` restricted along the embeddings `A ↦ A ⊗ 1` and `B ↦ 1 ⊗ B`,
which commute; the half-integral shifts are the trace characters that make the vacuum have the
right weight.

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

This is route step (1) of target 3.46a of the roadmap
`RiemannHypothesisForDirichletLFunctions/ThetaKernelsForUnitaryDualPairs`.

* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535--552.
* M. Kashiwara and M. Vergne, *On the Segal–Shale–Weil representations and harmonic
  polynomials*, Invent. Math. 44 (1978), 1--47.
* The oscillator actions are adapted from `New.FockDualPair.oscRows` and
  `New.FockDualPair.swap_oscRows_E` in `src/Lib/DiscreteSeries/Theta/FockDualPair.lean` of
  grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), and
  the oscillator operators from `New.Fock.raiseOp` and `New.Fock.lowerOp` in
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

variable (K : Type*) [Field K] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  (ε : I → Bool) (ε' : I' → Bool)

/-! ### Shifting a representation of `gl ι` by a multiple of the trace -/

section TraceShift

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra K A]

variable {K} in
/-- A representation of `gl ι` plus a multiple `c • trace` of the trace character, which is
again a representation since the trace kills commutators. -/
private noncomputable def addTraceShift (f : Matrix ι ι K →ₗ⁅K⁆ A) (c : K) :
    Matrix ι ι K →ₗ⁅K⁆ A where
  toFun X := f X + (c * X.trace) • 1
  map_add' X Y := by
    simp only [map_add, trace_add, mul_add, add_smul]
    abel
  map_smul' r X := by
    simp only [map_smul, trace_smul, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul,
      mul_left_comm r c]
  map_lie' {X Y} := by
    rw [LieAlgebra.matrix_trace_commutator_zero, mul_zero, zero_smul, add_zero, LieHom.map_lie]
    simp only [LieRing.of_associative_ring_bracket, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
    module

private theorem addTraceShift_apply (f : Matrix ι ι K →ₗ⁅K⁆ A) (c : K) (X : Matrix ι ι K) :
    addTraceShift f c X = f X + (c * X.trace) • 1 :=
  (rfl)

end TraceShift

/-! ### The two actions -/

/-- The embedding `A ↦ 1 ⊗ A` of `gl I'` into `gl (I × I')`. -/
private noncomputable def colEmbedding : Matrix I' I' K →ₗ⁅K⁆ Matrix (I × I') (I × I') K :=
  (reindexLieEquiv (Equiv.prodComm I' I)).toLieHom.comp (glBlockDiagonal K I' I)

private theorem colEmbedding_apply (B : Matrix I' I' K) :
    colEmbedding (I := I) K B = (1 : Matrix I I K) ⊗ₖ B := by
  simp [colEmbedding, one_kronecker]

private theorem glBlockDiagonal_eq_kronecker (A : Matrix I I K) :
    glBlockDiagonal K I I' A = A ⊗ₖ (1 : Matrix I' I' K) := by
  simp [kronecker_one]

/-- **The action of `gl I` on the Fock module**: the matrix unit `E a b` acts by
`∑ c, R a c L b c + (n' / 2) δ a b`, where `n'` is the number of elements of `I'`. -/
noncomputable def fockRowHom : Matrix I I K →ₗ⁅K⁆ Module.End K (MvPolynomial (I × I') K) :=
  addTraceShift ((oscillatorHom K (IsEvenPair ε ε')).comp (glBlockDiagonal K I I'))
    (Fintype.card I' / 2)

/-- **The action of `gl I'` on the Fock module**: the matrix unit `E c d` acts by
`∑ a, R a c L a d + (n / 2) δ c d`, where `n` is the number of elements of `I`. -/
noncomputable def fockColHom : Matrix I' I' K →ₗ⁅K⁆ Module.End K (MvPolynomial (I × I') K) :=
  addTraceShift ((oscillatorHom K (IsEvenPair ε ε')).comp (colEmbedding K))
    (Fintype.card I / 2)

variable {K ε ε'}

/-- The matrix unit `E a b` of `gl I` acts on the Fock module by
`∑ c, R a c L b c + (n' / 2) δ a b`. -/
theorem fockRowHom_single (a b : I) :
    fockRowHom K ε ε' (single a b 1) =
      ∑ c : I', oscRaise K (IsEvenPair ε ε') (a, c) * oscLower K (IsEvenPair ε ε') (b, c) +
        if a = b then (Fintype.card I' / 2 : K) • 1 else 0 := by
  rw [fockRowHom, addTraceShift_apply, LieHom.comp_apply, glBlockDiagonal_single, map_sum]
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
  have h : colEmbedding (I := I) K (single c d 1) = ∑ a : I, single (a, c) (a, d) (1 : K) := by
    rw [colEmbedding_apply]
    ext ⟨a, c'⟩ ⟨b, d'⟩
    rw [Matrix.sum_apply, kronecker_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single a (fun x _ hx ↦ by simp [hx]) (by simp)]
      simp [single_apply]
    · simp only [hab, ↓reduceIte, zero_mul]
      rw [Finset.sum_eq_zero fun x _ ↦ ?_]
      simp only [single_apply, Prod.mk.injEq]
      grind
  rw [fockColHom, addTraceShift_apply, LieHom.comp_apply, h, map_sum]
  simp only [oscillatorHom_single, one_smul]
  split_ifs with hcd
  · simp [hcd]
  · simp [hcd]

/-- **The actions of `gl I` and `gl I'` on the Fock module commute.** Both come from the
oscillator representation of `gl (I × I')`, along the embeddings `A ↦ A ⊗ 1` and `B ↦ 1 ⊗ B`,
whose images commute. -/
theorem commute_fockRowHom_fockColHom (A : Matrix I I K) (B : Matrix I' I' K) :
    Commute (fockRowHom K ε ε' A) (fockColHom K ε ε' B) := by
  have h : Commute (glBlockDiagonal K I I' A) (colEmbedding K B) := by
    rw [glBlockDiagonal_eq_kronecker, colEmbedding_apply, Commute, SemiconjBy,
      ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, one_mul, mul_one, one_mul]
  have h' : Commute (oscillatorHom K (IsEvenPair ε ε') (glBlockDiagonal K I I' A))
      (oscillatorHom K (IsEvenPair ε ε') (colEmbedding K B)) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, (commute_iff_lie_eq).1 h, map_zero]
  simp only [fockRowHom, fockColHom, addTraceShift_apply, LieHom.comp_apply]
  exact (h'.add_right (Commute.smul_right (Commute.one_right _) _)).add_left
    (Commute.smul_left (Commute.one_left _) _)

/-! ### The compact parts: weights and degrees -/

omit [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] in
/-- The variables `z a c` and `z b c` have the same parity when `a` and `b` have the same sign. -/
private theorem isEvenPair_iff_of_eq {a b : I} (h : ε a = ε b) (c : I') :
    IsEvenPair ε ε' (a, c) ↔ IsEvenPair ε ε' (b, c) := by
  simp [isEvenPair_iff, h]

omit [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] in
/-- The variables `z a c` and `z a d` have the same parity when `c` and `d` have the same sign. -/
private theorem isEvenPair_iff_of_eq' {c d : I'} (h : ε' c = ε' d) (a : I) :
    IsEvenPair ε ε' (a, c) ↔ IsEvenPair ε ε' (a, d) := by
  simp [isEvenPair_iff, h]

/-- In a sum over the variables of one row or column, `-1` for each odd variable and `n / 2`
in total give half the number of even variables minus half the number of odd ones. -/
private theorem half_card_add_sum_ite [NeZero (2 : K)] {α : Type*} [Fintype α] (q : α → Prop)
    [DecidablePred q] :
    (Fintype.card α / 2 : K) + ∑ x, (if q x then 0 else -1) =
      ((#{x | q x} : K) - #{x | ¬q x}) / 2 := by
  have h := card_filter_add_card_filter_not (s := univ) q
  rw [card_univ] at h
  simp only [sum_ite, sum_const_zero, sum_const, zero_add, nsmul_eq_mul, mul_neg, mul_one]
  rw [← h]
  push_cast
  field_simp
  ring

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
  rw [add_comm, half_card_add_sum_ite]

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
  have h (a : I) : (if IsEvenPair ε ε' (a, c) then (0 : MvPolynomial (I × I') K) else -1) =
      (if ε a = ε' c then (0 : K) else -1) • 1 := by
    split_ifs <;> simp_all [isEvenPair_iff]
  rw [fockColHom_single]
  simp only [↓reduceIte, LinearMap.add_apply, LinearMap.sum_apply,
    oscRaise_mul_oscLower_self_one, LinearMap.smul_apply, one_apply_eq_self, h, ← sum_smul,
    ← add_smul]
  rw [add_comm, half_card_add_sum_ite]

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

omit [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] in
/-- An operator that multiplies each monomial by a scalar depending on its exponent multiplies each
coefficient by the same scalar. -/
private theorem coeff_of_apply_monomial {ι : Type*} {f : Module.End K (MvPolynomial ι K)}
    {w : (ι →₀ ℕ) → K} (hf : ∀ m r, f (monomial m r) = w m • monomial m r)
    (P : MvPolynomial ι K) (m : ι →₀ ℕ) : (f P).coeff m = w m * P.coeff m := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  simp only [hf, coeff_sum, smul_monomial, MvPolynomial.coeff_monomial, smul_eq_mul]
  rw [sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.1 hm, mul_zero]

omit [DecidableEq I] [DecidableEq I'] in
/-- The exponent of a monomial of a homogeneous polynomial of degree `d` sums to `d`. -/
private theorem sum_sum_eq_of_mem_support {d : ℕ} {P : MvPolynomial (I × I') K}
    (hP : P ∈ homogeneousSubmodule (I × I') K d) {m : I × I' →₀ ℕ} (hm : m ∈ P.support) :
    ∑ a, ∑ c, m (a, c) = d := by
  rw [← (mem_homogeneousSubmodule _ _).1 hP (mem_support_iff.1 hm)]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_prod_type]

/-- If a sum of terms `±m x` over `x` equals `ν` in a field of characteristic zero, then
`|ν| ≤ ∑ m x`. -/
private theorem abs_le_sum_of_sum_ite_eq [CharZero K] {α : Type*} [Fintype α] (q : α → Prop)
    [DecidablePred q] (m : α → ℕ) (ν : ℤ)
    (h : ∑ x, (if q x then (m x : K) else -(m x : K)) = ν) : |ν| ≤ ∑ x, (m x : ℤ) := by
  have h' : ∑ x, (if q x then (m x : ℤ) else -(m x : ℤ)) = ν := by
    exact_mod_cast h
  rw [← h']
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
  split_ifs <;> simp

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
  have h_weight (a : I) :
      ∑ c, (if ε a = ε' c then (m (a, c) : K) else -(m (a, c) : K)) = ν a := by
    have h := coeff_of_apply_monomial (fockRowHom_single_self_monomial (ε := ε) (ε' := ε') a) P m
    rw [hν, smul_eq_C_mul, coeff_C_mul] at h
    have h' := mul_right_cancel₀ hm h
    rw [← half_card_add_sum_ite (K := K) (fun c ↦ ε a = ε' c)] at h'
    have h_split : ∑ c, (if ε a = ε' c then (m (a, c) : K) else -((m (a, c) : K) + 1)) =
        ∑ c, (if ε a = ε' c then (m (a, c) : K) else -(m (a, c) : K)) +
          ∑ c, (if ε a = ε' c then 0 else -1 : K) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun c _ ↦ by split_ifs <;> ring
    rw [h_split] at h'
    linear_combination -h'
  have h_le (a : I) : |ν a| ≤ ∑ c, (m (a, c) : ℤ) :=
    abs_le_sum_of_sum_ite_eq (K := K) (fun c ↦ ε a = ε' c) (fun c ↦ m (a, c)) (ν a) (h_weight a)
  calc ∑ a, |ν a| ≤ ∑ a, ∑ c, (m (a, c) : ℤ) := sum_le_sum fun a _ ↦ h_le a
    _ = d := by exact_mod_cast sum_sum_eq_of_mem_support hP (mem_support_iff.2 hm)

/-- **Weights bound the degree, for the columns.** Let `P ≠ 0` be homogeneous of degree `d` and
a weight vector for the diagonal matrix units of `gl I'`, of weight `ν c` relative to the weight
of the vacuum. Then `∑ |ν c| ≤ d`. -/
theorem sum_abs_le_of_fockColHom_single_self [CharZero K] {d : ℕ} {P : MvPolynomial (I × I') K}
    (hP : P ∈ homogeneousSubmodule (I × I') K d) (hP₀ : P ≠ 0) (ν : I' → ℤ)
    (hν : ∀ c, fockColHom K ε ε' (single c c 1) P =
      (((#{a | ε a = ε' c} : K) - #{a | ε a ≠ ε' c}) / 2 + ν c) • P) :
    ∑ c, |ν c| ≤ d := by
  obtain ⟨m, hm⟩ := ne_zero_iff.1 hP₀
  have h_weight (c : I') :
      ∑ a, (if ε a = ε' c then (m (a, c) : K) else -(m (a, c) : K)) = ν c := by
    have h := coeff_of_apply_monomial (fockColHom_single_self_monomial (ε := ε) (ε' := ε') c) P m
    rw [hν, smul_eq_C_mul, coeff_C_mul] at h
    have h' := mul_right_cancel₀ hm h
    rw [← half_card_add_sum_ite (K := K) (fun a ↦ ε a = ε' c)] at h'
    have h_split : ∑ a, (if ε a = ε' c then (m (a, c) : K) else -((m (a, c) : K) + 1)) =
        ∑ a, (if ε a = ε' c then (m (a, c) : K) else -(m (a, c) : K)) +
          ∑ a, (if ε a = ε' c then 0 else -1 : K) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun a _ ↦ by split_ifs <;> ring
    rw [h_split] at h'
    linear_combination -h'
  have h_le (c : I') : |ν c| ≤ ∑ a, (m (a, c) : ℤ) :=
    abs_le_sum_of_sum_ite_eq (K := K) (fun a ↦ ε a = ε' c) (fun a ↦ m (a, c)) (ν c) (h_weight c)
  calc ∑ c, |ν c| ≤ ∑ c, ∑ a, (m (a, c) : ℤ) := sum_le_sum fun c _ ↦ h_le c
    _ = ∑ a, ∑ c, (m (a, c) : ℤ) := sum_comm
    _ = d := by exact_mod_cast sum_sum_eq_of_mem_support hP (mem_support_iff.2 hm)

/-! ### The noncompact parts: raising and lowering components -/

omit [Fintype I] [DecidableEq I] [DecidableEq I'] in
variable (K ε ε') in
/-- The degree-raising component of the noncompact matrix unit `E a b` of the rows
(`ε a ≠ ε b`): the quadratic polynomial `∑ z a c z b c` over the columns `c` of the sign of `a`,
by which it multiplies. -/
noncomputable def fockRowRaise (a b : I) : MvPolynomial (I × I') K :=
  ∑ c with ε a = ε' c, X (a, c) * X (b, c)

omit [Fintype I] [DecidableEq I] [DecidableEq I'] in
variable (K ε ε') in
/-- The degree-lowering component of the noncompact matrix unit `E a b` of the rows
(`ε a ≠ ε b`), up to sign: the operator `∑ ∂ ∂ / ∂ z a c ∂ z b c` over the columns `c` of the
sign of `b`. -/
noncomputable def fockRowLower (a b : I) : Module.End K (MvPolynomial (I × I') K) :=
  ∑ c with ε a ≠ ε' c, (pderiv (a, c)).toLinearMap * (pderiv (b, c)).toLinearMap

omit [DecidableEq I] [Fintype I'] [DecidableEq I'] in
variable (K ε ε') in
/-- The degree-raising component of the noncompact matrix unit `E c d` of the columns
(`ε' c ≠ ε' d`): the quadratic polynomial `∑ z a c z a d` over the rows `a` of the sign of `c`,
by which it multiplies. -/
noncomputable def fockColRaise (c d : I') : MvPolynomial (I × I') K :=
  ∑ a with ε a = ε' c, X (a, c) * X (a, d)

omit [DecidableEq I] [Fintype I'] [DecidableEq I'] in
variable (K ε ε') in
/-- The degree-lowering component of the noncompact matrix unit `E c d` of the columns
(`ε' c ≠ ε' d`), up to sign: the operator `∑ ∂ ∂ / ∂ z a c ∂ z a d` over the rows `a` of the sign
of `d`. -/
noncomputable def fockColLower (c d : I') : Module.End K (MvPolynomial (I × I') K) :=
  ∑ a with ε a ≠ ε' c, (pderiv (a, c)).toLinearMap * (pderiv (a, d)).toLinearMap

omit [Fintype I] [DecidableEq I] [DecidableEq I'] in
theorem fockRowRaise_def (a b : I) :
    fockRowRaise K ε ε' a b = ∑ c with ε a = ε' c, X (a, c) * X (b, c) :=
  (rfl)

omit [Fintype I] [DecidableEq I] [DecidableEq I'] in
theorem fockRowLower_apply (a b : I) (P : MvPolynomial (I × I') K) :
    fockRowLower K ε ε' a b P = ∑ c with ε a ≠ ε' c, pderiv (a, c) (pderiv (b, c) P) := by
  simp [fockRowLower, LinearMap.sum_apply]

omit [DecidableEq I] [Fintype I'] [DecidableEq I'] in
theorem fockColRaise_def (c d : I') :
    fockColRaise K ε ε' c d = ∑ a with ε a = ε' c, X (a, c) * X (a, d) :=
  (rfl)

omit [DecidableEq I] [Fintype I'] [DecidableEq I'] in
theorem fockColLower_apply (c d : I') (P : MvPolynomial (I × I') K) :
    fockColLower K ε ε' c d P = ∑ a with ε a ≠ ε' c, pderiv (a, c) (pderiv (a, d) P) := by
  simp [fockColLower, LinearMap.sum_apply]

private theorem not_eq_iff_eq_of_ne {x y z : Bool} (h : x ≠ y) : ¬(x = z ↔ y = z) := by
  cases x <;> cases y <;> cases z <;> simp_all

private theorem not_eq_iff_eq_of_ne' {x y z : Bool} (h : x ≠ y) : ¬(z = x ↔ z = y) := by
  cases x <;> cases y <;> cases z <;> simp_all

omit [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] in
/-- A term `R i L j` for variables of opposite parity is multiplication by `z i z j` if `i` is
even, and `-∂ ∂ / ∂ z i ∂ z j` if `i` is odd. -/
private theorem oscRaise_mul_oscLower_of_not_iff {p : I × I' → Prop} [DecidablePred p]
    {i j : I × I'} (h : ¬(p i ↔ p j)) (P : MvPolynomial (I × I') K) :
    (oscRaise K p i * oscLower K p j) P =
      (if p i then X i * X j * P else 0) - if p i then 0 else pderiv i (pderiv j P) := by
  by_cases hi : p i
  · have hj : ¬p j := fun hj ↦ h (iff_of_true hi hj)
    simp [hi, hj, mul_assoc]
  · have hj : p j := by tauto
    simp [hi, hj]

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
  rw [oscRaise_mul_oscLower_of_not_iff (by simpa [isEvenPair_iff] using not_eq_iff_eq_of_ne h)]
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
  rw [oscRaise_mul_oscLower_of_not_iff (by simpa [isEvenPair_iff] using not_eq_iff_eq_of_ne' h)]
  simp [isEvenPair_iff]

omit [Fintype I] [DecidableEq I] [DecidableEq I'] in
/-- The degree-raising component of a noncompact matrix unit of the rows is homogeneous of
degree two. -/
theorem isHomogeneous_fockRowRaise (a b : I) : (fockRowRaise K ε ε' a b).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ (isHomogeneous_X K _).mul (isHomogeneous_X K _)

omit [DecidableEq I] [Fintype I'] [DecidableEq I'] in
/-- The degree-raising component of a noncompact matrix unit of the columns is homogeneous of
degree two. -/
theorem isHomogeneous_fockColRaise (c d : I') : (fockColRaise K ε ε' c d).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ (isHomogeneous_X K _).mul (isHomogeneous_X K _)

omit [Fintype I] [DecidableEq I] [DecidableEq I'] in
/-- The degree-lowering component of a noncompact matrix unit of the rows lowers the degree by
two. -/
theorem fockRowLower_mem_homogeneousSubmodule (a b : I) {d : ℕ} {P : MvPolynomial (I × I') K}
    (hP : P ∈ homogeneousSubmodule (I × I') K d) :
    fockRowLower K ε ε' a b P ∈ homogeneousSubmodule (I × I') K (d - 2) := by
  rw [fockRowLower_apply]
  exact sum_mem fun c _ ↦ by
    simpa [Nat.sub_sub] using
      (IsHomogeneous.pderiv (IsHomogeneous.pderiv ((mem_homogeneousSubmodule _ _).1 hP)))

omit [DecidableEq I] [Fintype I'] [DecidableEq I'] in
/-- The degree-lowering component of a noncompact matrix unit of the columns lowers the degree
by two. -/
theorem fockColLower_mem_homogeneousSubmodule (c d : I') {e : ℕ} {P : MvPolynomial (I × I') K}
    (hP : P ∈ homogeneousSubmodule (I × I') K e) :
    fockColLower K ε ε' c d P ∈ homogeneousSubmodule (I × I') K (e - 2) := by
  rw [fockColLower_apply]
  exact sum_mem fun a _ ↦ by
    simpa [Nat.sub_sub] using
      (IsHomogeneous.pderiv (IsHomogeneous.pderiv ((mem_homogeneousSubmodule _ _).1 hP)))

/-! ### Exchanging the two members of the pair -/

omit [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] in
private theorem isEvenPair_swap (x : I × I') :
    IsEvenPair ε' ε x.swap ↔ IsEvenPair ε ε' x := by
  simp [isEvenPair_iff, eq_comm]

/-- **Exchanging the two members of the pair, columns to rows.** Renaming each variable `z a c`
as `z c a` carries the action of `gl I'` on the Fock module of `(ε, ε')` to the action of `gl I'`
on the rows of the Fock module of `(ε', ε)`. -/
theorem rename_swap_fockColHom (B : Matrix I' I' K) (P : MvPolynomial (I × I') K) :
    rename Prod.swap (fockColHom K ε ε' B P) = fockRowHom K ε' ε B (rename Prod.swap P) := by
  induction B using Matrix.induction_on' with
  | h_zero => simp
  | h_add B B' hB hB' => simp only [map_add, LinearMap.add_apply, hB, hB']
  | h_std_basis c d x =>
    rw [show single _ _ x = x • single _ _ (1 : K) by rw [smul_single, smul_eq_mul, mul_one],
      map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      map_smul, fockColHom_single, fockRowHom_single]
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
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A A' hA hA' => simp only [map_add, LinearMap.add_apply, hA, hA']
  | h_std_basis a b x =>
    rw [show single _ _ x = x • single _ _ (1 : K) by rw [smul_single, smul_eq_mul, mul_one],
      map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      map_smul, fockRowHom_single, fockColHom_single]
    congr 1
    simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum, mul_apply_eq_comp,
      rename_oscRaise Prod.swap_injective isEvenPair_swap,
      rename_oscLower Prod.swap_injective isEvenPair_swap, Prod.swap_prod_mk]
    split_ifs <;> simp

variable (K ε ε') in
/-- **The action of `gl I × gl I'` on the Fock module**: `(A, B)` acts by the sum of the two
commuting actions `TauCeti.fockRowHom` and `TauCeti.fockColHom`. -/
noncomputable def fockHom :
    Matrix I I K × Matrix I' I' K →ₗ⁅K⁆ Module.End K (MvPolynomial (I × I') K) where
  toFun x := fockRowHom K ε ε' x.1 + fockColHom K ε ε' x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by simp [smul_add]
  map_lie' {x y} := by
    simp only [LieAlgebra.Prod.bracket_apply, LieHom.map_lie, lie_add, add_lie,
      (commute_iff_lie_eq).1 (commute_fockRowHom_fockColHom _ _),
      (commute_iff_lie_eq).1 (commute_fockRowHom_fockColHom _ _).symm, add_zero, zero_add]

@[simp]
theorem fockHom_apply (x : Matrix I I K × Matrix I' I' K) :
    fockHom K ε ε' x = fockRowHom K ε ε' x.1 + fockColHom K ε ε' x.2 :=
  (rfl)

end TauCeti
