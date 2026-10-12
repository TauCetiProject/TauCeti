/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Cohomology
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Prepend

/-!
# An `A∞` algebra as a right module over itself

An `A∞` algebra `A` is a right `A∞` module over itself, the free module of rank one, whose
operations are those of the algebra: `m_n^A(x, a₁, …, a_{n-1}) = m_n(x, a₁, …, a_{n-1})`.

The construction is made on the suspended bar side.  Concatenation `x ⊗ w ↦ x w`, the uncurried
`TauCeti.TensorWords.prepend`, maps the cofree right bar comodule `sA ⊗ Tᶜ(sA)` to the reduced bar
construction `ReducedTensorWords R A`.  The Taylor map of the module is the Taylor map of the
algebra read through concatenation.  Concatenation then carries the coderivation this Taylor map
generates over the bar differential of `A` to the bar differential of `A` itself
(`TauCeti.AInfinityAlgebra.lift_prepend_comp_barDifferential_toRightModule`): a block collapsed by
the module structure either starts at the module input or lies in the word to its right, and the
Koszul twist of the module input is the sign with which the bar differential passes the first
letter.  The module square-zero law is therefore the square-zero law of the algebra.

## Main definitions

* `TauCeti.AInfinityAlgebra.toRightModule`: an `A∞` algebra as a right module over itself.

## Main results

* `TauCeti.AInfinityAlgebra.lift_prepend_comp_barDifferential_toRightModule`: concatenation
  intertwines the module bar differential with the algebra bar differential.
* `TauCeti.AInfinityAlgebra.m_toRightModule`: the unsuspended module operations are the algebra
  operations, with the module input first.
* `TauCeti.AInfinityAlgebra.differential_toRightModule`: in particular, the module differential is
  the differential of the algebra.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.1.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped BigOperators TensorProduct

namespace TauCeti

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

namespace AInfinityAlgebra

open TensorWords InternalGrading

variable (AA : AInfinityAlgebra R A)

/-- The Taylor map of the algebra, read on `sA ⊗ Tᶜ(sA)` through concatenation, has degree one. -/
private theorem isHomogeneous_taylor_comp_lift_prepend :
    LinearMap.IsHomogeneous (AA.taylor ∘ₗ TensorProduct.lift (prepend R A))
      (AInfinityRightModule.barGrading AA AA.grading).piece (AA.grading.shift 1).piece 1 := by
  have hG : (AInfinityRightModule.barGrading AA AA.grading).piece =
      ((AA.grading.shift 1).tensorProduct (TensorWords.grading (AA.grading.shift 1))).piece :=
    funext (AInfinityRightModule.barGrading_piece AA AA.grading)
  rw [hG]
  simpa only [zero_add] using (AA.taylor_isSuspension.isHomogeneous AA.m_degree).comp
    (isHomogeneous_lift_prepend (AA.grading.shift 1))

/-- A term of the module coderivation on `x ⊗ a₁ ⋯ aₙ` whose block starts at the module input `x`
becomes, after concatenation, the collapse of the first `k + 1` letters of `x a₁ ⋯ aₙ`. -/
private theorem lift_prepend_taylor_tmul_subword {n : ℕ} (x : A) (a : Fin n → A) {k : ℕ}
    (hk : k ≤ n) :
    TensorProduct.lift (prepend R A)
        ((AA.taylor ∘ₗ TensorProduct.lift (prepend R A))
            (x ⊗ₜ[R] TensorWords.subword R a 0 k) ⊗ₜ[R] TensorWords.subword R a k (n - k)) =
      ReducedTensorWords.splice R (Fin.cons x a : Fin (n + 1) → A) 0 (n + 1) 0 (k + 1)
        (AA.taylor (ReducedTensorWords.subword R (Fin.cons x a : Fin (n + 1) → A) 0 (k + 1))) := by
  have h0 := prepend_subword (R := R) (Fin.cons x a : Fin (n + 1) → A) (Nat.succ_pos n) k
  rw [Fin.zero_eta, Fin.cons_zero] at h0
  have hsplice := prepend_subword_eq_splice (R := R) (Fin.cons x a : Fin (n + 1) → A) (a := 0)
    (b := n + 1) (Nat.succ_pos k) (by omega) (by omega)
    (AA.taylor (ReducedTensorWords.subword R (Fin.cons x a : Fin (n + 1) → A) 0 (k + 1)))
  rw [Nat.zero_add, Nat.add_sub_add_right] at hsplice
  rw [TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.lift.tmul,
    ← Fin.tail_cons (α := fun _ ↦ A) x a, subword_tail, subword_tail, Fin.tail_cons, h0]
  exact hsplice

/-- The term of the module coderivation on `x ⊗ a₁ ⋯ aₙ` in which the algebra bar differential
acts on `a₁ ⋯ aₙ` becomes, after concatenation, the sum of the collapses of the blocks of
`x a₁ ⋯ aₙ` that start after `x`, with `x` twisted. -/
private theorem lift_prepend_koszulTwist_tmul_coaugmentedBarDifferential {n : ℕ} (x : A)
    (a : Fin n → A) :
    TensorProduct.lift (prepend R A)
        ((AA.grading.shift 1).koszulTwist 1 x ⊗ₜ[R]
          AA.coaugmentedBarDifferential (of R A n (PiTensorProduct.tprod R a))) =
      ∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n + 1 + 1),
        ReducedTensorWords.splice R
          ((AA.grading.shift 1).twistedTuple 1 (Fin.cons x a : Fin (n + 1) → A) 0 (p + 1))
          0 (n + 1) (p + 1) d
          (AA.taylor
            (ReducedTensorWords.subword R (Fin.cons x a : Fin (n + 1) → A) (p + 1) d)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [of_tprod_congr R A (y := fun i : Fin 0 ↦ (i.elim0 : A)) fun i ↦ i.elim0,
      ← one_eq_of_zero, AA.coaugmentedBarDifferential_one, TensorProduct.tmul_zero, map_zero,
      Finset.sum_range_zero]
  rw [← reducedInclusion_of R A ⟨n, hn⟩, ← LinearMap.comp_apply AA.coaugmentedBarDifferential,
    AA.coaugmentedBarDifferential_comp_reducedInclusion, LinearMap.comp_apply,
    TensorProduct.lift.tmul, prepend_reducedInclusion, barDifferential_def,
    ReducedTensorWords.gradedCoderiv_of_tprod, map_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.mem_range] at hp
  -- A block of `n + 1` letters starting after the module input does not fit.
  rw [map_sum, Finset.sum_range_succ _ (n + 1),
    ReducedTensorWords.splice_eq_zero_of_block_lt_add R _ _ (by omega), add_zero]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  -- The twisted word `x a₁ ⋯ aₙ` starts with the twisted `x`, followed by the twisted `a`.
  set y := (AA.grading.shift 1).twistedTuple 1 (Fin.cons x a : Fin (n + 1) → A) 0 (p + 1)
  have hy : y 0 = (AA.grading.shift 1).koszulTwist 1 x := by
    simp [y]
  have htail : Fin.tail y = (AA.grading.shift 1).twistedTuple 1 a 0 p := by
    funext i
    simp only [y, Fin.tail, twistedTuple_apply, Fin.val_succ, Fin.cons_succ]
    split_ifs <;> first | rfl | omega
  rw [← hy, ← htail, ReducedTensorWords.prepend_splice, ← Fin.tail_cons (α := fun _ ↦ A) x a,
    ReducedTensorWords.subword_tail, Fin.tail_cons]

/-- Concatenation carries the coderivation generated by the module Taylor map to the bar
differential of the algebra.  A block collapsed by the module coderivation either starts at the
module input, or it lies in the word to the right of the module input. -/
private theorem lift_prepend_comp_gradedCoderiv :
    TensorProduct.lift (prepend R A) ∘ₗ
        AInfinityRightModule.gradedCoderiv AA AA.grading
          (AA.taylor ∘ₗ TensorProduct.lift (prepend R A)) =
      AA.barDifferential ∘ₗ TensorProduct.lift (prepend R A) := by
  refine TensorProduct.ext (LinearMap.ext fun x ↦ TensorWords.linearMap_ext R A fun n a ↦ ?_)
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
  rw [AInfinityRightModule.gradedCoderiv_tmul_of_tprod, map_add, map_sum,
    Finset.sum_congr rfl fun k hk ↦
      lift_prepend_taylor_tmul_subword AA x a (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
    lift_prepend_koszulTwist_tmul_coaugmentedBarDifferential, TensorProduct.lift.tmul,
    prepend_of_tprod, barDifferential_def, ReducedTensorWords.gradedCoderiv_of_tprod]
  -- Separate the blocks starting at the module input, which are not preceded by a twist.
  conv_rhs => rw [Finset.sum_range_succ', twistedTuple_zero_length, Finset.sum_range_succ',
    ReducedTensorWords.splice_zero_length, add_zero]
  rw [add_comm]

/-- An `A∞` algebra as a right `A∞` module over itself, the free module of rank one.  Its Taylor
map evaluates the Taylor map of the algebra on the concatenated word `x a₁ ⋯ aₙ`, so that its
operations are the algebra operations (`TauCeti.AInfinityAlgebra.m_toRightModule`). -/
noncomputable def toRightModule : AInfinityRightModule AA A :=
  AInfinityRightModule.ofTaylor AA.grading (AA.taylor ∘ₗ TensorProduct.lift (prepend R A))
    (isHomogeneous_taylor_comp_lift_prepend AA) (by
      rw [LinearMap.comp_assoc, lift_prepend_comp_gradedCoderiv, ← LinearMap.comp_assoc,
        ← letter_comp_barDifferential,
        LinearMap.comp_assoc AA.barDifferential AA.barDifferential (ReducedTensorWords.letter R A),
        barDifferential_sq, LinearMap.comp_zero, LinearMap.zero_comp])

/-- The free module of rank one carries the grading of the algebra. -/
@[simp]
theorem toRightModule_grading : AA.toRightModule.grading = AA.grading :=
  AInfinityRightModule.ofTaylor_grading _ _ _ _

/-- The Taylor map of the free module of rank one is the Taylor map of the algebra after
concatenation. -/
theorem toRightModule_taylor :
    AA.toRightModule.taylor = AA.taylor ∘ₗ TensorProduct.lift (prepend R A) :=
  AInfinityRightModule.ofTaylor_taylor _ _ _ _

/-- The Taylor map of the free module of rank one on `x ⊗ w` is the Taylor map of the algebra on
the word `x w`. -/
theorem toRightModule_taylor_tmul (x : A) (w : TensorWords R A) :
    AA.toRightModule.taylor (x ⊗ₜ[R] w) = AA.taylor (prepend R A x w) := by
  rw [toRightModule_taylor, LinearMap.comp_apply, TensorProduct.lift.tmul]

/-- Concatenation intertwines the bar differential of the free module of rank one with the bar
differential of the algebra: it is a chain map from the cofree bar comodule `sA ⊗ Tᶜ(sA)` of the
module to the reduced bar construction `ReducedTensorWords R A` of the algebra. -/
theorem lift_prepend_comp_barDifferential_toRightModule :
    TensorProduct.lift (prepend R A) ∘ₗ AA.toRightModule.barDifferential =
      AA.barDifferential ∘ₗ TensorProduct.lift (prepend R A) := by
  rw [toRightModule, AInfinityRightModule.ofTaylor_barDifferential,
    lift_prepend_comp_gradedCoderiv]

/-- The operations of the free module of rank one are the operations of the algebra, with the
module input first: `m_{n+1}^A(x, a₁, …, aₙ) = m_{n+1}(x, a₁, …, aₙ)`. -/
theorem m_toRightModule (n : ℕ) (x : A) (a : Fin n → A) :
    AA.toRightModule.m (n + 1) x a = AA.m (n + 1) (Fin.cons x a) := by
  rw [AInfinityRightModule.m_apply, ← AInfinityRightModule.taylor_tmul_of,
    toRightModule_taylor_tmul, toRightModule_grading, prepend_of_tprod, taylor_of_tprod]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero =>
    rw [Fin.cons_zero, Fin.cons_zero, Fin.val_zero, Nat.cast_zero, Nat.cast_add_one,
      add_sub_cancel_right, sub_zero, koszulTwist_koszulTwist]
  | succ j =>
    have h : ((n + 1 : ℕ) : ℤ) - 1 - ((j.succ : ℕ) : ℤ) = (n : ℤ) - 1 - j := by
      rw [Fin.val_succ]
      push_cast
      ring
    rw [Fin.cons_succ, Fin.cons_succ, h, koszulTwist_koszulTwist]

/-- The differential of the free module of rank one is the differential of the algebra. -/
@[simp]
theorem differential_toRightModule : AA.toRightModule.differential = AA.differential := by
  ext x
  rw [AInfinityRightModule.differential_apply, m_toRightModule, differential_apply]
  -- `![x]` is `Fin.cons x ![]`, and the two empty tuples agree.
  congr 1

end AInfinityAlgebra

end TauCeti
