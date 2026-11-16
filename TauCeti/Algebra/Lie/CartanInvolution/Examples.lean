/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Reductive
public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.Algebra.Lie.SpecialLinear.Cartan
public import TauCeti.Algebra.Lie.Symplectic.Cartan
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# Classical examples of Cartan and reductive Cartan involutions

This file certifies the classical matrix Lie algebras as examples and separating counterexamples
for `LieEquiv.IsCartanInvolution` and `LieEquiv.IsReductiveCartanInvolution`:

* `LieAlgebra.Symplectic.isCartanInvolution_cartanInvolution`: negative transpose `X ↦ -Xᵀ` is a
  Cartan involution of `sp l K` over any ordered field `K`.
* `LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution`: negative transpose `X ↦ -Xᵀ` is a
  Cartan involution of `sl n R` over any ordered principal ideal domain `R`.
* `LieAlgebra.SpecialLinear.not_isCartanInvolution_refl`: for nontrivial `n`, the identity is not
  a Cartan involution of `sl n R` over any ordered principal ideal domain `R` (non-compactness).
* `TauCeti.isReductiveCartanInvolution_negTransposeLieEquiv` and
  `TauCeti.not_isCartanInvolution_negTransposeLieEquiv`: negative transpose `X ↦ -Xᵀ` is a
  reductive Cartan involution of `gl n K` over any ordered field `K`, and for nonempty `n` over any
  nontrivial partially ordered commutative ring `R` is not a Cartan involution in the semisimple
  sense.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–2.
-/

public section

open Matrix LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section OrderedPID

variable {R : Type*} [CommRing R] [IsPrincipalIdealRing R] [LinearOrder R] [IsStrictOrderedRing R]

namespace LieAlgebra.SpecialLinear

/-- Negative transpose `X ↦ -Xᵀ` is a Cartan involution of the special linear Lie algebra `sl n R`
over any ordered principal ideal domain `R`. -/
theorem isCartanInvolution_cartanInvolution (n : Type*) [Fintype n] [DecidableEq n] :
    (cartanInvolution n R).IsCartanInvolution := by
  rw [LieEquiv.isCartanInvolution_iff]
  exact ⟨cartanInvolution_cartanInvolution,
    fun _ hX ↦ neg_pos.mpr (killingForm_cartanInvolution_self_neg hX)⟩

/-- For nontrivial `n`, the identity is not a Cartan involution of `sl n R` over any ordered
principal ideal domain `R` (the Killing form is positive on the diagonal matrix `Eᵢᵢ - Eⱼⱼ`). -/
theorem not_isCartanInvolution_refl (n : Type*) [Fintype n] [DecidableEq n] [Nontrivial n] :
    ¬ (LieEquiv.refl : sl n R ≃ₗ⁅R⁆ sl n R).IsCartanInvolution := by
  intro hrefl
  have hneg := LieEquiv.isCartanInvolution_refl_iff.mp hrefl
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  let Hmat : Matrix n n R := Matrix.single i i 1 - Matrix.single j j 1
  have hHmem : Hmat ∈ sl n R := by
    rw [mem_sl_iff]
    simp [Hmat, Matrix.trace, Matrix.single_apply]
  let H : sl n R := ⟨Hmat, hHmem⟩
  have hHne : H ≠ 0 := by
    intro h0
    have hval := congrArg (fun M : sl n R ↦ (M : Matrix n n R) i i) h0
    simp [H, Hmat, hij.symm] at hval
  have hlt := hneg H hHne
  have hsq : (Hmat * Hmat).trace = 2 := by
    have hmul : Hmat * Hmat = Matrix.single i i 1 + Matrix.single j j 1 := by
      simp [Hmat, sub_mul, mul_sub, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hij,
        Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
    rw [hmul]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.add_apply, Matrix.single_apply,
      and_self, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    norm_num
  have hpos : 0 < killingForm R (sl n R) H H := by
    rw [killingForm_apply]
    have : (0 : R) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
    simp only [H, hsq]
    positivity
  exact hlt.not_gt hpos

end LieAlgebra.SpecialLinear

end OrderedPID

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace LieAlgebra.Symplectic

/-- Negative transpose `X ↦ -Xᵀ` is a Cartan involution of the symplectic Lie algebra `sp l K`
over any ordered field `K`. -/
theorem isCartanInvolution_cartanInvolution (l : Type*) [Fintype l] [DecidableEq l] :
    (cartanInvolution l K).IsCartanInvolution := by
  rw [LieEquiv.isCartanInvolution_iff]
  exact ⟨cartanInvolution_cartanInvolution,
    fun _ hX ↦ neg_pos.mpr (killingForm_cartanInvolution_self_neg hX)⟩

end LieAlgebra.Symplectic

namespace TauCeti

/-- Negative transpose `X ↦ -Xᵀ` is a reductive Cartan involution of `gl n K = Matrix n n K` over
any ordered field `K`. -/
theorem isReductiveCartanInvolution_negTransposeLieEquiv (n : Type*) [Fintype n] [DecidableEq n] :
    (negTransposeLieEquiv n K).IsReductiveCartanInvolution := by
  by_cases hn : Nonempty n
  · let _ : Invertible (Fintype.card n : K) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    rw [LieEquiv.isReductiveCartanInvolution_iff]
    refine ⟨LieSubmodule.isCompl_toSubmodule.mp
        (isCompl_center_derivedSeries_one_matrix (R := K) (n := n)),
      fun X ↦ by simp, ?_⟩
    let e : SpecialLinear.sl n K ≃ₗ⁅K⁆ derivedSeries K (Matrix n n K) 1 :=
      LieEquiv.ofEq (SpecialLinear.sl n K) (derivedSeries K (Matrix n n K) 1).toLieSubalgebra
        (congrArg SetLike.coe (derivedSeries_one_toLieSubalgebra_eq_sl (R := K) (n := n)).symm)
    have hconj : (negTransposeLieEquiv n K).restrictDerivedSeries 1 =
        e.symm.trans ((SpecialLinear.cartanInvolution n K).trans e) := by
      apply LieEquiv.ext
      intro X
      apply Subtype.ext
      rw [LieEquiv.coe_restrictDerivedSeries, negTransposeLieEquiv_apply, LieEquiv.trans_apply,
        LieEquiv.trans_apply]
      exact (SpecialLinear.coe_cartanInvolution (e.symm X)).symm
    rw [hconj]
    exact (SpecialLinear.isCartanInvolution_cartanInvolution (R := K) n).conj e
  · have : IsEmpty n := not_nonempty_iff.mp hn
    have : IsLieAbelian (Matrix n n K) := ⟨fun _ _ ↦ Subsingleton.elim _ _⟩
    exact LieEquiv.isReductiveCartanInvolution_iff_involutive_of_isLieAbelian.mpr fun X ↦ by simp

end TauCeti

end OrderedField

section PartialOrder

variable {R : Type*} [CommRing R] [PartialOrder R] [Nontrivial R]

namespace TauCeti

/-- For nonempty `n`, negative transpose on `gl n R` is not a Cartan involution in the semisimple
sense, because the scalar matrices form a nontrivial centre. -/
theorem not_isCartanInvolution_negTransposeLieEquiv (n : Type*) [Fintype n] [DecidableEq n]
    [Nonempty n] :
    ¬ (negTransposeLieEquiv n R).IsCartanInvolution := by
  intro hθ
  have h1 : (1 : Matrix n n R) ∈ center R (Matrix n n R) := one_mem_center_matrix R n
  rw [hθ.center_eq_bot, LieSubmodule.mem_bot] at h1
  exact one_ne_zero h1

end TauCeti

end PartialOrder
