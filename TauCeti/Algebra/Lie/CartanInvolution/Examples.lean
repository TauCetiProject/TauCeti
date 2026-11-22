/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Reductive
public import TauCeti.Algebra.Lie.SpecialLinear.Cartan

import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.SpecialLinear.Killing

/-!
# Examples and non-examples of Cartan involutions

This file verifies the Cartan-involution predicates on the standard classical and abelian Lie
algebras:

* **Abelian Lie algebras:** every involutive automorphism of an abelian Lie algebra is a reductive
  Cartan involution (`LieEquiv.isReductiveCartanInvolution_iff_of_isLieAbelian`), whereas no
  automorphism of a nontrivial abelian Lie algebra is a (semisimple) Cartan involution
  (`LieEquiv.not_isCartanInvolution_of_isLieAbelian`). In particular, on `ℝ` with the commutator
  bracket, `LieEquiv.refl` is a reductive Cartan involution but not a Cartan involution.
* **Special linear Lie algebras `sl n K`:** negative transpose `X ↦ -Xᵀ`
  (`LieAlgebra.SpecialLinear.cartanInvolution`) is a Cartan involution over every ordered field `K`
  (`LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution`), with fixed subalgebra
  `LieAlgebra.Orthogonal.so n K` (when `2` is invertible) and `-1`-eigenspace the symmetric
  trace-zero matrices. By contrast, the identity `LieEquiv.refl` is not a Cartan involution of
  `sl n K` whenever `1 < Fintype.card n` (`LieAlgebra.SpecialLinear.not_isCartanInvolution_refl`),
  in particular on `sl (Fin 2) K`.
* **General linear Lie algebras `gl n K`:** negative transpose `TauCeti.negTransposeLieEquiv n K`
  is a reductive Cartan involution over every ordered field `K`
  (`TauCeti.isReductiveCartanInvolution_negTransposeLieEquiv`).

## Main results

* `LieEquiv.isReductiveCartanInvolution_iff_of_isLieAbelian` and
  `LieEquiv.not_isCartanInvolution_of_isLieAbelian`: characterization on abelian Lie algebras.
* `LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution` and
  `LieAlgebra.SpecialLinear.not_isCartanInvolution_refl`: `X ↦ -Xᵀ` is a Cartan involution of
  `sl n K`, while `LieEquiv.refl` is not when `1 < Fintype.card n`.
* `TauCeti.isReductiveCartanInvolution_negTransposeLieEquiv`: `X ↦ -Xᵀ` is a reductive Cartan
  involution of `gl n K`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–2.
-/

public section

open LieAlgebra Matrix

/-! ### Abelian Lie algebras -/

namespace LieEquiv

section Abelian

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [LieRing L] [LieAlgebra K L]

/-- On an abelian Lie algebra, an automorphism is a reductive Cartan involution if and only if it
is involutive (its derived ideal is `⊥`). -/
theorem isReductiveCartanInvolution_iff_of_isLieAbelian [IsLieAbelian L] (θ : L ≃ₗ⁅K⁆ L) :
    θ.IsReductiveCartanInvolution ↔ Function.Involutive θ := by
  have hbot : derivedSeries K L 1 = ⊥ := by
    rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, eq_bot_iff]
    refine (LieSubmodule.lie_le_iff _ _ _).mpr fun x _ y _ ↦ ?_
    simp [trivial_lie_zero]
  rw [isReductiveCartanInvolution_iff, isCartanInvolution_iff]
  constructor
  · exact And.left
  · intro hinv
    refine ⟨hinv, θ.involutive_derivedSeriesCongr hinv 1, fun x hx ↦ ?_⟩
    exfalso
    apply hx
    apply Subtype.ext
    have hx' : (x : L) ∈ (⊥ : LieIdeal K L) := hbot ▸ x.property
    exact hx'

omit [IsStrictOrderedRing K] in
/-- No automorphism of a nontrivial abelian Lie algebra is a (semisimple) Cartan involution, since
the Killing form vanishes identically. -/
theorem not_isCartanInvolution_of_isLieAbelian [Nontrivial L] [IsLieAbelian L] (θ : L ≃ₗ⁅K⁆ L) :
    ¬ θ.IsCartanInvolution := by
  intro hθ
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have had : ad K L x = 0 := by
    ext y
    simp [trivial_lie_zero]
  have hpos := hθ.twistedKillingForm_self_pos hx
  simp only [twistedKillingForm_apply, killingForm_apply_apply, had, LinearMap.zero_comp,
    map_zero, neg_zero] at hpos
  exact lt_irrefl 0 hpos

end Abelian

section Real

attribute [local instance 100] LieRing.ofAssociativeRing

/-- On `ℝ` with the commutator bracket, the identity is a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_refl_real :
    (LieEquiv.refl : ℝ ≃ₗ⁅ℝ⁆ ℝ).IsReductiveCartanInvolution := by
  have : IsLieAbelian ℝ := ⟨fun x y ↦ by rw [LieRing.of_associative_ring_bracket]; ring⟩
  exact (isReductiveCartanInvolution_iff_of_isLieAbelian LieEquiv.refl).mpr fun _ ↦ rfl

/-- On `ℝ` with the commutator bracket, the identity is not a (semisimple) Cartan involution. -/
theorem not_isCartanInvolution_refl_real :
    ¬ (LieEquiv.refl : ℝ ≃ₗ⁅ℝ⁆ ℝ).IsCartanInvolution := by
  have : IsLieAbelian ℝ := ⟨fun x y ↦ by rw [LieRing.of_associative_ring_bracket]; ring⟩
  exact not_isCartanInvolution_of_isLieAbelian LieEquiv.refl

end Real

end LieEquiv

/-! ### Special linear Lie algebras `sl n` -/

namespace LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Fixed vectors of `SpecialLinear.cartanInvolution` are the skew-symmetric matrices in
`sl n R`. -/
theorem mem_fixedSubalgebra_cartanInvolution_iff (X : sl n R) :
    X ∈ (cartanInvolution n R).toLieHom.fixedSubalgebra ↔
      (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, cartanInvolution_eq_self_iff]

/-- The `-1`-eigenspace of `SpecialLinear.cartanInvolution` consists of the symmetric matrices in
`sl n R`. -/
theorem mem_cartanP_cartanInvolution_iff (X : sl n R) :
    X ∈ (cartanInvolution n R).cartanP ↔ (X : Matrix n n R)ᵀ = (X : Matrix n n R) := by
  rw [LieEquiv.mem_cartanP, cartanInvolution_eq_neg_iff]

/-- When `2` is invertible, the fixed subalgebra of `SpecialLinear.cartanInvolution` embeds onto
`LieAlgebra.Orthogonal.so n R`. -/
theorem map_incl_fixedSubalgebra_cartanInvolution [Invertible (2 : R)] :
    (cartanInvolution n R).toLieHom.fixedSubalgebra.map (sl n R).incl =
      LieAlgebra.Orthogonal.so n R := by
  ext A
  rw [LieSubalgebra.mem_map, LieAlgebra.Orthogonal.mem_so]
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (mem_fixedSubalgebra_cartanInvolution_iff X).mp hX
  · intro hA
    have htr : A.trace = 0 := by
      have h : A.trace = -A.trace := by
        calc A.trace = Aᵀ.trace := (trace_transpose A).symm
          _ = (-A).trace := by rw [hA]
          _ = -A.trace := trace_neg A
      have h2 : (2 : R) * A.trace = 0 := by
        calc (2 : R) * A.trace = A.trace + A.trace := two_mul A.trace
          _ = A.trace + (-A.trace) := congrArg (A.trace + ·) h
          _ = 0 := add_neg_cancel A.trace
      calc A.trace = ⅟(2 : R) * ((2 : R) * A.trace) := by rw [invOf_mul_cancel_left]
        _ = 0 := by rw [h2, mul_zero]
    exact ⟨⟨A, mem_sl_iff.mpr htr⟩,
      (mem_fixedSubalgebra_cartanInvolution_iff _).mpr hA, rfl⟩

end CommRing

section PID

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R]

/-- The twisted Killing form of `X ↦ -Xᵀ` on `sl n R` is `B_θ(X, Y) = 2 n trace (X * Yᵀ)`. -/
theorem twistedKillingForm_cartanInvolution_apply (X Y : sl n R) :
    (cartanInvolution n R).twistedKillingForm X Y =
      2 * Fintype.card n * ((X : Matrix n n R) * (Y : Matrix n n R)ᵀ).trace := by
  rw [LieEquiv.twistedKillingForm_apply, killingForm_apply, coe_cartanInvolution, mul_neg,
    trace_neg, mul_neg, neg_neg]

end PID

section OrderedField

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- **`X ↦ -Xᵀ` is a Cartan involution of `sl n K`** over every ordered field `K`. -/
theorem isCartanInvolution_cartanInvolution :
    (cartanInvolution n K).IsCartanInvolution := by
  rw [LieEquiv.isCartanInvolution_iff]
  refine ⟨cartanInvolution_cartanInvolution, fun X hX ↦ ?_⟩
  rw [← neg_pos, ← LieEquiv.twistedKillingForm_apply, twistedKillingForm_cartanInvolution_apply]
  obtain ⟨i, j, hij⟩ : ∃ i j, (X : Matrix n n K) i j ≠ 0 := by
    by_contra! h
    exact hX (Subtype.ext (Matrix.ext h))
  have : Nonempty n := ⟨i⟩
  have : (0 : K) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have : 0 < ((X : Matrix n n K) * (X : Matrix n n K)ᵀ).trace := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_pos' (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ ↦ mul_self_nonneg _)
        ⟨j, Finset.mem_univ _, mul_self_pos.mpr hij⟩⟩
  positivity

/-- The identity automorphism is **not** a Cartan involution of `sl n K` whenever
`1 < Fintype.card n` (in particular for `sl (Fin 2) K`): `B_id(h, h) = -B(h, h) < 0` on a
nonzero diagonal trace-zero matrix `h = E_{ii} - E_{jj}`. -/
theorem not_isCartanInvolution_refl (hn : 1 < Fintype.card n) :
    ¬ (LieEquiv.refl : sl n K ≃ₗ⁅K⁆ sl n K).IsCartanInvolution := by
  intro hθ
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hn
  let H : sl n K := singleSubSingle i j (1 : K)
  have hH0 : H ≠ 0 := by
    intro h0
    have hentry := congrArg (fun M : sl n K ↦ (M : Matrix n n K) i i) h0
    simp [H, Matrix.single, hij.symm] at hentry
  have hpos := hθ.twistedKillingForm_self_pos hH0
  rw [LieEquiv.twistedKillingForm_apply, LieEquiv.refl_apply, killingForm_apply] at hpos
  have htr : ((H : Matrix n n K) * (H : Matrix n n K)).trace = 2 := by
    simp only [H, val_singleSubSingle, sub_mul, mul_sub, single_mul_single_same,
      single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ hij.symm,
      mul_one, sub_zero, zero_sub, sub_neg_eq_add, trace_add, trace_single_eq_same]
    norm_num
  rw [htr] at hpos
  have : (0 : K) < Fintype.card n := Nat.cast_pos.mpr (lt_trans zero_lt_one hn)
  have hneg : -(2 * (Fintype.card n : K) * 2) < 0 := by linarith
  exact lt_asymm hpos hneg

end OrderedField

end LieAlgebra.SpecialLinear

/-! ### General linear Lie algebras -/

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Negative transpose is a reductive Cartan involution of `gl n K`** over every ordered field
`K`, since its restriction to `[gl n K, gl n K] = sl n K` is
`LieAlgebra.SpecialLinear.cartanInvolution`. -/
theorem isReductiveCartanInvolution_negTransposeLieEquiv
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (negTransposeLieEquiv n K).IsReductiveCartanInvolution := by
  rw [LieEquiv.isReductiveCartanInvolution_iff]
  refine ⟨fun X ↦ by simp, ?_⟩
  let e : derivedSeries K (Matrix n n K) 1 ≃ₗ⁅K⁆ LieAlgebra.SpecialLinear.sl n K :=
    LieEquiv.ofEq (derivedSeries K (Matrix n n K) 1).toLieSubalgebra
      (LieAlgebra.SpecialLinear.sl n K)
      (by rw [derivedSeries_one_toLieSubalgebra_eq_sl])
  refine (LieEquiv.isCartanInvolution_iff_of_intertwine e
    (θ' := LieAlgebra.SpecialLinear.cartanInvolution n K) fun x ↦ ?_).mp ?_
  · apply Subtype.ext
    have he (y : derivedSeries K (Matrix n n K) 1) : (e y : Matrix n n K) = y := rfl
    rw [LieAlgebra.SpecialLinear.coe_cartanInvolution, he, he,
      LieEquiv.coe_derivedSeriesCongr, negTransposeLieEquiv_apply]
  · exact LieAlgebra.SpecialLinear.isCartanInvolution_cartanInvolution

end TauCeti
