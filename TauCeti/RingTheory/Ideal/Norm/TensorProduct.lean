/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import TauCeti.LinearAlgebra.TensorProduct.Quotient

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Cardinalities of finite modules under extension of Dedekind domains

Let `R → S` be a finite torsion-free extension of Dedekind domains, both free of finite rank over
`ℤ` (for instance rings of integers `𝓞 K → 𝓞 L` of a finite extension of number fields), and let
`n = finrank R S`. Scalar extension to `S` raises the cardinality of a finite `R`-module `T` to the
`n`-th power: `#(S ⊗ T) = #T ^ n` (`TauCeti.natCard_tensorProduct`). For a cyclic module `R / I`
this is `N(I S) = N(I) ^ n` (Mathlib's `Ideal.absNorm_algebraMap`); the general case follows by
induction on `#T`, since `S` is flat over `R`. For an infinite `T` both sides are `0`, since `S` is
faithfully flat over `R`, so `T` embeds into `S ⊗ T`.

So for a submodule `N` of an `R`-module `E`, the index of the base change `S ⊗ N` in `S ⊗ E` is
`#(E / N) ^ n` (`Submodule.cardQuot_baseChange`). In particular, for an element `s`, the index of
`S (1 ⊗ s)` is `#(E / R s) ^ n` (`TauCeti.cardQuot_span_one_tmul`).

## Main statements

* `TauCeti.natCard_tensorProduct_quotient`: `#(S ⊗ R / I) = #(R / I) ^ finrank R S`.
* `TauCeti.natCard_tensorProduct`: `#(S ⊗ T) = #T ^ finrank R S` for every `R`-module `T` (both
  sides are `0` for infinite `T`).
* `Submodule.cardQuot_baseChange`: `#(S ⊗ E / N.baseChange S) = #(E / N) ^ finrank R S`.
* `TauCeti.cardQuot_span_one_tmul`: `#(S ⊗ E / S (1 ⊗ s)) = #(E / R s) ^ finrank R S`.
* `TauCeti.finite_quotient_span_one_tmul`: if `E / R s` is finite, so is `S ⊗ E / S (1 ⊗ s)`.
-/

public section

open scoped TensorProduct
open Module

variable {R : Type*} (S : Type*) [CommRing R] [IsDedekindDomain R] [CommRing S]
  [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]
  [Module.Free ℤ R] [Module.Free ℤ S] [Module.Finite ℤ R] [Module.Finite ℤ S]

namespace TauCeti

/-- `#(S ⊗ R / I) = #(R / I) ^ finrank R S`: the tensor product is `S / I S`, whose cardinality
is the norm `N(I S) = N(I) ^ finrank R S`. -/
theorem natCard_tensorProduct_quotient (I : Ideal R) :
    Nat.card (S ⊗[R] (R ⧸ I)) = Nat.card (R ⧸ I) ^ finrank R S := by
  have : Infinite R := Module.Free.infinite ℤ R
  have : Infinite S := Module.Free.infinite ℤ S
  rw [Nat.card_congr
      (TensorProduct.AlgebraTensorModule.tensorQuotEquivQuotMapSMul (S := S) (N := S) I).toEquiv,
    smul_eq_mul, Ideal.mul_top, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_algebraMap, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- The case of `TauCeti.natCard_tensorProduct` for a finite module `T`. -/
private theorem natCard_tensorProduct_of_finite (T : Type*) [AddCommGroup T] [Module R T]
    [Finite T] : Nat.card (S ⊗[R] T) = Nat.card T ^ finrank R S := by
  induction hT : Nat.card T using Nat.strong_induction_on generalizing T with
  | _ m ih =>
  subst hT
  rcases subsingleton_or_nontrivial T with hT | hT
  · simp [Nat.card_unique]
  obtain ⟨t, ht⟩ := exists_ne (0 : T)
  set C := Submodule.span R {t}
  -- The cyclic submodule `C ≅ R / Ann(t)`.
  have hC : Nat.card (S ⊗[R] C) = Nat.card C ^ finrank R S := by
    rw [Nat.card_congr ((Ideal.quotTorsionOfEquivSpanSingleton R T t).lTensor
      S).toEquiv.symm, natCard_tensorProduct_quotient S,
      Nat.card_congr (Ideal.quotTorsionOfEquivSpanSingleton R T t).toEquiv]
  have : Finite (T ⧸ C) := Finite.of_surjective C.mkQ C.mkQ_surjective
  -- The quotient `T / C` is smaller.
  have hlt : Nat.card (T ⧸ C) < Nat.card T := by
    rw [C.card_eq_card_quotient_mul_card]
    have hC1 : 1 < Nat.card C := by
      have : Nontrivial C := ⟨⟨0, ⟨t, Submodule.mem_span_singleton_self t⟩,
        fun h ↦ ht (congrArg Subtype.val h).symm⟩⟩
      exact Finite.one_lt_card
    have hQ : 0 < Nat.card (T ⧸ C) := Nat.card_pos
    nlinarith
  have hQ := ih _ hlt (T ⧸ C) rfl
  -- Flatness: `S ⊗ C ↪ S ⊗ T` with cokernel `S ⊗ (T / C)`.
  have hf : Function.Injective (C.subtype.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap C.subtype C.injective_subtype
  have := (LinearMap.range (C.subtype.lTensor S)).card_eq_card_quotient_mul_card
  rw [Nat.card_congr (LinearEquiv.ofInjective _ hf).toEquiv.symm, LinearMap.lTensor_def,
    ← Nat.card_congr (TensorProduct.tensorQuotientEquiv S C).toEquiv, hC, hQ] at this
  rw [this, C.card_eq_card_quotient_mul_card, mul_pow]

/-- **Scalar extension to `S` raises the cardinality of a module to the power `finrank R S`.**
For an infinite module both sides are `0`: `S` is faithfully flat over `R`, so `T` embeds into
`S ⊗ T` by `t ↦ 1 ⊗ t`, and `finrank R S` is positive. -/
theorem natCard_tensorProduct (T : Type*) [AddCommGroup T] [Module R T] :
    Nat.card (S ⊗[R] T) = Nat.card T ^ finrank R S := by
  rcases finite_or_infinite T with hT | hT
  · exact natCard_tensorProduct_of_finite S T
  have : Infinite (S ⊗[R] T) :=
    Infinite.of_injective _ (Module.FaithfullyFlat.tensorProduct_mk_injective (B := S) T)
  have hpos : 0 < finrank R S := Module.finrank_pos
  rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_pow hpos.ne']

end TauCeti

namespace Submodule

/-- **The index of a submodule under base change**:
`#(S ⊗ E / N.baseChange S) = #(E / N) ^ finrank R S`. -/
theorem cardQuot_baseChange {E : Type*} [AddCommGroup E] [Module R E] (N : Submodule R E) :
    (N.baseChange S).cardQuot = N.cardQuot ^ finrank R S := by
  -- The `R`-submodule cut out by `S ⊗ N → S ⊗ E` is the base change of `N`, viewed over `R`.
  have hrange : LinearMap.range (N.subtype.lTensor S) = (N.baseChange S).restrictScalars R := by
    have hmap : (N.subtype.baseChange S).restrictScalars R = N.subtype.lTensor S :=
      LinearMap.ext fun x ↦ by
        rw [LinearMap.restrictScalars_apply, LinearMap.baseChange_eq_lTensor]
    rw [Submodule.baseChange, ← LinearMap.range_restrictScalars, hmap]
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply,
    ← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv R (N.baseChange S)).toEquiv,
    ← hrange, ← TauCeti.natCard_tensorProduct S (E ⧸ N),
    Nat.card_congr (TensorProduct.tensorQuotientEquiv S N).toEquiv, LinearMap.lTensor_def]

end Submodule

namespace TauCeti

/-- **The index of an element under base change**:
`#(S ⊗ E / S (1 ⊗ s)) = #(E / R s) ^ finrank R S`. -/
theorem cardQuot_span_one_tmul {E : Type*} [AddCommGroup E] [Module R E] (s : E) :
    (Submodule.span S {(1 : S) ⊗ₜ[R] s}).cardQuot =
      (Submodule.span R {s}).cardQuot ^ finrank R S := by
  rw [← Submodule.cardQuot_baseChange S, Submodule.baseChange_span, Set.image_singleton,
    TensorProduct.mk_apply]

/-- If `E / R s` is finite, so is `S ⊗ E / S (1 ⊗ s)`. -/
theorem finite_quotient_span_one_tmul {E : Type*} [AddCommGroup E] [Module R E] {s : E}
    [Finite (E ⧸ Submodule.span R {s})] :
    Finite ((S ⊗[R] E) ⧸ Submodule.span S {(1 : S) ⊗ₜ[R] s}) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [← Submodule.cardQuot_apply, cardQuot_span_one_tmul, Submodule.cardQuot_apply]
  exact pow_ne_zero _ Nat.card_pos.ne'

end TauCeti
