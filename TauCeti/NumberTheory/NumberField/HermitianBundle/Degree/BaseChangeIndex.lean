/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.BaseChange

/-!
# The Arakelov degree under base change: the finite part

Let `L/K` be a finite extension of number fields, of degree `n = [L : K]`. Scalar extension to
`𝓞 L` raises the cardinality of a finite `𝓞 K`-module `T` to the `n`-th power:
`#(𝓞 L ⊗ T) = #T ^ n` (`TauCeti.natCard_tensorProduct_ringOfIntegers`). For a cyclic
module `𝓞 K / I` this is `N(I 𝓞 L) = N(I) ^ n` (Mathlib's `Ideal.absNorm_algebraMap`); the general
case follows by induction on `#T`, since `𝓞 L` is flat over `𝓞 K`.

So for a section `s` of an `𝓞 K`-module `E` with finite cokernel, the index of `𝓞 L (1 ⊗ s)` in
`𝓞 L ⊗ E` is `#(E / 𝓞 K s) ^ n` (`TauCeti.cardQuot_span_ringOfIntegers_one_tmul`), and with the
archimedean half on main, `deg(Ē_{𝓞 L}) = [L : K] deg(Ē)` computed with `1 ⊗ s` and `s`
(`TauCeti.HermitianMetric.sectionDegree_baseChange`). This removes the generating-section
hypothesis of `TauCeti.HermitianMetric.sectionDegree_baseChange_of_span_eq_top`.

## Main statements

* `TauCeti.natCard_tensorProduct_ringOfIntegers`: `#(𝓞 L ⊗ T) = #T ^ [L : K]` for a
  finite `𝓞 K`-module `T`.
* `TauCeti.cardQuot_span_ringOfIntegers_one_tmul`: `#(𝓞 L ⊗ E / 𝓞 L (1 ⊗ s)) = #(E / 𝓞 K s)^[L : K]`
  when `E / 𝓞 K s` is finite.
* `TauCeti.HermitianMetric.sectionDegree_baseChange`: `deg(1 ⊗ s) = [L : K] deg(s)` when
  `E / 𝓞 K s` is finite.

## References

* P. Deligne, *Preuves des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616,
  §1.2 (Remarque), p. 27.
-/

public noncomputable section

open scoped TensorProduct
open NumberField Module

namespace TauCeti

section IndexBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (L) in
/-- `#(𝓞 L ⊗ 𝓞 K / I) = #(𝓞 K / I) ^ [L : K]`: the tensor product is `𝓞 L / I 𝓞 L`, whose
cardinality is the norm `N(I 𝓞 L) = N(I) ^ [L : K]`. -/
theorem natCard_ringOfIntegers_tensorProduct_quotient (I : Ideal (𝓞 K)) :
    Nat.card (𝓞 L ⊗[𝓞 K] (𝓞 K ⧸ I)) = Nat.card (𝓞 K ⧸ I) ^ finrank K L := by
  have hsmul : I • (⊤ : Submodule (𝓞 K) (𝓞 L)) =
      (I.map (algebraMap (𝓞 K) (𝓞 L))).restrictScalars (𝓞 K) := by
    rw [Ideal.smul_top_eq_map]
  rw [Nat.card_congr (TensorProduct.tensorQuotEquivQuotSMul (𝓞 L) I).toEquiv, hsmul,
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (𝓞 K) _).toEquiv]
  have h1 := Ideal.absNorm_algebraMap (R := 𝓞 K) (S := 𝓞 L) I
  rw [← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L, Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h1
  exact h1

variable (L) in
/-- **Scalar extension to `𝓞 L` raises the cardinality of a finite module to the power
`[L : K]`.** -/
theorem natCard_tensorProduct_ringOfIntegers (T : Type*) [AddCommGroup T] [Module (𝓞 K) T]
    [Finite T] : Nat.card (𝓞 L ⊗[𝓞 K] T) = Nat.card T ^ finrank K L := by
  induction hT : Nat.card T using Nat.strong_induction_on generalizing T with
  | _ m ih =>
  subst hT
  rcases subsingleton_or_nontrivial T with hT | hT
  · simp [Nat.card_unique]
  obtain ⟨t, ht⟩ := exists_ne (0 : T)
  set C := Submodule.span (𝓞 K) {t}
  -- The cyclic submodule `C ≅ 𝓞 K / Ann(t)`.
  have hC : Nat.card (𝓞 L ⊗[𝓞 K] C) = Nat.card C ^ finrank K L := by
    rw [Nat.card_congr ((Ideal.quotTorsionOfEquivSpanSingleton (𝓞 K) T t).lTensor
      (𝓞 L)).toEquiv.symm, natCard_ringOfIntegers_tensorProduct_quotient L,
      Nat.card_congr (Ideal.quotTorsionOfEquivSpanSingleton (𝓞 K) T t).toEquiv]
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
  -- Flatness: `𝓞 L ⊗ C ↪ 𝓞 L ⊗ T` with cokernel `𝓞 L ⊗ (T / C)`.
  set f := TensorProduct.map (LinearMap.id : 𝓞 L →ₗ[𝓞 K] 𝓞 L) C.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap C.subtype C.injective_subtype
  have := (LinearMap.range f).card_eq_card_quotient_mul_card
  rw [Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv.symm,
    ← Nat.card_congr (TensorProduct.tensorQuotientEquiv (𝓞 L) C).toEquiv, hC, hQ] at this
  rw [this, C.card_eq_card_quotient_mul_card, mul_pow]

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]

variable (L) in
/-- **The index of a section under base change.** If `E / 𝓞 K s` is finite, then
`#(𝓞 L ⊗ E / 𝓞 L (1 ⊗ s)) = #(E / 𝓞 K s) ^ [L : K]`. -/
theorem cardQuot_span_ringOfIntegers_one_tmul {s : E} [Finite (E ⧸ Submodule.span (𝓞 K) {s})] :
    (Submodule.span (𝓞 L) {(1 : 𝓞 L) ⊗ₜ[𝓞 K] s}).cardQuot =
      (Submodule.span (𝓞 K) {s}).cardQuot ^ finrank K L := by
  set C := Submodule.span (𝓞 K) {s}
  have hrange : (LinearMap.range (TensorProduct.map (LinearMap.id : 𝓞 L →ₗ[𝓞 K] 𝓞 L) C.subtype))
      = (Submodule.span (𝓞 L) {(1 : 𝓞 L) ⊗ₜ[𝓞 K] s}).restrictScalars (𝓞 K) := by
    have hbc : C.baseChange (𝓞 L) = Submodule.span (𝓞 L) {(1 : 𝓞 L) ⊗ₜ[𝓞 K] s} := by
      rw [Submodule.baseChange_span, Set.image_singleton, TensorProduct.mk_apply]
    ext x
    rw [Submodule.restrictScalars_mem, ← hbc]
    exact Iff.rfl
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply,
    ← natCard_tensorProduct_ringOfIntegers L (E ⧸ C),
    Nat.card_congr (TensorProduct.tensorQuotientEquiv (𝓞 L) C).toEquiv, hrange]
  rfl

end IndexBaseChange

namespace HermitianMetric

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] (h : HermitianMetric K E)

/-- **The degree under base change.** If `E / 𝓞 K s` is finite (for instance `s` a nonzero
section of a hermitian line), then `deg(Ē_{𝓞 L}) = [L : K] deg(Ē)`, computed with `1 ⊗ s` and
`s`. -/
theorem sectionDegree_baseChange {s : E} [Finite (E ⧸ Submodule.span (𝓞 K) {s})] :
    h.baseChange.sectionDegree ((1 : 𝓞 L) ⊗ₜ s) = finrank K L * h.sectionDegree s := by
  rw [sectionDegree_def, sectionDegree_def, sum_log_norm_baseChange_one_tmul,
    cardQuot_span_ringOfIntegers_one_tmul L, Nat.cast_pow, Real.log_pow]
  ring

end HermitianMetric

end TauCeti
