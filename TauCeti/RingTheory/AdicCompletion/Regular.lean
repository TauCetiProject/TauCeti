/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.Regular.RegularSequence
-- Proof-only: the first term of a weakly regular pair is regular modulo powers of the second.
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Regularity of the parameter on principal-adic completions

If multiplication by `r` is injective on a module, it remains injective on its `(r)`-adic
completion. This needs neither Noetherianity nor finite generation.
In particular the parameter remains a non-zero-divisor
when forming a localization of its own adic completion.

An element that is regular modulo every power of an ideal `I` is regular on the `I`-adic
completion. For a weakly regular pair `(a, b)` on `M`, this makes `a` regular on the `(b)`-adic
completion of `M`, even when `b` itself is not regular on `M`. This is the form in which a
regular pair `(p, v)` makes the `(v)`-adic completion `p`-torsion-free before it is completed a
second time, `p`-adically.
-/

public section

open AdicCompletion RingTheory.Sequence

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {r : R}

/-- A regular element on a module is regular on its own principal-adic completion, without
Noetherian or finiteness hypotheses. -/
theorem IsSMulRegular.adicCompletion (hr : IsSMulRegular M r) :
    IsSMulRegular (AdicCompletion (Ideal.span {r}) M) r := by
  apply (injective_iff_map_eq_zero (DistribSMul.toLinearMap R _ r)).mpr
  intro x hx
  apply AdicCompletion.ext
  intro n
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (eval (Ideal.span {r}) M (n + 1) x)
  have hzero : Submodule.Quotient.mk (r • a) =
      (0 : M ⧸ ((Ideal.span {r}) ^ (n + 1) • ⊤ : Submodule R M)) := by
    rw [Submodule.Quotient.mk_smul, ha, ← map_smul]
    simpa using congrArg (eval (Ideal.span {r}) M (n + 1)) hx
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hzero
  simp only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and] at hmem
  obtain ⟨b, hb⟩ := hmem
  have hab : a = r ^ n • b := hr (by simpa [pow_succ', mul_smul] using hb.symm)
  have han : Submodule.Quotient.mk a =
      (0 : M ⧸ ((Ideal.span {r}) ^ n • ⊤ : Submodule R M)) := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    exact ⟨b, trivial, hab.symm⟩
  rw [← transitionMap_comp_eval_apply (Ideal.span {r}) M (Nat.le_succ n) x,
    ← eval_apply, ← ha]
  exact han

/-- A regular element remains regular in its own principal-adic completion as a ring. -/
theorem IsRegular.adicCompletion (hr : IsRegular r) :
    IsRegular (algebraMap R (AdicCompletion (Ideal.span {r}) R) r) :=
  (Commute.isRegular_iff fun _ ↦ Commute.all _ _).mpr
    ((isSMulRegular_algebraMap_iff (AdicCompletion (Ideal.span {r}) R)).mpr
      hr.left.isSMulRegular.adicCompletion)

/-- An element that is regular on `M ⧸ Iⁿ M` for every `n` is regular on the `I`-adic completion
of `M`. -/
theorem AdicCompletion.isSMulRegular_of_forall_isSMulRegular_quotient {I : Ideal R}
    (h : ∀ n : ℕ, IsSMulRegular (M ⧸ (I ^ n • ⊤ : Submodule R M)) r) :
    IsSMulRegular (AdicCompletion I M) r :=
  fun x y hxy ↦ AdicCompletion.ext fun n ↦ h n <| by
    simpa only [val_smul_apply] using congrArg (fun z ↦ z.val n) hxy

/-- For a weakly regular pair `(a, b)` on `M`, the element `a` is regular on the `(b)`-adic
completion of `M`. The element `b` need not be regular on `M`. -/
theorem RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_adicCompletion {a b : R}
    (h : IsWeaklyRegular M [a, b]) : IsSMulRegular (AdicCompletion (Ideal.span {b}) M) a :=
  AdicCompletion.isSMulRegular_of_forall_isSMulRegular_quotient fun n ↦ by
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    simpa only [pow_one] using h.isSMulRegular_quotSMulTop_pow_swap n 1
