/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Algebra.Regular.SMul

/-!
# Regularity of the parameter on principal-adic completions

If multiplication by `r` is injective on a module, it remains injective on its `(r)`-adic
completion. This needs neither Noetherianity nor finite generation.
In particular the parameter remains a non-zero-divisor
when forming a localization of its own adic completion.
-/

public section

open AdicCompletion

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
