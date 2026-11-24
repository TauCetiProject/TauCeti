/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import TauCeti.RingTheory.Derivation.Ideal

/-!
# Derivations of adic completions

Let `I` be an ideal of a commutative `R`-algebra `A` and `M` an `A`-module. Every `R`-derivation
`D : A → M` extends to an `R`-derivation `D̂ : Â → M̂` from the `I`-adic completion of `A` to the
`I`-adic completion of `M`. By the Leibniz rule `D` maps `I ^ (n + 1)` into `I ^ n • M`
(`Derivation.apply_mem_pow_smul_top_of_mem_pow_succ`), so it induces maps
`A ⧸ I ^ (n + 1) → M ⧸ I ^ n • M`, and `D̂` is the limit of these maps: if `x ∈ Â` is represented
by `a` modulo `I ^ (n + 1)`, then `D̂ x` is represented by `D a` modulo `I ^ n`.

When `I` is finitely generated, `D̂` is the only `R`-derivation `Â → M̂` agreeing with `D` on `A`:
a derivation vanishing on `A` is `A`-linear, every element of `Â` is congruent to an element of
`A` modulo `I ^ n • Â`, and `M̂` is `I`-adically separated. No continuity has to be assumed, and
the same argument applies to derivations into any `I`-adically separated `Â`-module.

This is how a derivation of a ring extends to its completion, for instance a derivation of the
local ring of an affine lift at the generic point of its special fibre to the completed generic
field. Unlike the topological extension `TauCeti.derivationLieAlgebra.extend` along a dense
uniform embedding, the construction uses no topology on `A` or `M`, applies to derivations with
values in a module, and its uniqueness needs no continuity hypothesis.

## Main definitions

* `Derivation.adicCompletion`: the extension of `D : A → M` to `Â → M̂`.

## Main results

* `Derivation.val_adicCompletion_apply`: `D̂ x` is represented by `D a` modulo `I ^ n` when `x` is
  represented by `a` modulo `I ^ (n + 1)`.
* `Derivation.adicCompletion_of`: `D̂` extends `D`.
* `Derivation.adicCompletion_ext`: for finitely generated `I`, a derivation from `Â` into an
  `I`-adically separated module, such as `M̂`, is determined by its values on `A`;
  `Derivation.eq_adicCompletion` characterises `D̂` accordingly.
-/

public section

open Submodule AdicCompletion

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M] (I : Ideal A)

/-- A derivation identifies `I ^ (n + 1)`-congruent elements up to `I ^ n • M`. -/
private theorem apply_smodEq_of_smodEq (D : Derivation R A M) {n : ℕ} {a b : A}
    (h : a ≡ b [SMOD (I ^ (n + 1) • ⊤ : Submodule A A)]) :
    D a ≡ D b [SMOD (I ^ n • ⊤ : Submodule A M)] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  rw [SModEq.sub_mem, ← map_sub]
  exact D.apply_mem_pow_smul_top_of_mem_pow_succ h

/-- Applying `D` to the terms of an `I`-adic Cauchy sequence, shifted by one, gives an `I`-adic
Cauchy sequence. -/
private noncomputable def adicCauchySequenceMap (D : Derivation R A M)
    (f : AdicCauchySequence I A) : AdicCauchySequence I M :=
  AdicCauchySequence.mk I M (fun n ↦ D (f (n + 1)))
    fun n ↦ apply_smodEq_of_smodEq I D (f.property (Nat.le_succ (n + 1)))

/-- The underlying function of `Derivation.adicCompletion`, through a choice of Cauchy
representative. -/
private noncomputable def adicCompletionFun (D : Derivation R A M) (x : AdicCompletion I A) :
    AdicCompletion I M :=
  AdicCompletion.mk I M (adicCauchySequenceMap I D (AdicCompletion.mk_surjective I A x).choose)

private theorem adicCompletionFun_val (D : Derivation R A M) {x : AdicCompletion I A} {n : ℕ}
    {a : A} (ha : x.val (n + 1) = Submodule.Quotient.mk a) :
    (adicCompletionFun I D x).val n = Submodule.Quotient.mk (D a) := by
  have hx := congrArg (fun y ↦ y.val (n + 1)) (AdicCompletion.mk_surjective I A x).choose_spec
  refine apply_smodEq_of_smodEq I D ?_
  unfold SModEq
  rw [← ha, ← hx, mk_apply_coe, mkQ_apply]

/-- Every coordinate of an element of the completion has a representative. -/
private theorem exists_val_eq (x : AdicCompletion I A) (n : ℕ) :
    ∃ a : A, x.val n = Submodule.Quotient.mk a :=
  (Submodule.Quotient.mk_surjective _ (x.val n)).imp fun _ h ↦ h.symm

/-- The coordinate at `n` of an element of the completion is the reduction of a representative of
its coordinate at `n + 1`. -/
private theorem val_eq_of_val_succ_eq {N : Type*} [AddCommGroup N] [Module A N]
    {x : AdicCompletion I N} {n : ℕ} {a : N} (ha : x.val (n + 1) = Submodule.Quotient.mk a) :
    x.val n = Submodule.Quotient.mk a := by
  rw [← x.property (Nat.le_succ n), ha, transitionMap, factorPow, ← mkQ_apply, factor_mk,
    mkQ_apply]

variable [IsScalarTower R A M]

/-- The extension of an `R`-derivation `D : A → M` to the `I`-adic completions. If `x` is
represented by `a` modulo `I ^ (n + 1)`, then its image is represented by `D a` modulo `I ^ n`
(`Derivation.val_adicCompletion_apply`). -/
noncomputable def adicCompletion (D : Derivation R A M) :
    Derivation R (AdicCompletion I A) (AdicCompletion I M) where
  toFun := adicCompletionFun I D
  map_add' x y := by
    ext n
    obtain ⟨a, ha⟩ := exists_val_eq I x (n + 1)
    obtain ⟨b, hb⟩ := exists_val_eq I y (n + 1)
    rw [val_add_apply, adicCompletionFun_val I D ha, adicCompletionFun_val I D hb,
      adicCompletionFun_val I D (a := a + b) (by rw [val_add_apply, ha, hb, Quotient.mk_add]),
      map_add, Quotient.mk_add]
  map_smul' r x := by
    ext n
    obtain ⟨a, ha⟩ := exists_val_eq I x (n + 1)
    rw [RingHom.id_apply, val_smul_apply, adicCompletionFun_val I D ha,
      adicCompletionFun_val I D (a := r • a) (by rw [val_smul_apply, ha, Quotient.mk_smul]),
      map_smul, Quotient.mk_smul]
  map_one_eq_zero' := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, val_zero_apply]
    rw [adicCompletionFun_val I D (a := 1) (by rw [val_one, Ideal.Quotient.mk_eq_mk, map_one]),
      map_one_eq_zero, Quotient.mk_zero]
  leibniz' x y := by
    ext n
    obtain ⟨a, ha⟩ := exists_val_eq I x (n + 1)
    obtain ⟨b, hb⟩ := exists_val_eq I y (n + 1)
    simp only [LinearMap.coe_mk, AddHom.coe_mk, val_add_apply, smul_eval]
    rw [adicCompletionFun_val I D ha, adicCompletionFun_val I D hb,
      adicCompletionFun_val I D (a := a * b)
        (by rw [val_mul, ha, hb, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.mk_eq_mk, ← map_mul,
          Ideal.Quotient.mk_eq_mk]),
      val_eq_of_val_succ_eq I ha, val_eq_of_val_succ_eq I hb, leibniz, Quotient.mk_add,
      Quotient.mk_smul, Quotient.mk_smul, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.mk_eq_mk,
      mk_smul_mk, mk_smul_mk]

/-- If `x` is represented by `a` modulo `I ^ (n + 1)`, then `D̂ x` is represented by `D a`
modulo `I ^ n`. -/
theorem val_adicCompletion_apply (D : Derivation R A M) {x : AdicCompletion I A} {n : ℕ} {a : A}
    (ha : x.val (n + 1) = Submodule.Quotient.mk a) :
    (D.adicCompletion I x).val n = Submodule.Quotient.mk (D a) :=
  adicCompletionFun_val I D ha

/-- The extension of `D` to the completions agrees with `D` on `A`. -/
@[simp]
theorem adicCompletion_of (D : Derivation R A M) (a : A) :
    D.adicCompletion I (of I A a) = of I M (D a) := by
  ext n
  exact D.val_adicCompletion_apply I (of_apply I A a (n + 1))

/-- A derivation of the completion vanishing on `A` is `A`-linear. -/
private theorem smul_apply_of_apply_of_eq_zero {N : Type*} [AddCommGroup N]
    [Module (AdicCompletion I A) N] [Module R N] [Module A N]
    [IsScalarTower A (AdicCompletion I A) N] (Δ : Derivation R (AdicCompletion I A) N)
    (h : ∀ a : A, Δ (of I A a) = 0) (a : A) (x : AdicCompletion I A) :
    Δ (a • x) = a • Δ x := by
  have hof : algebraMap A (AdicCompletion I A) a = of I A a := by
    rw [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Algebra.smul_def, leibniz, hof, h, smul_zero, add_zero, ← hof, algebraMap_smul]

/-- For a finitely generated ideal `I`, an `R`-derivation of the `I`-adic completion of `A` into
an `I`-adically separated module, such as the completion of an `A`-module, is determined by its
values on `A`. -/
theorem adicCompletion_ext (hI : I.FG) {N : Type*} [AddCommGroup N]
    [Module (AdicCompletion I A) N] [Module R N] [Module A N]
    [IsScalarTower A (AdicCompletion I A) N] [IsHausdorff I N]
    {D₁ D₂ : Derivation R (AdicCompletion I A) N} (h : ∀ a : A, D₁ (of I A a) = D₂ (of I A a)) :
    D₁ = D₂ := by
  rw [← sub_eq_zero]
  set Δ := D₁ - D₂
  have hΔ (a : A) : Δ (of I A a) = 0 := by simp [Δ, h]
  refine Derivation.ext fun x ↦ ?_
  rw [zero_apply, IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  rw [SModEq.zero]
  -- `x` is congruent modulo `I ^ n` to an element of `A`, on which `Δ` vanishes
  obtain ⟨a, ha⟩ := exists_val_eq I x n
  have hmem : x - of I A a ∈ (I ^ n • ⊤ : Submodule A (AdicCompletion I A)) := by
    rw [pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, eval_of, eval_apply, ha,
      mkQ_apply, sub_self]
  have hΔx : Δ x = Δ (x - of I A a) := by rw [map_sub, hΔ, sub_zero]
  rw [hΔx]
  refine Submodule.smul_induction_on hmem (fun b hb y _ ↦ ?_) fun y z hy hz ↦ ?_
  · rw [smul_apply_of_apply_of_eq_zero I Δ hΔ]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  · rw [map_add]
    exact add_mem hy hz

/-- For a finitely generated ideal `I`, the extension `D̂` is the only derivation of the
completions agreeing with `D` on `A`. -/
theorem eq_adicCompletion (hI : I.FG) (D : Derivation R A M)
    {D' : Derivation R (AdicCompletion I A) (AdicCompletion I M)}
    (h : ∀ a : A, D' (of I A a) = of I M (D a)) : D' = D.adicCompletion I :=
  adicCompletion_ext I hI fun a ↦ by rw [h, adicCompletion_of]

end Derivation
