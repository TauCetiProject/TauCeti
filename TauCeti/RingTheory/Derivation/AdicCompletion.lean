/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.Basic
import TauCeti.RingTheory.Derivation.Basic
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
* `Derivation.liftAdicCompletion`: the extension of `D : A → N` to `Â → N` when `N` is an
  `I`-adically complete `Â`-module, such as `Â` itself.

## Main results

* `Derivation.val_adicCompletion_apply`: `D̂ x` is represented by `D a` modulo `I ^ n` when `x` is
  represented by `a` modulo `I ^ (n + 1)`.
* `Derivation.adicCompletion_of`: `D̂` extends `D`.
* `Derivation.adicCompletion_ext`: for finitely generated `I`, a derivation from `Â` into an
  `I`-adically separated module, such as `M̂`, is determined by its values on `A`;
  `Derivation.eq_adicCompletion` characterises `D̂` accordingly.
* `Derivation.liftAdicCompletion_of` and `Derivation.eq_liftAdicCompletion`: for finitely
  generated `I` and an `I`-adically complete `Â`-module `N`, the extension of `D : A → N` to `Â`
  agrees with `D` on `A` and is the only derivation `Â → N` that does.
-/

public section

open Submodule AdicCompletion

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M] (I : Ideal A)

/-- Applying `D` to the terms of an `I`-adic Cauchy sequence, shifted by one, gives an `I`-adic
Cauchy sequence. -/
private noncomputable def adicCauchySequenceMap (D : Derivation R A M)
    (f : AdicCauchySequence I A) : AdicCauchySequence I M :=
  AdicCauchySequence.mk I M (fun n ↦ D (f (n + 1)))
    fun n ↦ D.apply_smodEq_of_smodEq (f.property (Nat.le_succ (n + 1)))

/-- The underlying function of `Derivation.adicCompletion`, through a choice of Cauchy
representative. -/
private noncomputable def adicCompletionFun (D : Derivation R A M) (x : AdicCompletion I A) :
    AdicCompletion I M :=
  AdicCompletion.mk I M (adicCauchySequenceMap I D (AdicCompletion.mk_surjective I A x).choose)

private theorem adicCompletionFun_val (D : Derivation R A M) {x : AdicCompletion I A} {n : ℕ}
    {a : A} (ha : x.val (n + 1) = Submodule.Quotient.mk a) :
    (adicCompletionFun I D x).val n = Submodule.Quotient.mk (D a) := by
  have hx := congrArg (fun y ↦ y.val (n + 1)) (AdicCompletion.mk_surjective I A x).choose_spec
  rw [adicCompletionFun, mk_apply_coe, mkQ_apply, adicCauchySequenceMap, AdicCauchySequence.mk_coe]
  refine SModEq.def.mp (D.apply_smodEq_of_smodEq ?_)
  rw [SModEq.def, ← ha, ← hx, mk_apply_coe, mkQ_apply]

/-- Every coordinate of an element of the completion has a representative. -/
private theorem exists_val_eq (x : AdicCompletion I A) (n : ℕ) :
    ∃ a : A, x.val n = Submodule.Quotient.mk a :=
  (Submodule.Quotient.mk_surjective _ (x.val n)).imp fun _ h ↦ h.symm

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
    have hab : (x + y).val (n + 1) = Submodule.Quotient.mk (a + b) := by simp [ha, hb]
    simp [adicCompletionFun_val I D ha, adicCompletionFun_val I D hb, adicCompletionFun_val I D hab]
  map_smul' r x := by
    ext n
    obtain ⟨a, ha⟩ := exists_val_eq I x (n + 1)
    have hra : (r • x).val (n + 1) = Submodule.Quotient.mk (r • a) := by
      rw [val_smul_apply, ha, Quotient.mk_smul]
    simp [val_smul_apply, adicCompletionFun_val I D ha, adicCompletionFun_val I D hra]
  map_one_eq_zero' := by
    ext n
    have h1 : (1 : AdicCompletion I A).val (n + 1) = Submodule.Quotient.mk 1 := by simp
    simp [adicCompletionFun_val I D h1]
  leibniz' x y := by
    ext n
    obtain ⟨a, ha⟩ := exists_val_eq I x (n + 1)
    obtain ⟨b, hb⟩ := exists_val_eq I y (n + 1)
    have hab : (x * y).val (n + 1) = Submodule.Quotient.mk (a * b) := by simp [ha, hb]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, adicCompletionFun_val I D hab, val_add,
      Pi.add_apply, smul_eval, adicCompletionFun_val I D ha, adicCompletionFun_val I D hb,
      val_eq_mk_of_le I n.le_succ ha, val_eq_mk_of_le I n.le_succ hb, Ideal.Quotient.mk_eq_mk,
      mk_smul_mk, leibniz, Quotient.mk_add, Quotient.mk_smul]

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
  · -- `Δ` vanishes on `A`, so it is `A`-linear
    have hΔA (a : A) : Δ (algebraMap A (AdicCompletion I A) a) = 0 := by
      rw [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΔ]
    rw [← coe_ofMapAlgebraMap Δ hΔA, map_smul]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  · rw [map_add]
    exact add_mem hy hz

/-- For a finitely generated ideal `I`, the extension `D̂` is the only derivation of the
completions agreeing with `D` on `A`. -/
theorem eq_adicCompletion (hI : I.FG) (D : Derivation R A M)
    {D' : Derivation R (AdicCompletion I A) (AdicCompletion I M)}
    (h : ∀ a : A, D' (of I A a) = of I M (D a)) : D' = D.adicCompletion I :=
  adicCompletion_ext I hI fun a ↦ by rw [h, adicCompletion_of]

section IsAdicComplete

variable {N : Type*} [AddCommGroup N] [Module (AdicCompletion I A) N] [Module A N] [Module R N]
  [IsScalarTower A (AdicCompletion I A) N] [IsScalarTower R A N] [IsAdicComplete I N]

/-- For a finitely generated ideal `I` and an `I`-adically complete module `N` over the
completion `Â`, an `R`-derivation `D : A → N` extends to an `R`-derivation `Â → N`: the extension
`Â → N̂` of `D` followed by the inverse of the canonical isomorphism `N ≃ N̂`, which is `Â`-linear
by `AdicCompletion.of_smul`. By `Derivation.eq_liftAdicCompletion` it is the only derivation
`Â → N` agreeing with `D` on `A`. -/
noncomputable def liftAdicCompletion (hI : I.FG) (D : Derivation R A N) :
    Derivation R (AdicCompletion I A) N :=
  haveI := IsScalarTower.to₁₃₄ R A (AdicCompletion I A) N
  haveI := IsScalarTower.to₁₃₄ R A (AdicCompletion I A) (AdicCompletion I N)
  let e : AdicCompletion I N →ₗ[AdicCompletion I A] N :=
    { toFun := (ofLinearEquiv I N).symm
      map_add' := map_add _
      map_smul' x m := (ofLinearEquiv I N).injective <| by
        simp [AdicCompletion.of_smul hI] }
  e.compDer (D.adicCompletion I)

/-- The image of `D.liftAdicCompletion I hI x` in the completion `N̂` is `D̂ x`. -/
@[simp]
theorem of_liftAdicCompletion (hI : I.FG) (D : Derivation R A N) (x : AdicCompletion I A) :
    of I N (D.liftAdicCompletion I hI x) = D.adicCompletion I x :=
  of_ofLinearEquiv_symm I (D.adicCompletion I x)

/-- The extension of `D : A → N` to the completion agrees with `D` on `A`. -/
@[simp]
theorem liftAdicCompletion_of (hI : I.FG) (D : Derivation R A N) (a : A) :
    D.liftAdicCompletion I hI (of I A a) = D a :=
  (ofLinearEquiv I N).injective <| by simp

/-- For a finitely generated ideal `I` and an `I`-adically complete `Â`-module `N`, the extension
`D.liftAdicCompletion I hI` is the only derivation `Â → N` agreeing with `D` on `A`. -/
theorem eq_liftAdicCompletion (hI : I.FG) (D : Derivation R A N)
    {D' : Derivation R (AdicCompletion I A) N} (h : ∀ a : A, D' (of I A a) = D a) :
    D' = D.liftAdicCompletion I hI :=
  adicCompletion_ext I hI fun a ↦ by rw [h, liftAdicCompletion_of]

end IsAdicComplete

end Derivation
