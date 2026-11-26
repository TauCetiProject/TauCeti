/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Adic limits and the map to the adic completion

Let `I` be an ideal of a commutative ring `R` and `M` an `I`-adically Hausdorff `R`-module. An
`I`-adic limit of a sequence in `M` is unique, and `R`-linear maps preserve `I`-adic convergence,
since they map `I ^ n • M` into `I ^ n • M`. Consequently a linear map fixing every term of a
sequence fixes its `I`-adic limit. This is how a fixed-point equation such as `c * x = x` passes
from the terms of an `I`-adically convergent sequence in an algebra to its limit.

The coordinates of an element of the completion `AdicCompletion I M` are compatible: a
representative of its coordinate modulo `I ^ n` also represents its coordinate modulo `I ^ m` for
every `m ≤ n`.

The kernel of the canonical map `AdicCompletion.of I M : M → M̂` is `⋂ₙ Iⁿ M`, so it vanishes
exactly when `M` is `I`-adically Hausdorff. When `I` is finitely generated, `I M̂` is the kernel of
the evaluation at level one; hence the image of `M` and `I M̂` together span `M̂`, and an element of
`M` whose image lies in `I M̂` already lies in `I M`. These are the facts that the regular-element
reduction results in `TauCeti.RingTheory.AdicCompletion.Regular.Reduction` consume.

## Main results

* `IsHausdorff.map_eq_of_forall_sub_mem`: an `R`-linear endomorphism of an `I`-adically Hausdorff
  module that fixes every term of a sequence fixes its `I`-adic limit.
* `AdicCompletion.transitionMap_mk`: the transition maps send the class of an element to its
  class.
* `AdicCompletion.val_eq_mk_of_le`: a representative of a coordinate of an element of the
  completion represents all its lower coordinates.
* `IsHausdorff.iInf_pow_smul_top_eq_bot_of_span_singleton`: in an `(r)`-adically Hausdorff
  module, `⋂ₙ rⁿ M = 0`.
* `AdicCompletion.ker_of`, `AdicCompletion.ker_of_span_singleton`: the kernel of `M → M̂` is
  `⋂ₙ Iⁿ M`.
* `AdicCompletion.range_of_sup_smul_top_eq_top`: for finitely generated `I`, the image of `M` and
  `I M̂` span `M̂`.
* `AdicCompletion.smul_top_eq_ker_eval_one`, `AdicCompletion.comap_of_smul_top_le`: for finitely
  generated `I`, `I M̂` is the kernel of the evaluation at level one, and an element of `M` whose
  image lies in `I M̂` lies in `I M`.
-/

public section

variable {R : Type*} [CommRing R] (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]

/-- In an `I`-adically Hausdorff module, an `R`-linear endomorphism that fixes every term of a
sequence fixes its `I`-adic limit. -/
theorem IsHausdorff.map_eq_of_forall_sub_mem [IsHausdorff I M] (g : M →ₗ[R] M) {L : M}
    {x : ℕ → M} (hx : ∀ n, g (x n) = x n) (hL : ∀ n, L - x n ∈ I ^ n • (⊤ : Submodule R M)) :
    g L = L := by
  refine sub_eq_zero.mp <| IsHausdorff.haus' (I := I) (g L - L) fun n ↦ SModEq.sub_mem.mpr ?_
  have hsplit : g L - L - 0 = g (L - x n) - (L - x n) := by
    rw [map_sub, hx n, sub_zero, sub_sub_sub_cancel_right]
  rw [hsplit]
  exact sub_mem (Submodule.smul_top_le_comap_smul_top _ g (hL n)) (hL n)

/-- The transition map `M ⧸ I ^ n • M → M ⧸ I ^ m • M` sends the class of `a` to the class
of `a`. -/
@[simp]
theorem AdicCompletion.transitionMap_mk {m n : ℕ} (hmn : m ≤ n) (a : M) :
    transitionMap I M hmn (Submodule.Quotient.mk a) = Submodule.Quotient.mk a :=
  rfl

/-- A representative of the coordinate modulo `I ^ n` of an element of the `I`-adic completion
also represents its coordinate modulo `I ^ m` for every `m ≤ n`. -/
theorem AdicCompletion.val_eq_mk_of_le {x : AdicCompletion I M} {m n : ℕ} (hmn : m ≤ n) {a : M}
    (ha : x.val n = Submodule.Quotient.mk a) : x.val m = Submodule.Quotient.mk a := by
  rw [← x.property hmn, ha, AdicCompletion.transitionMap_mk]

open Pointwise

/-- In an `(r)`-adically Hausdorff module, `⋂ₙ rⁿ M = 0`. -/
theorem IsHausdorff.iInf_pow_smul_top_eq_bot_of_span_singleton {r : R}
    (h : IsHausdorff (Ideal.span {r}) M) : ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R M) = ⊥ := by
  simpa only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] using h.iInf_pow_smul

namespace AdicCompletion

open Submodule

/-- The kernel of the map from a module to its `I`-adic completion is `⋂ₙ Iⁿ M`. -/
@[simp]
theorem ker_of (M : Type*) [AddCommGroup M] [Module R M] :
    LinearMap.ker (of I M) = ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) := by
  ext x
  simp only [LinearMap.mem_ker, mem_iInf]
  refine ⟨fun hx n ↦ ?_, fun hx ↦ AdicCompletion.ext fun n ↦ ?_⟩
  · have := congrArg (fun y ↦ y.val n) hx
    simpa [of_apply, Submodule.Quotient.mk_eq_zero] using this
  · simpa [of_apply, Submodule.Quotient.mk_eq_zero] using hx n

/-- For a finitely generated ideal `I`, the submodule `I M̂` of the `I`-adic completion is the
kernel of the evaluation at level one. -/
theorem smul_top_eq_ker_eval_one {I : Ideal R} (hI : I.FG) {M : Type*} [AddCommGroup M]
    [Module R M] : (I • ⊤ : Submodule R (AdicCompletion I M)) = LinearMap.ker (eval I M 1) := by
  simpa using pow_smul_top_eq_ker_eval (M := M) (n := 1) hI

/-- For a finitely generated ideal `I`, the image of `M` and `I M̂` span the `I`-adic
completion `M̂`. -/
theorem range_of_sup_smul_top_eq_top {I : Ideal R} (hI : I.FG) (M : Type*) [AddCommGroup M]
    [Module R M] : LinearMap.range (of I M) ⊔ I • ⊤ = ⊤ := by
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (eval I M 1 y)
  have hy : y - of I M m ∈ I • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [smul_top_eq_ker_eval_one hI, LinearMap.mem_ker, map_sub, eval_of, ← hm, mkQ_apply,
      sub_self]
  simpa using add_mem_sup (LinearMap.mem_range_self (of I M) m) hy

/-- For a finitely generated ideal `I`, an element of `M` whose image in the `I`-adic completion
lies in `I M̂` already lies in `I M`. -/
theorem comap_of_smul_top_le {I : Ideal R} (hI : I.FG) (M : Type*) [AddCommGroup M]
    [Module R M] : (I • ⊤ : Submodule R (AdicCompletion I M)).comap (of I M) ≤ I • ⊤ := by
  intro m hm
  rw [mem_comap, smul_top_eq_ker_eval_one hI, LinearMap.mem_ker, eval_of, mkQ_apply,
    Submodule.Quotient.mk_eq_zero, pow_one] at hm
  exact hm

/-- The kernel of the map from a module to its `(r)`-adic completion is `⋂ₙ rⁿ M`. -/
theorem ker_of_span_singleton (r : R) (M : Type*) [AddCommGroup M] [Module R M] :
    LinearMap.ker (of (Ideal.span {r}) M) = ⨅ n : ℕ, r ^ n • (⊤ : Submodule R M) := by
  simp [Ideal.span_singleton_pow, ideal_span_singleton_smul]

end AdicCompletion
