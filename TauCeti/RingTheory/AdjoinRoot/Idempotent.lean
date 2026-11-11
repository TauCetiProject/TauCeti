/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Jacobson.Ideal
import TauCeti.Algebra.Polynomial.AlgebraMap
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.RingTheory.Idempotents.Jacobson
import TauCeti.RingTheory.Idempotents.Projective

/-!
# Simple roots modulo an ideal and idempotents of `R[X]/(f)`

Let `I` be an ideal of `R` and `f` a polynomial over `R`. A simple root `a₀` of `f` modulo `I`
gives an element of `R[X]/(f)` that is idempotent modulo `I` and cuts out the factor
`R[X]/(X - a₀)`. Conversely, if `f` is monic and `I` lies in the Jacobson radical, an idempotent
of `R[X]/(f)` cutting out such a factor modulo `I` yields a root `a ≡ a₀` of `f`. These are the
two halves of the passage from lifting idempotents of finite algebras to lifting simple roots.

## Main results

* `TauCeti.exists_mul_self_sub_mem_of_isUnit_eval_derivative`: a simple root `a₀` of `f` modulo
  `I` gives an element `γ` of `R[X]/(f)`, idempotent modulo `I`, with `(X - a₀) γ ≡ 0` and
  `r γ ≡ 0` modulo `I` only for `r ∈ I`.
* `Polynomial.Monic.exists_isRoot_of_isIdempotentElem`: for monic `f` and `I` in the Jacobson
  radical, an idempotent `e` of `R[X]/(f)` with these properties gives a root `a ≡ a₀` of `f`.

## Implementation notes

For the root: Nakayama's lemma gives `e R[X]/(f) = R e`, so `X e = a e` for some `a : R`. The
`R`-module `R e` is projective, being a direct summand of the free module `R[X]/(f)`, and this
forces it to be free on `e`, so `f(a) e = f(X) e = 0` gives `f(a) = 0`.

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), proof of
  (3) ⇒ (1).
-/

public section

open Polynomial

variable {R : Type*} [CommRing R]

namespace TauCeti

/-- Let `a₀` be a simple root modulo `I` of `f`. Then `R[X]/(f)` has an element `γ` that is
idempotent modulo `I`, with `(X - a₀) γ ≡ 0` modulo `I`, such that `r γ ≡ 0` modulo `I` only for
`r ∈ I`: with `f = (X - a₀) q + f(a₀)` and `u f'(a₀) ≡ 1`, take `γ = u q(X)`. -/
theorem exists_mul_self_sub_mem_of_isUnit_eval_derivative {I : Ideal R} {f : R[X]}
    {a₀ : R} (hfa₀ : f.eval a₀ ∈ I)
    (hunit : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ γ : AdjoinRoot f, γ * γ - γ ∈ I.map (algebraMap R (AdjoinRoot f)) ∧
      (AdjoinRoot.root f - algebraMap R _ a₀) * γ ∈ I.map (algebraMap R (AdjoinRoot f)) ∧
      ∀ r : R, r • γ ∈ I.map (algebraMap R (AdjoinRoot f)) → r ∈ I := by
  set S := AdjoinRoot f
  set J := I.map (algebraMap R S)
  set x := AdjoinRoot.root f
  -- Evaluation at `a₀` modulo `I` kills `J`.
  let χ : S →ₐ[R] R ⧸ I :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R (R ⧸ I)) (Ideal.Quotient.mk I a₀) (by
      rw [Algebra.toRingHom_ofId, Ideal.Quotient.algebraMap_eq, eval₂_hom,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hfa₀)
  have hχJ : ∀ y ∈ J, χ y = 0 := by
    refine fun y hy ↦ (Ideal.map_le_iff_le_comap.mpr fun r hr ↦ ?_ : J ≤ RingHom.ker χ) hy
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hr
  -- Split off the root modulo `I`: `f = (X - a₀) q + f(a₀)` and `q(a₀) = f'(a₀)`.
  set q := f /ₘ (X - C a₀)
  have hfq : (X - C a₀) * q + C (f.eval a₀) = f := by
    rw [← modByMonic_X_sub_C_eq_C_eval, add_comm, modByMonic_add_div f (X - C a₀)]
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv'.mp hunit
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← eval_divByMonic_X_sub_C_self, ← map_one (Ideal.Quotient.mk I),
    Ideal.Quotient.eq] at hv
  -- `γ = u q(x)` is idempotent modulo `J`, with `(x - a₀) γ ∈ J` and `χ(γ) = 1`.
  have hxq : (x - algebraMap R S a₀) * aeval x q ∈ J := by
    have hfx : aeval x f = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have := congrArg (aeval x) hfq
    rw [map_add, map_mul, map_sub, aeval_X, aeval_C, aeval_C, hfx] at this
    rw [eq_neg_of_add_eq_zero_left this]
    exact neg_mem (Ideal.mem_map_of_mem _ hfa₀)
  set γ := algebraMap R S u * aeval x q
  refine ⟨γ, ?_, ?_, fun r hr ↦ ?_⟩
  · have h1 := aeval_sub_algebraMap_eval_mul_mem hxq q
    have h2 : algebraMap R S (u * q.eval a₀ - 1) ∈ J := Ideal.mem_map_of_mem _ hv
    have : γ * γ - γ = algebraMap R S u ^ 2 * ((aeval x q - algebraMap R S (q.eval a₀)) *
        aeval x q) + γ * algebraMap R S (u * q.eval a₀ - 1) := by
      simp only [γ, map_sub, map_mul, map_one]
      ring
    rw [this]
    exact add_mem (J.mul_mem_left _ h1) (J.mul_mem_left _ h2)
  · rw [mul_left_comm]
    exact J.mul_mem_left _ hxq
  · have hχγ : χ γ = 1 := by
      simpa [γ, χ, x, S, q] using Ideal.Quotient.eq.mpr hv
    have := hχJ _ hr
    rwa [map_smul, hχγ, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem] at this

end TauCeti

namespace Polynomial.Monic

/-- Let `I` lie in the Jacobson radical of `R`, let `f` be monic and let `e` be an idempotent of
`R[X]/(f)` with `(X - a₀) e ≡ 0` modulo `I`, such that `r e ≡ 0` modulo `I` only for `r ∈ I`.
Then `f` has a root `a ≡ a₀` modulo `I`: Nakayama's lemma gives `e R[X]/(f) = R e`, so
`X e = a e`, and `R e` is free on `e`. -/
theorem exists_isRoot_of_isIdempotentElem {I : Ideal R} {f : R[X]} (hf : f.Monic)
    (hjac : I ≤ Ring.jacobson R) {a₀ : R} {e : AdjoinRoot f} (he : IsIdempotentElem e)
    (hxe : (AdjoinRoot.root f - algebraMap R _ a₀) * e ∈ I.map (algebraMap R (AdjoinRoot f)))
    (hI : ∀ r : R, r • e ∈ I.map (algebraMap R (AdjoinRoot f)) → r ∈ I) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  have : Module.Free R (AdjoinRoot f) := hf.free_adjoinRoot
  have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  set x := AdjoinRoot.root f
  have hσ : ∀ y : AdjoinRoot f, ∃ σ : R, σ • e = e * y :=
    he.exists_smul_eq_mul_of_mul_sub_smul_mem (by simpa only [Ideal.jacobson_bot] using hjac)
      fun y ↦ by
        induction y using AdjoinRoot.induction_on with | ih p =>
        refine ⟨p.eval a₀, ?_⟩
        rw [← AdjoinRoot.aeval_eq, Algebra.smul_def, mul_comm e, ← sub_mul]
        exact aeval_sub_algebraMap_eval_mul_mem hxe p
  obtain ⟨a, ha⟩ := hσ x
  refine ⟨a, ?_, hI _ ?_⟩
  · -- `x e = a e` gives `f(a) e = f(x) e = 0`, and `r e = 0` forces `r c = 0` for a unit `c`.
    have hxa : (x - algebraMap R _ a) * e ∈ (⊥ : Ideal (AdjoinRoot f)) := by
      rw [Ideal.mem_bot, sub_mul, ← Algebra.smul_def, ha, mul_comm, sub_self]
    have hfa := aeval_sub_algebraMap_eval_mul_mem hxa f
    rw [Ideal.mem_bot, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_sub, neg_mul, neg_eq_zero,
      ← Algebra.smul_def] at hfa
    obtain ⟨c, hce, hc⟩ := he.exists_smul_eq_self_and_mul_eq_zero hσ
    have hcu : IsUnit c := Ideal.isUnit_of_sub_one_mem_jacobson _ (hjac (hI _ (by
      rw [sub_smul, hce, one_smul, sub_self]; exact zero_mem _)))
    exact hcu.mul_left_eq_zero.mp (hc _ hfa)
  · convert hxe using 1
    rw [sub_smul, ha, Algebra.smul_def]
    ring

end Polynomial.Monic
