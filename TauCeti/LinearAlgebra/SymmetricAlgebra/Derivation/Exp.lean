/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.OfEnd
public import TauCeti.RingTheory.Derivation.TaylorExp
import TauCeti.RingTheory.Derivation.LocallyNilpotent

/-!
# Exponentials of nilpotent endomorphisms on a symmetric algebra

A linear endomorphism `f` of a module `M` acts on the symmetric algebra `S(M)` in two ways: by the
algebra endomorphism `SymmetricAlgebra.map f`, and by the derivation
`SymmetricAlgebra.derivationOfEnd R M f` extending it. When `f` is nilpotent the two are related
by exponentiation. The derivation `D_f` is then locally nilpotent, because its iterates send the
generator `ι x` to `ι (fⁿ x)` and the generators span `S(M)` as an algebra. Over a `ℚ`-algebra its
Taylor exponential `∑ D_fⁿ / n!` is an algebra endomorphism of `S(M)`
(`Derivation.taylorExp`), and it is the map induced by the endomorphism `exp f` of `M`:

`map (exp f) = exp D_f`.

Consequently every element of `S(M)` killed by `D_f` is fixed by `map (exp f)`. This is how
infinitesimal invariance under a Lie algebra acting nilpotently passes to invariance under the
corresponding unipotent automorphisms: for the adjoint action of a Lie algebra `L`, the
exponentials `exp (ad x)` generate the group of inner automorphisms of `L`, whose invariant
polynomial functions Chevalley's restriction theorem describes.

## Main results

* `SymmetricAlgebra.exists_iterate_derivationOfEnd_eq_zero`: `D_f` is locally nilpotent when `f`
  is nilpotent.
* `SymmetricAlgebra.iterate_derivationOfEnd_prod_ι_eq_zero`: if `f ^ k = 0`, then `D_f` kills
  every product of `n` generators after `n * (k - 1) + 1` iterations.
* `SymmetricAlgebra.taylorExp_derivationOfEnd`: `exp D_f = map (exp f)`.
* `SymmetricAlgebra.map_exp_apply_of_derivationOfEnd_eq_zero`: an element killed by `D_f` is
  fixed by `map (exp f)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §2.3, for
  exponentials of nilpotent derivations, and §23.1, where the invariance of polynomial functions
  under the inner automorphisms is used.
* G. Freudenburg, *Algebraic Theory of Locally Nilpotent Derivations*, Chapter 1, for the
  exponential of a locally nilpotent derivation.
-/

public section

namespace SymmetricAlgebra

open Finset

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The derivation induced by a nilpotent endomorphism is locally nilpotent**: some iterate of it
kills each element of the symmetric algebra. -/
theorem exists_iterate_derivationOfEnd_eq_zero {f : Module.End R M} (hf : IsNilpotent f)
    (p : SymmetricAlgebra R M) : ∃ n, (derivationOfEnd R M f)^[n] p = 0 := by
  obtain ⟨n, hn⟩ := hf
  refine (derivationOfEnd R M f).exists_iterate_eq_zero_of_adjoin_eq_top
    (adjoin_range_ι R M) ?_ p
  rintro _ ⟨x, rfl⟩
  exact ⟨n, by rw [iterate_derivationOfEnd_ι, hn, LinearMap.zero_apply, map_zero]⟩

/-- **Nilpotency on products of generators**: if `f ^ k = 0`, then the derivation induced by `f`
kills every product of `n` generators after `n * (k - 1) + 1` iterations. -/
theorem iterate_derivationOfEnd_prod_ι_eq_zero {f : Module.End R M} {k : ℕ} (hf : f ^ k = 0)
    {n : ℕ} (v : Fin n → M) {j : ℕ} (hj : n * (k - 1) < j) :
    (derivationOfEnd R M f)^[j] (∏ i, ι R M (v i)) = 0 := by
  induction n generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hj
    simp [Function.iterate_succ_apply]
  | succ n ih =>
    rw [Fin.prod_univ_succ, Derivation.iterate_apply_mul]
    refine sum_eq_zero fun ab hab ↦ ?_
    rw [mem_antidiagonal] at hab
    by_cases ha : k ≤ ab.1
    · have h : (f ^ ab.1) (v 0) = 0 := by
        rw [← Nat.sub_add_cancel ha, pow_add, hf, mul_zero, LinearMap.zero_apply]
      rw [iterate_derivationOfEnd_ι, h, map_zero, zero_mul, smul_zero]
    · rw [ih _ (j := ab.2) (by rw [Nat.succ_mul] at hj; omega), mul_zero, smul_zero]

variable [Module ℚ M]

/-- **The exponential of the derivation induced by a nilpotent endomorphism** `f` is the algebra
map induced by `exp f`: `exp D_f = map (exp f)`. -/
theorem taylorExp_derivationOfEnd [Algebra ℚ (SymmetricAlgebra R M)] {f : Module.End R M}
    (hf : IsNilpotent f) :
    (derivationOfEnd R M f).taylorExp (exists_iterate_derivationOfEnd_eq_zero hf) =
      map R (IsNilpotent.exp f) := by
  refine (map_unique R _ _).mp fun x ↦ ?_
  obtain ⟨n, hn⟩ := hf
  have hfx : (f ^ n) x = 0 := by rw [hn, LinearMap.zero_apply]
  rw [Derivation.taylorExp_apply_eq_sum _ _ (n := n) (by rw [iterate_derivationOfEnd_ι, hfx,
      map_zero]), IsNilpotent.exp_eq_sum hn, LinearMap.sum_apply, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [iterate_derivationOfEnd_ι, LinearMap.smul_apply, map_rat_smul]

/-- **Infinitesimal invariants of a nilpotent endomorphism are fixed by its exponential.** If the
derivation induced by a nilpotent endomorphism `f` kills `p`, then the algebra map induced by
`exp f` fixes `p`. -/
theorem map_exp_apply_of_derivationOfEnd_eq_zero [Algebra ℚ R] {f : Module.End R M}
    (hf : IsNilpotent f) {p : SymmetricAlgebra R M} (hp : derivationOfEnd R M f p = 0) :
    map R (IsNilpotent.exp f) p = p := by
  -- The symmetric algebra of a module over a `ℚ`-algebra is a `ℚ`-algebra through its scalars.
  let : Algebra ℚ (SymmetricAlgebra R M) :=
    ((algebraMap R (SymmetricAlgebra R M)).comp (algebraMap ℚ R)).toAlgebra
  rw [← taylorExp_derivationOfEnd hf]
  exact Derivation.taylorExp_apply_of_apply_eq_zero _ _ hp

end SymmetricAlgebra
