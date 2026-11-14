/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical

/-!
# Changing the sign of the Temperley–Lieb loop parameter

Negating every generator identifies the algebras at loop parameters `-δ` and `δ`, over
any commutative ring. The isomorphism `signEquiv` commutes with strand inclusions and
with the analytic adjoint for self-adjoint loop parameters. Taking the trivial star on
the coefficient ring also gives compatibility with the linear word reversal.

An unnormalized Markov trace changes by the factor `(-1) ^ n` on `n` strands.
`signTrace` transports a Markov family, and `IsMarkovTrace.map_signEquiv` compares
any two Markov families at opposite parameters by uniqueness. In particular the sign
isomorphism preserves and reflects the multiplication-pairing trace radical, even
at zero loop parameter and in characteristic two.

This is an isomorphism of towers of algebras, not an identification of signed cups
in a tensor category: the cup and its zigzag sign are separate data.

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  Section 2.5, for signed cups and the Temperley–Lieb generators they determine.
-/

public section

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommRing R] {δ : R} {n : ℕ}

/-- Negating generators respects the presentation when the two loop values are opposites. -/
private def signHom (δ δ' : R) (h : δ = -δ') (n : ℕ) :
    TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ' n :=
  lift (fun i ↦ -e δ' i)
    (fun i ↦ by simp [h])
    (fun h ↦ by simpa using congrArg Neg.neg (e_mul_e_mul_e (δ := δ') h))
    (fun h ↦ by simpa using (commute_e (δ := δ') h).eq)

private theorem signHom_e (δ δ' : R) (h : δ = -δ') (i : Fin (n - 1)) :
    signHom δ δ' h n (e δ i) = -e δ' i :=
  lift_e _ _ _ _ i

/-- The sign isomorphism from loop parameter `-δ` to `δ`, sending `e i` to `-e i`.
It exists over every commutative ring, with no invertibility hypothesis on `δ`. -/
def signEquiv (δ : R) (n : ℕ) : TemperleyLieb R (-δ) n ≃ₐ[R] TemperleyLieb R δ n :=
  AlgEquiv.ofAlgHom (signHom (-δ) δ rfl n) (signHom δ (-δ) (neg_neg δ).symm n)
    (hom_ext fun i ↦ by simp [signHom_e])
    (hom_ext fun i ↦ by simp [signHom_e])

/-- The sign isomorphism negates each generator. -/
@[simp]
theorem signEquiv_e (i : Fin (n - 1)) : signEquiv δ n (e (-δ) i) = -e δ i :=
  signHom_e _ _ _ _

/-- The inverse sign isomorphism also negates each generator. -/
@[simp]
theorem signEquiv_symm_e (i : Fin (n - 1)) : (signEquiv δ n).symm (e δ i) = -e (-δ) i :=
  signHom_e _ _ _ _

/-- Changing the loop sign commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_strandIncl (x : TemperleyLieb R (-δ) (n + 1)) :
    signEquiv δ (n + 2) (strandIncl x) = strandIncl (signEquiv δ (n + 1) x) := by
  have h : (signEquiv δ (n + 2)).toAlgHom.comp strandIncl =
      strandIncl.comp (signEquiv δ (n + 1)).toAlgHom := hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun h x

/-- The inverse sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_symm_strandIncl (x : TemperleyLieb R δ (n + 1)) :
    (signEquiv δ (n + 2)).symm (strandIncl x) =
      strandIncl ((signEquiv δ (n + 1)).symm x) := by
  apply (signEquiv δ (n + 2)).injective
  simp

section Star

variable [StarRing R] [Fact (IsSelfAdjoint δ)]

local instance : Fact (IsSelfAdjoint (-δ)) := ⟨(Fact.out : IsSelfAdjoint δ).neg⟩

/-- The sign isomorphism preserves the analytic adjoint. For a trivial coefficient star,
this is compatibility with linear word reversal. -/
@[simp]
theorem signEquiv_star (x : TemperleyLieb R (-δ) n) :
    signEquiv δ n (star x) = star (signEquiv δ n x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint, signHom_e]) x

/-- The inverse sign isomorphism preserves the analytic adjoint. -/
@[simp]
theorem signEquiv_symm_star (x : TemperleyLieb R δ n) :
    (signEquiv δ n).symm (star x) = star ((signEquiv δ n).symm x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint, signHom_e]) x

end Star

/-- Transport a family of unnormalized traces from `-δ` to `δ`, with the degree-dependent
sign needed to retain the Markov normalization. -/
def signTrace (tr : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R) :
    ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R :=
  fun n ↦ (-1 : R) ^ n • (tr n ∘ₗ (signEquiv δ n).symm.toLinearMap)

/-- Evaluation of the transported trace. -/
@[simp]
theorem signTrace_apply (tr : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R)
    (x : TemperleyLieb R δ n) :
    signTrace tr n x = (-1 : R) ^ n * tr n ((signEquiv δ n).symm x) := (rfl)

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- The signed transport of a Markov family is again a Markov family, including at `δ = 0`. -/
theorem signTrace (htr' : IsMarkovTrace R (-δ) tr') :
    IsMarkovTrace R δ (TemperleyLieb.signTrace tr') where
  map_one n := by
    rw [signTrace_apply, _root_.map_one, htr'.map_one, ← mul_pow]
    simp
  map_mul_comm n x y := by simp only [signTrace_apply, map_mul, htr'.map_mul_comm]
  map_strandIncl n x := by
    simp only [signTrace_apply, signEquiv_symm_strandIncl, htr'.map_strandIncl]
    simp [pow_succ, mul_comm, mul_left_comm]
  map_strandIncl_mul_e_last n x := by
    simp only [signTrace_apply, map_mul, signEquiv_symm_strandIncl, signEquiv_symm_e,
      mul_neg, map_neg, htr'.map_strandIncl_mul_e_last]
    simp [pow_succ]

/-- At opposite loop parameters the unnormalized Markov traces differ by `(-1) ^ n`
under the sign isomorphism. No existence of either family is assumed implicitly. -/
theorem map_signEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    tr n (signEquiv δ n x) = (-1 : R) ^ n * tr' n x := by
  have h := congrFun (htr.unique htr'.signTrace) n
  simpa using LinearMap.congr_fun h (signEquiv δ n x)

/-- The sign isomorphism carries the trace radical at `-δ` exactly onto the one at `δ`.
This holds over commutative rings, so in particular at every complex loop parameter. -/
theorem signEquiv_mem_traceRadical_iff (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    signEquiv δ n x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔
      x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) := by
  simp only [LinearMap.mem_traceRadical]
  rw [(signEquiv δ n).surjective.forall]
  simp only [← map_mul, htr.map_signEquiv htr', neg_one_pow_mul_eq_zero_iff]

end IsMarkovTrace

end TauCeti.TemperleyLieb
