/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.PolynomialRing.Basic

/-!
# Injectivity of the presentation, and the rank-one case

The injectivity half of **Shimura's Theorem 3.20** at rank one, and the transfer of injectivity
from `evalHom` to its codomain restriction `evalHomLocal`. The generators and the surjectivity half
at rank one are in `PolynomialRing/Basic.lean`; the theorem at every rank, for prime `p`, is
`HeckeRing.GLn.polynomialRingEquiv` in `PolynomialRing/Triangular.lean`.

At rank one the generator is the scalar coset `T(p)`, its powers are the cosets `T(p ^ k)`, and
these are distinct as soon as `1 < p`. This needs no primality, so the rank-one isomorphism is
stated for every `1 < p`.

## Main results

* `HeckeRing.GLn.evalHom_one_injective`: evaluation at the generator is injective for `n = 1`.
* `HeckeRing.GLn.evalHomLocal_injective`: injectivity passes from `evalHom` to `evalHomLocal`.
* `HeckeRing.GLn.polynomialRingEquivOne`: **Shimura, Theorem 3.20** for `n = 1` and any `1 < p`,
  `pLocalSubring ≅ ℤ[X]`.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), the `Inj` section.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

public section

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

attribute [local instance] commSemiringIntegralHeckeRingLocal

/-- For n=1, `heckeGen(0)^k = diagElem(fun _ => p^k)`. -/
private lemma heckeGen_pow_one (p : ℕ) (hp : 0 < p) (k : ℕ) :
    heckeGen 1 p (0 : Fin 1) ^ k = diagElem (fun _ : Fin 1 ↦ p ^ k) := by
  -- `heckeGen` is sealed (`public section`, no `@[expose]`), so neither `rw [heckeGen]` nor
  -- `unfold` sees through it; `heckeGen_def` supplies the equation and this states its target.
  rw [show heckeGen 1 p (0 : Fin 1) = diagElem (fun _ : Fin 1 ↦ p) from by
    rw [heckeGen_def]; exact congrArg diagElem (heckeGenDiag_one_eq_const p)]
  exact diagElem_const_pow 1 p hp k

/-- For `n = 1` and any base `1 < p`, the cosets `diagCoset (fun _ => p^k)` are injective in `k`:
if they coincide for `b 0` and `s 0`, then `b 0 = s 0`. -/
private lemma T_diag_one_ppow_inj (p : ℕ) (hp : 1 < p) {b s : Fin 1 →₀ ℕ}
    (hb : (diagCoset (n := 1) (fun _ ↦ p ^ b 0) : HeckeCoset (posDetInt 1) (SLnZ 1) (SLnZ 1)) =
      diagCoset (fun _ ↦ p ^ s 0)) : b 0 = s 0 := by
  -- each diagonal here is constant, so the chain condition is `isDvdChain_const`
  have hdiv : ∀ c : Fin 1 →₀ ℕ, IsDvdChain (fun _ : Fin 1 ↦ p ^ c 0) :=
    fun c ↦ isDvdChain_const 1 (p ^ c 0)
  have hpos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le
  have heq := eq_of_diagCoset_eq (fun _ ↦ Nat.pow_pos hpos)
    (fun _ ↦ Nat.pow_pos hpos) (hdiv b) (hdiv s) hb
  exact Nat.pow_right_injective hp (congr_fun heq 0)

/-- For `n = 1` and any base `1 < p`, evaluation at the Hecke generator is injective. -/
theorem evalHom_one_injective (p : ℕ) (hp : 1 < p) : Function.Injective (evalHom 1 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]
  set R := P - Q
  have hR : evalHom 1 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hne
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hne
  have hcoeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  set D := diagCoset (n := 1) (fun _ ↦ p ^ (s 0))
  have h0 : evalHom 1 p R D = 0 := by rw [hR]; rfl
  apply hcoeff
  suffices h : evalHom 1 p R D = R.coeff s from h ▸ h0
  rw [evalHom_apply]
  classical
  -- each monomial `X^k` evaluates to the basis element at `T(p^k)`, so its contribution at
  -- `D = T(p^{s 0})` is its own coefficient when `k = s 0` and zero otherwise
  have hterm : ∀ x ∈ R.support,
      R.coeff x • (∏ i, heckeGen 1 p i ^ x i : IntegralHeckeRing 1) D =
        if x = s then R.coeff s else 0 := by
    intro x _
    rw [Fin.prod_univ_one, heckeGen_pow_one p (Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le),
      diagElem_def, HeckeCosetModule.single_apply]
    by_cases hxs : x = s
    · subst hxs; simp [D]
    · rw [ite_eq_right (fun hb ↦ hxs (Finsupp.ext fun j ↦ by
        rw [Fin.fin_one_eq_zero j]; exact T_diag_one_ppow_inj p hp hb)),
        ite_eq_right hxs, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq_of_mem' R.support s _ hs]

/-- Injectivity transfers from `evalHom` to its codomain restriction `evalHomLocal`: two
polynomials with the same image in `pLocalSubring` have the same image in the ambient ring. -/
lemma evalHomLocal_injective (n : ℕ) [NeZero n] (p : ℕ)
    (h_inj : Function.Injective (evalHom n p)) :
    Function.Injective (evalHomLocal n p) := by
  intro P Q hPQ
  refine h_inj ?_
  -- not `RingHom.injective_codRestrict`: its `f`, `s`, `h` are implicit and only solvable by
  -- unfolding `evalHomLocal`, which is sealed here ("definition is not exposed").
  -- `evalHomLocal_coe` is the exported stand-in for that unfolding.
  rw [← evalHomLocal_coe n p P, ← evalHomLocal_coe n p Q, hPQ]

variable (p : ℕ)

/-- **Shimura, Theorem 3.20 for `n = 1`**: the `p`-local Hecke ring of `GL₁` is the
polynomial ring `ℤ[X]` on the single generator `T(p)`.

Stated for `1 < p` rather than `p.Prime`: rank one needs only that `k ↦ p^k` is injective. -/
noncomputable def polynomialRingEquivOne (hp : 1 < p) :
    MvPolynomial (Fin 1) ℤ ≃+* pLocalSubring 1 p :=
  RingEquiv.ofBijective (evalHomLocal 1 p)
    ⟨evalHomLocal_injective 1 p (evalHom_one_injective p hp),
     evalHomLocal_one_surjective p (Nat.zero_lt_of_lt hp)⟩

/-- The rank-one presentation isomorphism is the evaluation map. -/
@[simp] lemma polynomialRingEquivOne_apply (hp : 1 < p) (f : MvPolynomial (Fin 1) ℤ) :
    polynomialRingEquivOne p hp f = evalHomLocal 1 p f := (rfl)

end HeckeRing.GLn
