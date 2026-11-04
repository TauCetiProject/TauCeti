/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.NumberTheory.HeckeRing.GL2.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.PrimeDecomposition

/-!
# Generators of the `p`-local Hecke ring

Towards **Shimura's Theorem 3.20**, that the `p`-local Hecke ring `pLocalSubring` of `GL_n` is a
polynomial ring `ℤ[X₁, …, Xₙ]` on the `n` diagonal prime cosets. This file sets up the
generators and the evaluation map; the theorem itself is proved in
`PolynomialRing/Presentation.lean`.

## Main definitions

* `HeckeRing.GLn.heckeGenExponent k` — the exponent vector of the `k`-th generator's diagonal,
  `0` on the first `n - 1 - k` positions and `1` on the last `k + 1`.
* `HeckeRing.GLn.heckeGen k` — the `k`-th generator `T(1, …, 1, p, …, p)`, with `k + 1` entries
  equal to `p`.
* `HeckeRing.GLn.evalHom` — evaluation of `ℤ[X₁, …, Xₙ]` at the generators, into the ambient
  Hecke ring.
* `HeckeRing.GLn.evalHomLocal` — the same map with codomain `pLocalSubring n p`, which is the
  presentation map Theorem 3.20 is about.

## Main results

* `HeckeRing.GLn.heckeGen_mem_pLocalSubring`: each generator lies in `pLocalSubring`.
* `HeckeRing.GLn.evalHom_apply`: the coefficient of the image of a polynomial at a double coset.
* `HeckeRing.GLn.heckeGen_zero_eq_heckeTDiag`, `HeckeRing.GLn.heckeGen_one_eq_heckeTScalar`:
  for `n = 2` the generators are the classical `T(1, p)` and `T(p, p)`.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), first three sections.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

public section

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

/-- The `CommSemiring` structure this module needs on `IntegralHeckeRing n`, rebuilt **locally**
from the two public ingredients `HeckeCosetModule.instSemiringHeckeRing` and
`HeckeCosetModule.mul_comm_of_antiInvolution`.

`commSemiringIntegralHeckeRing` already packages exactly this, but as a sealed `def`: its body
does not reduce across the module boundary, so the `NonAssocSemiring` it carries is not
*definitionally* the ambient one and `MvPolynomial.eval₂Hom` will not typecheck against it.
Writing the same structure here makes its body transparent where it is needed and nowhere else,
which is why the upstream definitions stay sealed rather than `@[expose]`d. -/
noncomputable local instance commSemiringIntegralHeckeRingLocal [NeZero n] :
    CommSemiring (IntegralHeckeRing n) :=
  { (HeckeCosetModule.instSemiringHeckeRing ℤ : Semiring (IntegralHeckeRing n)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution n)
      (transposeAntiInvolution_onHeckeCoset_eq_self n) }

section TGen

variable (p : ℕ) (hp : p.Prime)

/-- The exponent vector of the `k`-th generator's diagonal: `0` on the first `n - 1 - k`
positions and `1` on the last `k + 1`, so that `heckeGenDiag n p k` is `p` raised to it
entrywise (`heckeGenDiag_eq_primePowDiag`). -/
def heckeGenExponent (k : Fin n) : Fin n → ℕ :=
  fun i ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1

/-- Defining equation for the sealed definition `heckeGenExponent`. -/
@[simp]
lemma heckeGenExponent_apply (k : Fin n) (i : Fin n) :
    heckeGenExponent n k i = if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1 :=
  -- `(rfl)` rather than `rfl`: see `heckeGenDiag_apply` below.
  (rfl)

/-- The diagonal for the k-th generator: `(1,...,1,p,...,p)` with `n-1-k` ones
    followed by `k+1` entries of `p`. Here `k : Fin n`, giving `n` generators. -/
def heckeGenDiag (k : Fin n) : Fin n → ℕ :=
  fun i ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p

@[simp]
lemma heckeGenDiag_apply (k : Fin n) (i : Fin n) :
    heckeGenDiag n p k i =
    if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p :=
  -- `(rfl)` rather than `rfl`: `heckeGenDiag` is not `@[expose]`d, so the parentheses opt out
  -- of exporting the definitional equality this lemma exists to replace.
  (rfl)

/-- The heckeGen diagonal has p-power entries (each entry is 1 = p^0 or p = p^1): it is `p`
raised entrywise to `heckeGenExponent n k`. -/
lemma heckeGenDiag_eq_primePowDiag (k : Fin n) :
    heckeGenDiag n p k = primePowDiag n p (heckeGenExponent n k) := by
  funext i
  simp only [heckeGenDiag_apply, primePowDiag_apply, heckeGenExponent_apply]
  split_ifs <;> simp

/-- The exponent function for heckeGen is monotone. -/
lemma heckeGenExponent_monotone (k : Fin n) : Monotone (heckeGenExponent n k) := by
  intro i j hij
  simp only [heckeGenExponent_apply]
  split_ifs <;> omega

variable [NeZero n]

include hp in
/-- The k-th generator of pLocalSubring: `T(1,...,1,p,...,p)` with `k+1` entries of `p`. -/
noncomputable def heckeGen (k : Fin n) : IntegralHeckeRing n :=
  diagElem (heckeGenDiag n p k)

include hp in
omit hp [NeZero n] in
/-- Defining equation for the sealed definition `heckeGen`. -/
lemma heckeGen_def (k : Fin n) : heckeGen n p k = diagElem (heckeGenDiag n p k) := (rfl)

include hp in
omit hp in
/-- Each generator lies in the `p`-local subsemiring `R_p`. -/
lemma heckeGen_mem_pLocalSubring (k : Fin n) : heckeGen n p k ∈ pLocalSubring n p := by
  have h_eq : heckeGen n p k = diagElem (primePowDiag n p (heckeGenExponent n k)) :=
    congrArg diagElem (heckeGenDiag_eq_primePowDiag n p k)
  rw [h_eq]
  exact diagElem_primePowDiag_mem_pLocalSubring n p _ (heckeGenExponent_monotone n k)

end TGen

section PolynomialRing

variable [NeZero n] (p : ℕ) (hp : p.Prime)

/-- Evaluation homomorphism: `Xₖ ↦ heckeGen k`.
    Maps `ℤ[X₁,...,Xₙ]` into the Hecke algebra. -/
noncomputable def evalHom : MvPolynomial (Fin n) ℤ →+* IntegralHeckeRing n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (IntegralHeckeRing n)) (fun k ↦ heckeGen n p k)

/-- Defining equation for the sealed definition `evalHom`: evaluation of a polynomial at the
generators, with integer coefficients cast into the Hecke ring. -/
lemma evalHom_def : evalHom n p =
    MvPolynomial.eval₂Hom (Int.castRingHom (IntegralHeckeRing n)) (fun k ↦ heckeGen n p k) :=
  (rfl)

/-- `evalHom` sends the `k`-th variable to the `k`-th generator. -/
@[simp] lemma evalHom_X (k : Fin n) : evalHom n p (MvPolynomial.X k) = heckeGen n p k :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- `evalHom` sends a constant to its image under `ℤ → IntegralHeckeRing n`.

Deliberately not `@[simp]`: `simp` already discharges this through `eq_intCast` and
`map_intCast`, `evalHom` being a ring hom, and `simpNF` rejects the redundant marking. The
lemma is kept as the named computation rule for `rw`. -/
lemma evalHom_C (a : ℤ) : evalHom n p (MvPolynomial.C a) = (a : IntegralHeckeRing n) :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- **Evaluation rule for `evalHom` at a double coset.** The coefficient of `evalHom P` at `D`
is the sum, over the support of `P`, of `P.coeff d` times the coefficient of the monomial
`∏ heckeGen i ^ d i` at `D`.

This is the wrapper-level counterpart of `evalHom_def`: it is stated here, where `evalHom` and
`IntegralHeckeRing` are both transparent, so that consumers can evaluate a polynomial image at
a coset without depending on either definition reducing at their own use site. -/
lemma evalHom_apply (P : MvPolynomial (Fin n) ℤ)
    (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) :
    evalHom n p P D =
      ∑ d ∈ P.support, P.coeff d • (∏ i, heckeGen n p i ^ d i : IntegralHeckeRing n) D := by
  rw [evalHom_def, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  refine (Finset.sum_apply' D).trans (Finset.sum_congr rfl fun d _ ↦ ?_)
  -- beta-reduce the cast left by `eval₂_eq'`, then turn the `ℤ`-multiple into a `ℤ`-scalar so
  -- that the wrapper's own `smul_apply` closes the goal
  change (((P.coeff d : ℤ) : IntegralHeckeRing n) * ∏ i, heckeGen n p i ^ d i) D = _
  rw [← zsmul_one (P.coeff d), smul_mul_assoc, one_mul]
  exact HeckeCosetModule.smul_apply _ _ _

/-- Each `heckeGen k` lies in the range of `evalHom`. -/
lemma heckeGen_mem_evalHom_range (k : Fin n) :
    heckeGen n p k ∈ (evalHom n p).range :=
  ⟨MvPolynomial.X k, MvPolynomial.eval₂Hom_X' _ _ _⟩

/-- Every value of `evalHom` lies in `R_p`: the generators do, and `pLocalSubring` is a subring,
so it absorbs the constants, sums and products that build an arbitrary polynomial. -/
lemma evalHom_mem_pLocalSubring (f : MvPolynomial (Fin n) ℤ) :
    evalHom n p f ∈ pLocalSubring n p := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [evalHom_C]; exact intCast_mem (pLocalSubring n p) a
  | add q r hq hr => rw [map_add]; exact (pLocalSubring n p).add_mem hq hr
  | mul_X q k hq =>
    rw [map_mul, evalHom_X]
    exact (pLocalSubring n p).mul_mem hq (heckeGen_mem_pLocalSubring n p k)

/-- The evaluation homomorphism with its true codomain: `ℤ[X₁, …, Xₙ] →+* R_p`.

`evalHom` lands in the ambient Hecke ring, which makes the results below mere inclusions;
this is the map whose surjectivity is the presentation statement of Theorem 3.20. -/
noncomputable def evalHomLocal : MvPolynomial (Fin n) ℤ →+* pLocalSubring n p :=
  (evalHom n p).codRestrict _ (evalHom_mem_pLocalSubring n p)

@[simp] lemma evalHomLocal_coe (f : MvPolynomial (Fin n) ℤ) :
    (evalHomLocal n p f : IntegralHeckeRing n) = evalHom n p f := (rfl)

/-- The computation rule of the presentation map: the `k`-th variable goes to the `k`-th
generator, taken in `pLocalSubring` rather than in the ambient ring. -/
@[simp] lemma evalHomLocal_X (k : Fin n) :
    evalHomLocal n p (MvPolynomial.X k) = ⟨heckeGen n p k, heckeGen_mem_pLocalSubring n p k⟩ :=
  Subtype.ext (evalHom_X n p k)

end PolynomialRing

open HeckeRing.GL2

/-- `heckeGen 2 p 0 = heckeTDiag 1 p`: the first generator is `T(1,p)`.

Positivity, not primality: nothing here needs `p` prime. -/
lemma heckeGen_zero_eq_heckeTDiag (p : ℕ) (hp : 0 < p) :
    heckeGen 2 p (0 : Fin 2) = heckeTDiag 1 p := by
  rw [heckeGen_def]
  have h : heckeGenDiag 2 p (0 : Fin 2) = ![1, p] := by
    funext i; simp only [heckeGenDiag_apply]; fin_cases i <;> simp
  rw [h, heckeTDiag_eq_diagElem Nat.one_pos hp (one_dvd _)]

/-- `heckeGen 2 p 1 = heckeTScalar p`: the second generator is the diamond operator.

Positivity, not primality, for the same reason as `heckeGen_zero_eq_heckeTDiag`. -/
lemma heckeGen_one_eq_heckeTScalar (p : ℕ) (hp : 0 < p) :
    heckeGen 2 p (1 : Fin 2) = heckeTScalar p := by
  rw [heckeGen_def]
  have h : heckeGenDiag 2 p (1 : Fin 2) = ![p, p] := by
    funext i; simp only [heckeGenDiag_apply]; fin_cases i <;> simp
  rw [h, heckeTScalar_of_pos hp]
  exact congrArg diagElem (funext fun i ↦ by fin_cases i <;> rfl)

/-- `heckeT(p) = heckeGen 0`: the sum T(p) is the first generator for p prime. -/
lemma heckeT_prime_eq_heckeGen_zero (p : ℕ) (hp : p.Prime) :
    heckeT p = heckeGen 2 p (0 : Fin 2) := by
  rw [heckeGen_zero_eq_heckeTDiag p hp.pos, heckeT_prime p hp]

end HeckeRing.GLn
