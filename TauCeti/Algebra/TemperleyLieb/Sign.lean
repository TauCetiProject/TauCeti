/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star

/-!
# The sign isomorphism and positivity at negative loop parameters

For every commutative ring `R`, loop parameter `δ : R`, and strand count `n : ℕ`, negating every
Temperley–Lieb generator `e δ i ↦ -e (-δ) i` defines an `R`-algebra isomorphism
`TauCeti.TemperleyLieb.negEquiv : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n`. On two
strands, no algebra homomorphism can instead fix the generator unless `2 * δ = 0`
(`TauCeti.TemperleyLieb.two_mul_eq_zero_of_map_e_eq`), because `e² = δ • e` and
`(-e)² = (-δ) • (-e)` differ by a sign.

The sign isomorphism is compatible with the tower, star, projection, and trace structures:

* It commutes with the strand inclusion `strandIncl` and preserves the augmentation `aug`.
* It maps `jonesWenzl δ n` to `jonesWenzl (-δ) n` over every commutative ring without invertibility
  hypotheses: negating `δ` flips the relative sign of consecutive quantum integers `[m + 1]` and
  `[m + 2]`, cancelling the negation of `e (Fin.last m)` in Wenzl's recursion.
* When `δ` and `-δ` are self-adjoint, it commutes with the analytic adjoint (`negStarAlgEquiv`),
  since `-e (-δ) i` remains self-adjoint.
* By uniqueness of the Markov trace (`IsMarkovTrace.unique`), any Markov traces `tr` at `δ` and
  `tr'` at `-δ` satisfy `tr' n (negEquiv δ n x) = (-1) ^ n * tr n x`. Thus the unnormalized
  closure trace acquires the parity sign `(-1) ^ n`, whereas the normalized trace expression
  `(Ring.inverse δ) ^ n * tr n x` is invariant under `negEquiv`.
* Consequently `negEquiv` pulls back the multiplication-pairing radical `traceRadical` on the nose
  and descends to algebra and star-algebra isomorphisms `IsMarkovTrace.quotientNegEquiv` and
  `IsMarkovTrace.quotientNegStarAlgEquiv` intertwining `quotientStrandIncl` and scaling
  `quotientTrace` by `(-1) ^ n`.

Over `ℂ` with a negative real loop parameter `δ < 0`, transporting Jones's positivity theorem from
`-δ > 0` across `negEquiv` characterizes positivity of the signed closure forms
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)`: they are positive semidefinite on every number of strands
precisely when `-δ ∈ jonesLoopParameters`, and otherwise take a negative value on every level
`n ≥ ⌊π / arccos (-δ / 2)⌋₊`. Combining positive and negative parameters characterizes positivity
of the normalized trace forms `((δ : ℂ)⁻¹) ^ n * tr n (x⋆ * x)` for every nonzero real loop
parameter `δ ≠ 0` by `|δ| ∈ jonesLoopParameters`. Both hypotheses `δ < 0` and `δ ≠ 0` are sharp:
at `δ = 0` (realized in the spin model at `q = i`), every closure on `n ≥ 1` strands contains at
least one loop and vanishes, making the forms positive semidefinite while `0 ∉ jonesLoopParameters`.

## Main definitions

* `TauCeti.TemperleyLieb.negEquivOfEq`: the sign isomorphism `TemperleyLieb R δ n ≃ₐ[R]
  TemperleyLieb R δ' n` for `-δ = δ'`.
* `TauCeti.TemperleyLieb.negEquiv`: the sign isomorphism `TemperleyLieb R δ n ≃ₐ[R]
  TemperleyLieb R (-δ) n`.
* `TauCeti.TemperleyLieb.negStarAlgEquivOfEq`, `TauCeti.TemperleyLieb.negStarAlgEquiv`: the sign
  isomorphism bundled as a `StarAlgEquiv` at self-adjoint loop parameters.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientNegEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientNegStarAlgEquiv`: the induced algebra and
  star-algebra isomorphisms between trace-radical quotients at `δ` and `-δ`.

## Main results

* `TauCeti.TemperleyLieb.negEquiv_strandIncl`, `TauCeti.TemperleyLieb.aug_negEquiv`,
  `TauCeti.TemperleyLieb.negEquiv_jonesWenzl`: compatibility with strand inclusion, augmentation,
  and Jones–Wenzl projections.
* `TauCeti.TemperleyLieb.two_mul_eq_zero_of_map_e_eq`: a generator-fixing algebra map
  `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` forces `2 * δ = 0`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_negEquiv`,
  `TauCeti.TemperleyLieb.markovTrace_negEquiv`: the Markov-trace sign relation
  `tr' n (negEquiv δ n x) = (-1) ^ n * tr n x`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientNegEquiv_quotientStrandIncl`: `quotientNegEquiv`
  intertwines the tower maps on trace-radical quotients.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff`: positivity of
  `(-1) ^ n * tr n (x⋆ * x)` for `δ < 0` holds if and only if `-δ ∈ jonesLoopParameters`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_inv_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_inv_pow_nonneg_iff`: positivity of
  `((δ : ℂ)⁻¹) ^ n * tr n (x⋆ * x)` for `δ ≠ 0` holds if and only if `|δ| ∈ jonesLoopParameters`.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Section 4.4, Facts 4.4.14 (TB6).
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
-/

public section

namespace TauCeti.TemperleyLieb

open Real

private theorem inverse_neg {R : Type*} [MonoidWithZero R] [HasDistribNeg R] (a : R) :
    Ring.inverse (-a) = -Ring.inverse a := by
  have h1 : Ring.inverse (-1 : R) = -1 := by
    simpa using Ring.inverse_unit (-1 : Rˣ)
  calc
    Ring.inverse (-a) = Ring.inverse ((-1 : R) * a) := by rw [neg_one_mul]
    _ = Ring.inverse a * Ring.inverse (-1 : R) := Ring.inverse_mul (Or.inl isUnit_one.neg)
    _ = -Ring.inverse a := by rw [h1, mul_neg_one]

section NegEquiv

variable {R : Type*} [CommRing R]

/-- The `R`-algebra homomorphism sending each generator `e δ i` to `-e δ' i` when `-δ = δ'`. -/
private def negHom {δ δ' : R} (h : -δ = δ') (n : ℕ) :
    TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ' n :=
  lift (fun i ↦ -e δ' i)
    (fun i ↦ by
      subst h
      simp only [neg_mul_neg, e_mul_self, neg_smul, smul_neg])
    (fun hadj ↦ by rw [neg_mul_neg, mul_neg, e_mul_e_mul_e hadj])
    (fun hdist ↦ by rw [neg_mul_neg, neg_mul_neg, (commute_e hdist).eq])

private theorem negHom_e {δ δ' : R} (h : -δ = δ') {n : ℕ} (i : Fin (n - 1)) :
    negHom h n (e δ i) = -e δ' i :=
  lift_e _ _ _ _ i

/-- The **sign isomorphism** `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R δ' n` for `-δ = δ'`,
sending each generator `e δ i` to `-e δ' i`. Taking `δ'` as a separate parameter with `-δ = δ'`
avoids casts when `-δ` simplifies to another expression such as `((-δ : ℝ) : ℂ)`. -/
def negEquivOfEq {δ δ' : R} (h : -δ = δ') (n : ℕ) :
    TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R δ' n :=
  AlgEquiv.ofAlgHom (negHom h n) (negHom (by rw [← h, neg_neg]) n)
    (hom_ext fun i ↦ by simp [negHom_e])
    (hom_ext fun i ↦ by simp [negHom_e])

/-- `negEquivOfEq` sends each generator `e δ i` to `-e δ' i`. -/
@[simp]
theorem negEquivOfEq_e {δ δ' : R} (h : -δ = δ') {n : ℕ} (i : Fin (n - 1)) :
    negEquivOfEq h n (e δ i) = -e δ' i :=
  negHom_e h i

/-- The inverse of `negEquivOfEq` is `negEquivOfEq` for the symmetric parameter relation. -/
@[simp]
theorem negEquivOfEq_symm {δ δ' : R} (h : -δ = δ') (n : ℕ) :
    (negEquivOfEq h n).symm = negEquivOfEq (by rw [← h, neg_neg]) n := (rfl)

/-- Composing two sign isomorphisms with `-δ = δ'` and `-δ' = δ` gives the identity. -/
@[simp]
theorem negEquivOfEq_apply_negEquivOfEq {δ δ' : R} (h₁ : -δ = δ') (h₂ : -δ' = δ) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    negEquivOfEq h₂ n (negEquivOfEq h₁ n x) = x :=
  (negEquivOfEq h₁ n).symm_apply_apply x

/-- The **sign isomorphism** between Temperley–Lieb algebras at opposite loop parameters `δ` and
`-δ`, sending `e δ i` to `-e (-δ) i`. -/
def negEquiv (δ : R) (n : ℕ) : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n :=
  negEquivOfEq rfl n

/-- The sign isomorphism sends each generator `e δ i` to `-e (-δ) i`. -/
@[simp]
theorem negEquiv_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    negEquiv δ n (e δ i) = -e (-δ) i :=
  negHom_e rfl i

/-- The inverse of the sign isomorphism sends each generator `e (-δ) i` to `-e δ i`. -/
@[simp]
theorem negEquiv_symm_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    (negEquiv δ n).symm (e (-δ) i) = -e δ i :=
  negHom_e (neg_neg δ) i

/-- `negEquivOfEq` commutes with adding a straight strand. -/
@[simp]
theorem negEquivOfEq_strandIncl {δ δ' : R} (h : -δ = δ') {n : ℕ}
    (x : TemperleyLieb R δ (n + 1)) :
    negEquivOfEq h (n + 2) (strandIncl x) = strandIncl (negEquivOfEq h (n + 1) x) := by
  have hcomp : (negEquivOfEq h (n + 2)).toAlgHom.comp strandIncl =
      strandIncl.comp (negEquivOfEq h (n + 1)).toAlgHom :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun hcomp x

/-- The sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem negEquiv_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R δ (n + 1)) :
    negEquiv δ (n + 2) (strandIncl x) = strandIncl (negEquiv δ (n + 1) x) :=
  negEquivOfEq_strandIncl rfl x

/-- The inverse of the sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem negEquiv_symm_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R (-δ) (n + 1)) :
    (negEquiv δ (n + 2)).symm (strandIncl x) = strandIncl ((negEquiv δ (n + 1)).symm x) :=
  negEquivOfEq_strandIncl (neg_neg δ) x

/-- `negEquivOfEq` preserves the augmentation. -/
@[simp]
theorem aug_negEquivOfEq {δ δ' : R} (h : -δ = δ') {n : ℕ} (x : TemperleyLieb R δ n) :
    aug (negEquivOfEq h n x) = aug x := by
  have hcomp : (aug : TemperleyLieb R δ' n →ₐ[R] R).comp (negEquivOfEq h n).toAlgHom = aug :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun hcomp x

/-- The sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_negEquiv (δ : R) {n : ℕ} (x : TemperleyLieb R δ n) :
    aug (negEquiv δ n x) = aug x :=
  aug_negEquivOfEq rfl x

/-- The inverse of the sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_negEquiv_symm (δ : R) {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    aug ((negEquiv δ n).symm x) = aug x :=
  aug_negEquivOfEq (neg_neg δ) x

/-- `negEquivOfEq` negates the cap coefficient of a Kauffman crossing. -/
theorem negEquivOfEq_crossing {δ δ' : R} (h : -δ = δ') (α β : R) {n : ℕ} (i : Fin (n - 1)) :
    negEquivOfEq h n (crossing δ α β i) = crossing δ' α (-β) i := by
  simp [crossing_def, neg_smul]

/-- The sign isomorphism negates the cap coefficient of a Kauffman crossing. -/
theorem negEquiv_crossing (δ α β : R) {n : ℕ} (i : Fin (n - 1)) :
    negEquiv δ n (crossing δ α β i) = crossing (-δ) α (-β) i :=
  negEquivOfEq_crossing rfl α β i

/-- `negEquivOfEq` maps the Jones–Wenzl projection at `δ` to the Jones–Wenzl projection at `δ'`,
over every commutative ring and with no invertibility assumption on quantum integers. -/
@[simp]
theorem negEquivOfEq_jonesWenzl {δ δ' : R} (h : -δ = δ') (n : ℕ) :
    negEquivOfEq h n (jonesWenzl δ n) = jonesWenzl δ' n := by
  subst h
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m _ ih1 =>
    have hinv : Ring.inverse (qInt R (-δ) (m + 2)) =
        -((-1 : R) ^ (m + 2) * Ring.inverse (qInt R δ (m + 2))) := by
      have hu : Ring.inverse ((-1 : R) ^ (m + 2)) = (-1 : R) ^ (m + 2) := by
        have hpow : (((-1 : Rˣ) ^ (m + 2))⁻¹ : Rˣ) = (-1 : Rˣ) ^ (m + 2) := by
          rw [← inv_pow, inv_neg, inv_one]
        simpa [hpow] using Ring.inverse_unit ((-1 : Rˣ) ^ (m + 2))
      rw [qInt_neg_left, pow_succ (-1 : R) (m + 2), mul_neg_one, neg_mul, inverse_neg,
        Ring.inverse_mul (Or.inl ((isUnit_one.neg).pow (m + 2))), hu, mul_comm]
    have hcoeff : qInt R (-δ) (m + 1) * Ring.inverse (qInt R (-δ) (m + 2)) =
        -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
      rw [qInt_neg_left, hinv]
      have hsq : (-1 : R) ^ (m + 2) * (-1 : R) ^ (m + 2) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      linear_combination -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) * hsq
    rw [jonesWenzl_add_two, jonesWenzl_add_two, map_sub, map_smul, map_mul, map_mul,
      negEquivOfEq_strandIncl, ih1, negEquivOfEq_e, hcoeff]
    simp [mul_neg, neg_mul, neg_smul, smul_neg]

/-- The sign isomorphism preserves Jones–Wenzl projections unconditionally. -/
@[simp]
theorem negEquiv_jonesWenzl (δ : R) (n : ℕ) :
    negEquiv δ n (jonesWenzl δ n) = jonesWenzl (-δ) n :=
  negEquivOfEq_jonesWenzl rfl n

/-- The inverse of the sign isomorphism preserves Jones–Wenzl projections unconditionally. -/
@[simp]
theorem negEquiv_symm_jonesWenzl (δ : R) (n : ℕ) :
    (negEquiv δ n).symm (jonesWenzl (-δ) n) = jonesWenzl δ n :=
  negEquivOfEq_jonesWenzl (neg_neg δ) n

/-- On two strands, an `R`-algebra homomorphism `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2`
sending the generator to the generator forces `2 * δ = 0`. Thus when `2 * δ ≠ 0`, negating the
generators in `negEquiv` is unavoidable. -/
theorem two_mul_eq_zero_of_map_e_eq {δ : R}
    (F : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2) (i : Fin (2 - 1))
    (hF : F (e δ i) = e (-δ) i) : 2 * δ = 0 := by
  have h := congrArg F (e_mul_self (δ := δ) i)
  rw [map_mul, map_smul, hF, e_mul_self] at h
  have hδ : -δ = δ := smul_left_injective_e_two i h
  linear_combination -hδ

end NegEquiv

section Star

variable {R : Type*} [CommRing R] [StarRing R]

/-- `negEquivOfEq` commutes with the analytic adjoint when both loop parameters are
self-adjoint. -/
@[simp]
theorem negEquivOfEq_star {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    (h : -δ = δ') {n : ℕ} (x : TemperleyLieb R δ n) :
    negEquivOfEq h n (star x) = star (negEquivOfEq h n x) :=
  map_star_iff (F := (negEquivOfEq h n).toAlgHom).mpr
    (fun i ↦ by simpa using (isSelfAdjoint_e (δ := δ') i).neg) x

/-- The sign isomorphism commutes with the analytic adjoint. -/
@[simp]
theorem negEquiv_star (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {n : ℕ} (x : TemperleyLieb R δ n) :
    negEquiv δ n (star x) = star (negEquiv δ n x) :=
  negEquivOfEq_star rfl x

/-- The inverse of the sign isomorphism commutes with the analytic adjoint. -/
@[simp]
theorem negEquiv_symm_star (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    (negEquiv δ n).symm (star x) = star ((negEquiv δ n).symm x) :=
  negEquivOfEq_star (neg_neg δ) x

/-- `negEquivOfEq` bundled as a `StarAlgEquiv` at self-adjoint loop parameters. -/
def negStarAlgEquivOfEq {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    (h : -δ = δ') (n : ℕ) :
    TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R δ' n :=
  StarAlgEquiv.ofAlgEquiv (negEquivOfEq h n) (negEquivOfEq_star h)

/-- `negStarAlgEquivOfEq` agrees with `negEquivOfEq` on elements. -/
@[simp]
theorem negStarAlgEquivOfEq_apply {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    (h : -δ = δ') {n : ℕ} (x : TemperleyLieb R δ n) :
    negStarAlgEquivOfEq h n x = negEquivOfEq h n x := (rfl)

/-- The sign isomorphism bundled as a `StarAlgEquiv` at self-adjoint loop parameters. -/
def negStarAlgEquiv (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))] (n : ℕ) :
    TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n :=
  negStarAlgEquivOfEq rfl n

/-- `negStarAlgEquiv` agrees with `negEquiv` on elements. -/
@[simp]
theorem negStarAlgEquiv_apply (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {n : ℕ} (x : TemperleyLieb R δ n) :
    negStarAlgEquiv δ n x = negEquiv δ n x := (rfl)

/-- The inverse of `negStarAlgEquiv` agrees with `(negEquiv δ n).symm` on elements. -/
@[simp]
theorem negStarAlgEquiv_symm_apply (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    (negStarAlgEquiv δ n).symm x = (negEquiv δ n).symm x := (rfl)

end Star

section MarkovTrace

/-- If `δ = -(q + q⁻¹)` for a unit `q`, then `-δ = -((-q) + (-q)⁻¹)`. -/
theorem neg_eq_neg_add_inv {R : Type*} [Ring R] {δ : R} {q : Rˣ}
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) :
    -δ = -(((-q : Rˣ) : R) + (((-q : Rˣ)⁻¹ : Rˣ) : R)) := by
  rw [hq, inv_neg, Units.val_neg, Units.val_neg, ← neg_add, neg_neg]

variable {R : Type*} [CommRing R]

namespace IsMarkovTrace

private theorem neg_one_pow_mul_self (n : ℕ) : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- Pulling back a Markov trace at `δ'` along `negEquivOfEq h` (with `-δ = δ'`) and multiplying by
`(-1) ^ n` on `n` strands yields a Markov trace at `δ`. -/
theorem comp_negEquivOfEq {δ δ' : R} {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr' : IsMarkovTrace R δ' tr') (h : -δ = δ') :
    IsMarkovTrace R δ (fun n ↦ (-1 : R) ^ n • (tr' n ∘ₗ (negEquivOfEq h n).toLinearMap)) where
  map_one n := by
    subst h
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, smul_eq_mul]
    rw [_root_.map_one, htr'.map_one, neg_pow δ n, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  map_mul_comm n x y := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      htr'.map_mul_comm]
  map_strandIncl n x := by
    subst h
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      negEquivOfEq_strandIncl, htr'.map_strandIncl, smul_eq_mul, pow_succ]
    ring
  map_strandIncl_mul_e_last n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      negEquivOfEq_strandIncl, negEquivOfEq_e, mul_neg, map_neg, htr'.map_strandIncl_mul_e_last,
      smul_eq_mul, pow_succ]
    ring

/-- Pulling back a Markov trace at `-δ` along `negEquiv` and scaling by `(-1) ^ n` gives a Markov
trace at `δ`. -/
theorem comp_negEquiv {δ : R} {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr' : IsMarkovTrace R (-δ) tr') :
    IsMarkovTrace R δ (fun n ↦ (-1 : R) ^ n • (tr' n ∘ₗ (negEquiv δ n).toLinearMap)) :=
  htr'.comp_negEquivOfEq rfl

/-- Any Markov traces at `δ` and `δ'` with `-δ = δ'` are related across `negEquivOfEq` by the sign
`(-1) ^ n`. -/
theorem eq_neg_one_pow_mul_map_negEquivOfEq {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : -δ = δ') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    tr n x = (-1 : R) ^ n * tr' n (negEquivOfEq h n x) := by
  have heq := LinearMap.congr_fun (congrFun (htr.unique (htr'.comp_negEquivOfEq h)) n) x
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    smul_eq_mul] using heq

/-- Evaluating a Markov trace at `δ'` on `negEquivOfEq h n x` multiplies the Markov trace at `δ`
by `(-1) ^ n`. -/
theorem map_negEquivOfEq {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : -δ = δ') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    tr' n (negEquivOfEq h n x) = (-1 : R) ^ n * tr n x := by
  rw [htr.eq_neg_one_pow_mul_map_negEquivOfEq htr' h x, ← mul_assoc, neg_one_pow_mul_self,
    one_mul]

/-- Any Markov traces at `δ` and `-δ` satisfy `tr n x = (-1) ^ n * tr' n (negEquiv δ n x)`. -/
theorem eq_neg_one_pow_mul_map_negEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    tr n x = (-1 : R) ^ n * tr' n (negEquiv δ n x) :=
  htr.eq_neg_one_pow_mul_map_negEquivOfEq htr' rfl x

/-- Evaluating a Markov trace at `-δ` on `negEquiv δ n x` multiplies the Markov trace at `δ` by
`(-1) ^ n`. -/
theorem map_negEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    tr' n (negEquiv δ n x) = (-1 : R) ^ n * tr n x :=
  htr.map_negEquivOfEq htr' rfl x

/-- The normalized Markov trace expression `(Ring.inverse δ) ^ n * tr n x` is invariant under the
sign isomorphism, over every commutative ring and with no unit hypothesis on `δ`. -/
theorem inverse_pow_mul_map_negEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    (Ring.inverse (-δ)) ^ n * tr' n (negEquiv δ n x) = (Ring.inverse δ) ^ n * tr n x := by
  rw [inverse_neg, neg_pow, htr.map_negEquiv htr' x]
  linear_combination ((Ring.inverse δ) ^ n * tr n x) * neg_one_pow_mul_self (R := R) n

/-! ### Trace radicals and algebraic trace quotients -/

/-- `negEquiv` preserves and reflects membership in the trace radical of a Markov trace. -/
theorem negEquiv_mem_traceRadical_iff {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    negEquiv δ n x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  simp only [LinearMap.mem_traceRadical]
  refine ⟨fun hx y ↦ ?_, fun hx y ↦ ?_⟩
  · have hz := hx (negEquiv δ n y)
    rwa [← map_mul, htr.map_negEquiv htr' (x * y), neg_one_pow_mul_eq_zero_iff] at hz
  · obtain ⟨y, rfl⟩ := (negEquiv δ n).surjective y
    rw [← map_mul, htr.map_negEquiv htr' (x * y), hx y, mul_zero]

/-- Pulling back the trace radical at `-δ` along `negEquiv` gives the trace radical at `δ`. -/
theorem comap_traceRadical_negEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.comap (negEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
      ((tr' n).traceRadical (htr'.map_mul_comm n)) =
        (tr n).traceRadical (htr.map_mul_comm n) := by
  ext x
  exact htr.negEquiv_mem_traceRadical_iff htr' x

/-- Pushing forward the trace radical at `δ` along `negEquiv` gives the trace radical at `-δ`. -/
theorem map_traceRadical_negEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.map (negEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
      ((tr n).traceRadical (htr.map_mul_comm n)) =
        (tr' n).traceRadical (htr'.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_negEquiv htr' n]
  exact Ideal.map_comap_of_surjective (negEquiv δ n).toRingHom (negEquiv δ n).surjective _

/-- The `R`-algebra isomorphism between the trace-radical quotients at `δ` and `-δ` induced by
`negEquiv`. -/
def quotientNegEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  Ideal.quotientEquivAlg _ _ (negEquiv δ n) (htr.map_traceRadical_negEquiv htr' n).symm

/-- `quotientNegEquiv` acts on quotient classes by applying `negEquiv` to representatives. -/
@[simp]
theorem quotientNegEquiv_mk {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    htr.quotientNegEquiv htr' n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (negEquiv δ n x) := (rfl)

/-- `quotientNegEquiv` intertwines the strand inclusions `quotientStrandIncl` on the trace-radical
quotients. -/
@[simp]
theorem quotientNegEquiv_quotientStrandIncl {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientNegEquiv htr' (n + 2) (htr.quotientStrandIncl n x) =
      htr'.quotientStrandIncl n (htr.quotientNegEquiv htr' (n + 1) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- Evaluating `quotientTrace` after `quotientNegEquiv` multiplies `quotientTrace` by `(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientNegEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientNegEquiv htr' n x) =
      (-1 : R) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr.map_negEquiv htr']

/-- At self-adjoint loop parameters, `quotientNegEquiv` commutes with the quotient star operation.
Install the star-stability instances via `htr.isStar_traceRadical n` and
`htr'.isStar_traceRadical n` when not already in context. -/
@[simp]
theorem quotientNegEquiv_star {δ : R} [StarRing R]
    [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientNegEquiv htr' n (star x) = star (htr.quotientNegEquiv htr' n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- At self-adjoint loop parameters, `quotientNegEquiv` bundled as a `StarAlgEquiv` between the
trace-radical quotients. Install the star-stability instances via `htr.isStar_traceRadical n` and
`htr'.isStar_traceRadical n` when not already in context. -/
def quotientNegStarAlgEquiv {δ : R} [StarRing R]
    [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃⋆ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  StarAlgEquiv.ofAlgEquiv (htr.quotientNegEquiv htr' n) (htr.quotientNegEquiv_star htr')

/-- `quotientNegStarAlgEquiv` agrees with `quotientNegEquiv` on quotient elements. -/
@[simp]
theorem quotientNegStarAlgEquiv_apply {δ : R} [StarRing R]
    [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientNegStarAlgEquiv htr' n x = htr.quotientNegEquiv htr' n x := (rfl)

end IsMarkovTrace

/-- The spin-model Markov trace at `-q` evaluated on `negEquiv δ n x` equals `(-1) ^ n` times the
spin-model Markov trace at `q` evaluated on `x`. -/
@[simp]
theorem markovTrace_negEquiv {δ : R} (q : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hnq : -δ = -(((-q : Rˣ) : R) + (((-q : Rˣ)⁻¹ : Rˣ) : R))) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    markovTrace (-q) hnq (negEquiv δ n x) = (-1 : R) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_negEquiv (isMarkovTrace_markovTrace (-q) hnq) x

end MarkovTrace

section Positivity

open scoped ComplexOrder

private theorem nonneg_ofReal_mul_iff {c : ℝ} (hc : 0 < c) {z : ℂ} :
    0 ≤ (c : ℂ) * z ↔ 0 ≤ z := by
  refine ⟨fun h ↦ ?_, fun h ↦ mul_nonneg (Complex.zero_le_real.2 hc.le) h⟩
  have hinv : 0 ≤ ((c⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.2 (inv_pos.2 hc).le
  have hmul := mul_nonneg hinv h
  rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one,
    one_mul] at hmul

namespace IsMarkovTrace

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- **Failure of signed positivity from level `k` on.** Let `δ < 0` be a negative real loop
parameter with `-δ ∉ jonesLoopParameters` and let `k = ⌊π / arccos (-δ / 2)⌋₊`. On every number
`n ≥ k` of strands the signed Hermitian form `(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` of a Markov
trace takes a negative value. -/
theorem exists_neg_one_pow_mul_map_star_mul_self_neg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ}
    (hn : ⌊π / arccos (-δ / 2)⌋₊ ≤ n) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) n, (-1 : ℂ) ^ n * tr n (star x * x) < 0 := by
  have : Fact (IsSelfAdjoint ((-δ : ℝ) : ℂ)) := ⟨Complex.conj_ofReal (-δ)⟩
  have hneg : -((-δ : ℝ) : ℂ) = (δ : ℂ) := by simp [Complex.ofReal_neg]
  have htr' := htr.comp_negEquivOfEq hneg
  obtain ⟨y, hy⟩ := htr'.exists_map_star_mul_self_neg (neg_pos.mpr hδ) hδJ hn
  refine ⟨negEquivOfEq hneg n y, ?_⟩
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
    negEquivOfEq_star, smul_eq_mul] using hy

/-- If `δ < 0` and the signed Hermitian forms `(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` of a Markov
trace are positive semidefinite on every number of strands, then `-δ ∈ jonesLoopParameters`. -/
theorem mem_jonesLoopParameters_neg_of_forall_neg_one_pow_mul_nonneg
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0)
    (h : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    -δ ∈ jonesLoopParameters := by
  by_contra hδJ
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_mul_map_star_mul_self_neg hδ hδJ le_rfl
  exact (h _ x).not_gt hx

/-- At a negative loop parameter `δ < 0` with `-δ ∉ jonesLoopParameters`, the signed Hermitian
form `(-1) ^ n * tr n (x⋆ * y)` on `n` strands can be positive semidefinite only below level
`⌊π / arccos (-δ / 2)⌋₊`. -/
theorem lt_floor_of_forall_neg_one_pow_mul_nonneg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ}
    (h : ∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    n < ⌊π / arccos (-δ / 2)⌋₊ := by
  by_contra hn
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_mul_map_star_mul_self_neg hδ hδJ (not_lt.1 hn)
  exact (h x).not_gt hx

/-- **Signed positivity at negative loop parameters.** For `δ < 0`, the signed Hermitian forms
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every number
of strands if and only if `-δ ∈ jonesLoopParameters`. -/
theorem forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) ↔
      -δ ∈ jonesLoopParameters := by
  have : Fact (IsSelfAdjoint ((-δ : ℝ) : ℂ)) := ⟨Complex.conj_ofReal (-δ)⟩
  have hneg : -((-δ : ℝ) : ℂ) = (δ : ℂ) := by simp [Complex.ofReal_neg]
  have htr' := htr.comp_negEquivOfEq hneg
  rw [← htr'.forall_map_star_mul_self_nonneg_iff (neg_pos.mpr hδ)]
  refine ⟨fun h n y ↦ ?_, fun h n x ↦ ?_⟩
  · simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      negEquivOfEq_star, smul_eq_mul] using h n (negEquivOfEq hneg n y)
  · simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      negEquivOfEq_star, smul_eq_mul, (negEquivOfEq hneg n).apply_symm_apply] using
      h n ((negEquivOfEq hneg n).symm x)

/-- **Positivity of the normalized Markov trace at nonzero loop parameters.** For every real
`δ ≠ 0`, the normalized Hermitian forms `(x, y) ↦ ((δ : ℂ)⁻¹) ^ n * tr n (x⋆ * y)` of a Markov
trace are positive semidefinite on every number of strands if and only if
`|δ| ∈ jonesLoopParameters`. -/
theorem forall_inv_pow_mul_map_star_mul_self_nonneg_iff
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ≠ 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ ((δ : ℂ)⁻¹) ^ n * tr n (star x * x)) ↔
      |δ| ∈ jonesLoopParameters := by
  rcases hδ.lt_or_gt with hlt | hgt
  · rw [abs_of_neg hlt, ← htr.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hlt]
    have hscale (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
        ((δ : ℂ)⁻¹) ^ n * tr n (star x * x) =
          ((((-δ)⁻¹ ^ n : ℝ) : ℂ) * ((-1 : ℂ) ^ n * tr n (star x * x))) := by
      rw [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg, inv_neg, neg_pow]
      have hsq : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := neg_one_pow_mul_self n
      linear_combination (((δ : ℂ)⁻¹) ^ n * tr n (star x * x)) * hsq.symm
    exact forall_congr' fun n ↦ forall_congr' fun x ↦ by
      rw [hscale n x, nonneg_ofReal_mul_iff (pow_pos (inv_pos.2 (neg_pos.mpr hlt)) n)]
  · rw [abs_of_pos hgt, ← htr.forall_map_star_mul_self_nonneg_iff hgt]
    have hscale (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
        ((δ : ℂ)⁻¹) ^ n * tr n (star x * x) = (((δ⁻¹ ^ n : ℝ) : ℂ) * tr n (star x * x)) := by
      rw [Complex.ofReal_pow, Complex.ofReal_inv]
    exact forall_congr' fun n ↦ forall_congr' fun x ↦ by
      rw [hscale n x, nonneg_ofReal_mul_iff (pow_pos (inv_pos.2 hgt) n)]

end IsMarkovTrace

/-- **Signed positivity at negative loop parameters** for the spin-model Markov trace. Let `δ < 0`
and let `q` be a unit with `δ = -(q + q⁻¹)`. Then `(-1) ^ n * markovTrace q hq (x⋆ * x)` is real
and nonnegative for every number `n` of strands and every `x` if and only if `-δ` is an admissible
Jones loop parameter (`-δ = 2 cos (π / m)` for some `m ≥ 3`, or `-δ ≥ 2`). -/
theorem markovTrace_neg_one_pow_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ < 0)
    (q : ℂˣ) (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
      0 ≤ (-1 : ℂ) ^ n * markovTrace q hq (star x * x)) ↔ -δ ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hδ

/-- **Positivity of the normalized spin-model Markov trace** at nonzero loop parameters. Let
`δ ≠ 0` and let `q` be a unit with `δ = -(q + q⁻¹)`. Then
`((δ : ℂ)⁻¹) ^ n * markovTrace q hq (x⋆ * x)` is real and nonnegative for every number `n` of
strands and every `x` if and only if `|δ|` is an admissible Jones loop parameter. -/
theorem markovTrace_inv_pow_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ ≠ 0)
    (q : ℂˣ) (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
      0 ≤ ((δ : ℂ)⁻¹) ^ n * markovTrace q hq (star x * x)) ↔ |δ| ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_inv_pow_mul_map_star_mul_self_nonneg_iff hδ

end Positivity

end TauCeti.TemperleyLieb
