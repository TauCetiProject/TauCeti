/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star

/-!
# The sign isomorphism of the Temperley–Lieb tower

Over any commutative ring `R`, negating every generator `e_i ↦ -e_i` defines an `R`-algebra
isomorphism between the Temperley–Lieb algebras at opposite loop parameters:
`(-e_i) ^ 2 = δ • e_i = (-δ) • (-e_i)`, `(-e_i) * (-e_j) * (-e_i) = -e_i` for adjacent strands,
and distant generators still commute. By contrast, when `2 • δ ≠ 0` no `R`-algebra map on two
strands can send `e δ 0` to `e (-δ) 0` without the sign (`not_exists_algHom_e_neg_two`).

To avoid transporting types along `-(-δ) = δ` or `(↑(-δ) : ℂ) = -(↑δ : ℂ)`, the primary
equivalence `TauCeti.TemperleyLieb.signEquivOfAddEqZero` is stated for any pair of loop parameters
satisfying `δ + δ' = 0`; its inverse is definitionally the same construction with `δ` and `δ'`
swapped, and `TauCeti.TemperleyLieb.signEquiv` specializes it to `δ' = -δ`.

The sign isomorphism commutes with every structural operation of the Temperley–Lieb tower:

* **Tower, augmentation, crossings, and Jones–Wenzl projections**: `signEquivOfAddEqZero`
  intertwines `strandIncl` and `aug`, flips the `e_i`-coefficient of `crossing`, and sends
  `jonesWenzl δ n` to `jonesWenzl δ' n` unconditionally (`signEquivOfAddEqZero_jonesWenzl`), since
  the sign `(-1) ^ (k + 1)` of `qInt R (-δ) k` (`TauCeti.qInt_neg`) cancels the sign of
  `-e δ' (Fin.last m)` in Wenzl's recursion.
* **The analytic adjoint**: for self-adjoint opposite loop parameters, `-e δ' i` is self-adjoint,
  so `signEquivOfAddEqZero` preserves `star` (`signEquivOfAddEqZero_star`) and upgrades to a
  `⋆`-algebra equivalence (`signStarAlgEquivOfAddEqZero`, `signStarAlgEquiv`).
* **Markov traces and normalized traces**: pulling a Markov trace at `δ'` back along
  `signEquivOfAddEqZero` and multiplying at level `n` by `(-1) ^ n` gives a Markov trace at `δ`
  (`IsMarkovTrace.pullback_signEquivOfAddEqZero`). By uniqueness of Markov traces, any Markov
  traces `tr` at `δ` and `tr'` at `δ'` satisfy `tr' n (s x) = (-1) ^ n * tr n x`
  (`IsMarkovTrace.map_signEquivOfAddEqZero`, `markovTrace_signEquiv`), while the normalized forms
  `Ring.inverse δ ^ n * tr n x` are invariant (`IsMarkovTrace.inverse_pow_mul_map_signEquiv`).
* **Trace radicals and Jones quotients**: since `(-1) ^ n` is a unit, the sign isomorphism maps
  the trace radical at `δ` onto the trace radical at `δ'` and descends to algebra and `⋆`-algebra
  equivalences on the trace-radical quotients (`IsMarkovTrace.quotientSignEquivOfAddEqZero`,
  `IsMarkovTrace.quotientSignStarAlgEquivOfAddEqZero`), intertwining `quotientStrandIncl` and
  scaling `quotientTrace` by `(-1) ^ n`.

## Main definitions

* `TauCeti.TemperleyLieb.signEquivOfAddEqZero`, `TauCeti.TemperleyLieb.signEquiv`: the `R`-algebra
  isomorphism `e_i ↦ -e_i` between opposite loop parameters.
* `TauCeti.TemperleyLieb.signStarAlgEquivOfAddEqZero`, `TauCeti.TemperleyLieb.signStarAlgEquiv`:
  the `⋆`-algebra equivalence at self-adjoint loop parameters.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquivOfAddEqZero`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`: the induced algebra equivalence on
  trace-radical quotients.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquivOfAddEqZero`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquiv`: the induced `⋆`-algebra
  equivalence on trace-radical quotients.

## Main results

* `TauCeti.TemperleyLieb.signEquivOfAddEqZero_strandIncl`,
  `TauCeti.TemperleyLieb.signEquivOfAddEqZero_jonesWenzl`,
  `TauCeti.TemperleyLieb.signEquivOfAddEqZero_star`: compatibility with `strandIncl`,
  `jonesWenzl`, and `star`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.pullback_signEquivOfAddEqZero`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquivOfAddEqZero`,
  `TauCeti.TemperleyLieb.markovTrace_signEquiv`: the `(-1) ^ n` transformation law of Markov
  traces under the sign isomorphism.
* `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_signEquivOfAddEqZero`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_star_mul_self_signEquivOfAddEqZero`:
  invariance of the normalized trace and its Hermitian form.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquivOfAddEqZero_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_quotientSignEquivOfAddEqZero`: tower and
  trace compatibility on the trace-radical quotients.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Facts 4.4.14 (TB6).
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb

/-! ### The sign algebra isomorphism and tower compatibilities -/

section SignEquiv

variable {R : Type*} [CommRing R]

/-- Auxiliary `R`-algebra map sending each generator `e δ i` to `-e δ' i` when `δ + δ' = 0`. -/
private def signHomOfAddEqZero {δ δ' : R} (h : δ + δ' = 0) (n : ℕ) :
    TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ' n :=
  lift (fun i ↦ -e δ' i)
    (fun i ↦ by
      rw [neg_mul_neg, e_mul_self, smul_neg, eq_neg_of_add_eq_zero_left h, neg_smul, neg_neg])
    (fun hadj ↦ by
      rw [neg_mul_neg, mul_neg, e_mul_e_mul_e hadj])
    (fun hdist ↦ by
      rw [neg_mul_neg, neg_mul_neg, (commute_e hdist).eq])

/-- The **sign isomorphism** between Temperley–Lieb algebras at opposite loop parameters
`δ + δ' = 0`: the `R`-algebra equivalence sending every generator `e δ i` to `-e δ' i`. -/
def signEquivOfAddEqZero {δ δ' : R} (h : δ + δ' = 0) (n : ℕ) :
    TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R δ' n :=
  AlgEquiv.ofAlgHom (signHomOfAddEqZero h n) (signHomOfAddEqZero (by rwa [add_comm]) n)
    (hom_ext fun i ↦ by simp [signHomOfAddEqZero])
    (hom_ext fun i ↦ by simp [signHomOfAddEqZero])

/-- `signEquivOfAddEqZero` sends each generator `e δ i` to `-e δ' i`. -/
@[simp]
theorem signEquivOfAddEqZero_e {δ δ' : R} (h : δ + δ' = 0) {n : ℕ} (i : Fin (n - 1)) :
    signEquivOfAddEqZero h n (e δ i) = -e δ' i := by
  simp [signEquivOfAddEqZero, signHomOfAddEqZero]

/-- The inverse of `signEquivOfAddEqZero` is `signEquivOfAddEqZero` with the parameters swapped. -/
theorem signEquivOfAddEqZero_symm {δ δ' : R} (h : δ + δ' = 0) (n : ℕ) :
    (signEquivOfAddEqZero h n).symm = signEquivOfAddEqZero (by rwa [add_comm]) n :=
  (rfl)

/-- `(signEquivOfAddEqZero h n).symm` sends each generator `e δ' i` to `-e δ i`. -/
@[simp]
theorem signEquivOfAddEqZero_symm_e {δ δ' : R} (h : δ + δ' = 0) {n : ℕ} (i : Fin (n - 1)) :
    (signEquivOfAddEqZero h n).symm (e δ' i) = -e δ i :=
  signEquivOfAddEqZero_e (by rwa [add_comm]) i

/-- Applying `signEquivOfAddEqZero` across opposite fibers and back is the identity. -/
@[simp]
theorem signEquivOfAddEqZero_apply_self {δ δ' : R} (h₁ : δ + δ' = 0) (h₂ : δ' + δ = 0)
    {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquivOfAddEqZero h₂ n (signEquivOfAddEqZero h₁ n x) = x :=
  (signEquivOfAddEqZero h₁ n).symm_apply_apply x

/-- `signEquivOfAddEqZero` commutes with adding a straight strand. -/
@[simp]
theorem signEquivOfAddEqZero_strandIncl {δ δ' : R} (h : δ + δ' = 0) {n : ℕ}
    (x : TemperleyLieb R δ (n + 1)) :
    signEquivOfAddEqZero h (n + 2) (strandIncl x) =
      strandIncl (signEquivOfAddEqZero h (n + 1) x) := by
  have hhom : (signEquivOfAddEqZero h (n + 2)).toAlgHom.comp strandIncl =
      strandIncl.comp (signEquivOfAddEqZero h (n + 1)).toAlgHom :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun hhom x

/-- `signEquivOfAddEqZero` preserves the augmentation. -/
@[simp]
theorem aug_signEquivOfAddEqZero {δ δ' : R} (h : δ + δ' = 0) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    aug (signEquivOfAddEqZero h n x) = aug x := by
  have hhom : aug.comp (signEquivOfAddEqZero h n).toAlgHom = aug :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun hhom x

/-- On at most one strand, `signEquivOfAddEqZero` commutes with the identification with `R`. -/
theorem algEquivOfLeOne_signEquivOfAddEqZero {δ δ' : R} (h : δ + δ' = 0) {n : ℕ} (hn : n ≤ 1)
    (x : TemperleyLieb R δ n) :
    algEquivOfLeOne δ' hn (signEquivOfAddEqZero h n x) = algEquivOfLeOne δ hn x := by
  simp

/-- `signEquivOfAddEqZero` negates the second coefficient of a Kauffman crossing. -/
theorem signEquivOfAddEqZero_crossing {δ δ' : R} (h : δ + δ' = 0) (α β : R) {n : ℕ}
    (i : Fin (n - 1)) :
    signEquivOfAddEqZero h n (crossing δ α β i) = crossing δ' α (-β) i := by
  simp

/-- `signEquivOfAddEqZero` carries the Jones–Wenzl projection at `δ` to the Jones–Wenzl projection
at `δ'`, with no invertibility assumption on the quantum integers: in Wenzl's recursion, the sign
`(-1) ^ (k + 1)` of `qInt R (-δ) k` cancels the negation of `e (Fin.last m)`. -/
@[simp]
theorem signEquivOfAddEqZero_jonesWenzl {δ δ' : R} (h : δ + δ' = 0) :
    ∀ n : ℕ, signEquivOfAddEqZero h n (jonesWenzl δ n) = jonesWenzl δ' n
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have hδ' : δ' = -δ := eq_neg_of_add_eq_zero_right h
    have hu : ((((-1 : Rˣ) ^ (m + 3) : Rˣ)) : R) = (-1 : R) ^ (m + 3) := by simp
    have hinv_sign : Ring.inverse ((-1 : R) ^ (m + 3)) = (-1 : R) ^ (m + 3) := by
      rw [← hu, Ring.inverse_unit]
      simp
    have hscalar : qInt R δ' (m + 1) * Ring.inverse (qInt R δ' (m + 2)) =
        -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
      rw [hδ', qInt_neg δ (m + 1), qInt_neg δ (m + 2),
        Ring.inverse_mul (Or.inl (isUnit_neg_one.pow (m + 3))), hinv_sign]
      calc
        (-1 : R) ^ (m + 2) * qInt R δ (m + 1) *
            (Ring.inverse (qInt R δ (m + 2)) * (-1 : R) ^ (m + 3))
            = (((-1 : R) * (-1 : R)) ^ (m + 2) * (-1 : R)) *
                (qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
              rw [mul_pow]
              simp only [pow_succ]
              ring
        _ = -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by simp
    rw [jonesWenzl_add_two, jonesWenzl_add_two, map_sub, map_smul, map_mul, map_mul,
      signEquivOfAddEqZero_strandIncl, signEquivOfAddEqZero_e,
      signEquivOfAddEqZero_jonesWenzl h (m + 1), hscalar]
    simp [sub_eq_add_neg]

/-- The **sign isomorphism** `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` sending each
generator `e δ i` to `-e (-δ) i`. -/
def signEquiv (δ : R) (n : ℕ) : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n :=
  signEquivOfAddEqZero (add_neg_cancel δ) n

/-- Unfolding `signEquiv` as `signEquivOfAddEqZero (add_neg_cancel δ)`. -/
theorem signEquiv_def (δ : R) (n : ℕ) :
    signEquiv δ n = signEquivOfAddEqZero (add_neg_cancel δ) n :=
  (rfl)

/-- `signEquiv` sends each generator `e δ i` to `-e (-δ) i`. -/
@[simp]
theorem signEquiv_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ n (e δ i) = -e (-δ) i :=
  signEquivOfAddEqZero_e (add_neg_cancel δ) i

/-- `(signEquiv δ n).symm` sends each generator `e (-δ) i` to `-e δ i`. -/
@[simp]
theorem signEquiv_symm_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    (signEquiv δ n).symm (e (-δ) i) = -e δ i :=
  signEquivOfAddEqZero_symm_e (add_neg_cancel δ) i

/-- `signEquiv` commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R δ (n + 1)) :
    signEquiv δ (n + 2) (strandIncl x) = strandIncl (signEquiv δ (n + 1) x) :=
  signEquivOfAddEqZero_strandIncl (add_neg_cancel δ) x

/-- `signEquiv` preserves the augmentation. -/
@[simp]
theorem aug_signEquiv (δ : R) {n : ℕ} (x : TemperleyLieb R δ n) :
    aug (signEquiv δ n x) = aug x :=
  aug_signEquivOfAddEqZero (add_neg_cancel δ) x

/-- On at most one strand, `signEquiv` commutes with the identification with `R`. -/
theorem algEquivOfLeOne_signEquiv (δ : R) {n : ℕ} (hn : n ≤ 1) (x : TemperleyLieb R δ n) :
    algEquivOfLeOne (-δ) hn (signEquiv δ n x) = algEquivOfLeOne δ hn x :=
  algEquivOfLeOne_signEquivOfAddEqZero (add_neg_cancel δ) hn x

/-- `signEquiv` negates the second coefficient of a Kauffman crossing. -/
theorem signEquiv_crossing (δ α β : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ n (crossing δ α β i) = crossing (-δ) α (-β) i :=
  signEquivOfAddEqZero_crossing (add_neg_cancel δ) α β i

/-- `signEquiv` carries `jonesWenzl δ n` to `jonesWenzl (-δ) n`. -/
@[simp]
theorem signEquiv_jonesWenzl (δ : R) (n : ℕ) :
    signEquiv δ n (jonesWenzl δ n) = jonesWenzl (-δ) n :=
  signEquivOfAddEqZero_jonesWenzl (add_neg_cancel δ) n

end SignEquiv

/-! ### Compatibility with the analytic adjoint -/

section Star

variable {R : Type*} [CommRing R] [StarRing R]

/-- Helper packaging `IsSelfAdjoint (-δ)` as a `Fact` from `Fact (IsSelfAdjoint δ)`. Kept as a
theorem rather than a global instance so `Fact (IsSelfAdjoint ?x)` cannot loop on `-?y`. -/
theorem isSelfAdjoint_neg_fact (δ : R) [h : Fact (IsSelfAdjoint δ)] :
    Fact (IsSelfAdjoint (-δ)) :=
  ⟨h.out.neg⟩

/-- At self-adjoint opposite loop parameters `δ + δ' = 0`, `signEquivOfAddEqZero` commutes with
the analytic adjoint. -/
@[simp]
theorem signEquivOfAddEqZero_star {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    (h : δ + δ' = 0) {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquivOfAddEqZero h n (star x) = star (signEquivOfAddEqZero h n x) :=
  map_star_iff (F := (signEquivOfAddEqZero h n).toAlgHom).mpr
    (fun i ↦ by
      simpa [signEquivOfAddEqZero_e] using (isSelfAdjoint_e (R := R) (δ := δ') (n := n) i).neg) x

/-- At a self-adjoint loop parameter, `signEquiv` commutes with the analytic adjoint. -/
@[simp]
theorem signEquiv_star (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquiv δ n (star x) = star (signEquiv δ n x) :=
  signEquivOfAddEqZero_star (add_neg_cancel δ) x

/-- The **sign `⋆`-algebra isomorphism** between Temperley–Lieb algebras at self-adjoint opposite
loop parameters `δ + δ' = 0`. -/
def signStarAlgEquivOfAddEqZero {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    (h : δ + δ' = 0) (n : ℕ) :
    TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R δ' n :=
  StarAlgEquiv.ofAlgEquiv (signEquivOfAddEqZero h n) (signEquivOfAddEqZero_star h)

/-- Coercing `signStarAlgEquivOfAddEqZero` to an algebra equivalence recovers
`signEquivOfAddEqZero`. -/
@[simp]
theorem toAlgEquiv_signStarAlgEquivOfAddEqZero {δ δ' : R} [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint δ')] (h : δ + δ' = 0) (n : ℕ) :
    (signStarAlgEquivOfAddEqZero h n).toAlgEquiv = signEquivOfAddEqZero h n :=
  (rfl)

/-- Evaluation of `signStarAlgEquivOfAddEqZero` agrees with `signEquivOfAddEqZero`. -/
@[simp]
theorem signStarAlgEquivOfAddEqZero_apply {δ δ' : R} [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint δ')] (h : δ + δ' = 0) (n : ℕ) (x : TemperleyLieb R δ n) :
    signStarAlgEquivOfAddEqZero h n x = signEquivOfAddEqZero h n x :=
  (rfl)

/-- The inverse of `signStarAlgEquivOfAddEqZero` is `signStarAlgEquivOfAddEqZero` with the
parameters swapped. -/
theorem signStarAlgEquivOfAddEqZero_symm {δ δ' : R} [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint δ')] (h : δ + δ' = 0) (n : ℕ) :
    (signStarAlgEquivOfAddEqZero h n).symm =
      signStarAlgEquivOfAddEqZero (by rwa [add_comm]) n :=
  (rfl)

/-- The **sign `⋆`-algebra isomorphism** `TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n`. -/
def signStarAlgEquiv (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))] (n : ℕ) :
    TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n :=
  signStarAlgEquivOfAddEqZero (add_neg_cancel δ) n

/-- Coercing `signStarAlgEquiv` to an algebra equivalence recovers `signEquiv`. -/
@[simp]
theorem toAlgEquiv_signStarAlgEquiv (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (n : ℕ) :
    (signStarAlgEquiv δ n).toAlgEquiv = signEquiv δ n :=
  (rfl)

/-- Evaluation of `signStarAlgEquiv` agrees with `signEquiv`. -/
@[simp]
theorem signStarAlgEquiv_apply (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (n : ℕ) (x : TemperleyLieb R δ n) :
    signStarAlgEquiv δ n x = signEquiv δ n x :=
  (rfl)

end Star

/-! ### Markov traces, normalized traces, and trace-radical quotients -/

section Trace

variable {R : Type*} [CommRing R]

namespace IsMarkovTrace

/-- Pulling a Markov trace at `δ'` back along `signEquivOfAddEqZero` with the levelwise sign
`(-1) ^ n` gives a Markov trace at `δ` whenever `δ + δ' = 0`. -/
theorem pullback_signEquivOfAddEqZero {δ δ' : R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) :
    IsMarkovTrace R δ
      (fun n ↦ (-1 : R) ^ n • (tr' n ∘ₗ (signEquivOfAddEqZero h n).toLinearMap)) := by
  have hδ : δ = (-1 : R) * δ' := by
    rw [eq_neg_of_add_eq_zero_left h]
    ring
  constructor
  · intro n
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      smul_eq_mul]
    rw [_root_.map_one, htr'.map_one n, ← mul_pow, ← hδ]
  · intro n x y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      smul_eq_mul]
    rw [map_mul, htr'.map_mul_comm n, ← map_mul]
  · intro n x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      signEquivOfAddEqZero_strandIncl, htr'.map_strandIncl, smul_eq_mul]
    have hsign : (-1 : R) ^ (n + 2) * δ' = δ * (-1 : R) ^ (n + 1) := by
      rw [hδ, pow_succ (-1 : R) (n + 1)]
      ring
    calc (-1 : R) ^ (n + 2) * (δ' * tr' (n + 1) (signEquivOfAddEqZero h (n + 1) x))
        = ((-1 : R) ^ (n + 2) * δ') * tr' (n + 1) (signEquivOfAddEqZero h (n + 1) x) := by ring
      _ = (δ * (-1 : R) ^ (n + 1)) * tr' (n + 1) (signEquivOfAddEqZero h (n + 1) x) := by
          rw [hsign]
      _ = δ * ((-1 : R) ^ (n + 1) * tr' (n + 1) (signEquivOfAddEqZero h (n + 1) x)) := by ring
  · intro n x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      signEquivOfAddEqZero_strandIncl, signEquivOfAddEqZero_e, mul_neg, map_neg,
      htr'.map_strandIncl_mul_e_last, smul_eq_mul]
    simp only [pow_succ]
    ring

/-- Pulling a Markov trace at `-δ` back along `signEquiv δ` with the sign `(-1) ^ n` gives a
Markov trace at `δ`. -/
theorem pullback_signEquiv {δ : R} {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr' : IsMarkovTrace R (-δ) tr') :
    IsMarkovTrace R δ (fun n ↦ (-1 : R) ^ n • (tr' n ∘ₗ (signEquiv δ n).toLinearMap)) :=
  htr'.pullback_signEquivOfAddEqZero (add_neg_cancel δ)

/-- **Sign transformation of Markov traces.** If `tr` and `tr'` are Markov traces at opposite loop
parameters `δ + δ' = 0`, then `tr' n (signEquivOfAddEqZero h n x) = (-1) ^ n * tr n x`. -/
theorem map_signEquivOfAddEqZero {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0)
    (n : ℕ) (x : TemperleyLieb R δ n) :
    tr' n (signEquivOfAddEqZero h n x) = (-1 : R) ^ n * tr n x := by
  have heq := LinearMap.congr_fun (congrFun (htr.unique (htr'.pullback_signEquivOfAddEqZero h)) n) x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    smul_eq_mul] at heq
  calc
    tr' n (signEquivOfAddEqZero h n x)
        = ((-1 : R) * (-1 : R)) ^ n * tr' n (signEquivOfAddEqZero h n x) := by simp
    _ = (-1 : R) ^ n * ((-1 : R) ^ n * tr' n (signEquivOfAddEqZero h n x)) := by
          rw [mul_pow, mul_assoc]
    _ = (-1 : R) ^ n * tr n x := by rw [← heq]

/-- **Sign transformation of Markov traces** between `δ` and `-δ`. -/
theorem map_signEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R δ n) :
    tr' n (signEquiv δ n x) = (-1 : R) ^ n * tr n x :=
  htr.map_signEquivOfAddEqZero htr' (add_neg_cancel δ) n x

/-- **Invariance of the normalized Markov trace** under `signEquivOfAddEqZero`: since
`Ring.inverse δ' = -Ring.inverse δ` when `δ + δ' = 0`, the factors `Ring.inverse δ' ^ n` and
`(-1) ^ n` combine to `Ring.inverse δ ^ n`. No invertibility assumption on `δ` is needed. -/
theorem inverse_pow_mul_map_signEquivOfAddEqZero {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0)
    (n : ℕ) (x : TemperleyLieb R δ n) :
    Ring.inverse δ' ^ n * tr' n (signEquivOfAddEqZero h n x) =
      Ring.inverse δ ^ n * tr n x := by
  have hδ' : δ' = (-1 : R) * δ := by
    rw [eq_neg_of_add_eq_zero_right h]
    ring
  have hinv_neg_one : Ring.inverse (-1 : R) = -1 := by
    simpa using Ring.inverse_unit (-1 : Rˣ)
  have hinv : Ring.inverse δ' = Ring.inverse δ * (-1 : R) := by
    rw [hδ', Ring.inverse_mul (Or.inl isUnit_neg_one), hinv_neg_one]
  rw [htr.map_signEquivOfAddEqZero htr' h n x, hinv, mul_pow, mul_assoc, ← mul_assoc ((-1 : R) ^ n),
    ← mul_pow]
  simp

/-- **Invariance of the normalized Markov trace** between `δ` and `-δ`. -/
theorem inverse_pow_mul_map_signEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R δ n) :
    Ring.inverse (-δ) ^ n * tr' n (signEquiv δ n x) = Ring.inverse δ ^ n * tr n x :=
  htr.inverse_pow_mul_map_signEquivOfAddEqZero htr' (add_neg_cancel δ) n x

/-- **Invariance of the normalized Hermitian trace form** under `signEquivOfAddEqZero`. -/
theorem inverse_pow_mul_map_star_mul_self_signEquivOfAddEqZero [StarRing R]
    {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0)
    (n : ℕ) (x : TemperleyLieb R δ n) :
    Ring.inverse δ' ^ n *
        tr' n (star (signEquivOfAddEqZero h n x) * signEquivOfAddEqZero h n x) =
      Ring.inverse δ ^ n * tr n (star x * x) := by
  rw [← signEquivOfAddEqZero_star, ← map_mul,
    htr.inverse_pow_mul_map_signEquivOfAddEqZero htr' h n]

/-- **Invariance of the normalized Hermitian trace form** between `δ` and `-δ`. -/
theorem inverse_pow_mul_map_star_mul_self_signEquiv [StarRing R]
    {δ : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R δ n) :
    Ring.inverse (-δ) ^ n * tr' n (star (signEquiv δ n x) * signEquiv δ n x) =
      Ring.inverse δ ^ n * tr n (star x * x) :=
  htr.inverse_pow_mul_map_star_mul_self_signEquivOfAddEqZero htr' (add_neg_cancel δ) n x

/-! #### Trace-radical and quotient-tower transport -/

/-- `signEquivOfAddEqZero` preserves and reflects membership in the trace radical. -/
theorem mem_traceRadical_signEquivOfAddEqZero_iff {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0)
    {n : ℕ} {x : TemperleyLieb R δ n} :
    signEquivOfAddEqZero h n x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  simp only [LinearMap.mem_traceRadical]
  refine (signEquivOfAddEqZero h n).surjective.forall.trans ?_
  refine forall_congr' fun y ↦ ?_
  rw [← map_mul, htr.map_signEquivOfAddEqZero htr' h n]
  exact ⟨fun hy ↦ by simpa [← mul_assoc, ← mul_pow] using congrArg ((-1 : R) ^ n * ·) hy,
    fun hy ↦ by simp [hy]⟩

/-- Pulling back the trace radical at `δ'` along `signEquivOfAddEqZero` gives the trace radical at
`δ`. -/
theorem comap_traceRadical_signEquivOfAddEqZero {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ) :
    Ideal.comap (signEquivOfAddEqZero h n : TemperleyLieb R δ n →+* TemperleyLieb R δ' n)
        ((tr' n).traceRadical (htr'.map_mul_comm n)) =
      (tr n).traceRadical (htr.map_mul_comm n) := by
  ext x
  exact htr.mem_traceRadical_signEquivOfAddEqZero_iff htr' h

/-- Pushing forward the trace radical at `δ` along `signEquivOfAddEqZero` gives the trace radical
at `δ'`. -/
theorem map_traceRadical_signEquivOfAddEqZero {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ) :
    Ideal.map (signEquivOfAddEqZero h n : TemperleyLieb R δ n →+* TemperleyLieb R δ' n)
        ((tr n).traceRadical (htr.map_mul_comm n)) =
      (tr' n).traceRadical (htr'.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_signEquivOfAddEqZero htr' h n]
  exact Ideal.map_comap_of_surjective _ (signEquivOfAddEqZero h n).surjective _

/-- `signEquiv` preserves and reflects membership in the trace radical. -/
theorem mem_traceRadical_signEquiv_iff {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    {n : ℕ} {x : TemperleyLieb R δ n} :
    signEquiv δ n x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) :=
  htr.mem_traceRadical_signEquivOfAddEqZero_iff htr' (add_neg_cancel δ)

/-- Pulling back the trace radical at `-δ` along `signEquiv` gives the trace radical at `δ`. -/
theorem comap_traceRadical_signEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.comap (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
        ((tr' n).traceRadical (htr'.map_mul_comm n)) =
      (tr n).traceRadical (htr.map_mul_comm n) :=
  htr.comap_traceRadical_signEquivOfAddEqZero htr' (add_neg_cancel δ) n

/-- Pushing forward the trace radical at `δ` along `signEquiv` gives the trace radical at `-δ`. -/
theorem map_traceRadical_signEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.map (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
        ((tr n).traceRadical (htr.map_mul_comm n)) =
      (tr' n).traceRadical (htr'.map_mul_comm n) :=
  htr.map_traceRadical_signEquivOfAddEqZero htr' (add_neg_cancel δ) n

/-- The **sign isomorphism on trace-radical quotients** for opposite loop parameters
`δ + δ' = 0`. -/
def quotientSignEquivOfAddEqZero {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      (TemperleyLieb R δ' n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  Ideal.quotientEquivAlg
    ((tr n).traceRadical (htr.map_mul_comm n))
    ((tr' n).traceRadical (htr'.map_mul_comm n))
    (signEquivOfAddEqZero h n)
    (htr.map_traceRadical_signEquivOfAddEqZero htr' h n).symm

/-- `quotientSignEquivOfAddEqZero` acts on quotient classes via `signEquivOfAddEqZero`. -/
@[simp]
theorem quotientSignEquivOfAddEqZero_mk {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ)
    (x : TemperleyLieb R δ n) :
    htr.quotientSignEquivOfAddEqZero htr' h n
        (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
      Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n))
        (signEquivOfAddEqZero h n x) :=
  (rfl)

/-- `quotientSignEquivOfAddEqZero` intertwines the quotient strand inclusions
`quotientStrandIncl`. -/
@[simp]
theorem quotientSignEquivOfAddEqZero_quotientStrandIncl {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ)
    (q : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientSignEquivOfAddEqZero htr' h (n + 2) (htr.quotientStrandIncl n q) =
      htr'.quotientStrandIncl n (htr.quotientSignEquivOfAddEqZero htr' h (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- `quotientSignEquivOfAddEqZero` scales `quotientTrace` by `(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientSignEquivOfAddEqZero {δ δ' : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ)
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n)
        (htr.quotientSignEquivOfAddEqZero htr' h n q) =
      (-1 : R) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.map_signEquivOfAddEqZero htr' h n]

/-- The **sign isomorphism on trace-radical quotients** between `δ` and `-δ`. -/
def quotientSignEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  htr.quotientSignEquivOfAddEqZero htr' (add_neg_cancel δ) n

/-- `quotientSignEquiv` acts on quotient classes via `signEquiv`. -/
@[simp]
theorem quotientSignEquiv_mk {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ n) :
    htr.quotientSignEquiv htr' n
        (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
      Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n))
        (signEquiv δ n x) :=
  (rfl)

/-- `quotientSignEquiv` intertwines the quotient strand inclusions `quotientStrandIncl`. -/
@[simp]
theorem quotientSignEquiv_quotientStrandIncl {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (q : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientSignEquiv htr' (n + 2) (htr.quotientStrandIncl n q) =
      htr'.quotientStrandIncl n (htr.quotientSignEquiv htr' (n + 1) q) :=
  htr.quotientSignEquivOfAddEqZero_quotientStrandIncl htr' (add_neg_cancel δ) n q

/-- `quotientSignEquiv` scales `quotientTrace` by `(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientSignEquiv {δ : R}
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n)
        (htr.quotientSignEquiv htr' n q) =
      (-1 : R) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) q :=
  htr.quotientTrace_quotientSignEquivOfAddEqZero htr' (add_neg_cancel δ) n q

/-- The **sign `⋆`-algebra isomorphism on trace-radical quotients** for self-adjoint opposite loop
parameters `δ + δ' = 0`. -/
def quotientSignStarAlgEquivOfAddEqZero [StarRing R]
    {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ + δ' = 0) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃⋆ₐ[R]
      (TemperleyLieb R δ' n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  Ideal.quotientEquivStarAlg
    ((tr n).traceRadical (htr.map_mul_comm n))
    ((tr' n).traceRadical (htr'.map_mul_comm n))
    (signStarAlgEquivOfAddEqZero h n)
    (htr.map_traceRadical_signEquivOfAddEqZero htr' h n).symm

/-- Forgetting the star structure on `quotientSignStarAlgEquivOfAddEqZero` recovers
`quotientSignEquivOfAddEqZero`. -/
@[simp]
theorem toAlgEquiv_quotientSignStarAlgEquivOfAddEqZero [StarRing R]
    {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ + δ' = 0) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (htr.quotientSignStarAlgEquivOfAddEqZero htr' h n).toAlgEquiv =
      htr.quotientSignEquivOfAddEqZero htr' h n :=
  Ideal.toAlgEquiv_quotientEquivStarAlg _ _ _ _

/-- Evaluation of `quotientSignStarAlgEquivOfAddEqZero` agrees with
`quotientSignEquivOfAddEqZero`. -/
@[simp]
theorem quotientSignStarAlgEquivOfAddEqZero_apply [StarRing R]
    {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ + δ' = 0) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientSignStarAlgEquivOfAddEqZero htr' h n q =
      htr.quotientSignEquivOfAddEqZero htr' h n q :=
  Ideal.quotientEquivStarAlg_apply _ _ _ _ q

/-- The **sign `⋆`-algebra isomorphism on trace-radical quotients** between `δ` and `-δ`. -/
def quotientSignStarAlgEquiv [StarRing R]
    {δ : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃⋆ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  htr.quotientSignStarAlgEquivOfAddEqZero htr' (add_neg_cancel δ) n

/-- Forgetting the star structure on `quotientSignStarAlgEquiv` recovers `quotientSignEquiv`. -/
@[simp]
theorem toAlgEquiv_quotientSignStarAlgEquiv [StarRing R]
    {δ : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (htr.quotientSignStarAlgEquiv htr' n).toAlgEquiv =
      htr.quotientSignEquiv htr' n :=
  htr.toAlgEquiv_quotientSignStarAlgEquivOfAddEqZero htr' (add_neg_cancel δ) n

/-- Evaluation of `quotientSignStarAlgEquiv` agrees with `quotientSignEquiv`. -/
@[simp]
theorem quotientSignStarAlgEquiv_apply [StarRing R]
    {δ : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientSignStarAlgEquiv htr' n q =
      htr.quotientSignEquiv htr' n q :=
  htr.quotientSignStarAlgEquivOfAddEqZero_apply htr' (add_neg_cancel δ) n q

end IsMarkovTrace

/-! #### Spin-model `markovTrace` specializations -/

/-- If `δ = -(q + q⁻¹)` for a unit `q`, then `-δ = -((-q) + (-q)⁻¹)`. -/
theorem neg_loop_eq_of_loop_eq {δ : R} (q : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) :
    -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := by
  rw [hq, inv_neg]
  simp
  ring

/-- **Sign transformation of the spin-model Markov trace** for opposite loop parameters
`δ + δ' = 0` and any units `q`, `q'` realizing them. -/
theorem markovTrace_signEquivOfAddEqZero {δ δ' : R} (h : δ + δ' = 0)
    (q : Rˣ) (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (q' : Rˣ) (hq' : δ' = -((q' : R) + ((q'⁻¹ : Rˣ) : R)))
    {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace q' hq' (signEquivOfAddEqZero h n x) =
      (-1 : R) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_signEquivOfAddEqZero (isMarkovTrace_markovTrace q' hq') h n x

/-- **Sign transformation of the spin-model Markov trace**: for `δ = -(q + q⁻¹)`,
`markovTrace (-q) hq' (signEquiv δ n x) = (-1) ^ n * markovTrace q hq x`. -/
theorem markovTrace_signEquiv {δ : R} (q : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hq' : -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := neg_loop_eq_of_loop_eq q hq)
    {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace (-q) hq' (signEquiv δ n x) = (-1 : R) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_signEquiv (isMarkovTrace_markovTrace (-q) hq') n x

/-- **Invariance of the normalized spin-model Markov trace** under `signEquiv`. -/
theorem inverse_pow_mul_markovTrace_signEquiv {δ : R} (q : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hq' : -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := neg_loop_eq_of_loop_eq q hq)
    {n : ℕ} (x : TemperleyLieb R δ n) :
    Ring.inverse (-δ) ^ n * markovTrace (-q) hq' (signEquiv δ n x) =
      Ring.inverse δ ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).inverse_pow_mul_map_signEquiv
    (isMarkovTrace_markovTrace (-q) hq') n x

end Trace

end TauCeti.TemperleyLieb
