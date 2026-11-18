/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star

import TauCeti.Algebra.Ring.Invertible

/-!
# The sign isomorphism of Temperley–Lieb algebras

Over every commutative ring `R` and for every loop parameter `δ : R`, negating each generator
`e δ i ↦ -e (-δ) i` reverses the sign of the loop parameter while preserving all three families
of Temperley–Lieb relations:
* `(-e (-δ) i) * (-e (-δ) i) = (-δ) • e (-δ) i = δ • (-e (-δ) i)`;
* `(-e (-δ) i) * (-e (-δ) j) * (-e (-δ) i) = -e (-δ) i` for adjacent indices `i` and `j`;
* `(-e (-δ) i)` and `(-e (-δ) j)` commute for distant indices `i` and `j`.

By the universal property `TauCeti.TemperleyLieb.lift`, this defines an `R`-algebra isomorphism
`TauCeti.TemperleyLieb.signEquiv δ n : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` whose
inverse is the same sign-reversal construction at `-δ`. By contrast, any `R`-algebra homomorphism
`TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` fixing the generator forces `2 * δ = 0`
(`TauCeti.TemperleyLieb.two_mul_eq_zero_of_algHom_e_two`), since distinct scalar multiples of the
two-strand generator are distinct (`TauCeti.TemperleyLieb.smul_left_injective_e_two`).

The sign isomorphism commutes with adding a straight strand (`signEquiv_strandIncl`), preserves the
augmentation (`aug_signEquiv`), sends Jones–Wenzl projections to Jones–Wenzl projections
(`signEquiv_jonesWenzl`), and, when both `δ` and `-δ` are self-adjoint, commutes with the analytic
adjoint (`signEquiv_star`), giving a star-algebra isomorphism
`TauCeti.TemperleyLieb.signStarAlgEquiv`.

On unnormalized Markov traces, uniqueness (`TauCeti.TemperleyLieb.IsMarkovTrace.unique`) forces the
parity relation `tr' n (signEquiv δ n x) = (-1) ^ n * tr n x`
(`TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquiv`), specializing on the spin-model trace to
`markovTrace (-q) _ (signEquiv δ n x) = (-1) ^ n * markovTrace q hq x`
(`TauCeti.TemperleyLieb.markovTrace_neg_signEquiv`). Scaling by `Ring.inverse (δ ^ n)` cancels the
`(-1) ^ n` factor, so the normalized traces agree (`inverse_pow_mul_map_signEquiv`), and the trace
radicals correspond (`comap_traceRadical_signEquiv`), inducing algebra isomorphisms
`TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv` between the trace-radical quotients that
intertwine the quotient strand inclusions.

To avoid transporting types along `-(-δ) = δ` or `(↑(-δ) : ℂ) = -(↑δ : ℂ)`, the construction is
carried out for any pair of loop parameters with `δ + δ' = 0`
(`TauCeti.TemperleyLieb.signEquivOfAddEqZero`), whose inverse is definitionally the same
construction with `δ` and `δ'` swapped; `signEquiv` is its specialization to `δ' = -δ`. The
compatibilities above hold for `signEquivOfAddEqZero` as well, together with the induced
`⋆`-algebra equivalences `TauCeti.TemperleyLieb.signStarAlgEquivOfAddEqZero` and
`TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquivOfAddEqZero` on the algebras and on
their star-stable trace-radical quotients.

## Main definitions

* `TauCeti.TemperleyLieb.signEquivOfAddEqZero`: the algebra isomorphism
  `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R δ' n` sending `e δ i` to `-e δ' i` when `δ + δ' = 0`.
* `TauCeti.TemperleyLieb.signEquiv δ n`: the algebra isomorphism
  `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` sending `e δ i` to `-e (-δ) i`.
* `TauCeti.TemperleyLieb.signStarAlgEquiv δ n`: `signEquiv` bundled as a star-algebra isomorphism
  `TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n` for self-adjoint `δ` and `-δ`.
* `TauCeti.TemperleyLieb.signStarAlgEquivOfAddEqZero`: `signEquivOfAddEqZero` bundled as a
  star-algebra isomorphism for self-adjoint `δ` and `δ'`.
* `TauCeti.TemperleyLieb.signTraceOfAddEqZero`: the signed transport of trace families, a linear
  equivalence preserving Markov traces.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquivOfAddEqZero`: the induced algebra
  isomorphisms between the trace-radical quotients at `δ` and `-δ` (respectively `δ'`).
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquivOfAddEqZero`: the induced
  `⋆`-algebra isomorphisms between star-stable trace-radical quotients.

## Main results

* `TauCeti.TemperleyLieb.signEquiv_e`, `TauCeti.TemperleyLieb.signEquiv_symm_e`: action on
  generators.
* `TauCeti.TemperleyLieb.two_mul_eq_zero_of_algHom_e_two`: an algebra map
  `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` fixing the generator forces `2 * δ = 0`.
* `TauCeti.TemperleyLieb.signEquiv_strandIncl`, `TauCeti.TemperleyLieb.aug_signEquiv`,
  `TauCeti.TemperleyLieb.signEquiv_jonesWenzl`, `TauCeti.TemperleyLieb.signEquiv_star`:
  compatibility with strand inclusion, augmentation, Jones–Wenzl projections, and the adjoint.
* `TauCeti.TemperleyLieb.algEquivOfLeOne_signEquiv`, `TauCeti.TemperleyLieb.signEquiv_crossing`:
  compatibility with the identification with `R` on at most one strand, and negation of the
  `e`-coefficient of a Kauffman crossing.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquivOfAddEqZero`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_signEquivOfAddEqZero`: the trace
  transformation laws for `signEquivOfAddEqZero`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquiv`,
  `TauCeti.TemperleyLieb.markovTrace_signEquiv`,
  `TauCeti.TemperleyLieb.markovTrace_neg_signEquiv`: Markov traces transform by `(-1) ^ n`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_signEquiv`: invariance of the
  normalized trace `Ring.inverse (δ ^ n) * tr n x`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_quotientSignEquiv`: compatibility of the
  quotient sign isomorphism with the tower inclusions and quotient traces.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Facts 4.4.14 (TB6).
-/

public section

namespace TauCeti.TemperleyLieb

section Algebra

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

/-- The **sign isomorphism** of Temperley–Lieb algebras: negating every generator
`e δ i ↦ -e (-δ) i` identifies the Temperley–Lieb algebra at loop parameter `δ` with that
at `-δ`. -/
def signEquiv (δ : R) (n : ℕ) : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n :=
  signEquivOfAddEqZero (add_neg_cancel δ) n

/-- Unfolding `signEquiv` as `signEquivOfAddEqZero (add_neg_cancel δ)`. -/
theorem signEquiv_def (δ : R) (n : ℕ) :
    signEquiv δ n = signEquivOfAddEqZero (add_neg_cancel δ) n :=
  (rfl)

/-- The sign isomorphism sends each generator `e δ i` to `-e (-δ) i`. -/
@[simp]
theorem signEquiv_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ n (e δ i) = -e (-δ) i :=
  signEquivOfAddEqZero_e (add_neg_cancel δ) i

/-- The inverse sign isomorphism sends each generator `e (-δ) i` to `-e δ i`. -/
@[simp]
theorem signEquiv_symm_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    (signEquiv δ n).symm (e (-δ) i) = -e δ i :=
  signEquivOfAddEqZero_symm_e (add_neg_cancel δ) i

/-- The sign isomorphism is the unique `R`-algebra homomorphism negating every generator. -/
theorem eq_signEquiv_of_map_e {δ : R} {n : ℕ}
    {F : TemperleyLieb R δ n →ₐ[R] TemperleyLieb R (-δ) n}
    (hF : ∀ i, F (e δ i) = -e (-δ) i) :
    F = (signEquiv δ n).toAlgHom :=
  hom_ext fun i ↦ by simp [hF]

/-- Already on two strands, an `R`-homogeneous multiplicative map sending `e δ i` to `e (-δ) i`
without negating it forces `δ = -δ`. -/
theorem eq_neg_self_of_map_e_two {δ : R}
    {f : TemperleyLieb R δ 2 → TemperleyLieb R (-δ) 2}
    (hsmul : ∀ (r : R) x, f (r • x) = r • f x)
    (hmul : ∀ x y, f (x * y) = f x * f y)
    (i : Fin (2 - 1)) (he : f (e δ i) = e (-δ) i) : δ = -δ := by
  apply smul_left_injective_e_two (δ := -δ) i
  have h := hmul (e δ i) (e δ i)
  rw [e_mul_self, hsmul, he, e_mul_self] at h
  exact h

/-- Any `R`-algebra homomorphism `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` fixing the
two-strand generator forces `2 * δ = 0`. In particular, when `2 * δ ≠ 0`, no `R`-algebra
homomorphism `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` fixes the two-strand generator. -/
theorem two_mul_eq_zero_of_algHom_e_two {δ : R}
    (F : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2)
    (i : Fin (2 - 1)) (he : F (e δ i) = e (-δ) i) : 2 * δ = 0 := by
  have h := eq_neg_self_of_map_e_two (map_smul F) (map_mul F) i he
  linear_combination h

/-- The sign isomorphism commutes with adding a straight strand, as algebra homomorphisms. -/
theorem signEquiv_comp_strandIncl (δ : R) (n : ℕ) :
    (signEquiv δ (n + 2)).toAlgHom.comp strandIncl =
      strandIncl.comp (signEquiv δ (n + 1)).toAlgHom :=
  hom_ext fun i ↦ by simp

/-- The sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R δ (n + 1)) :
    signEquiv δ (n + 2) (strandIncl x) = strandIncl (signEquiv δ (n + 1) x) :=
  DFunLike.congr_fun (signEquiv_comp_strandIncl δ n) x

/-- The inverse sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_symm_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R (-δ) (n + 1)) :
    (signEquiv δ (n + 2)).symm (strandIncl x) = strandIncl ((signEquiv δ (n + 1)).symm x) := by
  apply (signEquiv δ (n + 2)).injective
  simp

/-- Composing the augmentation with the sign isomorphism recovers the augmentation. -/
theorem aug_comp_signEquiv (δ : R) (n : ℕ) :
    aug.comp (signEquiv δ n).toAlgHom = aug :=
  hom_ext fun i ↦ by simp

/-- The sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv (δ : R) {n : ℕ} (x : TemperleyLieb R δ n) :
    aug (signEquiv δ n x) = aug x :=
  DFunLike.congr_fun (aug_comp_signEquiv δ n) x

/-- The inverse sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv_symm (δ : R) {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    aug ((signEquiv δ n).symm x) = aug x := by
  simpa using (aug_signEquiv δ ((signEquiv δ n).symm x)).symm

/-- The sign isomorphism sends the Jones–Wenzl projection at `δ` to the Jones–Wenzl projection at
`-δ`, over every commutative ring and with no invertibility assumption on the quantum integers. -/
@[simp]
theorem signEquiv_jonesWenzl (δ : R) :
    ∀ n : ℕ, signEquiv δ n (jonesWenzl δ n) = jonesWenzl (-δ) n
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have hneg_sq : (-1 : R) ^ m * (-1 : R) ^ m = 1 := by
      rw [← mul_pow]
      simp
    have hcoeff :
        qInt R (-δ) (m + 1) * Ring.inverse (qInt R (-δ) (m + 2)) =
          -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
      rw [qInt_neg δ (m + 1), qInt_neg δ (m + 2), ringInverse_neg_one_pow_mul]
      simp only [pow_succ]
      linear_combination -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) * hneg_sq
    simp [jonesWenzl_add_two, signEquiv_jonesWenzl δ (m + 1), hcoeff]

/-- The inverse sign isomorphism sends the Jones–Wenzl projection at `-δ` to that at `δ`. -/
@[simp]
theorem signEquiv_symm_jonesWenzl (δ : R) (n : ℕ) :
    (signEquiv δ n).symm (jonesWenzl (-δ) n) = jonesWenzl δ n :=
  (signEquiv δ n).symm_apply_eq.2 (signEquiv_jonesWenzl δ n).symm

/-- On at most one strand, `signEquiv` commutes with the identification with `R`. -/
theorem algEquivOfLeOne_signEquiv (δ : R) {n : ℕ} (hn : n ≤ 1) (x : TemperleyLieb R δ n) :
    algEquivOfLeOne (-δ) hn (signEquiv δ n x) = algEquivOfLeOne δ hn x := by
  simp

/-- `signEquiv` negates the second coefficient of a Kauffman crossing. -/
theorem signEquiv_crossing (δ α β : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ n (crossing δ α β i) = crossing (-δ) α (-β) i := by
  simp [crossing_def]

/-! #### Opposite loop parameters `δ + δ' = 0` -/

/-- `signEquivOfAddEqZero` commutes with adding a straight strand. -/
@[simp]
theorem signEquivOfAddEqZero_strandIncl {δ δ' : R} (h : δ + δ' = 0) {n : ℕ}
    (x : TemperleyLieb R δ (n + 1)) :
    signEquivOfAddEqZero h (n + 2) (strandIncl x) =
      strandIncl (signEquivOfAddEqZero h (n + 1) x) := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact signEquiv_strandIncl δ x

/-- `signEquivOfAddEqZero` preserves the augmentation. -/
@[simp]
theorem aug_signEquivOfAddEqZero {δ δ' : R} (h : δ + δ' = 0) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    aug (signEquivOfAddEqZero h n x) = aug x := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact aug_signEquiv δ x

/-- On at most one strand, `signEquivOfAddEqZero` commutes with the identification with `R`. -/
theorem algEquivOfLeOne_signEquivOfAddEqZero {δ δ' : R} (h : δ + δ' = 0) {n : ℕ} (hn : n ≤ 1)
    (x : TemperleyLieb R δ n) :
    algEquivOfLeOne δ' hn (signEquivOfAddEqZero h n x) = algEquivOfLeOne δ hn x := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact algEquivOfLeOne_signEquiv δ hn x

/-- `signEquivOfAddEqZero` negates the second coefficient of a Kauffman crossing. -/
theorem signEquivOfAddEqZero_crossing {δ δ' : R} (h : δ + δ' = 0) (α β : R) {n : ℕ}
    (i : Fin (n - 1)) :
    signEquivOfAddEqZero h n (crossing δ α β i) = crossing δ' α (-β) i := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact signEquiv_crossing δ α β i

/-- `signEquivOfAddEqZero` carries the Jones–Wenzl projection at `δ` to the Jones–Wenzl projection
at `δ'`, with no invertibility assumption on the quantum integers. -/
@[simp]
theorem signEquivOfAddEqZero_jonesWenzl {δ δ' : R} (h : δ + δ' = 0) (n : ℕ) :
    signEquivOfAddEqZero h n (jonesWenzl δ n) = jonesWenzl δ' n := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact signEquiv_jonesWenzl δ n

end Algebra

section Star

variable {R : Type*} [CommRing R] [StarRing R] {δ : R}
  [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- When `δ` and `-δ` are self-adjoint, the sign isomorphism commutes with the analytic adjoint:
`-e (-δ) i` is self-adjoint for every generator `e (-δ) i`. -/
@[simp]
theorem signEquiv_star {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquiv δ n (star x) = star (signEquiv δ n x) :=
  map_star_iff (F := (signEquiv δ n).toAlgHom) |>.mpr
    (fun i ↦ by simpa using (isSelfAdjoint_e i).neg) x

/-- When `δ` and `-δ` are self-adjoint, the inverse sign isomorphism commutes with the analytic
adjoint. -/
@[simp]
theorem signEquiv_symm_star {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    (signEquiv δ n).symm (star x) = star ((signEquiv δ n).symm x) := by
  apply (signEquiv δ n).injective
  simp

section Apply

variable (δ)

/-- The sign isomorphism bundled as a star-algebra equivalence
`TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n`, for self-adjoint `δ` and `-δ`. -/
def signStarAlgEquiv (n : ℕ) : TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n :=
  StarAlgEquiv.ofAlgEquiv (signEquiv δ n) fun x ↦ signEquiv_star x

/-- Applying `signStarAlgEquiv` agrees with `signEquiv`. -/
@[simp]
theorem signStarAlgEquiv_apply {n : ℕ} (x : TemperleyLieb R δ n) :
    signStarAlgEquiv δ n x = signEquiv δ n x := by
  rw [signStarAlgEquiv, StarAlgEquiv.ofAlgEquiv_apply]

/-- Applying the inverse of `signStarAlgEquiv` agrees with `(signEquiv δ n).symm`. -/
@[simp]
theorem signStarAlgEquiv_symm_apply {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    (signStarAlgEquiv δ n).symm x = (signEquiv δ n).symm x := by
  rw [StarAlgEquiv.symm_apply_eq, signStarAlgEquiv_apply, AlgEquiv.apply_symm_apply]

/-- The underlying algebra equivalence of `signStarAlgEquiv` is `signEquiv`. -/
@[simp]
theorem toAlgEquiv_signStarAlgEquiv (n : ℕ) :
    (signStarAlgEquiv δ n).toAlgEquiv = signEquiv δ n := by
  rw [signStarAlgEquiv, StarAlgEquiv.toAlgEquiv_ofAlgEquiv]

end Apply

end Star

section StarAddEqZero

variable {R : Type*} [CommRing R] [StarRing R] {δ δ' : R}
  [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]

/-- At self-adjoint opposite loop parameters `δ + δ' = 0`, `signEquivOfAddEqZero` commutes with
the analytic adjoint. -/
@[simp]
theorem signEquivOfAddEqZero_star (h : δ + δ' = 0) {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquivOfAddEqZero h n (star x) = star (signEquivOfAddEqZero h n x) := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact signEquiv_star x

/-- The **sign `⋆`-algebra isomorphism** between Temperley–Lieb algebras at self-adjoint opposite
loop parameters `δ + δ' = 0`. -/
def signStarAlgEquivOfAddEqZero (h : δ + δ' = 0) (n : ℕ) :
    TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R δ' n :=
  StarAlgEquiv.ofAlgEquiv (signEquivOfAddEqZero h n) (signEquivOfAddEqZero_star h)

/-- Coercing `signStarAlgEquivOfAddEqZero` to an algebra equivalence recovers
`signEquivOfAddEqZero`. -/
@[simp]
theorem toAlgEquiv_signStarAlgEquivOfAddEqZero (h : δ + δ' = 0) (n : ℕ) :
    (signStarAlgEquivOfAddEqZero h n).toAlgEquiv = signEquivOfAddEqZero h n :=
  (rfl)

/-- Evaluation of `signStarAlgEquivOfAddEqZero` agrees with `signEquivOfAddEqZero`. -/
@[simp]
theorem signStarAlgEquivOfAddEqZero_apply (h : δ + δ' = 0) (n : ℕ) (x : TemperleyLieb R δ n) :
    signStarAlgEquivOfAddEqZero h n x = signEquivOfAddEqZero h n x :=
  (rfl)

/-- The inverse of `signStarAlgEquivOfAddEqZero` is `signStarAlgEquivOfAddEqZero` with the
parameters swapped. -/
theorem signStarAlgEquivOfAddEqZero_symm (h : δ + δ' = 0) (n : ℕ) :
    (signStarAlgEquivOfAddEqZero h n).symm =
      signStarAlgEquivOfAddEqZero (by rwa [add_comm]) n :=
  (rfl)

end StarAddEqZero

section SignTrace

variable {R : Type*} [CommRing R]

/-- The **signed transport of trace families** between opposite loop parameters `δ + δ' = 0`: the
linear equivalence sending a family `tr'` at `δ'` to `n ↦ (-1) ^ n • (tr' n ∘ s)`, where `s` is
`signEquivOfAddEqZero h n`. It carries Markov traces to Markov traces
(`IsMarkovTrace.signTraceOfAddEqZero`). -/
def signTraceOfAddEqZero {δ δ' : R} (h : δ + δ' = 0) :
    (∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R) ≃ₗ[R] (∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) where
  toFun tr n := (-1 : R) ^ n • (tr n ∘ₗ (signEquivOfAddEqZero h n).toLinearMap)
  invFun tr n := (-1 : R) ^ n • (tr n ∘ₗ (signEquivOfAddEqZero h n).symm.toLinearMap)
  left_inv tr := by ext n x; simp [← mul_assoc, ← mul_pow]
  right_inv tr := by ext n x; simp [← mul_assoc, ← mul_pow]
  map_add' tr₁ tr₂ := by ext n x; simp [mul_add]
  map_smul' r tr := by ext n x; simp [mul_left_comm]

/-- Evaluation of the signed transport of a trace family. -/
@[simp]
theorem signTraceOfAddEqZero_apply {δ δ' : R} (h : δ + δ' = 0)
    (tr : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R) {n : ℕ} (x : TemperleyLieb R δ n) :
    signTraceOfAddEqZero h tr n x = (-1 : R) ^ n * tr n (signEquivOfAddEqZero h n x) :=
  (rfl)

/-- Evaluation of the inverse signed transport of a trace family. -/
@[simp]
theorem signTraceOfAddEqZero_symm_apply {δ δ' : R} (h : δ + δ' = 0)
    (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) {n : ℕ} (x : TemperleyLieb R δ' n) :
    (signTraceOfAddEqZero h).symm tr n x =
      (-1 : R) ^ n * tr n ((signEquivOfAddEqZero h n).symm x) :=
  (rfl)

end SignTrace

namespace IsMarkovTrace

section Trace

variable {R : Type*} [CommRing R] {δ : R}

private theorem neg_one_pow_smul_comp_aux {δ δ' : R} (h : δ' = -δ)
    {F : ∀ n : ℕ, TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R δ' n}
    (he : ∀ (n : ℕ) (i : Fin (n - 1)), F n (e δ i) = -e δ' i)
    (hstrand : ∀ (n : ℕ) (x : TemperleyLieb R δ (n + 1)),
      F (n + 2) (strandIncl x) = strandIncl (F (n + 1) x))
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr' : IsMarkovTrace R δ' tr') :
    IsMarkovTrace R δ (fun n ↦ (-1 : R) ^ n • (tr' n).comp (F n).toLinearMap) where
  map_one n := by
    simp [htr'.map_one, h, ← mul_pow]
  map_mul_comm n x y := by
    simp [htr'.map_mul_comm]
  map_strandIncl n x := by
    simp [hstrand, htr'.map_strandIncl, h, pow_succ]
    ring
  map_strandIncl_mul_e_last n x := by
    simp [hstrand, he, htr'.map_strandIncl_mul_e_last, pow_succ]

/-- Pulling back a Markov trace at `-δ` along `signEquiv` and scaling level `n` by `(-1) ^ n`
produces a Markov trace at `δ`. -/
theorem neg_one_pow_smul_comp_signEquiv {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr' : IsMarkovTrace R (-δ) tr') :
    IsMarkovTrace R δ (fun n ↦ (-1 : R) ^ n • (tr' n).comp (signEquiv δ n).toLinearMap) :=
  neg_one_pow_smul_comp_aux rfl (fun _ ↦ signEquiv_e δ) (fun _ ↦ signEquiv_strandIncl δ) htr'

/-- Pushing forward a Markov trace at `δ` along `signEquiv` and scaling level `n` by `(-1) ^ n`
produces a Markov trace at `-δ`. -/
theorem neg_one_pow_smul_comp_signEquiv_symm {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) :
    IsMarkovTrace R (-δ)
      (fun n ↦ (-1 : R) ^ n • (tr n).comp (signEquiv δ n).symm.toLinearMap) :=
  neg_one_pow_smul_comp_aux (neg_neg δ).symm (fun _ ↦ signEquiv_symm_e δ)
    (fun _ ↦ signEquiv_symm_strandIncl δ) htr

/-- **Sign transformation of Markov traces.** For Markov traces `tr` at `δ` and `tr'` at `-δ`,
the sign isomorphism multiplies the trace on `n` strands by `(-1) ^ n`. -/
theorem map_signEquiv {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    tr' n (signEquiv δ n x) = (-1) ^ n * tr n x := by
  have heq := LinearMap.congr_fun
    (congrFun (htr'.unique htr.neg_one_pow_smul_comp_signEquiv_symm) n) (signEquiv δ n x)
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply, smul_eq_mul] using heq

/-- **Sign transformation of Markov traces** along the inverse sign isomorphism. -/
theorem map_signEquiv_symm {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R (-δ) n) :
    tr n ((signEquiv δ n).symm x) = (-1) ^ n * tr' n x := by
  have heq := LinearMap.congr_fun
    (congrFun (htr.unique htr'.neg_one_pow_smul_comp_signEquiv) n) ((signEquiv δ n).symm x)
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply, smul_eq_mul] using heq

/-- **Invariance of the normalized Markov trace** under the sign isomorphism: scaling the
unnormalized trace on `n` strands by `Ring.inverse (δ ^ n)` cancels the `(-1) ^ n` sign factor,
over every commutative ring. -/
theorem inverse_pow_mul_map_signEquiv {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    Ring.inverse ((-δ) ^ n) * tr' n (signEquiv δ n x) = Ring.inverse (δ ^ n) * tr n x := by
  rw [neg_pow, ringInverse_neg_one_pow_mul, htr.map_signEquiv htr', mul_mul_mul_comm, ← mul_pow]
  simp

end Trace

section Star

variable {R : Type*} [CommRing R] [StarRing R] {δ : R}
  [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- The sign isomorphism multiplies the Hermitian sesquilinear trace form on `n` strands by
`(-1) ^ n`. -/
theorem traceSesqForm_signEquiv {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x y : TemperleyLieb R δ n) :
    (tr' n).traceSesqForm (signEquiv δ n x) (signEquiv δ n y) =
      (-1) ^ n * (tr n).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← signEquiv_star, ← map_mul,
    htr.map_signEquiv htr']

/-- The sign isomorphism preserves the normalized Hermitian square
`Ring.inverse (δ ^ n) * tr n (star x * x)`. -/
theorem inverse_pow_mul_map_star_signEquiv_mul_signEquiv
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    Ring.inverse ((-δ) ^ n) * tr' n (star (signEquiv δ n x) * signEquiv δ n x) =
      Ring.inverse (δ ^ n) * tr n (star x * x) := by
  rw [← signEquiv_star, ← map_mul, htr.inverse_pow_mul_map_signEquiv htr']

end Star

section Radical

variable {R : Type*} [CommRing R] {δ : R}
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
  (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')

/-- The sign isomorphism preserves and reflects membership in the trace radical, since `(-1) ^ n`
is a unit in every commutative ring. -/
theorem signEquiv_mem_traceRadical_iff {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquiv δ n x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  simp only [LinearMap.mem_traceRadical]
  rw [← (signEquiv δ n).toEquiv.forall_congr_right]
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul, htr.map_signEquiv htr',
    (isUnit_one.neg.pow n).mul_right_eq_zero]

/-- The inverse sign isomorphism preserves and reflects membership in the trace radical. -/
theorem signEquiv_symm_mem_traceRadical_iff {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    (signEquiv δ n).symm x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔
      x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) := by
  simpa using (htr.signEquiv_mem_traceRadical_iff htr' ((signEquiv δ n).symm x)).symm

/-- Pulling back the trace radical at `-δ` along `signEquiv` yields the trace radical at `δ`. -/
theorem comap_traceRadical_signEquiv (n : ℕ) :
    Ideal.comap (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
      ((tr' n).traceRadical (htr'.map_mul_comm n)) =
        (tr n).traceRadical (htr.map_mul_comm n) :=
  Ideal.ext fun x ↦ htr.signEquiv_mem_traceRadical_iff htr' x

/-- Mapping the trace radical at `δ` forward along `signEquiv` yields the trace radical at `-δ`. -/
theorem map_traceRadical_signEquiv (n : ℕ) :
    Ideal.map (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
      ((tr n).traceRadical (htr.map_mul_comm n)) =
        (tr' n).traceRadical (htr'.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_signEquiv htr' n, Ideal.map_coe, Ideal.comap_coe,
    Ideal.map_comap_of_surjective _ (signEquiv δ n).surjective]

/-- The algebra isomorphism between the trace-radical quotients at `δ` and `-δ` induced by
`TauCeti.TemperleyLieb.signEquiv`. -/
def quotientSignEquiv (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  Ideal.quotientEquivAlg _ _ (signEquiv δ n) (htr.map_traceRadical_signEquiv htr' n).symm

/-- `quotientSignEquiv` acts on quotient classes by applying `signEquiv` to representatives. -/
@[simp]
theorem quotientSignEquiv_mk (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientSignEquiv htr' n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (signEquiv δ n x) := by
  rw [quotientSignEquiv, Ideal.quotientEquivAlg_mk]

/-- The inverse of `quotientSignEquiv` acts on quotient classes by applying `(signEquiv δ n).symm`
to representatives. -/
@[simp]
theorem quotientSignEquiv_symm_mk (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    (htr.quotientSignEquiv htr' n).symm
      (Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n))
          ((signEquiv δ n).symm x) := by
  rw [quotientSignEquiv, Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]

/-- The quotient sign isomorphisms commute with the injective strand maps `quotientStrandIncl`
between trace-radical quotients. -/
@[simp]
theorem quotientSignEquiv_quotientStrandIncl (n : ℕ)
    (x : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientSignEquiv htr' (n + 2) (htr.quotientStrandIncl n x) =
      htr'.quotientStrandIncl n (htr.quotientSignEquiv htr' (n + 1) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- The inverse quotient sign isomorphisms commute with `quotientStrandIncl`. -/
@[simp]
theorem quotientSignEquiv_symm_quotientStrandIncl (n : ℕ)
    (x : TemperleyLieb R (-δ) (n + 1) ⧸
      (tr' (n + 1)).traceRadical (htr'.map_mul_comm (n + 1))) :
    (htr.quotientSignEquiv htr' (n + 2)).symm (htr'.quotientStrandIncl n x) =
      htr.quotientStrandIncl n ((htr.quotientSignEquiv htr' (n + 1)).symm x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- On the trace-radical quotients, `quotientSignEquiv` multiplies `quotientTrace` by `(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientSignEquiv (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientSignEquiv htr' n x) =
      (-1) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr.map_signEquiv htr']

/-- On the trace-radical quotients, `quotientSignEquiv` preserves the normalized trace
`Ring.inverse (δ ^ n) * quotientTrace`. -/
theorem inverse_pow_mul_quotientTrace_quotientSignEquiv (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    Ring.inverse ((-δ) ^ n) *
        (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientSignEquiv htr' n x) =
      Ring.inverse (δ ^ n) * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa using htr.inverse_pow_mul_map_signEquiv htr' x

end Radical

section AddEqZero

/-! #### Opposite loop parameters `δ + δ' = 0` -/

variable {R : Type*} [CommRing R] {δ δ' : R}
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}

/-- Pulling a Markov trace at `δ'` back along `signEquivOfAddEqZero` with the levelwise sign
`(-1) ^ n` gives a Markov trace at `δ` whenever `δ + δ' = 0`. -/
theorem neg_one_pow_smul_comp_signEquivOfAddEqZero (htr' : IsMarkovTrace R δ' tr')
    (h : δ + δ' = 0) :
    IsMarkovTrace R δ
      (fun n ↦ (-1 : R) ^ n • (tr' n).comp (signEquivOfAddEqZero h n).toLinearMap) := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact htr'.neg_one_pow_smul_comp_signEquiv

/-- The signed transport `signTraceOfAddEqZero` of a Markov trace family is again a Markov trace
family, including at zero loop parameter. -/
theorem signTraceOfAddEqZero (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) :
    IsMarkovTrace R δ (TemperleyLieb.signTraceOfAddEqZero h tr') :=
  htr'.neg_one_pow_smul_comp_signEquivOfAddEqZero h

/-- **Sign transformation of Markov traces.** If `tr` and `tr'` are Markov traces at opposite loop
parameters `δ + δ' = 0`, then `tr' n (signEquivOfAddEqZero h n x) = (-1) ^ n * tr n x`. -/
theorem map_signEquivOfAddEqZero (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ + δ' = 0) {n : ℕ} (x : TemperleyLieb R δ n) :
    tr' n (signEquivOfAddEqZero h n x) = (-1) ^ n * tr n x := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact htr.map_signEquiv htr' x

/-- **Invariance of the normalized Markov trace** under `signEquivOfAddEqZero`, over every
commutative ring and with no invertibility assumption on `δ`. -/
theorem inverse_pow_mul_map_signEquivOfAddEqZero (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) {n : ℕ} (x : TemperleyLieb R δ n) :
    Ring.inverse (δ' ^ n) * tr' n (signEquivOfAddEqZero h n x) =
      Ring.inverse (δ ^ n) * tr n x := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact htr.inverse_pow_mul_map_signEquiv htr' x

/-- **Invariance of the normalized Hermitian trace form** under `signEquivOfAddEqZero`. -/
theorem inverse_pow_mul_map_star_signEquivOfAddEqZero_mul_signEquivOfAddEqZero [StarRing R]
    [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    Ring.inverse (δ' ^ n) *
        tr' n (star (signEquivOfAddEqZero h n x) * signEquivOfAddEqZero h n x) =
      Ring.inverse (δ ^ n) * tr n (star x * x) := by
  rw [← signEquivOfAddEqZero_star, ← map_mul, htr.inverse_pow_mul_map_signEquivOfAddEqZero htr' h]

variable (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0)

/-- `signEquivOfAddEqZero` preserves and reflects membership in the trace radical. -/
theorem signEquivOfAddEqZero_mem_traceRadical_iff {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquivOfAddEqZero h n x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  obtain rfl := eq_neg_of_add_eq_zero_right h
  exact htr.signEquiv_mem_traceRadical_iff htr' x

/-- Pulling back the trace radical at `δ'` along `signEquivOfAddEqZero` gives the trace radical at
`δ`. -/
theorem comap_traceRadical_signEquivOfAddEqZero (n : ℕ) :
    Ideal.comap (signEquivOfAddEqZero h n : TemperleyLieb R δ n →+* TemperleyLieb R δ' n)
        ((tr' n).traceRadical (htr'.map_mul_comm n)) =
      (tr n).traceRadical (htr.map_mul_comm n) :=
  Ideal.ext fun x ↦ htr.signEquivOfAddEqZero_mem_traceRadical_iff htr' h x

/-- Pushing forward the trace radical at `δ` along `signEquivOfAddEqZero` gives the trace radical
at `δ'`. -/
theorem map_traceRadical_signEquivOfAddEqZero (n : ℕ) :
    Ideal.map (signEquivOfAddEqZero h n : TemperleyLieb R δ n →+* TemperleyLieb R δ' n)
        ((tr n).traceRadical (htr.map_mul_comm n)) =
      (tr' n).traceRadical (htr'.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_signEquivOfAddEqZero htr' h n]
  exact Ideal.map_comap_of_surjective _ (signEquivOfAddEqZero h n).surjective _

/-- The **sign isomorphism on trace-radical quotients** for opposite loop parameters
`δ + δ' = 0`. -/
def quotientSignEquivOfAddEqZero (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      (TemperleyLieb R δ' n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  Ideal.quotientEquivAlg _ _ (signEquivOfAddEqZero h n)
    (htr.map_traceRadical_signEquivOfAddEqZero htr' h n).symm

/-- `quotientSignEquivOfAddEqZero` acts on quotient classes via `signEquivOfAddEqZero`. -/
@[simp]
theorem quotientSignEquivOfAddEqZero_mk (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientSignEquivOfAddEqZero htr' h n
        (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
      Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n))
        (signEquivOfAddEqZero h n x) := by
  rw [quotientSignEquivOfAddEqZero, Ideal.quotientEquivAlg_mk]

/-- `quotientSignEquivOfAddEqZero` intertwines the quotient strand inclusions
`quotientStrandIncl`. -/
@[simp]
theorem quotientSignEquivOfAddEqZero_quotientStrandIncl (n : ℕ)
    (q : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientSignEquivOfAddEqZero htr' h (n + 2) (htr.quotientStrandIncl n q) =
      htr'.quotientStrandIncl n (htr.quotientSignEquivOfAddEqZero htr' h (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- `quotientSignEquivOfAddEqZero` scales `quotientTrace` by `(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientSignEquivOfAddEqZero (n : ℕ)
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientSignEquivOfAddEqZero htr' h n q) =
      (-1) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.map_signEquivOfAddEqZero htr' h]

end AddEqZero

section QuotientStar

variable {R : Type*} [CommRing R] [StarRing R]

/-- The **sign `⋆`-algebra isomorphism on trace-radical quotients** for self-adjoint opposite loop
parameters `δ + δ' = 0`. -/
def quotientSignStarAlgEquivOfAddEqZero {δ δ' : R} [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint δ')] {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃⋆ₐ[R]
      (TemperleyLieb R δ' n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  Ideal.quotientEquivStarAlg _ _ (signStarAlgEquivOfAddEqZero h n)
    (htr.map_traceRadical_signEquivOfAddEqZero htr' h n).symm

/-- Forgetting the star structure on `quotientSignStarAlgEquivOfAddEqZero` recovers
`quotientSignEquivOfAddEqZero`. -/
@[simp]
theorem toAlgEquiv_quotientSignStarAlgEquivOfAddEqZero {δ δ' : R} [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint δ')] {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (htr.quotientSignStarAlgEquivOfAddEqZero htr' h n).toAlgEquiv =
      htr.quotientSignEquivOfAddEqZero htr' h n :=
  Ideal.toAlgEquiv_quotientEquivStarAlg _ _ _ _

/-- Evaluation of `quotientSignStarAlgEquivOfAddEqZero` agrees with
`quotientSignEquivOfAddEqZero`. -/
@[simp]
theorem quotientSignStarAlgEquivOfAddEqZero_apply {δ δ' : R} [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint δ')] {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr') (h : δ + δ' = 0) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientSignStarAlgEquivOfAddEqZero htr' h n q =
      htr.quotientSignEquivOfAddEqZero htr' h n q :=
  Ideal.quotientEquivStarAlg_apply _ _ _ _ q

/-- The **sign `⋆`-algebra isomorphism on trace-radical quotients** between `δ` and `-δ`. -/
def quotientSignStarAlgEquiv {δ : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃⋆ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  htr.quotientSignStarAlgEquivOfAddEqZero htr' (add_neg_cancel δ) n

/-- Forgetting the star structure on `quotientSignStarAlgEquiv` recovers `quotientSignEquiv`. -/
@[simp]
theorem toAlgEquiv_quotientSignStarAlgEquiv {δ : R} [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint (-δ))] {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (htr.quotientSignStarAlgEquiv htr' n).toAlgEquiv = htr.quotientSignEquiv htr' n :=
  htr.toAlgEquiv_quotientSignStarAlgEquivOfAddEqZero htr' (add_neg_cancel δ) n

/-- Evaluation of `quotientSignStarAlgEquiv` agrees with `quotientSignEquiv`. -/
@[simp]
theorem quotientSignStarAlgEquiv_apply {δ : R} [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint (-δ))] {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientSignStarAlgEquiv htr' n q = htr.quotientSignEquiv htr' n q :=
  htr.quotientSignStarAlgEquivOfAddEqZero_apply htr' (add_neg_cancel δ) n q

end QuotientStar

end IsMarkovTrace

section SpinMarkovTrace

variable {R : Type*} [CommRing R] {δ : R}

/-- If a unit `q` parametrizes the loop value `δ = -(q + q⁻¹)`, then `-q` parametrizes `-δ`. -/
theorem neg_eq_neg_unit_add_inv {q : Rˣ} (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) :
    -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := by
  rw [hq, inv_neg, Units.val_neg, Units.val_neg]
  ring

/-- **Sign transformation of the spin-model Markov trace.** For any units `q` and `q'`
parametrizing `δ` and `-δ`, the sign isomorphism multiplies `markovTrace` on `n` strands by
`(-1) ^ n`. -/
theorem markovTrace_signEquiv (q q' : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hq' : -δ = -((q' : R) + ((q'⁻¹ : Rˣ) : R))) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    markovTrace q' hq' (signEquiv δ n x) = (-1) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_signEquiv (isMarkovTrace_markovTrace q' hq') x

/-- **Sign transformation of the spin-model Markov trace** at the negated unit `-q`:
`markovTrace (-q) _ (signEquiv δ n x) = (-1) ^ n * markovTrace q hq x`. -/
theorem markovTrace_neg_signEquiv (q : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    markovTrace (-q) (neg_eq_neg_unit_add_inv hq) (signEquiv δ n x) =
      (-1) ^ n * markovTrace q hq x :=
  markovTrace_signEquiv q (-q) hq (neg_eq_neg_unit_add_inv hq) x

/-- **Sign transformation of the spin-model Markov trace** for opposite loop parameters
`δ + δ' = 0` and any units `q`, `q'` realizing them. -/
theorem markovTrace_signEquivOfAddEqZero {δ' : R} (h : δ + δ' = 0) (q q' : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) (hq' : δ' = -((q' : R) + ((q'⁻¹ : Rˣ) : R)))
    {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace q' hq' (signEquivOfAddEqZero h n x) = (-1) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_signEquivOfAddEqZero (isMarkovTrace_markovTrace q' hq') h x

/-- **Invariance of the normalized spin-model Markov trace** under `signEquiv`. -/
theorem inverse_pow_mul_markovTrace_signEquiv (q q' : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hq' : -δ = -((q' : R) + ((q'⁻¹ : Rˣ) : R))) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    Ring.inverse ((-δ) ^ n) * markovTrace q' hq' (signEquiv δ n x) =
      Ring.inverse (δ ^ n) * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).inverse_pow_mul_map_signEquiv
    (isMarkovTrace_markovTrace q' hq') x

end SpinMarkovTrace

end TauCeti.TemperleyLieb
