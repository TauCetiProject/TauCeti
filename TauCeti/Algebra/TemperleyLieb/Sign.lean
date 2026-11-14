/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star

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
(`TauCeti.TemperleyLieb.two_mul_eq_zero_of_algHom_e_two`), since scalar multiples of the
two-strand generator are linearly independent (`TauCeti.TemperleyLieb.smul_left_injective_e_two`).

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

## Main definitions

* `TauCeti.TemperleyLieb.signEquiv δ n`: the algebra isomorphism
  `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` sending `e δ i` to `-e (-δ) i`.
* `TauCeti.TemperleyLieb.signStarAlgEquiv δ n`: `signEquiv` bundled as a star-algebra isomorphism
  `TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n` for self-adjoint `δ` and `-δ`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`: the induced algebra isomorphism between
  the trace-radical quotients at `δ` and `-δ`.

## Main results

* `TauCeti.TemperleyLieb.signEquiv_e`, `TauCeti.TemperleyLieb.signEquiv_symm_e`: action on
  generators.
* `TauCeti.TemperleyLieb.two_mul_eq_zero_of_algHom_e_two`: an algebra map
  `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` fixing the generator forces `2 * δ = 0`.
* `TauCeti.TemperleyLieb.signEquiv_strandIncl`, `TauCeti.TemperleyLieb.aug_signEquiv`,
  `TauCeti.TemperleyLieb.signEquiv_jonesWenzl`, `TauCeti.TemperleyLieb.signEquiv_star`:
  compatibility with strand inclusion, augmentation, Jones–Wenzl projections, and the adjoint.
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

/-- Auxiliary sign-reversing algebra map between fibers whose loop parameters are negatives of one
another, avoiding definitional reliance on `-(-δ) = δ` when constructing the inverse. -/
private def signHomAux {δ δ' : R} (h : δ' = -δ) (n : ℕ) :
    TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ' n :=
  lift (fun i ↦ -e δ' i)
    (fun i ↦ by rw [neg_mul_neg, e_mul_self, h, neg_smul, ← smul_neg])
    (fun hadj ↦ by
      rw [neg_mul_neg, mul_neg, e_mul_e_mul_e hadj])
    (fun hdist ↦ by
      rw [neg_mul_neg, neg_mul_neg, (commute_e hdist).eq])

private theorem signHomAux_e {δ δ' : R} (h : δ' = -δ) {n : ℕ} (i : Fin (n - 1)) :
    signHomAux h n (e δ i) = -e δ' i :=
  lift_e _ _ _ _ i

private theorem signHomAux_comp_signHomAux {δ δ' : R} (h : δ' = -δ) (h' : δ = -δ') (n : ℕ) :
    (signHomAux h' n).comp (signHomAux h n) = AlgHom.id R (TemperleyLieb R δ n) :=
  hom_ext fun i ↦ by simp [signHomAux_e]

/-- The **sign isomorphism** of Temperley–Lieb algebras: negating every generator
`e δ i ↦ -e (-δ) i` identifies the Temperley–Lieb algebra at loop parameter `δ` with that
at `-δ`. -/
def signEquiv (δ : R) (n : ℕ) : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n :=
  AlgEquiv.ofAlgHom (signHomAux rfl n) (signHomAux (neg_neg δ).symm n)
    (signHomAux_comp_signHomAux (neg_neg δ).symm rfl n)
    (signHomAux_comp_signHomAux rfl (neg_neg δ).symm n)

/-- The sign isomorphism sends each generator `e δ i` to `-e (-δ) i`. -/
@[simp]
theorem signEquiv_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ n (e δ i) = -e (-δ) i := by
  rw [signEquiv, AlgEquiv.ofAlgHom_apply, signHomAux_e]

/-- The inverse sign isomorphism sends each generator `e (-δ) i` to `-e δ i`. -/
@[simp]
theorem signEquiv_symm_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    (signEquiv δ n).symm (e (-δ) i) = -e δ i := by
  rw [signEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply, signHomAux_e]

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
two-strand generator forces `2 * δ = 0`. In particular, when `2 * δ ≠ 0`, negating the generators
is necessary to map `TemperleyLieb R δ n` to `TemperleyLieb R (-δ) n`. -/
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
`-δ`, over every commutative ring and with no invertibility assumption on the quantum integers:
the parity signs of `[m + 1]`, `[m + 2]`, and `-e (-δ) (Fin.last m)` cancel in Wenzl's recursion. -/
@[simp]
theorem signEquiv_jonesWenzl (δ : R) :
    ∀ n : ℕ, signEquiv δ n (jonesWenzl δ n) = jonesWenzl (-δ) n
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have hinv1 : Ring.inverse (-1 : R) = -1 := by
      simpa using Ring.inverse_unit (-1 : Rˣ)
    have hinv_pow (k : ℕ) : Ring.inverse ((-1 : R) ^ k) = (-1 : R) ^ k := by
      rw [← Ring.inverse_pow, hinv1]
    have hneg_sq : (-1 : R) ^ m * (-1 : R) ^ m = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have hcoeff :
        qInt R (-δ) (m + 1) * Ring.inverse (qInt R (-δ) (m + 2)) =
          -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
      rw [qInt_neg δ (m + 1), qInt_neg δ (m + 2),
        Ring.inverse_mul (Or.inl (isUnit_one.neg.pow (m + 3))), hinv_pow]
      simp only [pow_succ]
      linear_combination -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) * hneg_sq
    rw [jonesWenzl_add_two, jonesWenzl_add_two, map_sub, map_smul, map_mul, map_mul,
      signEquiv_strandIncl, signEquiv_jonesWenzl δ (m + 1), signEquiv_e, hcoeff]
    simp [neg_smul, smul_neg]

/-- The inverse sign isomorphism sends the Jones–Wenzl projection at `-δ` to that at `δ`. -/
@[simp]
theorem signEquiv_symm_jonesWenzl (δ : R) (n : ℕ) :
    (signEquiv δ n).symm (jonesWenzl (-δ) n) = jonesWenzl δ n :=
  (signEquiv δ n).symm_apply_eq.2 (signEquiv_jonesWenzl δ n).symm

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
    signStarAlgEquiv δ n x = signEquiv δ n x := (rfl)

/-- Applying the inverse of `signStarAlgEquiv` agrees with `(signEquiv δ n).symm`. -/
@[simp]
theorem signStarAlgEquiv_symm_apply {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    (signStarAlgEquiv δ n).symm x = (signEquiv δ n).symm x := (rfl)

/-- The underlying algebra equivalence of `signStarAlgEquiv` is `signEquiv`. -/
@[simp]
theorem toAlgEquiv_signStarAlgEquiv (n : ℕ) :
    (signStarAlgEquiv δ n).toAlgEquiv = signEquiv δ n := (rfl)

end Apply

end Star

namespace IsMarkovTrace

section Trace

variable {R : Type*} [CommRing R] {δ : R}

/-- Pulling back a Markov trace at `-δ` along `signEquiv` and scaling level `n` by `(-1) ^ n`
produces a Markov trace at `δ`. -/
theorem signPullback {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr' : IsMarkovTrace R (-δ) tr') :
    IsMarkovTrace R δ (fun n ↦ (-1 : R) ^ n • (tr' n).comp (signEquiv δ n).toLinearMap) where
  map_one n := by
    rw [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, _root_.map_one,
      htr'.map_one, smul_eq_mul, ← mul_pow, neg_one_mul, neg_neg]
  map_mul_comm n x y := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      htr'.map_mul_comm]
  map_strandIncl n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      signEquiv_strandIncl, htr'.map_strandIncl, smul_eq_mul, pow_succ]
    ring
  map_strandIncl_mul_e_last n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      signEquiv_strandIncl, signEquiv_e, mul_neg, map_neg, htr'.map_strandIncl_mul_e_last,
      smul_eq_mul, pow_succ]
    ring

/-- Pushing forward a Markov trace at `δ` along `(signEquiv δ n).symm` and scaling level `n` by
`(-1) ^ n` produces a Markov trace at `-δ`. -/
theorem signPushforward {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) :
    IsMarkovTrace R (-δ)
      (fun n ↦ (-1 : R) ^ n • (tr n).comp (signEquiv δ n).symm.toLinearMap) where
  map_one n := by
    rw [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, _root_.map_one,
      htr.map_one, smul_eq_mul, ← mul_pow, neg_one_mul]
  map_mul_comm n x y := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      htr.map_mul_comm]
  map_strandIncl n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      signEquiv_symm_strandIncl, htr.map_strandIncl, smul_eq_mul, pow_succ]
    ring
  map_strandIncl_mul_e_last n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      signEquiv_symm_strandIncl, signEquiv_symm_e, mul_neg, map_neg,
      htr.map_strandIncl_mul_e_last, smul_eq_mul, pow_succ]
    ring

/-- **Sign transformation of Markov traces.** For Markov traces `tr` at `δ` and `tr'` at `-δ`,
the sign isomorphism multiplies the trace on `n` strands by `(-1) ^ n`. -/
theorem map_signEquiv {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    tr' n (signEquiv δ n x) = (-1) ^ n * tr n x := by
  have heq := LinearMap.congr_fun (congrFun (htr'.unique htr.signPushforward) n) (signEquiv δ n x)
  simpa using heq

/-- **Sign transformation of Markov traces** along the inverse sign isomorphism. -/
theorem map_signEquiv_symm {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R (-δ) n) :
    tr n ((signEquiv δ n).symm x) = (-1) ^ n * tr' n x := by
  have heq := LinearMap.congr_fun (congrFun (htr.unique htr'.signPullback) n)
    ((signEquiv δ n).symm x)
  simpa using heq

/-- **Invariance of the normalized Markov trace** under the sign isomorphism: scaling the
unnormalized trace on `n` strands by `Ring.inverse (δ ^ n)` cancels the `(-1) ^ n` sign factor,
over every commutative ring. -/
theorem inverse_pow_mul_map_signEquiv {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    Ring.inverse ((-δ) ^ n) * tr' n (signEquiv δ n x) = Ring.inverse (δ ^ n) * tr n x := by
  have hinv1 : Ring.inverse (-1 : R) = -1 := by
    simpa using Ring.inverse_unit (-1 : Rˣ)
  have hinv_neg : Ring.inverse (-δ) = -Ring.inverse δ := by
    rw [← neg_one_mul, Ring.inverse_mul (Or.inl isUnit_one.neg), hinv1, mul_neg_one]
  rw [htr.map_signEquiv htr', ← Ring.inverse_pow, ← Ring.inverse_pow, hinv_neg, ← mul_assoc,
    ← mul_pow]
  ring

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
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, htr.comap_traceRadical_signEquiv htr']
  · intro y hy
    rw [← (signEquiv δ n).apply_symm_apply y]
    exact Ideal.mem_map_of_mem _ ((htr.signEquiv_symm_mem_traceRadical_iff htr' y).2 hy)

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
        Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (signEquiv δ n x) :=
  (rfl)

/-- The inverse of `quotientSignEquiv` acts on quotient classes by applying `(signEquiv δ n).symm`
to representatives. -/
@[simp]
theorem quotientSignEquiv_symm_mk (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    (htr.quotientSignEquiv htr' n).symm
      (Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n))
          ((signEquiv δ n).symm x) :=
  (rfl)

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

end SpinMarkovTrace

end TauCeti.TemperleyLieb
