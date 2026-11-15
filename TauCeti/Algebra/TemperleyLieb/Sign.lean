/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.RingTheory.Ideal.Quotient.Star

/-!
# The sign isomorphism on the Temperley–Lieb algebra

Over a commutative ring `R`, negating every Temperley–Lieb generator `e i ↦ -e i` reverses the sign
of the loop parameter:
`(-e i) * (-e i) = e i * e i = δ • e i = (-δ) • (-e i)`,
`(-e i) * (-e j) * (-e i) = -(e i * e j * e i) = -e i` for adjacent `i`, `j`, and distant
generators still commute. By the universal property `TauCeti.TemperleyLieb.lift` in both
directions, this defines an `R`-algebra isomorphism
`TauCeti.TemperleyLieb.signEquiv δ n : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n`.
By contrast, no algebra homomorphism on two strands can send `e δ 0` to `e (-δ) 0` unless
`2 * δ = 0` (`TauCeti.TemperleyLieb.two_mul_eq_zero_of_map_e_two`).

Because `signEquiv` negates `e (Fin.last m)` while `[m + 1] / [m + 2]` also changes sign under
`δ ↦ -δ` (`TauCeti.qInt_neg_left`, `TauCeti.inverse_qInt_neg_left`), `signEquiv` commutes with the
strand inclusion `strandIncl`, preserves the augmentation `aug`, and sends the Jones–Wenzl
element `jonesWenzl δ n` to `jonesWenzl (-δ) n` unconditionally over every commutative ring. Over a
commutative star ring, `signEquiv` intertwines any generator-fixing conjugate-linear star
structures on the two fibers, and in particular the analytic adjoint `instStarRing` when `δ` and
`-δ` are self-adjoint.

On Markov traces, precomposing a Markov trace `tr'` at `-δ` with `signEquiv δ n` and multiplying by
`(-1) ^ n` produces a Markov trace at `δ` (`TauCeti.TemperleyLieb.IsMarkovTrace.signedTrace`):
`(-1) ^ n * (-δ) ^ n = δ ^ n` on `1`, `strandIncl` contributes `(-1) * (-δ) = δ`, and the minus sign
from `signEquiv δ (n + 2) (e δ (Fin.last n)) = -e (-δ) (Fin.last n)` cancels the change in parity
from `(-1) ^ (n + 2)` to `(-1) ^ (n + 1)`. By uniqueness of Markov traces
(`TauCeti.TemperleyLieb.IsMarkovTrace.unique`), every pair of Markov traces `tr` at `δ` and `tr'`
at `-δ` satisfies `tr' n (signEquiv δ n x) = (-1) ^ n * tr n x`, and for the spin-model trace at
`δ = -(q + q⁻¹)` this specializes to
`markovTrace (-q) _ (signEquiv δ n x) = (-1) ^ n * markovTrace q hq x`. Multiplying by
`Ring.inverse ((-δ) ^ n)` absorbs `(-1) ^ n`, so the normalized traces and normalized Hermitian
forms are invariant under `signEquiv`. Consequently `signEquiv` maps the trace radical at `δ` onto
the trace radical at `-δ` and descends to star-compatible algebra isomorphisms
`TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv` on the algebraic Jones quotients,
commuting with `quotientStrandIncl` and scaling `quotientTrace` by `(-1) ^ n`.

## Main definitions

* `TauCeti.TemperleyLieb.signEquiv δ n`: the `R`-algebra isomorphism
  `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` sending `e δ i` to `-e (-δ) i`.
* `TauCeti.TemperleyLieb.signedTrace`, `TauCeti.TemperleyLieb.signedTraceSymm`: signed pullback and
  pushforward of trace families along `signEquiv`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`: the induced `R`-algebra isomorphism
  between the trace-radical quotients at `δ` and `-δ`.

## Main results

* `TauCeti.TemperleyLieb.eq_of_map_e_two`, `TauCeti.TemperleyLieb.two_mul_eq_zero_of_map_e_two`:
  an algebra map on two strands sending the generator to the generator forces equal loop parameters
  (hence `2 * δ = 0` from `δ` to `-δ`).
* `TauCeti.TemperleyLieb.signEquiv_e`, `TauCeti.TemperleyLieb.signEquiv_symm_e`,
  `TauCeti.TemperleyLieb.eq_signEquiv_iff`: generator action and uniqueness of `signEquiv`.
* `TauCeti.TemperleyLieb.signEquiv_strandIncl`, `TauCeti.TemperleyLieb.aug_signEquiv`,
  `TauCeti.TemperleyLieb.signEquiv_crossing`, `TauCeti.TemperleyLieb.signEquiv_jonesWenzl`:
  compatibility with strand inclusion, augmentation, Kauffman crossings, and Jones–Wenzl elements.
* `TauCeti.TemperleyLieb.signEquiv_star_of_star_e`, `TauCeti.TemperleyLieb.signEquiv_star`:
  compatibility with generator-fixing conjugate-linear star structures and `instStarRing`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.signedTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.signedTraceSymm`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquiv`,
  `TauCeti.TemperleyLieb.markovTrace_signEquiv`: the signed Markov-trace relation
  `tr' n (signEquiv δ n x) = (-1) ^ n * tr n x`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_signEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.inv_pow_mul_map_star_mul_self_signEquiv`: invariance of the
  normalized trace and normalized Hermitian form under `signEquiv`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.comap_traceRadical_signEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_quotientSignEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv_star`: preservation of the trace radical
  and induced tower/star isomorphism on the trace-radical quotients.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Facts 4.4.14 (TB6), p. 155.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb

section TwoStrands

/-- On two strands over any commutative semiring, an algebra homomorphism sending the generator to
the generator forces the two loop parameters to agree: applying it to `e * e = δ₁ • e` yields
`δ₁ • e = δ₂ • e`, and scalar multiples of the two-strand generator are read off by
`TauCeti.TemperleyLieb.smul_left_injective_e_two`. -/
theorem eq_of_map_e_two {R : Type*} [CommSemiring R] {δ₁ δ₂ : R}
    (f : TemperleyLieb R δ₁ 2 →ₐ[R] TemperleyLieb R δ₂ 2) (i : Fin (2 - 1))
    (hf : f (e δ₁ i) = e δ₂ i) : δ₁ = δ₂ := by
  apply smul_left_injective_e_two (δ := δ₂) i
  calc
    δ₁ • e δ₂ i = f (δ₁ • e δ₁ i) := by rw [map_smul, hf]
    _ = f (e δ₁ i * e δ₁ i) := by rw [e_mul_self]
    _ = e δ₂ i * e δ₂ i := by rw [map_mul, hf]
    _ = δ₂ • e δ₂ i := e_mul_self i

/-- On two strands over a commutative ring, an algebra homomorphism from loop parameter `δ` to `-δ`
fixing the generator exists only when `2 * δ = 0`. -/
theorem two_mul_eq_zero_of_map_e_two {R : Type*} [CommRing R] {δ : R}
    (f : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2) (i : Fin (2 - 1))
    (hf : f (e δ i) = e (-δ) i) : 2 * δ = 0 := by
  rw [two_mul]
  exact add_eq_zero_iff_eq_neg.mpr (eq_of_map_e_two f i hf)

end TwoStrands

section SignEquiv

variable {R : Type*} [CommRing R]

/-- The forward algebra homomorphism `TemperleyLieb R δ n →ₐ[R] TemperleyLieb R (-δ) n` sending
`e δ i` to `-e (-δ) i`. -/
private def signHom (δ : R) (n : ℕ) : TemperleyLieb R δ n →ₐ[R] TemperleyLieb R (-δ) n :=
  lift (fun i ↦ -e (-δ) i)
    (fun i ↦ by simp [neg_smul, smul_neg])
    (fun h ↦ by simp [e_mul_e_mul_e h])
    (fun h ↦ by simp [(commute_e h).eq])

/-- The inverse algebra homomorphism `TemperleyLieb R (-δ) n →ₐ[R] TemperleyLieb R δ n` sending
`e (-δ) i` to `-e δ i`, defined directly by `lift` without casting along `-(-δ) = δ`. -/
private def signInvHom (δ : R) (n : ℕ) : TemperleyLieb R (-δ) n →ₐ[R] TemperleyLieb R δ n :=
  lift (fun i ↦ -e δ i)
    (fun i ↦ by simp [neg_smul, smul_neg])
    (fun h ↦ by simp [e_mul_e_mul_e h])
    (fun h ↦ by simp [(commute_e h).eq])

/-- **The sign isomorphism** `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n`, sending each
generator `e δ i` to `-e (-δ) i` and having inverse sending `e (-δ) i` to `-e δ i`. -/
def signEquiv (δ : R) (n : ℕ) : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n :=
  AlgEquiv.ofAlgHom (signHom δ n) (signInvHom δ n)
    (hom_ext fun i ↦ by simp [signHom, signInvHom])
    (hom_ext fun i ↦ by simp [signHom, signInvHom])

/-- `signEquiv` negates every Temperley–Lieb generator. -/
@[simp]
theorem signEquiv_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ n (e δ i) = -e (-δ) i := by
  simp [signEquiv, signHom]

/-- The inverse of `signEquiv` also negates every Temperley–Lieb generator. -/
@[simp]
theorem signEquiv_symm_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    (signEquiv δ n).symm (e (-δ) i) = -e δ i := by
  simp [signEquiv, signInvHom]

/-- `signEquiv` is the unique `R`-algebra map sending each `e δ i` to `-e (-δ) i`. -/
theorem eq_signEquiv_of_map_e {δ : R} {n : ℕ}
    {f : TemperleyLieb R δ n →ₐ[R] TemperleyLieb R (-δ) n}
    (hf : ∀ i, f (e δ i) = -e (-δ) i) : f = (signEquiv δ n).toAlgHom :=
  hom_ext fun i ↦ by simp [hf]

/-- Characterization of `signEquiv` among `R`-algebra maps by its action on generators. -/
theorem eq_signEquiv_iff {δ : R} {n : ℕ}
    {f : TemperleyLieb R δ n →ₐ[R] TemperleyLieb R (-δ) n} :
    f = (signEquiv δ n).toAlgHom ↔ ∀ i, f (e δ i) = -e (-δ) i :=
  ⟨fun h i ↦ by simp [h], eq_signEquiv_of_map_e⟩

/-- `signEquiv` commutes with adding a straight last strand. -/
@[simp]
theorem signEquiv_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R δ (n + 1)) :
    signEquiv δ (n + 2) (strandIncl x) = strandIncl (signEquiv δ (n + 1) x) := by
  have h : (signEquiv δ (n + 2)).toAlgHom.comp strandIncl =
      strandIncl.comp (signEquiv δ (n + 1)).toAlgHom :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun h x

/-- The inverse of `signEquiv` commutes with adding a straight last strand. -/
@[simp]
theorem signEquiv_symm_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R (-δ) (n + 1)) :
    (signEquiv δ (n + 2)).symm (strandIncl x) = strandIncl ((signEquiv δ (n + 1)).symm x) := by
  have h : (signEquiv δ (n + 2)).symm.toAlgHom.comp strandIncl =
      strandIncl.comp (signEquiv δ (n + 1)).symm.toAlgHom :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun h x

/-- `signEquiv` preserves the augmentation, since both `e δ i` and `-e (-δ) i` augment to `0`. -/
@[simp]
theorem aug_signEquiv (δ : R) {n : ℕ} (x : TemperleyLieb R δ n) :
    aug (signEquiv δ n x) = aug x := by
  have h : (aug : TemperleyLieb R (-δ) n →ₐ[R] R).comp (signEquiv δ n).toAlgHom = aug :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun h x

/-- The inverse of `signEquiv` preserves the augmentation. -/
@[simp]
theorem aug_signEquiv_symm (δ : R) {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    aug ((signEquiv δ n).symm x) = aug x := by
  have h : (aug : TemperleyLieb R δ n →ₐ[R] R).comp (signEquiv δ n).symm.toAlgHom = aug :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun h x

/-- `signEquiv` negates the cap-cup coefficient of a Kauffman crossing. -/
theorem signEquiv_crossing (δ α β : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ n (crossing δ α β i) = crossing (-δ) α (-β) i := by
  simp [crossing_def, neg_smul]

/-- `(signEquiv δ n).symm` negates the cap-cup coefficient of a Kauffman crossing. -/
theorem signEquiv_symm_crossing (δ α β : R) {n : ℕ} (i : Fin (n - 1)) :
    (signEquiv δ n).symm (crossing (-δ) α β i) = crossing δ α (-β) i := by
  simp [crossing_def, neg_smul]

/-- `signEquiv` sends the Jones–Wenzl element at `δ` to the Jones–Wenzl element at `-δ`, with no
invertibility assumption on the quantum integers: in Wenzl's recursion, the sign from
`signEquiv δ (m + 2) (e δ (Fin.last m)) = -e (-δ) (Fin.last m)` cancels the sign of
`[m + 1] / [m + 2]` under `δ ↦ -δ`. -/
@[simp]
theorem signEquiv_jonesWenzl (δ : R) :
    ∀ n : ℕ, signEquiv δ n (jonesWenzl δ n) = jonesWenzl (-δ) n
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have hcoeff : qInt R (-δ) (m + 1) * Ring.inverse (qInt R (-δ) (m + 2)) =
        -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
      rw [qInt_neg_left, inverse_qInt_neg_left]
      have hpow : (-1 : R) ^ (m + 1 + 1) * (-1 : R) ^ (m + 2 + 1) = -1 := by
        rw [← pow_add, show m + 1 + 1 + (m + 2 + 1) = 2 * (m + 2) + 1 by omega, pow_add, pow_mul]
        simp
      calc
        ((-1 : R) ^ (m + 1 + 1) * qInt R δ (m + 1)) *
            ((-1 : R) ^ (m + 2 + 1) * Ring.inverse (qInt R δ (m + 2))) =
          ((-1 : R) ^ (m + 1 + 1) * (-1 : R) ^ (m + 2 + 1)) *
            (qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by ring
        _ = -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by rw [hpow, neg_one_mul]
    rw [jonesWenzl_add_two, jonesWenzl_add_two, hcoeff]
    simp [signEquiv_jonesWenzl δ (m + 1), neg_smul, smul_neg]

/-- `(signEquiv δ n).symm` sends the Jones–Wenzl element at `-δ` to that at `δ`. -/
@[simp]
theorem signEquiv_symm_jonesWenzl (δ : R) (n : ℕ) :
    (signEquiv δ n).symm (jonesWenzl (-δ) n) = jonesWenzl δ n :=
  (signEquiv δ n).symm_apply_eq.mpr (signEquiv_jonesWenzl δ n).symm

end SignEquiv

section Star

variable {R : Type*} [CommRing R] [StarRing R] {δ : R} {n : ℕ}

/-- `signEquiv` intertwines any conjugate-linear star-ring structures on `TemperleyLieb R δ n` and
`TemperleyLieb R (-δ) n` that fix the generators: `star (-e (-δ) i) = -e (-δ) i`. -/
theorem signEquiv_star_of_star_e
    [StarRing (TemperleyLieb R δ n)] [StarModule R (TemperleyLieb R δ n)]
    [StarRing (TemperleyLieb R (-δ) n)] [StarModule R (TemperleyLieb R (-δ) n)]
    (he₁ : ∀ i : Fin (n - 1), star (e δ i) = e δ i)
    (he₂ : ∀ i : Fin (n - 1), star (e (-δ) i) = e (-δ) i)
    (x : TemperleyLieb R δ n) :
    signEquiv δ n (star x) = star (signEquiv δ n x) := by
  induction x using TemperleyLieb.induction with
  | e i => rw [he₁, signEquiv_e, star_neg, he₂]
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => rw [star_add, map_add, map_add, star_add, hx, hy]
  | mul x y hx hy => rw [star_mul, map_mul, map_mul, star_mul, hx, hy]

/-- `(signEquiv δ n).symm` intertwines any conjugate-linear star-ring structures on
`TemperleyLieb R (-δ) n` and `TemperleyLieb R δ n` that fix the generators. -/
theorem signEquiv_symm_star_of_star_e
    [StarRing (TemperleyLieb R δ n)] [StarModule R (TemperleyLieb R δ n)]
    [StarRing (TemperleyLieb R (-δ) n)] [StarModule R (TemperleyLieb R (-δ) n)]
    (he₁ : ∀ i : Fin (n - 1), star (e δ i) = e δ i)
    (he₂ : ∀ i : Fin (n - 1), star (e (-δ) i) = e (-δ) i)
    (x : TemperleyLieb R (-δ) n) :
    (signEquiv δ n).symm (star x) = star ((signEquiv δ n).symm x) := by
  apply (signEquiv δ n).injective
  rw [AlgEquiv.apply_symm_apply, signEquiv_star_of_star_e he₁ he₂, AlgEquiv.apply_symm_apply]

/-- For self-adjoint `δ` and `-δ`, `signEquiv` preserves the analytic adjoint `instStarRing`. -/
@[simp]
theorem signEquiv_star [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (x : TemperleyLieb R δ n) :
    signEquiv δ n (star x) = star (signEquiv δ n x) :=
  signEquiv_star_of_star_e star_e star_e x

/-- For self-adjoint `δ` and `-δ`, `(signEquiv δ n).symm` preserves the analytic adjoint
`instStarRing`. -/
@[simp]
theorem signEquiv_symm_star [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (x : TemperleyLieb R (-δ) n) :
    (signEquiv δ n).symm (star x) = star ((signEquiv δ n).symm x) :=
  signEquiv_symm_star_of_star_e star_e star_e x

end Star

section Trace

variable {R : Type*} [CommRing R]

/-- The signed pullback of a trace family at `-δ` along `signEquiv`: at `n` strands,
`x ↦ (-1) ^ n * tr' n (signEquiv δ n x)`. -/
def signedTrace (δ : R) (tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R) (n : ℕ) :
    TemperleyLieb R δ n →ₗ[R] R :=
  ((-1 : R) ^ n) • (tr' n ∘ₗ (signEquiv δ n).toLinearMap)

/-- Evaluation of `TauCeti.TemperleyLieb.signedTrace`. -/
@[simp]
theorem signedTrace_apply (δ : R) (tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R) (n : ℕ)
    (x : TemperleyLieb R δ n) :
    signedTrace δ tr' n x = (-1 : R) ^ n * tr' n (signEquiv δ n x) :=
  smul_eq_mul _ _

/-- The signed pushforward of a trace family at `δ` along `(signEquiv δ n).symm`: at `n` strands,
`y ↦ (-1) ^ n * tr n ((signEquiv δ n).symm y)`. -/
def signedTraceSymm (δ : R) (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) (n : ℕ) :
    TemperleyLieb R (-δ) n →ₗ[R] R :=
  ((-1 : R) ^ n) • (tr n ∘ₗ (signEquiv δ n).symm.toLinearMap)

/-- Evaluation of `TauCeti.TemperleyLieb.signedTraceSymm`. -/
@[simp]
theorem signedTraceSymm_apply (δ : R) (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) (n : ℕ)
    (x : TemperleyLieb R (-δ) n) :
    signedTraceSymm δ tr n x = (-1 : R) ^ n * tr n ((signEquiv δ n).symm x) :=
  smul_eq_mul _ _

namespace IsMarkovTrace

variable {δ : R} {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- Pulling a Markov trace at `-δ` back along `signEquiv` with sign `(-1) ^ n` yields a Markov
trace at `δ`. -/
theorem signedTrace (htr' : IsMarkovTrace R (-δ) tr') :
    IsMarkovTrace R δ (TemperleyLieb.signedTrace δ tr') where
  map_one n := by
    rw [signedTrace_apply, _root_.map_one, htr'.map_one, ← mul_pow]
    ring
  map_mul_comm n x y := by
    simp only [signedTrace_apply, _root_.map_mul, htr'.map_mul_comm]
  map_strandIncl n x := by
    rw [signedTrace_apply, signedTrace_apply, signEquiv_strandIncl, htr'.map_strandIncl]
    simp only [pow_succ]
    ring
  map_strandIncl_mul_e_last n x := by
    rw [signedTrace_apply, signedTrace_apply, _root_.map_mul, signEquiv_strandIncl, signEquiv_e,
      mul_neg, map_neg, htr'.map_strandIncl_mul_e_last]
    simp only [pow_succ]
    ring

/-- Pushing a Markov trace at `δ` forward along `(signEquiv δ ·).symm` with sign `(-1) ^ n` yields
a Markov trace at `-δ`. -/
theorem signedTraceSymm (htr : IsMarkovTrace R δ tr) :
    IsMarkovTrace R (-δ) (TemperleyLieb.signedTraceSymm δ tr) where
  map_one n := by
    rw [signedTraceSymm_apply, _root_.map_one, htr.map_one, ← mul_pow]
    ring
  map_mul_comm n x y := by
    simp only [signedTraceSymm_apply, _root_.map_mul, htr.map_mul_comm]
  map_strandIncl n x := by
    rw [signedTraceSymm_apply, signedTraceSymm_apply, signEquiv_symm_strandIncl, htr.map_strandIncl]
    simp only [pow_succ]
    ring
  map_strandIncl_mul_e_last n x := by
    rw [signedTraceSymm_apply, signedTraceSymm_apply, map_mul, signEquiv_symm_strandIncl,
      signEquiv_symm_e, mul_neg, map_neg, htr.map_strandIncl_mul_e_last]
    simp only [pow_succ]
    ring

/-- **The signed Markov-trace relation.** For any Markov traces `tr` at `δ` and `tr'` at `-δ`,
`tr' n (signEquiv δ n x) = (-1) ^ n * tr n x` on `n` strands. -/
theorem map_signEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R δ n) :
    tr' n (signEquiv δ n x) = (-1 : R) ^ n * tr n x := by
  have heq := LinearMap.congr_fun (congrFun (htr'.unique htr.signedTraceSymm) n) (signEquiv δ n x)
  simpa only [signedTraceSymm_apply, AlgEquiv.symm_apply_apply] using heq

/-- Expressing a Markov trace at `δ` in terms of a Markov trace at `-δ` via `signEquiv`. -/
theorem eq_neg_one_pow_mul_map_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ} (x : TemperleyLieb R δ n) :
    tr n x = (-1 : R) ^ n * tr' n (signEquiv δ n x) := by
  have heq := LinearMap.congr_fun (congrFun (htr.unique htr'.signedTrace) n) x
  simpa only [signedTrace_apply] using heq

/-- For any Markov traces `tr` at `δ` and `tr'` at `-δ`,
`tr n ((signEquiv δ n).symm x) = (-1) ^ n * tr' n x` on `n` strands. -/
theorem map_signEquiv_symm (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x : TemperleyLieb R (-δ) n) :
    tr n ((signEquiv δ n).symm x) = (-1 : R) ^ n * tr' n x := by
  have heq := LinearMap.congr_fun (congrFun (htr'.unique htr.signedTraceSymm) n) x
  rw [heq, signedTraceSymm_apply, ← mul_assoc, ← mul_pow]
  simp

/-- On `n` strands, `signEquiv` multiplies the Hermitian sesquilinear Markov-trace form by
`(-1) ^ n`. -/
theorem traceSesqForm_signEquiv [StarRing R] [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ}
    (x y : TemperleyLieb R δ n) :
    (tr' n).traceSesqForm (signEquiv δ n x) (signEquiv δ n y) =
      (-1 : R) ^ n * (tr n).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← signEquiv_star, ← map_mul, htr.map_signEquiv htr']

/-- Normalizing by `Ring.inverse (δ ^ n)` absorbs the sign `(-1) ^ n`, so the normalized Markov
trace is invariant under `signEquiv` over any commutative ring. -/
theorem inverse_pow_mul_map_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ} (x : TemperleyLieb R δ n) :
    Ring.inverse ((-δ) ^ n) * tr' n (signEquiv δ n x) = Ring.inverse (δ ^ n) * tr n x := by
  have hu : IsUnit ((-1 : R) ^ n) := isUnit_one.neg.pow n
  have hinv : Ring.inverse ((-1 : R) ^ n) = (-1 : R) ^ n := by
    simpa only [mul_one] using
      (Ring.inverse_mul_eq_iff_eq_mul ((-1 : R) ^ n) 1 ((-1 : R) ^ n) hu).mpr
        (by rw [← mul_pow]; simp)
  have hpow : (-δ) ^ n = (-1 : R) ^ n * δ ^ n := by
    rw [← mul_pow, neg_one_mul]
  rw [hpow, Ring.inverse_mul (Or.inl hu), hinv, htr.map_signEquiv htr', mul_assoc, ← mul_assoc
    ((-1 : R) ^ n), ← mul_pow]
  simp

/-- Normalizing by `Ring.inverse (δ ^ n)` makes the Hermitian sesquilinear Markov-trace form
invariant under `signEquiv`. -/
theorem inverse_pow_mul_traceSesqForm_signEquiv [StarRing R] [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint (-δ))] (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    {n : ℕ} (x y : TemperleyLieb R δ n) :
    Ring.inverse ((-δ) ^ n) * (tr' n).traceSesqForm (signEquiv δ n x) (signEquiv δ n y) =
      Ring.inverse (δ ^ n) * (tr n).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← signEquiv_star, ← map_mul,
    htr.inverse_pow_mul_map_signEquiv htr']

/-- Over a field, the normalized Markov trace `(δ ^ n)⁻¹ * tr n x` is invariant under
`signEquiv`. -/
theorem inv_pow_mul_map_signEquiv {K : Type*} [Field K] {δ : K}
    {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    {tr' : ∀ n : ℕ, TemperleyLieb K (-δ) n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (htr' : IsMarkovTrace K (-δ) tr') {n : ℕ}
    (x : TemperleyLieb K δ n) :
    ((-δ) ^ n)⁻¹ * tr' n (signEquiv δ n x) = (δ ^ n)⁻¹ * tr n x := by
  simpa only [Ring.inverse_eq_inv'] using htr.inverse_pow_mul_map_signEquiv htr' x

/-- Over a star field with self-adjoint `δ` and `-δ`, the normalized Hermitian form
`(δ ^ n)⁻¹ * tr n (star x * x)` is invariant under `signEquiv`. -/
theorem inv_pow_mul_map_star_mul_self_signEquiv {K : Type*} [Field K] [StarRing K] {δ : K}
    [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    {tr' : ∀ n : ℕ, TemperleyLieb K (-δ) n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (htr' : IsMarkovTrace K (-δ) tr') {n : ℕ}
    (x : TemperleyLieb K δ n) :
    ((-δ) ^ n)⁻¹ * tr' n (star (signEquiv δ n x) * signEquiv δ n x) =
      (δ ^ n)⁻¹ * tr n (star x * x) := by
  simpa only [Ring.inverse_eq_inv', LinearMap.traceSesqForm_apply] using
    htr.inverse_pow_mul_traceSesqForm_signEquiv htr' x x

end IsMarkovTrace

/-- If `q` is a unit parametrizing `δ = -(q + q⁻¹)`, then `-q` parametrizes `-δ = -((-q) + (-q)⁻¹)`.
-/
theorem neg_eq_neg_add_inv_neg {δ : R} {q : Rˣ}
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) :
    -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := by
  rw [hq, inv_neg, Units.val_neg, Units.val_neg]
  ring

/-- For any units `q`, `q'` parametrizing `δ = -(q + q⁻¹)` and `-δ = -(q' + q'⁻¹)`, the spin-model
Markov traces satisfy `markovTrace q' hq' (signEquiv δ n x) = (-1) ^ n * markovTrace q hq x`. -/
theorem markovTrace_signEquiv_of_eq {δ : R} (q q' : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hq' : -δ = -((q' : R) + ((q'⁻¹ : Rˣ) : R))) {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace q' hq' (signEquiv δ n x) = (-1 : R) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_signEquiv (isMarkovTrace_markovTrace q' hq') x

/-- **The signed spin-model trace relation.** For a unit `q` with `δ = -(q + q⁻¹)`,
`markovTrace (-q) hq' (signEquiv δ n x) = (-1) ^ n * markovTrace q hq x` on `n` strands. -/
theorem markovTrace_signEquiv {δ : R} (q : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hq' : -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := neg_eq_neg_add_inv_neg hq) {n : ℕ}
    (x : TemperleyLieb R δ n) :
    markovTrace (-q) hq' (signEquiv δ n x) = (-1 : R) ^ n * markovTrace q hq x :=
  markovTrace_signEquiv_of_eq q (-q) hq hq' x

end Trace

namespace IsMarkovTrace

section Quotient

variable {R : Type*} [CommRing R] {δ : R}
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- `signEquiv` preserves and reflects membership in the trace radical: `(-1) ^ n` is a unit, and
`signEquiv δ n` is surjective. -/
theorem signEquiv_mem_traceRadical_iff (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquiv δ n x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  simp only [LinearMap.mem_traceRadical]
  refine ⟨fun hx y ↦ ?_, fun hx y ↦ ?_⟩
  · have hz := hx (signEquiv δ n y)
    rw [← map_mul, htr.map_signEquiv htr'] at hz
    have hmul := congrArg ((-1 : R) ^ n * ·) hz
    simpa only [mul_zero, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
      using hmul
  · obtain ⟨y, rfl⟩ := (signEquiv δ n).surjective y
    rw [← map_mul, htr.map_signEquiv htr', hx y, mul_zero]

/-- Pulling back the trace radical at `-δ` along `signEquiv` gives the trace radical at `δ`. -/
theorem comap_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.comap (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
      ((tr' n).traceRadical (htr'.map_mul_comm n)) =
        (tr n).traceRadical (htr.map_mul_comm n) := by
  ext x
  exact htr.signEquiv_mem_traceRadical_iff htr' x

/-- Pushing forward the trace radical at `δ` along `signEquiv` gives the trace radical at `-δ`. -/
theorem map_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.map (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
      ((tr n).traceRadical (htr.map_mul_comm n)) =
        (tr' n).traceRadical (htr'.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_signEquiv htr' n]
  exact Ideal.map_comap_of_surjective _ (signEquiv δ n).surjective _

/-- **The sign isomorphism on trace-radical quotients**: `signEquiv` descends to an `R`-algebra
isomorphism between the algebraic Jones quotients at `δ` and `-δ`. -/
def quotientSignEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n) :=
  Ideal.quotientEquivAlg _ _ (signEquiv δ n) (htr.map_traceRadical_signEquiv htr' n).symm

/-- `quotientSignEquiv` acts on quotient classes by applying `signEquiv` to representatives. -/
@[simp]
theorem quotientSignEquiv_mk (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientSignEquiv htr' n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (signEquiv δ n x) :=
  (rfl)

/-- `(quotientSignEquiv _ _ _).symm` acts on quotient classes by applying `(signEquiv δ n).symm` to
representatives. -/
@[simp]
theorem quotientSignEquiv_symm_mk (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    (htr.quotientSignEquiv htr' n).symm
      (Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) ((signEquiv δ n).symm x) :=
  (rfl)

/-- `quotientSignEquiv` commutes with the quotient strand inclusions `quotientStrandIncl`. -/
@[simp]
theorem quotientSignEquiv_quotientStrandIncl (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientSignEquiv htr' (n + 2) (htr.quotientStrandIncl n x) =
      htr'.quotientStrandIncl n (htr.quotientSignEquiv htr' (n + 1) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- `(quotientSignEquiv _ _ _).symm` commutes with `quotientStrandIncl`. -/
@[simp]
theorem quotientSignEquiv_symm_quotientStrandIncl (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R (-δ) (n + 1) ⧸ (tr' (n + 1)).traceRadical (htr'.map_mul_comm (n + 1))) :
    (htr.quotientSignEquiv htr' (n + 2)).symm (htr'.quotientStrandIncl n x) =
      htr.quotientStrandIncl n ((htr.quotientSignEquiv htr' (n + 1)).symm x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- `quotientSignEquiv` scales the induced quotient trace by `(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientSignEquiv htr' n x) =
      (-1 : R) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr.map_signEquiv htr']

/-- `(quotientSignEquiv _ _ _).symm` scales the induced quotient trace by `(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientSignEquiv_symm (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :
    (tr n).quotientTrace (htr.map_mul_comm n) ((htr.quotientSignEquiv htr' n).symm x) =
      (-1 : R) ^ n * (tr' n).quotientTrace (htr'.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr.map_signEquiv_symm htr']

/-- At a self-adjoint loop parameter, the trace radical of any Markov trace is star-stable
(`Ideal.IsStar`), equipping the trace-radical quotient with `Ideal.Quotient.instStarRing`. -/
theorem isStar_traceRadical [StarRing R] [Fact (IsSelfAdjoint δ)] (htr : IsMarkovTrace R δ tr)
    (n : ℕ) : ((tr n).traceRadical (htr.map_mul_comm n)).IsStar where
  star_mem ha := ((tr n).star_mem_traceRadical_iff (htr.map_mul_comm n) (htr.map_star n)).mpr ha

/-- For self-adjoint `δ` and `-δ`, `quotientSignEquiv` preserves the quotient star structure on the
trace-radical quotients. -/
@[simp]
theorem quotientSignEquiv_star [StarRing R] [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientSignEquiv htr' n (star x) = star (htr.quotientSignEquiv htr' n x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- For self-adjoint `δ` and `-δ`, `(quotientSignEquiv _ _ _).symm` preserves the quotient star
structure on the trace-radical quotients. -/
@[simp]
theorem quotientSignEquiv_symm_star [StarRing R] [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint (-δ))] (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :
    (htr.quotientSignEquiv htr' n).symm (star x) =
      star ((htr.quotientSignEquiv htr' n).symm x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

end Quotient

end IsMarkovTrace

end TauCeti.TemperleyLieb
