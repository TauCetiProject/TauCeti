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

Over a commutative ring `R`, negating every generator identifies the Temperley–Lieb algebra at loop
parameter `δ` with the Temperley–Lieb algebra at `δ' = -δ`:

* `(-e_i) * (-e_i) = e_i * e_i = δ' • e_i = (-δ) • e_i = δ • (-e_i)`,
* `(-e_i) * (-e_j) * (-e_i) = -(e_i * e_j * e_i) = -e_i` when `|i - j| = 1`, and
* `(-e_i) * (-e_j) = e_i * e_j = e_j * e_i = (-e_j) * (-e_i)` when `|i - j| ≥ 2`.

This file constructs the resulting `R`-algebra equivalence `TauCeti.TemperleyLieb.equivNeg`. As in
`CliffordAlgebra.equivNeg`, the target loop parameter is taken as a separate parameter `δ'` with a
proof `h : δ' = -δ`: passing `rfl` specializes to `δ' = -δ`, while propositional equalities cover
the inverse direction `δ = -(-δ)` and scalar coercions such as `((-δ : ℝ) : ℂ) = -(δ : ℂ)` without
transport casts. Already on two strands, an algebra map fixing the generator forces equal loop
values (`TauCeti.TemperleyLieb.loop_eq_of_map_e_two`), so when `2 * δ ≠ 0` the sign on the
generators is forced.

The sign isomorphism commutes with strand inclusion, preserves the augmentation, negates the cap
coefficient of Kauffman crossings, and carries the Jones–Wenzl projection at `δ` to the Jones–Wenzl
projection at `δ'` over every commutative ring (`TauCeti.TemperleyLieb.equivNeg_jonesWenzl`): in
Wenzl's recursion, the alternating signs in `qInt R (-δ) k = (-1) ^ (k + 1) * qInt R δ k` negate
the scalar `[m + 1] / [m + 2]` and cancel the sign on the last generator. When `δ` and `δ'` are
self-adjoint, every negated generator remains self-adjoint, so `equivNeg` commutes with the
analytic adjoint and upgrades to `TauCeti.TemperleyLieb.starAlgEquivNeg`.

Pulling back an unnormalized Markov trace at `δ' = -δ` along `equivNeg` and multiplying by
`(-1) ^ n` on `n` strands yields an unnormalized Markov trace at `δ`
(`TauCeti.TemperleyLieb.IsMarkovTrace.comp_equivNeg`): on `1` it gives `(-1) ^ n * (-δ) ^ n =
δ ^ n`, adding a straight strand contributes both `-1` and `δ' = -δ`, and capping with the last
generator contributes both `-1` and the generator sign `-1`. By uniqueness of Markov traces, any
two Markov traces at opposite loop parameters satisfy
`tr' n (equivNeg δ δ' h n x) = (-1) ^ n * tr n x`
(`TauCeti.TemperleyLieb.IsMarkovTrace.map_equivNeg`), while the normalized trace
`Ring.inverse δ ^ n * tr n x` is strictly invariant. Consequently `equivNeg` identifies the trace
radicals and descends to algebra and `⋆`-algebra equivalences between the trace-radical quotients
(`TauCeti.TemperleyLieb.IsMarkovTrace.quotientEquivNeg`,
`TauCeti.TemperleyLieb.IsMarkovTrace.quotientStarAlgEquivNeg`).

## Main definitions

* `TauCeti.TemperleyLieb.equivNeg`: the sign isomorphism
  `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R δ' n` sending `e δ i ↦ -e δ' i` for `δ' = -δ`.
* `TauCeti.TemperleyLieb.starAlgEquivNeg`: the `⋆`-algebra equivalence for self-adjoint `δ`, `δ'`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientEquivNeg`: the induced algebra equivalence between
  trace-radical quotients at opposite loop parameters.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientStarAlgEquivNeg`: the induced `⋆`-algebra
  equivalence between trace-radical quotients at opposite self-adjoint loop parameters.

## Main results

* `TauCeti.TemperleyLieb.loop_eq_of_map_e_two`: a generator-fixing algebra map on two strands
  forces equal loop parameters.
* `TauCeti.TemperleyLieb.equivNeg_strandIncl`, `TauCeti.TemperleyLieb.aug_equivNeg`,
  `TauCeti.TemperleyLieb.equivNeg_jonesWenzl`, `TauCeti.TemperleyLieb.equivNeg_star`: compatibility
  with the tower, augmentation, Jones–Wenzl projections and analytic adjoint.
* `TauCeti.TemperleyLieb.IsMarkovTrace.comp_equivNeg`: signed pullback of a Markov trace along
  `equivNeg` is a Markov trace.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_equivNeg`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_equivNeg`: unnormalized and normalized
  Markov-trace intertwining under `equivNeg`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.comap_traceRadical_equivNeg`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_traceRadical_equivNeg`: correspondence of trace
  radicals under `equivNeg`.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, §4.4 (Facts 4.4.14 (TB6)).
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
-/

public section

namespace TauCeti.TemperleyLieb

section Semiring

variable {R : Type*} [CommSemiring R]

/-- Already on two strands, an algebra map fixing the generator forces equal loop parameters. In
particular, when `2 * δ ≠ 0` there is no generator-fixing algebra map from `TemperleyLieb R δ 2` to
`TemperleyLieb R (-δ) 2`: the sign on the generators in `equivNeg` is forced. -/
theorem loop_eq_of_map_e_two {δ δ' : R} (F : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R δ' 2)
    (i : Fin (2 - 1)) (he : F (e δ i) = e δ' i) : δ = δ' := by
  apply smul_left_injective_e_two (δ := δ') i
  have h := congrArg F (e_mul_self (R := R) (δ := δ) i)
  rw [map_mul, map_smul, he, e_mul_self] at h
  exact h.symm

end Semiring

variable {R : Type*} [CommRing R]

private theorem ringInverse_neg (a : R) : Ring.inverse (-a) = -Ring.inverse a := by
  have h1 : Ring.inverse (-1 : R) = -1 := by
    simpa using (Ring.inverse_mul_eq_iff_eq_mul (-1 : R) 1 (-1) isUnit_one.neg).2 (by ring)
  calc Ring.inverse (-a)
      = Ring.inverse ((-1 : R) * a) := by rw [neg_one_mul]
    _ = Ring.inverse a * Ring.inverse (-1 : R) := Ring.inverse_mul (Or.inl isUnit_one.neg)
    _ = -Ring.inverse a := by rw [h1, mul_neg_one]

private theorem ringInverse_neg_one_pow_mul (a : R) :
    ∀ k : ℕ, Ring.inverse ((-1 : R) ^ k * a) = (-1 : R) ^ k * Ring.inverse a
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ', mul_assoc, neg_one_mul, ringInverse_neg, ringInverse_neg_one_pow_mul a k,
      ← neg_one_mul, ← mul_assoc]

/-- The underlying algebra map of `equivNeg`, sending each generator `e δ i` to `-e δ' i` when
`δ' = -δ`. -/
private def toNeg (δ δ' : R) (h : δ' = -δ) (n : ℕ) :
    TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ' n :=
  lift (fun i ↦ -e δ' i)
    (fun i ↦ by rw [neg_mul_neg, e_mul_self, h, neg_smul, ← smul_neg])
    (fun hadj ↦ by rw [neg_mul_neg, mul_neg, e_mul_e_mul_e hadj])
    (fun hdist ↦ by simp only [neg_mul_neg, (commute_e hdist).eq])

private theorem toNeg_e (δ δ' : R) (h : δ' = -δ) (n : ℕ) (i : Fin (n - 1)) :
    toNeg δ δ' h n (e δ i) = -e δ' i :=
  lift_e _ _ _ _ i

/-- **The sign isomorphism** between the Temperley–Lieb algebras on `n` strands at opposite loop
parameters `δ` and `δ' = -δ`, sending each generator `e δ i` to `-e δ' i`. -/
def equivNeg (δ δ' : R) (h : δ' = -δ) (n : ℕ) :
    TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R δ' n :=
  AlgEquiv.ofAlgHom (toNeg δ δ' h n) (toNeg δ' δ (by rw [h, neg_neg]) n)
    (hom_ext fun i ↦ by simp [toNeg_e])
    (hom_ext fun i ↦ by simp [toNeg_e])

section Basic

variable {δ δ' : R} (h : δ' = -δ) {n : ℕ}

/-- The sign isomorphism negates every generator. -/
@[simp]
theorem equivNeg_e (i : Fin (n - 1)) : equivNeg δ δ' h n (e δ i) = -e δ' i :=
  toNeg_e δ δ' h n i

/-- The inverse of the sign isomorphism also negates every generator. -/
@[simp]
theorem equivNeg_symm_e (i : Fin (n - 1)) : (equivNeg δ δ' h n).symm (e δ' i) = -e δ i :=
  toNeg_e δ' δ _ n i

/-- The inverse of `equivNeg` is `equivNeg` in the opposite direction. -/
theorem equivNeg_symm (n : ℕ) :
    (equivNeg δ δ' h n).symm = equivNeg δ' δ (by rw [h, neg_neg]) n := by
  ext x
  have key : (equivNeg δ δ' h n).symm.toAlgHom = (equivNeg δ' δ (by rw [h, neg_neg]) n).toAlgHom :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun key x

/-- Applying `equivNeg` in opposite directions is the identity equivalence. -/
@[simp]
theorem equivNeg_trans_equivNeg (h' : δ = -δ') (n : ℕ) :
    (equivNeg δ δ' h n).trans (equivNeg δ' δ h' n) = AlgEquiv.refl := by
  rw [← equivNeg_symm h n]
  exact AlgEquiv.self_trans_symm _

/-- Applying `equivNeg` twice in opposite directions returns the original element. -/
@[simp]
theorem equivNeg_equivNeg (h' : δ = -δ') (x : TemperleyLieb R δ n) :
    equivNeg δ' δ h' n (equivNeg δ δ' h n x) = x :=
  AlgEquiv.congr_fun (equivNeg_trans_equivNeg h h' n) x

/-- The sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem equivNeg_strandIncl (x : TemperleyLieb R δ (n + 1)) :
    equivNeg δ δ' h (n + 2) (strandIncl x) = strandIncl (equivNeg δ δ' h (n + 1) x) := by
  have key : (equivNeg δ δ' h (n + 2)).toAlgHom.comp strandIncl =
      strandIncl.comp (equivNeg δ δ' h (n + 1)).toAlgHom :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun key x

/-- The sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_equivNeg (x : TemperleyLieb R δ n) : aug (equivNeg δ δ' h n x) = aug x := by
  have key : (aug : TemperleyLieb R δ' n →ₐ[R] R).comp (equivNeg δ δ' h n).toAlgHom = aug :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun key x

/-- On at most one strand there are no generators, so `equivNeg` is the composite of the scalar
identifications `algEquivOfLeOne`. -/
theorem equivNeg_eq_of_le_one (hn : n ≤ 1) :
    equivNeg δ δ' h n = (algEquivOfLeOne δ hn).trans (algEquivOfLeOne δ' hn).symm := by
  ext x
  apply (algEquivOfLeOne δ' hn).injective
  simp

/-- The sign isomorphism negates the cap coefficient of a Kauffman crossing. -/
theorem equivNeg_crossing (α β : R) (i : Fin (n - 1)) :
    equivNeg δ δ' h n (crossing δ α β i) = crossing δ' α (-β) i := by
  simp

/-- The sign isomorphism carries the Jones–Wenzl projection at `δ` to the Jones–Wenzl projection at
`δ' = -δ`, over every commutative ring and with no invertibility assumption on the quantum integers:
in Wenzl's recursion, the alternating signs of `qInt R (-δ)` negate `[m + 1] / [m + 2]` and cancel
the sign on the last generator. -/
@[simp]
theorem equivNeg_jonesWenzl :
    ∀ n : ℕ, equivNeg δ δ' h n (jonesWenzl δ n) = jonesWenzl δ' n
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have hpow : (-1 : R) ^ (m + 2) * (-1 : R) ^ (m + 3) = -1 := by
      rw [← pow_add, show m + 2 + (m + 3) = 2 * (m + 2) + 1 by omega, pow_add, pow_mul]
      simp
    have hscalar : qInt R δ' (m + 1) * Ring.inverse (qInt R δ' (m + 2)) =
        -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
      rw [h, qInt_neg_left, qInt_neg_left, ringInverse_neg_one_pow_mul]
      calc ((-1 : R) ^ (m + 2) * qInt R δ (m + 1)) *
            ((-1 : R) ^ (m + 3) * Ring.inverse (qInt R δ (m + 2)))
          = ((-1 : R) ^ (m + 2) * (-1 : R) ^ (m + 3)) *
              (qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by ring
        _ = -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by rw [hpow, neg_one_mul]
    rw [jonesWenzl_add_two, jonesWenzl_add_two, map_sub, map_smul, map_mul, map_mul,
      equivNeg_strandIncl h, equivNeg_jonesWenzl (m + 1), equivNeg_e, hscalar, neg_smul,
      mul_neg, neg_mul, smul_neg, sub_neg_eq_add]

end Basic

section Star

variable [StarRing R] {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]

/-- For self-adjoint loop parameters, the sign isomorphism commutes with the analytic adjoint. -/
@[simp]
theorem equivNeg_star (h : δ' = -δ) {n : ℕ} (x : TemperleyLieb R δ n) :
    equivNeg δ δ' h n (star x) = star (equivNeg δ δ' h n x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint, toNeg_e]) x

variable (δ δ') in
/-- **The sign `⋆`-isomorphism** between the Temperley–Lieb star algebras at opposite self-adjoint
loop parameters `δ` and `δ' = -δ`. -/
def starAlgEquivNeg (h : δ' = -δ) (n : ℕ) :
    TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R δ' n :=
  StarAlgEquiv.ofAlgEquiv (equivNeg δ δ' h n) (equivNeg_star h)

/-- Evaluation of `starAlgEquivNeg` reduces to `equivNeg`. -/
@[simp]
theorem starAlgEquivNeg_apply (h : δ' = -δ) {n : ℕ} (x : TemperleyLieb R δ n) :
    starAlgEquivNeg δ δ' h n x = equivNeg δ δ' h n x := (rfl)

/-- Forgetting the star structure on `starAlgEquivNeg` recovers `equivNeg`. -/
@[simp]
theorem toAlgEquiv_starAlgEquivNeg (h : δ' = -δ) (n : ℕ) :
    (starAlgEquivNeg δ δ' h n).toAlgEquiv = equivNeg δ δ' h n := (rfl)

/-- The inverse of `starAlgEquivNeg` is `starAlgEquivNeg` in the opposite direction. -/
theorem starAlgEquivNeg_symm (h : δ' = -δ) (n : ℕ) :
    (starAlgEquivNeg δ δ' h n).symm = starAlgEquivNeg δ' δ (by rw [h, neg_neg]) n :=
  StarAlgEquiv.ext fun x ↦ AlgEquiv.congr_fun (equivNeg_symm h n) x

end Star

namespace IsMarkovTrace

section Trace

variable {δ δ' : R} {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}

/-- Pulling back an unnormalized Markov trace at `δ' = -δ` along `equivNeg` and multiplying by
`(-1) ^ n` on `n` strands gives an unnormalized Markov trace at `δ`. -/
theorem comp_equivNeg (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) :
    IsMarkovTrace R δ (fun n ↦ (-1 : R) ^ n • (tr' n ∘ₗ (equivNeg δ δ' h n).toLinearMap)) where
  map_one n := by
    rw [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      _root_.map_one (equivNeg δ δ' h n), htr'.map_one, smul_eq_mul, h, ← mul_pow, neg_one_mul,
      neg_neg]
  map_mul_comm n x y := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      htr'.map_mul_comm]
  map_strandIncl n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      equivNeg_strandIncl, htr'.map_strandIncl, smul_eq_mul, h, pow_succ]
    ring
  map_strandIncl_mul_e_last n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      equivNeg_strandIncl, equivNeg_e, mul_neg, map_neg, htr'.map_strandIncl_mul_e_last,
      smul_eq_mul, pow_succ]
    ring

/-- **Markov-trace intertwining under the sign isomorphism.** By uniqueness of Markov traces, any
two unnormalized Markov traces at opposite loop parameters satisfy
`tr' n (equivNeg δ δ' h n x) = (-1) ^ n * tr n x`. -/
theorem map_equivNeg (htr' : IsMarkovTrace R δ' tr') (htr : IsMarkovTrace R δ tr) (h : δ' = -δ)
    {n : ℕ} (x : TemperleyLieb R δ n) :
    tr' n (equivNeg δ δ' h n x) = (-1 : R) ^ n * tr n x := by
  have heq := LinearMap.congr_fun (congrFun (htr.unique (htr'.comp_equivNeg h)) n) x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    smul_eq_mul] at heq
  have h1 : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
    rw [← mul_pow]
    simp
  calc tr' n (equivNeg δ δ' h n x)
      = ((-1 : R) ^ n * (-1 : R) ^ n) * tr' n (equivNeg δ δ' h n x) := by rw [h1, one_mul]
    _ = (-1 : R) ^ n * ((-1 : R) ^ n * tr' n (equivNeg δ δ' h n x)) := by ring
    _ = (-1 : R) ^ n * tr n x := by rw [← heq]

/-- The normalized Markov trace `Ring.inverse δ ^ n * tr n x` is strictly invariant under the sign
isomorphism, with no alternating sign and no invertibility hypothesis on `δ`. -/
theorem inverse_pow_mul_map_equivNeg (htr' : IsMarkovTrace R δ' tr') (htr : IsMarkovTrace R δ tr)
    (h : δ' = -δ) {n : ℕ} (x : TemperleyLieb R δ n) :
    Ring.inverse δ' ^ n * tr' n (equivNeg δ δ' h n x) = Ring.inverse δ ^ n * tr n x := by
  rw [htr'.map_equivNeg htr h, h, ringInverse_neg, ← mul_assoc, ← mul_pow, neg_mul_neg, mul_one]

/-- The sign isomorphism pulls back the trace radical at `δ' = -δ` to the trace radical at `δ`. -/
theorem comap_traceRadical_equivNeg (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (n : ℕ) :
    Ideal.comap (equivNeg δ δ' h n : TemperleyLieb R δ n →+* TemperleyLieb R δ' n)
      ((tr' n).traceRadical (htr'.map_mul_comm n)) =
        (tr n).traceRadical (htr.map_mul_comm n) := by
  ext x
  simp only [Ideal.mem_comap, RingHom.coe_coe, LinearMap.mem_traceRadical]
  constructor
  · intro hx y
    have hy := hx (equivNeg δ δ' h n y)
    rw [← map_mul, htr'.map_equivNeg htr h] at hy
    have h1 : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by rw [← mul_pow]; simp
    calc tr n (x * y) = ((-1 : R) ^ n * (-1 : R) ^ n) * tr n (x * y) := by rw [h1, one_mul]
      _ = (-1 : R) ^ n * ((-1 : R) ^ n * tr n (x * y)) := by ring
      _ = 0 := by rw [hy, mul_zero]
  · intro hx y
    rw [← (equivNeg δ δ' h n).apply_symm_apply y, ← map_mul, htr'.map_equivNeg htr h, hx, mul_zero]

/-- An element maps into the trace radical at `δ' = -δ` under `equivNeg` if and only if it lies in
the trace radical at `δ`. -/
theorem equivNeg_mem_traceRadical_iff (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) {n : ℕ} {x : TemperleyLieb R δ n} :
    equivNeg δ δ' h n x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_equivNeg htr' h n, Ideal.mem_comap, RingHom.coe_coe]

/-- The sign isomorphism maps the trace radical at `δ` onto the trace radical at `δ' = -δ`. -/
theorem map_traceRadical_equivNeg (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (n : ℕ) :
    ((tr n).traceRadical (htr.map_mul_comm n)).map
      (equivNeg δ δ' h n : TemperleyLieb R δ n →+* TemperleyLieb R δ' n) =
        (tr' n).traceRadical (htr'.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_equivNeg htr' h n]
  exact Ideal.map_comap_of_surjective _ (equivNeg δ δ' h n).surjective _

/-- **The sign isomorphism on trace-radical quotients.** At opposite loop parameters `δ` and
`δ' = -δ`, `equivNeg` descends to an algebra equivalence between the quotients by the
multiplication-pairing trace radicals. -/
def quotientEquivNeg (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      TemperleyLieb R δ' n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n) :=
  Ideal.quotientEquivAlg _ _ (equivNeg δ δ' h n) (htr.map_traceRadical_equivNeg htr' h n).symm

/-- On representatives, `quotientEquivNeg` acts through `equivNeg`. -/
@[simp]
theorem quotientEquivNeg_mk (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientEquivNeg htr' h n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (equivNeg δ δ' h n x) :=
  Ideal.quotientEquivAlg_mk _ _ _ x

/-- The inverse of `quotientEquivNeg` is `quotientEquivNeg` in the opposite direction. -/
theorem quotientEquivNeg_symm (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (n : ℕ) :
    (htr.quotientEquivNeg htr' h n).symm =
      htr'.quotientEquivNeg htr (by rw [h, neg_neg]) n := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AlgEquiv.symm_apply_eq]
  simp [equivNeg_equivNeg]

/-- The quotient sign isomorphism commutes with the quotient strand-inclusion maps. -/
@[simp]
theorem quotientEquivNeg_quotientStrandIncl (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) (n : ℕ)
    (x : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientEquivNeg htr' h (n + 2) (htr.quotientStrandIncl n x) =
      htr'.quotientStrandIncl n (htr.quotientEquivNeg htr' h (n + 1) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- The unnormalized quotient trace transforms by `(-1) ^ n` along `quotientEquivNeg`. -/
@[simp]
theorem quotientTrace_quotientEquivNeg (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientEquivNeg htr' h n x) =
      (-1 : R) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr'.map_equivNeg htr h]

/-- The normalized quotient trace is strictly invariant under `quotientEquivNeg`. -/
theorem inverse_pow_mul_quotientTrace_quotientEquivNeg (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    Ring.inverse δ' ^ n *
      (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientEquivNeg htr' h n x) =
        Ring.inverse δ ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa using htr'.inverse_pow_mul_map_equivNeg htr h x

end Trace

section StarTrace

variable [StarRing R] {δ δ' : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}

/-- On `n` strands, `equivNeg` multiplies the Hermitian sesquilinear form of a Markov trace by
`(-1) ^ n`. -/
theorem traceSesqForm_equivNeg (htr' : IsMarkovTrace R δ' tr') (htr : IsMarkovTrace R δ tr)
    (h : δ' = -δ) {n : ℕ} (x y : TemperleyLieb R δ n) :
    (tr' n).traceSesqForm (equivNeg δ δ' h n x) (equivNeg δ δ' h n y) =
      (-1 : R) ^ n * (tr n).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← equivNeg_star, ← map_mul, htr'.map_equivNeg htr h]

/-- The quotient sign isomorphism commutes with the quotient star involution. -/
@[simp]
theorem quotientEquivNeg_star (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientEquivNeg htr' h n (star x) = star (htr.quotientEquivNeg htr' h n x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- **The sign `⋆`-isomorphism on trace-radical quotients.** At opposite self-adjoint loop
parameters, `equivNeg` descends to a `⋆`-algebra equivalence between the trace-radical quotients;
the required `Ideal.IsStar` instances are supplied by `IsMarkovTrace.isStar_traceRadical`. -/
def quotientStarAlgEquivNeg (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃⋆ₐ[R]
      TemperleyLieb R δ' n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n) :=
  StarAlgEquiv.ofAlgEquiv (htr.quotientEquivNeg htr' h n) (htr.quotientEquivNeg_star htr' h n)

/-- Evaluation of `quotientStarAlgEquivNeg` reduces to `quotientEquivNeg`. -/
@[simp]
theorem quotientStarAlgEquivNeg_apply (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientStarAlgEquivNeg htr' h n x = htr.quotientEquivNeg htr' h n x := (rfl)

/-- Forgetting the star structure on `quotientStarAlgEquivNeg` recovers `quotientEquivNeg`. -/
@[simp]
theorem toAlgEquiv_quotientStarAlgEquivNeg (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (htr.quotientStarAlgEquivNeg htr' h n).toAlgEquiv = htr.quotientEquivNeg htr' h n := (rfl)

/-- The inverse of `quotientStarAlgEquivNeg` is `quotientStarAlgEquivNeg` in the opposite
direction. -/
theorem quotientStarAlgEquivNeg_symm (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (htr.quotientStarAlgEquivNeg htr' h n).symm =
      htr'.quotientStarAlgEquivNeg htr (by rw [h, neg_neg]) n :=
  StarAlgEquiv.ext fun x ↦ AlgEquiv.congr_fun (htr.quotientEquivNeg_symm htr' h n) x

end StarTrace

end IsMarkovTrace

/-- For the spin-model Markov traces at opposite loop parameters `δ = -(q + q⁻¹)` and
`δ' = -(q' + q'⁻¹)` with `δ' = -δ` (in particular `q' = -q`), `equivNeg` multiplies the trace on
`n` strands by `(-1) ^ n`. -/
theorem markovTrace_equivNeg {δ δ' : R} (q q' : Rˣ)
    (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) (hδ' : δ' = -((q' : R) + ((q'⁻¹ : Rˣ) : R)))
    (h : δ' = -δ) {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace q' hδ' (equivNeg δ δ' h n x) = (-1 : R) ^ n * markovTrace q hδ x :=
  (isMarkovTrace_markovTrace q' hδ').map_equivNeg (isMarkovTrace_markovTrace q hδ) h x

end TauCeti.TemperleyLieb
