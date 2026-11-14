/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.LinearCombination
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star

/-!
# Positivity of atomic traces

Let `R` be a commutative star ring and `q : Rˣ` a self-adjoint parameter, so that the type-A
Hecke algebras carry the real-parameter involution fixing every generator `T i`
(`TauCeti.Algebra.TypeAHeckeAlgebra.Star`). Let `ι` be a linearly ordered alphabet of positive
and negative letters, finite for the traces, with weights `p : ι → R`. The atomic trace
`TauCeti.TypeAHeckeAlgebra.atomicTrace pos q p n` is `x ↦ tr (ρ(x) * D)`, where `ρ` is the signed
checked representation on the word space and `D` is the diagonal product density of the weights.

The matrix of the signed checked R-matrix in the word basis is symmetric and its entries are
polynomials in `q`, so for self-adjoint `q` the generators act by self-adjoint matrices. Hence `ρ`
carries the involution to the conjugate transpose in the word basis
(`TauCeti.TypeAHeckeAlgebra.signedChecked_star_single_apply`). Consequently the diagonal
coefficient of `star x * x` at a word `w` is `∑ u, star (ρ(x) w u) * ρ(x) w u`, writing
`ρ(x) w u` for the coefficient of the word `u` in the image of `w`, and

`atomicTrace (star x * x) = ∑ w, (∏ i, p (w i)) * ∑ u, star (ρ(x) w u) * ρ(x) w u`.

Over a commutative star-ordered ring, such as `ℝ`, or `ℂ` with the order `ComplexOrder`, this is
nonnegative as soon as every weight is nonnegative
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg`). No normalization of the weights
and no Markov condition is needed.

When the weights sum to `1` and satisfy the slice condition, the atomic traces are the
restrictions of the Ocneanu trace `tr_z` to the finite stages
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace`). So `tr_z` is then a positive trace on
the whole infinite Hecke algebra: `0 ≤ tr_z (star x * x)` for every `x`
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg_of_atomic`). For the
geometric models on `r + 1` positive letters with weights proportional to `1, Q, …, Q ^ r`,
`Q = q ^ 2`, this shows that the Ocneanu trace with projection parameter `a_(r + 1)(Q)`
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_eigenprojection_geometric`) is positive
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg_geometric`).

## Main results

* `TauCeti.TypeAHeckeAlgebra.signedChecked_star_single_apply`: the signed checked representation
  carries the real-parameter involution to the conjugate transpose in the word basis.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_star`: for self-adjoint weights the atomic trace
  commutes with the involution.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg`: **positivity of atomic traces**
  with nonnegative weights.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg_of_atomic`: an Ocneanu
  trace realized by an atomic model with nonnegative weights is positive.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg_geometric`: the Ocneanu
  traces of the geometric atomic models are positive.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1, for the signed product model.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3,
  for the positive Markov traces with parameters `a_k(Q)`.
-/

public section

open Finsupp

namespace TauCeti

variable {R : Type*} [CommRing R] [StarRing R] {ι : Type*} [LinearOrder ι] {n : ℕ}

namespace TypeAHeckeAlgebra

variable (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) [hq : Fact (IsSelfAdjoint (q : R))]

/-- For self-adjoint `s`, the coefficients of the signed checked R-matrix in the word basis are
self-adjoint. -/
private theorem isSelfAdjoint_signedCheckedR_single_apply {s : R} (hs : IsSelfAdjoint s)
    (j k : Fin n) (w u : Fin n → ι) :
    IsSelfAdjoint (signedCheckedR pos s j k (single w 1) u) := by
  have hQ : IsSelfAdjoint (s ^ 2) := hs.pow 2
  rw [signedCheckedR_apply]
  simp only [Finsupp.single_apply]
  split_ifs <;> simp only [mul_one, mul_zero, sub_zero, zero_sub, neg_zero] <;>
    first
    | exact .zero R
    | exact hQ
    | exact (IsSelfAdjoint.one R).neg
    | exact hQ.sub (.one R)
    | exact hs.neg
    | exact (hQ.sub (.one R)).sub hs

/-- **The signed checked representation is a star representation.** For a self-adjoint parameter,
the coefficient of the word `u` in the image of the word `w` under `star x` is the conjugate of
the coefficient of `w` in the image of `u` under `x`: in the word basis, `star x` acts by the
conjugate transpose of the matrix of `x`. -/
@[simp]
theorem signedChecked_star_single_apply (x : TypeAHeckeAlgebra R q n) (w u : Fin n → ι) :
    signedChecked pos q (star x) (single w 1) u = star (signedChecked pos q x (single u 1) w) := by
  classical
  -- The coefficient of `u` in `f v` is a sum over any finite set of words containing `v.support`.
  have hsum (f : Module.End R ((Fin n → ι) →₀ R)) (v : (Fin n → ι) →₀ R) (u : Fin n → ι)
      {s : Finset (Fin n → ι)} (hs : v.support ⊆ s) :
      f v u = ∑ v' ∈ s, v v' * f (single v' 1) u := by
    conv_lhs => rw [← v.sum_single]
    rw [map_finsuppSum, Finsupp.sum_apply, Finsupp.sum_of_support_subset v hs _ (by simp)]
    refine Finset.sum_congr rfl fun v' _ ↦ ?_
    rw [← smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction generalizing w u with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hinv : IsSelfAdjoint ((q⁻¹ : Rˣ) : R) := by
      simpa only [Ring.inverse_unit] using hq.out.ringInverse
    rw [star_T, signedChecked_T, LinearMap.smul_apply, LinearMap.smul_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, star_mul', hinv.star_eq,
      (isSelfAdjoint_signedCheckedR_single_apply pos hq.out _ _ _ _).star_eq,
      signedCheckedR_single_apply_comm]
  | algebraMap r =>
    rw [← algebraMap_star_comm, AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul, star_mul', Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp_all
  | add y z _ _ hy hz =>
    simp only [star_add, map_add, LinearMap.add_apply, Finsupp.add_apply, hy, hz]
  | mul y z _ _ hy hz =>
    set s := (signedChecked pos q (star y) (single w 1)).support ∪
      (signedChecked pos q z (single u 1)).support
    rw [star_mul, map_mul, mul_apply_eq_comp, map_mul, mul_apply_eq_comp,
      hsum _ _ _ Finset.subset_union_left, hsum _ _ _ (s := s) Finset.subset_union_right,
      star_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [hy, hz, star_mul', mul_comm]

variable (p : ι → R)

/-- The diagonal coefficient of `star x * x` at a word `w` is the sum of the squared moduli of the
coefficients of the image of `w` under `x`. -/
private theorem signedChecked_star_mul_self_single_apply [Fintype ι] (x : TypeAHeckeAlgebra R q n)
    (w : Fin n → ι) :
    signedChecked pos q (star x * x) (single w 1) w =
      ∑ u, star (signedChecked pos q x (single w 1) u) * signedChecked pos q x (single w 1) u := by
  rw [map_mul, mul_apply_eq_comp, ← univ_sum_single (signedChecked pos q x (single w 1)),
    map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [univ_sum_single, ← smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul,
    signedChecked_star_single_apply, mul_comm]

/-- For self-adjoint weights, the atomic trace commutes with the real-parameter involution. -/
theorem atomicTrace_star [Finite ι] (hp : ∀ a, IsSelfAdjoint (p a)) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n (star x) = star (atomicTrace pos q p n x) := by
  have := Fintype.ofFinite ι
  simp only [atomicTrace_eq_sum, signedChecked_star_single_apply, star_sum, star_mul',
    star_prod, (hp _).star_eq]

/-- **Positivity of atomic traces.** Over a commutative star-ordered ring, for a self-adjoint
parameter and nonnegative weights, the atomic trace of `star x * x` is nonnegative. -/
theorem atomicTrace_star_mul_self_nonneg [Finite ι] [PartialOrder R] [StarOrderedRing R]
    (hp : ∀ a, 0 ≤ p a) (x : TypeAHeckeAlgebra R q n) :
    0 ≤ atomicTrace pos q p n (star x * x) := by
  have := Fintype.ofFinite ι
  rw [atomicTrace_eq_sum]
  refine Finset.sum_nonneg fun w _ ↦ mul_nonneg ?_ (Finset.prod_nonneg fun i _ ↦ hp (w i))
  rw [signedChecked_star_mul_self_single_apply]
  exact Finset.sum_nonneg fun u _ ↦ star_mul_self_nonneg _

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

variable [PartialOrder R] [StarOrderedRing R] {q : Rˣ} [hq : Fact (IsSelfAdjoint (q : R))]

/-- If the Ocneanu trace `tr_z` restricts to an atomic trace with nonnegative weights on every
finite presentation, then it is positive. -/
private theorem ocneanuTrace_star_mul_self_nonneg_of_eq_atomicTrace [Finite ι] (pos : ι → Prop)
    [DecidablePred pos] {p : ι → R} (hp₀ : ∀ a, 0 ≤ p a) {z : R}
    (h : ∀ m (y : TypeAHeckeAlgebra R q m), TypeAHeckeAlgebra.atomicTrace pos q p m y =
      ocneanuTrace R q z (TypeAHeckeAlgebra.toInfinite R q m y))
    (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ ocneanuTrace R q z (star x * x) := by
  obtain ⟨m, hm⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite] at hm
  obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).1 hm
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul, ← h]
  exact TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg pos q p hp₀ _

/-- **Positivity of the Ocneanu traces of atomic models.** If the Ocneanu trace `tr_z` is realized
by an atomic model with nonnegative weights, that is, if the weights sum to `1` and the right
slice `(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (c > b), p c` equals `q * z` for
every letter `b`, then `tr_z` is positive for the real-parameter involution. -/
theorem ocneanuTrace_star_mul_self_nonneg_of_atomic [Fintype ι] (pos : ι → Prop) [DecidablePred pos]
    {p : ι → R} (hp₀ : ∀ a, 0 ≤ p a) (hp : ∑ a, p a = 1) {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ c with b < c, p c = q * z) (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ ocneanuTrace R q z (star x * x) :=
  ocneanuTrace_star_mul_self_nonneg_of_eq_atomicTrace pos hp₀
    (fun _ ↦ TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace pos q p hp hz) x

/-- **Positivity of the geometric Ocneanu traces.** Let `Q = q ^ 2` and `c * [r + 1]_Q = 1`. The
Ocneanu trace with parameter `z = c * q ^ (2 * r + 1)`, whose projection parameter is
`a_(r + 1)(Q)` (`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_eigenprojection_geometric`),
is positive for the real-parameter involution. -/
theorem ocneanuTrace_star_mul_self_nonneg_geometric {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ ocneanuTrace R q (c * (q : R) ^ (2 * r + 1)) (star x * x) := by
  have hQ : 0 ≤ (q : R) ^ 2 := by
    simpa only [sq, hq.out.star_eq] using star_mul_self_nonneg (q : R)
  set S := ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a
  have hS : 0 ≤ S := Finset.sum_nonneg fun a _ ↦ pow_nonneg hQ a
  -- The inverse `c` of the nonnegative `S` is self-adjoint, so `c = star c * c * S ≥ 0`.
  have hc₀ : 0 ≤ c := by
    have h := congrArg star hc
    rw [star_mul', star_one, (IsSelfAdjoint.of_nonneg hS).star_eq] at h
    have hstar : star c = c := by linear_combination (-star c) * hc + c * h
    have hc' : c = star c * c * S := by
      rw [hstar]
      linear_combination (-c) * hc
    rw [hc']
    exact mul_nonneg (star_mul_self_nonneg c) hS
  exact ocneanuTrace_star_mul_self_nonneg_of_eq_atomicTrace (fun _ : Fin (r + 1) ↦ True)
    (fun a ↦ mul_nonneg hc₀ (pow_nonneg hQ _))
    (fun _ ↦ TypeAHeckeAlgebra.atomicTrace_geometric_eq q hc) x

end InfiniteTypeAHeckeAlgebra

end TauCeti
