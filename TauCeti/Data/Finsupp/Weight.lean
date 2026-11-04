/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Option
public import TauCeti.Data.Finsupp.Order

/-!
# Weights of finitely supported functions

If every variable occurring in a monomial `f : σ →₀ ℕ` has weight at most `c`, then the weight
of `f` is at most `degree f • c`. With `c = -1` over `ℤ`, this says that a monomial all of whose
variables have negative weight has weight at most minus its total degree, which is how
negatively graded variables bound the degree of elements of powers of the ideal of the
variables.

The weight of a multiset multiplicity function is the sum of the weights of its entries.

Weights also respect scaling of the weight vector and decompose into contributions before, at,
and after a chosen coordinate in a linear order. These identities support comparisons between
lexicographic order and weighted degree.

On a product `ι × κ` of blocks indexed by `ι`, the weight given by the indicator of block `b`
sums the coefficients in that block. For natural-valued exponents, this is the degree in block `b`.
More generally, for a block map `b : σ → τ`, the indicator weight of the fibre over `h` is the value
at `h` of the pushforward `Finsupp.mapDomain b`.

## Main results

* `Finsupp.weight_toFinsupp`: multiset multiplicities recover the sum of entry weights.
* `Finsupp.prod_pow_eq_pow_degree`: `∏ a ^ tᵢ = a ^ degree t`.
* `Finsupp.degree_optionElim`: extending by `y` at `none` adds `y` to the degree.
* `Finsupp.weight_mapDomain`: pushing forward along `f : α → β` pulls the weight vector back to
  `w ∘ f`.
* `Finsupp.prod_pow_sumElim`, `Finsupp.weight_sumElim`: splitting variables splits the weighted
  product into two factors, and the weight into two summands.
* `Finsupp.prod_pow_optionElim`, `Finsupp.sum_nsmul_optionElim`: extending by `n` at `none`
  splits off the factor `c none ^ n` from the weighted product `∏ c i ^ (f.optionElim n) i`, and
  the summand `n • c none` from the weighted sum.
* `Finsupp.pow_degree_le_pow_degree_optionElim`: `a ^ degree f ≤ b ^ degree (f.optionElim m)`
  for `0 ≤ a ≤ b` and `1 ≤ b`.
* `Finsupp.weight_mono_of_nonneg`, `Finsupp.weight_mono`: nonnegative weights define a monotone
  functional on `σ →₀ ℕ`.
* `Finsupp.weight_le_degree_nsmul`: if `w s ≤ c` for all `s`, then `weight w f ≤ degree f • c`.
* `Finsupp.weight_le_degree_nsmul_of_mem_support`: the same bound, assuming `w s ≤ c` only for
  the variables `s` occurring in `f`.
* `Finsupp.weight_le_degree_nsmul_of_monotone`: for monotone weights `w`, if every variable
  occurring in `f` is at most `i`, then `weight w f ≤ degree f • w i`.
* `Finsupp.weight_filter_lt_add_smul_add_weight_filter_gt`: split a weight at a coordinate.
* `Finsupp.weight_smul_left`: scaling the weight vector scales the weight.
* `Finsupp.weight_comp_eq_apply_linearCombination`: the weight of `u` for the weights `f ∘ w` is
  `f (∑ i, u i • w i)`, for an additive map `f`.
* `Finsupp.weight_ite_fst_eq_sum`: the indicator weight of a block sums its coefficients; for
  natural-valued exponents, this is the degree in that block.
* `Finsupp.weight_ite_eq_mapDomain_apply`: the indicator weight of a fibre of `b : σ → τ` is the
  corresponding value of `Finsupp.mapDomain b`.
* `Finsupp.weight_ite_sumElim_eq_add_mapDomain_apply`: for the block map `Sum.elim id b` on
  `τ ⊕ σ`, the indicator weight of block `h` of `a.sumElim e` is `a h + e.mapDomain b h`.
* `Finsupp.natCast_weight_eq_of_support_subset`: on monomials supported in a finite set `s`, the
  weight `weight w` agrees with any additive functional on `s → ℤ` taking the value `w i` on the
  `i`-th coordinate vector.
* `Finsupp.finite_degree_eq`, `Finsupp.finite_degree_le`: in finitely many variables there are
  finitely many exponent vectors of each degree, and of degree at most `n`.
* `Finsupp.fintypeDegreeEq`: for a fintype of variables with decidable equality, the exponent
  vectors of degree `n` form a fintype, enumerated by `Finset.finsuppAntidiag`.
-/

public section

namespace Finsupp

/-- The weight of the multiplicity function of a multiset is the sum of its entry weights. -/
@[simp]
theorem weight_toFinsupp {σ M : Type*} [DecidableEq σ] [AddCommMonoid M]
    (w : σ → M) (s : Multiset σ) :
    weight w s.toFinsupp = (s.map w).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, map_add, weight_single]
    simpa using congrArg (w i + ·) ih

/-- A product of powers of one fixed element `a`, with exponents given by `t`, is `a` raised to
the degree of `t`. -/
theorem prod_pow_eq_pow_degree {σ M : Type*} [CommMonoid M] (t : σ →₀ ℕ) (a : M) :
    (t.prod fun _ n ↦ a ^ n) = a ^ t.degree := by
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, degree_apply]

/-- Extending `f` to `Option σ` by the value `y` at `none` adds `y` to the degree. -/
@[simp]
theorem degree_optionElim {σ R : Type*} [AddCommMonoid R] (f : σ →₀ R) (y : R) :
    (f.optionElim y).degree = y + f.degree := by
  have h (g : Option σ →₀ R) : g.degree = g.sum fun _ e ↦ e := degree_apply g
  rw [h, sum_option_index _ _ (fun _ ↦ rfl) fun _ _ _ ↦ rfl, optionElim_apply_none,
    some_optionElim, degree_apply, Finsupp.sum]

/-- The weighted product of `f.optionElim n` splits off the factor `c none ^ n`. This is the
form of Mathlib's `Finsupp.prod_option_index` used to separate one variable from the monomial
weights of multivariate series. -/
@[to_additive /-- The weighted sum of `f.optionElim n` splits off the summand `n • c none`. -/]
theorem prod_pow_optionElim {α N : Type*} [CommMonoid N] (c : Option α → N) (n : ℕ)
    (f : α →₀ ℕ) :
    (f.optionElim n).prod (c · ^ ·) = c none ^ n * f.prod (fun i k ↦ c (Option.some i) ^ k) := by
  rw [prod_option_index _ _ (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _,
    optionElim_apply_none, some_optionElim]

/-- The weighted product on a disjoint union of variables is the product of the weights
on each set of variables. -/
theorem prod_pow_sumElim {α β N : Type*} [CommMonoid N] (a : α →₀ ℕ) (b : β →₀ ℕ)
    (c : α → N) (d : β → N) :
    (a.sumElim b).prod (Sum.elim c d · ^ ·) = a.prod (c · ^ ·) * b.prod (d · ^ ·) := by
  simp only [prod_sumElim, Function.comp_def, Sum.elim_inl, Sum.elim_inr]

/-- Pushing forward along `f : α → β` pulls the weight vector back along `f`. -/
theorem weight_mapDomain {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (w : β → M) (f : α → β) (a : α →₀ R) :
    weight w (a.mapDomain f) = weight (w ∘ f) a :=
  linearCombination_mapDomain (v' := w) (f := f) (l := a)

/-- The weight on a disjoint union of variables is the sum of the weights on each part. -/
theorem weight_sumElim {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (w₁ : α → M) (w₂ : β → M) (a : α →₀ R) (b : β →₀ R) :
    weight (Sum.elim w₁ w₂) (a.sumElim b) = weight w₁ a + weight w₂ b := by
  rw [sumElim_eq_add, map_add, weight_mapDomain, weight_mapDomain,
    Sum.elim_comp_inl, Sum.elim_comp_inr]

/-- A weighted product on disjoint variables, multiplied by `x`, can be evaluated with the
inner weight first and the outer weight last. -/
theorem mul_prod_pow_sumElim {α β N : Type*} [CommMonoid N] (x : N)
    (a : α →₀ ℕ) (b : β →₀ ℕ) (c : α → N) (d : β → N) :
    x * (a.sumElim b).prod (Sum.elim c d · ^ ·) =
      x * b.prod (d · ^ ·) * a.prod (c · ^ ·) := by
  rw [prod_pow_sumElim, mul_comm (a.prod (c · ^ ·)) (b.prod (d · ^ ·)), ← mul_assoc]

/-- A power `a ^ degree f` is bounded by the power `b ^ degree (f.optionElim m)` of a larger
base `b ≥ 1`, for any value `m` at `none`. -/
theorem pow_degree_le_pow_degree_optionElim {σ R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 1 ≤ b) (f : σ →₀ ℕ) (m : ℕ) :
    a ^ f.degree ≤ b ^ (f.optionElim m).degree := by
  rw [degree_optionElim, pow_add]
  exact (pow_le_pow_left₀ ha hab _).trans (le_mul_of_one_le_left (pow_nonneg (ha.trans hab) _)
    (one_le_pow₀ hb))

end Finsupp

namespace Finsupp

variable {σ M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]

/-- Nonnegative weights define a monotone functional on `σ →₀ ℕ`. -/
theorem weight_mono_of_nonneg {w : σ → M} (hw : ∀ s, 0 ≤ w s) :
    Monotone (weight w : (σ →₀ ℕ) →+ M) := by
  intro f g hfg
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp hfg
  rw [map_add, weight_apply w d, Finsupp.sum]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun s _ ↦ nsmul_nonneg (hw s) (d s))

/-- If every variable occurring in `f` has weight at most `c`, then the weight of `f` is at most
its degree times `c`. -/
theorem weight_le_degree_nsmul_of_mem_support (f : σ →₀ ℕ) {w : σ → M} {c : M}
    (hw : ∀ s ∈ f.support, w s ≤ c) : weight w f ≤ degree f • c := by
  rw [weight_apply, degree_apply, Finsupp.sum, ← Finset.sum_nsmul_assoc]
  gcongr with s hs
  exact hw s hs

/-- If every variable has weight at most `c`, then the weight of `f` is at most its degree times
`c`. -/
theorem weight_le_degree_nsmul (f : σ →₀ ℕ) {w : σ → M} {c : M} (hw : ∀ s, w s ≤ c) :
    weight w f ≤ degree f • c :=
  weight_le_degree_nsmul_of_mem_support f fun s _ ↦ hw s

/-- If the weights `w` are monotone and every variable occurring in `f` is at most `i`, then the
weight of `f` is at most its degree times `w i`. -/
theorem weight_le_degree_nsmul_of_monotone [Preorder σ] (f : σ →₀ ℕ) {w : σ → M}
    (hw : Monotone w) {i : σ} (hf : ∀ s ∈ f.support, s ≤ i) : weight w f ≤ degree f • w i :=
  weight_le_degree_nsmul_of_mem_support f fun s hs ↦ hw (hf s hs)

end Finsupp

namespace Finsupp

/-- In a canonically ordered additive commutative monoid, every weight functional on `σ →₀ ℕ` is
monotone. -/
theorem weight_mono {σ M : Type*} [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    (w : σ → M) : Monotone (weight w : (σ →₀ ℕ) →+ M) := fun _ _ hfg ↦ by
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp hfg
  rw [map_add]
  exact le_self_add

end Finsupp

namespace Finsupp

variable {σ M : Type*}

/-- The `c`-weight of a finitely supported function `w` splits into the weights before `i`, at
`i`, and after `i`. -/
theorem weight_filter_lt_add_smul_add_weight_filter_gt [LinearOrder σ] {R : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (c : σ → M) (w : σ →₀ R) (i : σ) :
    weight c (w.filter (· < i)) + w i • c i + weight c (w.filter (i < ·)) = weight c w := by
  conv_rhs => rw [← filter_lt_add_single_add_filter_gt w i]
  rw [map_add, map_add, weight_single]

/-- Scaling the weight vector scales the weight. -/
theorem weight_smul_left {R S : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DistribSMul S M] [SMulCommClass R S M] (s : S) (c : σ → M) (w : σ →₀ R) :
    weight (s • c) w = s • weight c w := by
  simp only [weight_apply, smul_sum, Pi.smul_apply]
  exact sum_congr fun _ _ ↦ smul_comm _ s _

/-- The weight of `u` for the weights `f ∘ w` is the image under `f` of `∑ i, u i • w i`. -/
theorem weight_comp_eq_apply_linearCombination {D : Type*} [AddCommMonoid M] [AddCommMonoid D]
    (f : M →+ D) (w : σ → M) (u : σ →₀ ℕ) :
    weight (f ∘ w) u = f (linearCombination ℕ w u) := by
  simp [weight_apply, linearCombination_apply, map_finsuppSum]

end Finsupp

namespace Finsupp

/-- The indicator weight of block `b` of a finitely supported function on `ι × κ` is the sum of
its coefficients in block `b`. -/
theorem weight_ite_fst_eq_sum {ι κ R : Type*} [Fintype κ] [DecidableEq ι] [Semiring R]
    (e : ι × κ →₀ R) (b : ι) :
    weight (fun p : ι × κ ↦ if p.1 = b then (1 : R) else 0) e = ∑ l, e (b, l) := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, Finsupp.add_apply, Finset.sum_add_distrib]
  | single p n =>
    obtain ⟨h, l⟩ := p
    by_cases hb : h = b
    · subst hb
      classical
      simp [Finsupp.weight_single, Finsupp.single_apply]
    · simp [Finsupp.weight_single, hb]

end Finsupp

namespace Finsupp

/-- The indicator weight of the fibre of `b` over `h` is the value at `h` of the pushforward of
`e` along `b`, that is, the sum of the coefficients of `e` at the indices lying over `h`. -/
theorem weight_ite_eq_mapDomain_apply {σ τ R : Type*} [DecidableEq τ] [Semiring R]
    (b : σ → τ) (e : σ →₀ R) (h : τ) :
    weight (fun j ↦ if b j = h then (1 : R) else 0) e = e.mapDomain b h := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, mapDomain_add, Finsupp.add_apply]
  | single j n => by_cases hj : b j = h <;> simp [weight_single, mapDomain_single, hj]

end Finsupp

namespace Finsupp

/-- On `τ ⊕ σ`, with the block map `Sum.elim id b` that puts the coordinate `.inl h` into block
`h`, the indicator weight of block `h` of `a.sumElim e` is `a h + e.mapDomain b h`. -/
theorem weight_ite_sumElim_eq_add_mapDomain_apply {σ τ R : Type*} [DecidableEq τ] [Semiring R]
    (b : σ → τ) (a : τ →₀ R) (e : σ →₀ R) (h : τ) :
    weight (fun v ↦ if Sum.elim id b v = h then (1 : R) else 0) (a.sumElim e) =
      a h + e.mapDomain b h := by
  rw [weight_ite_eq_mapDomain_apply, sumElim_eq_add, mapDomain_add, ← mapDomain_comp,
    ← mapDomain_comp]
  simp

end Finsupp

namespace Finsupp

/-- If an additive functional `μ` on the integer vectors indexed by a finite set `s` takes the
value `w i` on the `i`-th coordinate vector, then `μ` agrees with the weight `weight w` on every
monomial supported in `s`. -/
theorem natCast_weight_eq_of_support_subset {σ : Type*} [DecidableEq σ] {s : Finset σ}
    (μ : (s → ℤ) →+ ℤ) {w : σ → ℕ} (hμ : ∀ i : s, μ (Pi.single i 1) = w i) {a : σ →₀ ℕ}
    (ha : a.support ⊆ s) : (weight w a : ℤ) = μ fun i ↦ (a i : ℤ) := by
  rw [weight_apply, Finsupp.sum_of_support_subset a ha _ (by simp), Nat.cast_sum,
    ← Finset.sum_coe_sort s]
  conv_rhs => rw [← Finset.univ_sum_single fun i : s ↦ (a i : ℤ)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hc : (Pi.single i (a i : ℤ) : s → ℤ) = a i • Pi.single i 1 := by
    rw [← Pi.single_smul', Nat.smul_one_eq_cast]
  rw [hc, map_nsmul, hμ]
  simp

end Finsupp

namespace Finsupp

/-- In finitely many variables there are finitely many exponent vectors of each degree. -/
instance finite_degree_eq {σ : Type*} [Finite σ] (n : ℕ) :
    Finite {s : σ →₀ ℕ // s.degree = n} :=
  (finite_of_degree_eq n).to_subtype

/-- In finitely many variables there are finitely many exponent vectors of degree at most `n`. -/
instance finite_degree_le {σ : Type*} [Finite σ] (n : ℕ) :
    Finite {s : σ →₀ ℕ // s.degree ≤ n} :=
  (finite_of_degree_le n).to_subtype

/-- For a fintype of variables with decidable equality, the exponent vectors of degree `n` form a
fintype, enumerated by `Finset.finsuppAntidiag`. -/
instance fintypeDegreeEq {σ : Type*} [Fintype σ] [DecidableEq σ] (n : ℕ) :
    Fintype {s : σ →₀ ℕ // s.degree = n} :=
  Fintype.ofFinset (p := {s : σ →₀ ℕ | s.degree = n}) ((Finset.univ : Finset σ).finsuppAntidiag n)
    fun s ↦ by simp [Finset.mem_finsuppAntidiag, degree_eq_sum]

end Finsupp
