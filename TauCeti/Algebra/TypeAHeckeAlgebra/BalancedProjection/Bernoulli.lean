/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Zero
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The Bernoulli Markov trace at `τ = 0`

At `τ = 0` the balanced relation `e i * e (i + 1) * e i = e (i + 1) * e i * e (i + 1)` holds for
any two commuting idempotents. So every sequence of idempotents in a commutative algebra defines a
representation of `TauCeti.BalancedProjectionAlgebra R 0`
(`TauCeti.BalancedProjectionAlgebra.liftComm`). In particular each subset `s ⊆ ℕ`, that is each
point of `{0, 1} ^ ℕ`, gives a character sending `e i` to `1` for `i ∈ s` and to `0` otherwise
(`TauCeti.BalancedProjectionAlgebra.indicatorCharacter`).

For every `η : R` this file constructs the Bernoulli Markov trace
`TauCeti.BalancedProjectionAlgebra.bernoulliTrace η`: a normalized tracial `R`-linear functional
which multiplies by `η` when a new last projection `e n` is appended to an element of the stage of
the first `n + 1` strands. It is the expectation for the Bernoulli product measure of parameter
`η` on `{0, 1} ^ ℕ`: on the stage of the first `N + 1` strands it is the average of the indicator
characters at the subsets `s` of `{0, …, N - 1}` with weights `η ^ |s| * (1 - η) ^ (N - |s|)`
(`TauCeti.BalancedProjectionAlgebra.bernoulliTrace_eq_sum`). For real `0 ≤ η ≤ 1` these weights
are those of the Bernoulli product distribution.

The algebraic presentation at `τ = 0` is not commutative, but its representations by projections
in a ring with a proper star, such as a C⋆-algebra, have commutative image
(`TauCeti.BalancedProjectionAlgebra.commute_map_of_zero`). Among functionals which do not see the
order of two adjacent generators the Markov property determines the trace: the value on a product
of generators is `η` to the number of distinct generators occurring in it
(`TauCeti.BalancedProjectionAlgebra.eq_bernoulliTrace`). Consequently a normalized Markov
functional through a representation with commuting generators, in particular through a
representation by projections, is the Bernoulli trace
(`TauCeti.BalancedProjectionAlgebra.comp_eq_bernoulliTrace`,
`TauCeti.BalancedProjectionAlgebra.comp_eq_bernoulliTrace_of_isStarProjection`). The two scalar
characters are the Bernoulli traces with `η = 1` and `η = 0`.

The construction passes through the commutative algebra `MvPolynomial ℕ R` modulo the relations
`X i * X i = X i`, on which the trace is the linear functional sending a monomial to `η` to the
number of variables occurring in it.

## Main definitions

* `TauCeti.BalancedProjectionAlgebra.liftComm`: the representation defined by a sequence of
  idempotents in a commutative algebra.
* `TauCeti.BalancedProjectionAlgebra.indicatorCharacter`: the character at a subset of `ℕ`.
* `TauCeti.BalancedProjectionAlgebra.bernoulliTrace`: the Bernoulli Markov trace.

## Main results

* `TauCeti.BalancedProjectionAlgebra.bernoulliTrace_one`,
  `TauCeti.BalancedProjectionAlgebra.bernoulliTrace_mul_comm` and
  `TauCeti.BalancedProjectionAlgebra.bernoulliTrace_mul_e`: the Bernoulli trace is a normalized
  Markov trace.
* `TauCeti.BalancedProjectionAlgebra.bernoulliTrace_eq_sum`: the Bernoulli product expansion.
* `TauCeti.BalancedProjectionAlgebra.eq_bernoulliTrace`: uniqueness among functionals insensitive
  to the order of adjacent generators.
* `TauCeti.BalancedProjectionAlgebra.comp_eq_bernoulliTrace_of_isStarProjection`: uniqueness of
  the Markov functionals through representations by projections.

## References

* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett and A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246, for the C⋆-algebraic
  approach to the projection presentation and its Markov states.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, for
  the projection generators of the Hecke algebra.
-/

public section

open MvPolynomial

namespace TauCeti

namespace BalancedProjectionAlgebra

variable {R : Type*} [CommRing R]

/-! ### Representations in commutative algebras -/

section LiftComm

variable {A : Type*} [CommRing A] [Algebra R A]

/-- At `τ = 0`, a sequence of idempotents in a commutative algebra defines a representation of the
balanced projection algebra: for commuting idempotents both sides of the balanced relation are
`e i * e (i + 1)`. -/
def liftComm (f : ℕ → A) (hf : ∀ i, IsIdempotentElem (f i)) :
    BalancedProjectionAlgebra R (0 : R) →ₐ[R] A :=
  lift f hf (fun i ↦ by
    simp only [zero_smul, sub_zero]
    linear_combination f (i + 1) * (hf i).eq - f i * (hf (i + 1)).eq) fun _ ↦ mul_comm _ _

/-- The representation `TauCeti.BalancedProjectionAlgebra.liftComm f` sends `e i` to `f i`. -/
@[simp]
theorem liftComm_e (f : ℕ → A) (hf : ∀ i, IsIdempotentElem (f i)) (i : ℕ) :
    liftComm (R := R) f hf (e 0 i) = f i :=
  lift_e (τ := (0 : R)) _ _ _ _ i

end LiftComm

/-! ### Indicator characters -/

section IndicatorCharacter

/-- The character of `TauCeti.BalancedProjectionAlgebra R 0` at a subset `s ⊆ ℕ`, that is at a
point of `{0, 1} ^ ℕ`: it sends `e i` to `1` for `i ∈ s` and to `0` otherwise. -/
noncomputable def indicatorCharacter (s : Set ℕ) : BalancedProjectionAlgebra R (0 : R) →ₐ[R] R :=
  liftComm (s.indicator 1) fun i ↦ by
    by_cases hi : i ∈ s <;> simp [IsIdempotentElem, hi]

/-- The indicator character at `s` sends `e i` to `1` for `i ∈ s` and to `0` otherwise. -/
@[simp]
theorem indicatorCharacter_e (s : Set ℕ) (i : ℕ) :
    indicatorCharacter (R := R) s (e 0 i) = s.indicator 1 i :=
  liftComm_e _ _ i

end IndicatorCharacter

/-! ### The Boolean polynomial algebra -/

section Boolean

variable (R) in
/-- The ideal of `MvPolynomial ℕ R` generated by the relations `X i * X i = X i`. -/
private noncomputable def boolIdeal : Ideal (MvPolynomial ℕ R) :=
  Ideal.span (Set.range fun i ↦ X i * X i - X i)

variable (R) in
/-- The representation of `TauCeti.BalancedProjectionAlgebra R 0` on the polynomials in
idempotent variables, the universal commutative one. -/
private noncomputable def toBool :
    BalancedProjectionAlgebra R (0 : R) →ₐ[R] MvPolynomial ℕ R ⧸ boolIdeal R :=
  liftComm (fun i ↦ Ideal.Quotient.mk _ (X i)) fun i ↦ by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨i, rfl⟩

private theorem toBool_e (i : ℕ) :
    toBool R (e 0 i) = Ideal.Quotient.mkₐ R (boolIdeal R) (X i) :=
  liftComm_e _ _ i

/-- An element of the stage of the first `n + 1` strands is represented by a polynomial in the
variables `X i`, `i < n`. -/
private theorem exists_toBool_eq {n : ℕ} {w : BalancedProjectionAlgebra R (0 : R)}
    (hw : w ∈ stage R 0 (n + 1)) :
    ∃ p ∈ supported R (Set.Iio n), Ideal.Quotient.mkₐ R (boolIdeal R) p = toBool R w := by
  have h : stage R 0 (n + 1) ≤
      ((supported R (Set.Iio n)).map (Ideal.Quotient.mkₐ R (boolIdeal R))).comap (toBool R) :=
    stage_le_iff.2 fun i hi ↦
      ⟨X i, Algebra.subset_adjoin ⟨i, by simpa using hi, rfl⟩, (toBool_e i).symm⟩
  exact h hw

/-- The Bernoulli expectation of a polynomial in idempotent variables: the linear functional
sending a monomial to `η` to the number of variables occurring in it. -/
private noncomputable def boolExpect (η : R) : MvPolynomial ℕ R →ₗ[R] R :=
  (basisMonomials ℕ R).constr R fun m ↦ η ^ m.support.card

private theorem boolExpect_monomial (η : R) (m : ℕ →₀ ℕ) (c : R) :
    boolExpect η (monomial m c) = c * η ^ m.support.card := by
  have h := (basisMonomials ℕ R).constr_basis R (fun m : ℕ →₀ ℕ ↦ η ^ m.support.card) m
  rw [coe_basisMonomials] at h
  rw [show monomial m c = c • monomial m 1 by rw [smul_monomial, smul_eq_mul, mul_one], map_smul,
    boolExpect, h, smul_eq_mul]

private theorem boolExpect_one (η : R) : boolExpect η 1 = 1 := by
  simpa using boolExpect_monomial η 0 1

/-- Two linear functionals on polynomials agree on the polynomials in the variables `X i`,
`i < n`, once they agree on the monomials in these variables. -/
private theorem eq_of_mem_supported {f g : MvPolynomial ℕ R →ₗ[R] R} {n : ℕ}
    (h : ∀ m : ℕ →₀ ℕ, (∀ i ∈ m.support, i < n) → f (monomial m 1) = g (monomial m 1))
    {p : MvPolynomial ℕ R} (hp : p ∈ supported R (Set.Iio n)) : f p = g p := by
  rw [mem_supported] at hp
  rw [p.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' : ∀ i ∈ m.support, i < n := fun i hi ↦ hp (support_subset_vars_of_mem_support hm hi)
  rw [← mul_one (p.coeff m), ← smul_eq_mul, ← smul_monomial, map_smul, map_smul, h m hm']

private theorem boolExpect_mul_X_mul_X (η : R) (p : MvPolynomial ℕ R) (i : ℕ) :
    boolExpect η (p * (X i * X i)) = boolExpect η (p * X i) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    simp [X, monomial_mul_monomial, boolExpect_monomial, ← Finsupp.single_add,
      Finsupp.support_add_eq_union]
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]

/-- The Bernoulli expectation vanishes on the ideal of the relations `X i * X i = X i`. -/
private theorem boolExpect_eq_zero (η : R) {x : MvPolynomial ℕ R} (hx : x ∈ boolIdeal R) :
    boolExpect η x = 0 := by
  suffices ∀ a, boolExpect η (a * x) = 0 by simpa using this 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro a
    rw [mul_sub, map_sub, boolExpect_mul_X_mul_X, sub_self]
  | zero => simp
  | add x y _ _ hx hy => intro a; rw [mul_add, map_add, hx, hy, add_zero]
  | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc, hx]

/-- The Bernoulli expectation on the quotient by the relations `X i * X i = X i`. -/
private noncomputable def boolTrace (η : R) : (MvPolynomial ℕ R ⧸ boolIdeal R) →ₗ[R] R :=
  ((boolIdeal R).restrictScalars R).liftQ (boolExpect η) (fun _ hx ↦ boolExpect_eq_zero η hx) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (boolIdeal R)).symm.toLinearMap

private theorem boolTrace_mk (η : R) (p : MvPolynomial ℕ R) :
    boolTrace η (Ideal.Quotient.mkₐ R (boolIdeal R) p) = boolExpect η p := by
  simp only [boolTrace, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Ideal.Quotient.mkₐ_eq_mk]
  exact congr_arg _ (Submodule.Quotient.restrictScalarsEquiv_symm_mk _ _ p)

/-- Appending a new last variable multiplies the Bernoulli expectation by `η`. -/
private theorem boolExpect_mul_X {η : R} {n : ℕ} {p : MvPolynomial ℕ R}
    (hp : p ∈ supported R (Set.Iio n)) : boolExpect η (p * X n) = η * boolExpect η p := by
  refine eq_of_mem_supported (f := boolExpect η ∘ₗ LinearMap.mulRight R (X n))
    (g := η • boolExpect η) (fun m hm ↦ ?_) hp
  have hn : n ∉ m.support := fun h ↦ (hm n h).false
  simp [X, monomial_mul_monomial, boolExpect_monomial, Finsupp.support_add_eq_union,
    Finset.union_singleton, hn, pow_succ']

end Boolean

/-! ### The Bernoulli trace -/

section Trace

variable (η : R)

/-- The Bernoulli Markov trace with parameter `η` on the balanced projection algebra at `τ = 0`:
the normalized tracial functional which multiplies by `η` when a new last projection is appended
(`TauCeti.BalancedProjectionAlgebra.bernoulliTrace_mul_e`). On the stage of the first `N + 1`
strands it averages the indicator characters with the Bernoulli product weights
(`TauCeti.BalancedProjectionAlgebra.bernoulliTrace_eq_sum`). -/
noncomputable def bernoulliTrace : BalancedProjectionAlgebra R (0 : R) →ₗ[R] R :=
  boolTrace η ∘ₗ (toBool R).toLinearMap

private theorem bernoulliTrace_apply (x : BalancedProjectionAlgebra R (0 : R)) :
    bernoulliTrace η x = boolTrace η (toBool R x) :=
  rfl

/-- The Bernoulli trace is normalized. -/
@[simp]
theorem bernoulliTrace_one : bernoulliTrace η 1 = 1 := by
  rw [bernoulliTrace_apply, map_one, ← map_one (Ideal.Quotient.mkₐ R (boolIdeal R)), boolTrace_mk,
    boolExpect_one]

/-- The Bernoulli trace is tracial. -/
theorem bernoulliTrace_mul_comm (x y : BalancedProjectionAlgebra R (0 : R)) :
    bernoulliTrace η (x * y) = bernoulliTrace η (y * x) := by
  rw [bernoulliTrace_apply, bernoulliTrace_apply, map_mul (toBool R), map_mul (toBool R), mul_comm]

/-- **The Markov property.** Appending the projection `e n` to an element of the stage of the
first `n + 1` strands multiplies the Bernoulli trace by `η`. -/
theorem bernoulliTrace_mul_e {n : ℕ} {w : BalancedProjectionAlgebra R (0 : R)}
    (hw : w ∈ stage R 0 (n + 1)) : bernoulliTrace η (w * e 0 n) = η * bernoulliTrace η w := by
  obtain ⟨p, hp, hpw⟩ := exists_toBool_eq hw
  rw [bernoulliTrace_apply, bernoulliTrace_apply, map_mul, toBool_e, ← hpw, ← map_mul,
    boolTrace_mk, boolTrace_mk, boolExpect_mul_X hp]

/-- The Bernoulli trace takes the value `η` on every generator. -/
@[simp]
theorem bernoulliTrace_e (n : ℕ) : bernoulliTrace η (e 0 n) = η := by
  simpa using bernoulliTrace_mul_e η (one_mem (stage R 0 (n + 1)))

/-- The indicator characters factor through the polynomials in idempotent variables. -/
private theorem indicatorCharacter_apply_of_eq (s : Set ℕ) {x : BalancedProjectionAlgebra R (0 : R)}
    {p : MvPolynomial ℕ R} (h : Ideal.Quotient.mkₐ R (boolIdeal R) p = toBool R x) :
    indicatorCharacter s x = eval (s.indicator 1) p := by
  have hI (a : MvPolynomial ℕ R) (ha : a ∈ boolIdeal R) : aeval (s.indicator (1 : ℕ → R)) a = 0 :=
    RingHom.mem_ker.1 <| (Ideal.span_le (I := RingHom.ker (aeval (s.indicator (1 : ℕ → R))))).2
      (by
        rintro _ ⟨i, rfl⟩
        by_cases hi : i ∈ s <;> simp [hi]) ha
  have key : indicatorCharacter (R := R) s =
      (Ideal.Quotient.liftₐ (boolIdeal R) _ hI).comp (toBool R) := by
    ext i
    simp [toBool_e]
  rw [key, AlgHom.comp_apply, ← h, ← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp]
  exact congr_fun (aeval_eq_eval _) p

/-- The Bernoulli expansion of the expectation of a monomial in the variables indexed by `s`. -/
private theorem boolExpect_monomial_eq_sum (s : Finset ℕ) {m : ℕ →₀ ℕ} (hm : m.support ⊆ s) :
    boolExpect η (monomial m 1) = ∑ t ∈ s.powerset,
      η ^ t.card * (1 - η) ^ (s.card - t.card) * eval ((t : Set ℕ).indicator 1) (monomial m 1) := by
  classical
  -- Both sides are the expansion of `∏ i ∈ s, (η + g i)`, where `g i = 0` on the support of `m`
  -- and `g i = 1 - η` elsewhere.
  set g : ℕ → R := fun i ↦ if m i = 0 then 1 - η else 0
  have hprod : ∏ i ∈ s, (η + g i) = η ^ m.support.card := by
    rw [← Finset.prod_sdiff hm, Finset.prod_eq_one fun i hi ↦ ?_, one_mul, ← Finset.prod_const]
    · exact Finset.prod_congr rfl fun i hi ↦ by simp [g, Finsupp.mem_support_iff.1 hi]
    · simp [g, Finsupp.notMem_support_iff.1 (Finset.mem_sdiff.1 hi).2]
  rw [boolExpect_monomial, one_mul, ← hprod, Finset.prod_add]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have hts : t ⊆ s := Finset.mem_powerset.1 ht
  rw [eval_monomial, one_mul, Finset.prod_const, Finsupp.prod]
  by_cases hmt : m.support ⊆ t
  · have hg : ∏ i ∈ s \ t, g i = (1 - η) ^ (s.card - t.card) := by
      rw [← Finset.card_sdiff_of_subset hts, ← Finset.prod_const]
      exact Finset.prod_congr rfl fun i hi ↦ by
        simp [g, Finsupp.notMem_support_iff.1 fun h ↦ (Finset.mem_sdiff.1 hi).2 (hmt h)]
    have hind : ∏ i ∈ m.support, (t : Set ℕ).indicator (1 : ℕ → R) i ^ m i = 1 :=
      Finset.prod_eq_one fun i hi ↦ by simp [hmt hi]
    rw [hg, hind, mul_one]
  · obtain ⟨i, hi, hit⟩ := Finset.not_subset.1 hmt
    have hg : ∏ i ∈ s \ t, g i = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨hm hi, hit⟩) <| by
        simp [g, Finsupp.mem_support_iff.1 hi]
    have hind : ∏ i ∈ m.support, (t : Set ℕ).indicator (1 : ℕ → R) i ^ m i = 0 :=
      Finset.prod_eq_zero hi (by simp [hit, Finsupp.mem_support_iff.1 hi])
    rw [hg, hind, mul_zero, mul_zero]

/-- **The Bernoulli product expansion.** On the stage of the first `N + 1` strands, the Bernoulli
trace is the average of the indicator characters at the subsets `s` of `{0, …, N - 1}` with the
weights `η ^ |s| * (1 - η) ^ (N - |s|)`. -/
theorem bernoulliTrace_eq_sum {N : ℕ} {x : BalancedProjectionAlgebra R (0 : R)}
    (hx : x ∈ stage R 0 (N + 1)) :
    bernoulliTrace η x = ∑ s ∈ (Finset.range N).powerset,
      η ^ s.card * (1 - η) ^ (N - s.card) * indicatorCharacter (s : Set ℕ) x := by
  obtain ⟨p, hp, hpx⟩ := exists_toBool_eq hx
  rw [bernoulliTrace_apply, ← hpx, boolTrace_mk]
  simp only [indicatorCharacter_apply_of_eq _ hpx]
  refine (eq_of_mem_supported (f := boolExpect η) (g := ∑ s ∈ (Finset.range N).powerset,
    (η ^ s.card * (1 - η) ^ (N - s.card)) • (aeval ((s : Set ℕ).indicator (1 : ℕ → R))).toLinearMap)
    (fun m hm ↦ ?_) hp).trans ?_
  · simpa [LinearMap.sum_apply] using
      boolExpect_monomial_eq_sum η (Finset.range N) fun i hi ↦ Finset.mem_range.2 (hm i hi)
  · simp [LinearMap.sum_apply]

end Trace

/-! ### Uniqueness -/

section Uniqueness

variable {η : R} {μ : BalancedProjectionAlgebra R (0 : R) →ₗ[R] R}

/-- A functional which does not see the order of two adjacent generators does not see the order
of any two generators. -/
private theorem apply_mul_e_mul_e_mul_comm
    (hcomm : ∀ x y i, μ (x * e 0 i * e 0 (i + 1) * y) = μ (x * e 0 (i + 1) * e 0 i * y))
    (x y : BalancedProjectionAlgebra R (0 : R)) (i j : ℕ) :
    μ (x * e 0 i * e 0 j * y) = μ (x * e 0 j * e 0 i * y) := by
  by_cases h₁ : j = i + 1
  · subst h₁
    exact hcomm x y i
  by_cases h₂ : i = j + 1
  · subst h₂
    exact (hcomm x y j).symm
  by_cases h₃ : i = j
  · rw [h₃]
  rw [mul_assoc x, (commute_e (by omega)).eq, ← mul_assoc]

/-- A functional which does not see the order of two adjacent generators does not see the order
of the generators in a product. -/
private theorem apply_mul_prod_mul_of_perm
    (hcomm : ∀ x y i j, μ (x * e 0 i * e 0 j * y) = μ (x * e 0 j * e 0 i * y))
    {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) (x y : BalancedProjectionAlgebra R (0 : R)) :
    μ (x * (l₁.map (e 0)).prod * y) = μ (x * (l₂.map (e 0)).prod * y) := by
  induction h generalizing x with
  | nil => rfl
  | cons a _ ih =>
    simp only [List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih (x * e 0 a)
  | swap a b l =>
    simp only [List.map_cons, List.prod_cons, ← mul_assoc]
    rw [mul_assoc _ _ y, mul_assoc _ _ y]
    exact hcomm _ _ _ _
  | trans _ _ ih₁ ih₂ => exact (ih₁ x).trans (ih₂ x)

/-- A normalized Markov functional which does not see the order of two adjacent generators takes
the value `η ^ k` on a product of generators, where `k` is the number of distinct generators
occurring in it. -/
private theorem apply_prod_eq_pow (h1 : μ 1 = 1)
    (hmarkov : ∀ {n w}, w ∈ stage R 0 (n + 1) → μ (w * e 0 n) = η * μ w)
    (hcomm : ∀ x y i, μ (x * e 0 i * e 0 (i + 1) * y) = μ (x * e 0 (i + 1) * e 0 i * y))
    (l : List ℕ) :
    μ (l.map (e 0)).prod = η ^ l.toFinset.card := by
  induction hl : l.length using Nat.strong_induction_on generalizing l with
  | _ k ih =>
  subst hl
  by_cases hnil : l = []
  · simpa [hnil] using h1
  -- Move every occurrence of the largest index `a` to the end, where they collapse to `e 0 a`.
  set a := l.toFinset.max' ((List.toFinset_nonempty_iff l).2 hnil)
  have ha : a ∈ l := List.mem_toFinset.1 (l.toFinset.max'_mem _)
  set l' := l.filter fun x ↦ !(x == a)
  have hperm : l.Perm (l' ++ List.replicate (l.count a) a) := by
    rw [← List.filter_beq]
    exact (List.filter_append_perm _ l).symm.trans List.perm_append_comm
  have hword : ((l' ++ List.replicate (l.count a) a).map (e (R := R) 0)).prod =
      (l'.map (e 0)).prod * e 0 a := by
    rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
      (isIdempotentElem_e a).pow_eq (List.count_pos_iff.2 ha).ne']
  have hstage : (l'.map (e (R := R) 0)).prod ∈ stage R 0 (a + 1) := by
    refine Subalgebra.list_prod_mem _ fun x hx ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hil, hia⟩ := List.mem_filter.1 hi
    have : i < a := lt_of_le_of_ne (l.toFinset.le_max' i (List.mem_toFinset.2 hil))
      (by simpa using hia)
    exact e_mem_stage (by omega)
  have hlen : l'.length < l.length :=
    List.length_filter_lt_length_iff_exists.2 ⟨a, ha, by simp⟩
  have hcard : l'.toFinset.card + 1 = l.toFinset.card := by
    rw [List.toFinset_filter]
    convert Finset.card_erase_add_one (List.mem_toFinset.2 ha) using 3
    ext x
    simp [and_comm]
  calc μ (l.map (e 0)).prod = μ (1 * (l.map (e 0)).prod * 1) := by rw [one_mul, mul_one]
    _ = μ ((l'.map (e 0)).prod * e 0 a) := by
      rw [apply_mul_prod_mul_of_perm (apply_mul_e_mul_e_mul_comm hcomm) hperm, hword, one_mul,
        mul_one]
    _ = η ^ l.toFinset.card := by
      rw [hmarkov hstage, ih _ hlen l' rfl, ← hcard, pow_succ']

/-- **Uniqueness of the Bernoulli trace.** A normalized Markov functional with parameter `η` which
does not see the order of two adjacent generators `e i` and `e (i + 1)` is the Bernoulli trace. -/
theorem eq_bernoulliTrace (h1 : μ 1 = 1)
    (hmarkov : ∀ {n w}, w ∈ stage R 0 (n + 1) → μ (w * e 0 n) = η * μ w)
    (hcomm : ∀ x y i, μ (x * e 0 i * e 0 (i + 1) * y) = μ (x * e 0 (i + 1) * e 0 i * y)) :
    μ = bernoulliTrace η := by
  have hB (x y : BalancedProjectionAlgebra R (0 : R)) (i : ℕ) :
      bernoulliTrace η (x * e 0 i * e 0 (i + 1) * y) =
        bernoulliTrace η (x * e 0 (i + 1) * e 0 i * y) := by
    simp only [bernoulliTrace_apply, map_mul, mul_right_comm _ (toBool R (e 0 i))]
  ext x
  have hx : x ∈ Subalgebra.toSubmodule (Algebra.adjoin R (Set.range (e (R := R) 0))) := by simp
  rw [Algebra.adjoin_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ : ∃ l : List ℕ, (l.map (e 0)).prod = x := by
      induction hx using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨[i], by simp⟩
      | one => exact ⟨[], by simp⟩
      | mul x y _ _ hx hy =>
        obtain ⟨l₁, rfl⟩ := hx
        obtain ⟨l₂, rfl⟩ := hy
        exact ⟨l₁ ++ l₂, by simp⟩
    rw [apply_prod_eq_pow h1 hmarkov hcomm,
      apply_prod_eq_pow (bernoulliTrace_one η) (bernoulliTrace_mul_e η) hB]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]

/-- A normalized Markov functional through a representation in which adjacent generators commute
is the Bernoulli trace. -/
theorem comp_eq_bernoulliTrace {A : Type*} [Ring A] [Algebra R A]
    (φ : BalancedProjectionAlgebra R (0 : R) →ₐ[R] A)
    (hφ : ∀ i, Commute (φ (e 0 i)) (φ (e 0 (i + 1)))) {ν : A →ₗ[R] R} (h1 : ν 1 = 1)
    (hmarkov : ∀ {n w}, w ∈ stage R 0 (n + 1) → ν (φ (w * e 0 n)) = η * ν (φ w)) :
    ν ∘ₗ φ.toLinearMap = bernoulliTrace η :=
  eq_bernoulliTrace (by simpa using h1) hmarkov fun x y i ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      mul_assoc]
    rw [← mul_assoc (φ (e 0 i)), (hφ i).eq, mul_assoc]

/-- **Uniqueness of the Markov state at `τ = 0`.** A normalized Markov functional with parameter
`η` through a representation by projections in a ring with a proper star, for instance a
C⋆-algebra, is the Bernoulli trace. -/
theorem comp_eq_bernoulliTrace_of_isStarProjection {A : Type*} [Ring A] [StarRing A]
    [IsProperStar A] [Algebra R A] (φ : BalancedProjectionAlgebra R (0 : R) →ₐ[R] A)
    (hφ : ∀ i, IsStarProjection (φ (e 0 i))) {ν : A →ₗ[R] R} (h1 : ν 1 = 1)
    (hmarkov : ∀ {n w}, w ∈ stage R 0 (n + 1) → ν (φ (w * e 0 n)) = η * ν (φ w)) :
    ν ∘ₗ φ.toLinearMap = bernoulliTrace η :=
  comp_eq_bernoulliTrace φ (fun i ↦ commute_map_e_of_zero φ hφ i (i + 1)) h1 hmarkov

/-- At an idempotent parameter `c`, the Bernoulli trace is the scalar character sending every
generator to `c`. -/
theorem bernoulliTrace_eq_character {c : R} (hc : IsIdempotentElem c) :
    bernoulliTrace c = (character (τ := (0 : R)) c hc).toLinearMap :=
  (eq_bernoulliTrace (by simp) (fun {_ _} _ ↦ by simp [mul_comm]) fun _ _ _ ↦ by simp).symm

end Uniqueness

end BalancedProjectionAlgebra

end TauCeti
