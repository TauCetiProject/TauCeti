/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Basic
-- Proof-only: the rank of the span of a linearly independent family.
import Mathlib.LinearAlgebra.Dimension.Constructions
-- Proof-only: products of linearly independent families in a tower, and powers below the degree.
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.PowerBasis
-- Proof-only: a nontrivial commutative ring satisfies the strong rank condition.
import Mathlib.RingTheory.FiniteType
-- Proof-only: integral multiples of algebraic elements and finiteness of `R[x]` for integral `x`.
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Linear independence of powers and transcendence

The powers of a transcendental element of an algebra are linearly independent over the base ring.
Consequently, the first `n` powers span a submodule of rank `n` over a nontrivial commutative ring,
and in a tower `R → K → A` with `K` a field, the products `x ^ i y ^ j` of the powers of `x ∈ K`
transcendental over `R` with the powers `y ^ j`, `j < (minpoly K y).natDegree`, of `y ∈ A` are
linearly independent over `R`.

Conversely, the powers of an element algebraic over a domain admit only boundedly many linearly
independent members, so every sufficiently large finite family of its powers satisfies a
nontrivial linear relation over the base ring. In an algebra without zero divisors, a nontrivial
linear relation among the powers `f ^ q ^ j`, `j ≤ m`, of a nonzero `f` with `2 ≤ q` makes `f` a
root of a nonzero polynomial of degree at most `q ^ m - 1`.

## Main results

* `Transcendental.linearIndependent_pow`: the powers of a transcendental element are
  linearly independent over the base ring.
* `Transcendental.finrank_span_range_pow`: over a nontrivial commutative ring, the span of the
  first `n` powers of a transcendental element has rank `n`.
* `Transcendental.linearIndepOn_pow_mul_pow`: in a tower `R → K → A`, the products `x ^ i y ^ j`
  with `x ∈ K` transcendental over `R` and `j < (minpoly K y).natDegree` are linearly independent
  over `R`.
* `IsAlgebraic.exists_card_le_of_linearIndependent_pow`: a linearly independent family of powers
  of an element algebraic over a domain has boundedly many members.
* `TauCeti.exists_natDegree_le_aeval_eq_zero_of_sum_smul_pow_pow_eq_zero`: a nontrivial linear
  relation among the powers `f ^ q ^ j`, `j ≤ m`, makes `f ≠ 0` a root of a nonzero polynomial of
  degree at most `q ^ m - 1`.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The powers of a transcendental element are linearly independent over the base ring. -/
theorem _root_.Transcendental.linearIndependent_pow {x : A} (hx : Transcendental R x) :
    LinearIndependent R fun n : ℕ ↦ x ^ n := by
  simpa [Function.comp_def] using (Polynomial.basisMonomials R).linearIndependent.map_injOn
    (Polynomial.aeval x).toLinearMap (transcendental_iff_injective.mp hx).injOn

/-- The first `n` powers of a transcendental element span a submodule of rank `n` over a
nontrivial commutative ring. -/
theorem _root_.Transcendental.finrank_span_range_pow {K B : Type*} [CommRing K] [Nontrivial K]
    [Ring B] [Algebra K B] {x : B} (hx : Transcendental K x) (n : ℕ) :
    Module.finrank K (Submodule.span K (Set.range fun i : Fin n ↦ x ^ (i : ℕ))) = n :=
  (finrank_span_eq_card (hx.linearIndependent_pow.comp _ Fin.val_injective)).trans
    (Fintype.card_fin n)

/-- **The products `x ^ i y ^ j` are linearly independent**: in a tower `R → K → A` with `K` a
field, if `x ∈ K` is transcendental over `R` and `y ∈ A`, then the products `x ^ i y ^ j` with
`j < (minpoly K y).natDegree` are linearly independent over `R`. The bound is the degree of `y`
over `K` when `y` is integral over `K`; otherwise `minpoly K y = 0` and the statement is vacuous. -/
theorem _root_.Transcendental.linearIndepOn_pow_mul_pow {K : Type*} [Field K] [Algebra R K]
    [Algebra K A] [IsScalarTower R K A] {x : K} (hx : Transcendental R x) (y : A) :
    LinearIndepOn R (fun p : ℕ × ℕ ↦ algebraMap K A x ^ p.1 * y ^ p.2)
      {p | p.2 < (minpoly K y).natDegree} := by
  -- The powers of `x` are independent over `R`, those of `y` below `(minpoly K y).natDegree`
  -- over `K`.
  have h := linearIndependent_smul (R := R) hx.linearIndependent_pow (linearIndependent_pow y)
  have hinj : Function.Injective fun p : {p : ℕ × ℕ | p.2 < (minpoly K y).natDegree} ↦
      ((p : ℕ × ℕ).1, (⟨(p : ℕ × ℕ).2, p.2⟩ : Fin (minpoly K y).natDegree)) :=
    fun p q hpq ↦ by
      simp only [Prod.mk.injEq, Fin.mk.injEq] at hpq
      exact Subtype.ext (Prod.ext hpq.1 hpq.2)
  rw [← linearIndependent_set_coe_iff]
  convert h.comp _ hinj using 1
  ext p
  simp [Algebra.smul_def]

/-- **Linearly independent powers of an algebraic element are boundedly many**: if `x` is algebraic
over a domain `R`, there is a bound `d` such that every finite family of powers `x ^ e i` that is
linearly independent over `R` has at most `d` members. -/
theorem _root_.IsAlgebraic.exists_card_le_of_linearIndependent_pow [IsDomain R] {x : A}
    (hx : IsAlgebraic R x) :
    ∃ d : ℕ, ∀ {ι : Type*} [Fintype ι] (e : ι → ℕ),
      LinearIndependent R (fun i ↦ x ^ e i) → Fintype.card ι ≤ d := by
  -- Some nonzero multiple `c • x` is integral, so `R[c • x]` is a finite `R`-module containing
  -- `c ^ N • x ^ n` for every `n ≤ N`; its rank bounds the families.
  obtain ⟨c, hc, hint⟩ := hx.exists_integral_multiple
  set M := Subalgebra.toSubmodule (Algebra.adjoin R {c • x})
  have : Module.Finite R M := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  refine ⟨Module.finrank R M, fun {ι} _ e he ↦ ?_⟩
  set N := Finset.univ.sup e
  have hmem (i : ι) : c ^ N • x ^ e i ∈ M := by
    have hle : e i ≤ N := Finset.le_sup (Finset.mem_univ i)
    rw [Subalgebra.mem_toSubmodule, ← Nat.sub_add_cancel hle, pow_add, mul_smul, ← smul_pow]
    exact Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton R _) _) _
  have hreg : IsRightRegular (c ^ N) := (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hc)).right
  exact ((he.smul_of_isRightRegular (w := fun _ ↦ c ^ N) fun _ ↦ hreg).codRestrict M
    hmem).fintype_card_le_finrank

/-- A nontrivial relation `∑_{j ≤ m} cⱼ f ^ q ^ j = 0` with `2 ≤ q` and `f ≠ 0` makes `f` a root of
the nonzero polynomial `∑_{j ≤ m} cⱼ T ^ (q ^ j - 1)`, of degree at most `q ^ m - 1`. -/
theorem exists_natDegree_le_aeval_eq_zero_of_sum_smul_pow_pow_eq_zero [NoZeroDivisors A]
    {q m : ℕ} (hq : 2 ≤ q) {c : Fin (m + 1) → R} {i : Fin (m + 1)}
    (hi : c i ≠ 0) {f : A} (hf : f ≠ 0) (hc : ∑ j, c j • f ^ q ^ (j : ℕ) = 0) :
    ∃ Q : Polynomial R, Q ≠ 0 ∧ Q.natDegree ≤ q ^ m - 1 ∧ Polynomial.aeval f Q = 0 := by
  classical
  have hqj (j : ℕ) : 0 < q ^ j := Nat.pow_pos (by omega)
  -- The exponents `q ^ j - 1` are distinct, so `Q` has coefficient `c i ≠ 0` at `q ^ i - 1`.
  have hinj : Function.Injective fun j : Fin (m + 1) ↦ q ^ (j : ℕ) - 1 := fun a b hab ↦
    Fin.ext <| Nat.pow_right_injective hq <| Nat.sub_one_cancel (hqj a) (hqj b) hab
  set Q : Polynomial R := ∑ j : Fin (m + 1), Polynomial.monomial (q ^ (j : ℕ) - 1) (c j)
  have hQ : Q ≠ 0 := by
    intro hQ
    apply hi
    have := congrArg (Polynomial.coeff · (q ^ (i : ℕ) - 1)) hQ
    simpa [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hinj.eq_iff] using this
  have hQdeg : Q.natDegree ≤ q ^ m - 1 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦
      (Polynomial.natDegree_monomial_le _).trans <|
        Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega : 0 < q) (Nat.lt_succ_iff.mp j.isLt)) 1
  -- Multiplying `Q(f)` by `f` turns each `cⱼ f ^ (q ^ j - 1)` into `cⱼ f ^ q ^ j`.
  refine ⟨Q, hQ, hQdeg, (mul_eq_zero.mp ?_).resolve_right hf⟩
  rw [← hc, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [Polynomial.aeval_monomial, ← Algebra.smul_def, ← pow_succ, Nat.sub_add_cancel (hqj j)]

end TauCeti
