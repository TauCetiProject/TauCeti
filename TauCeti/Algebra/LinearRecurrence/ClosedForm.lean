/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Algebra.LinearRecurrence.ExponentialPolynomial

/-!
# Closed form of a linear recurrence

Let `E` be a linear recurrence over a field `K` of characteristic zero whose characteristic
polynomial splits and has nonzero constant term. Every solution `u` of `E` is an exponential
polynomial in the characteristic roots: there are polynomials `P θ`, one for each distinct root
`θ`, with `deg (P θ)` smaller than the multiplicity of `θ`, such that
`u n = ∑ θ, (P θ).eval n * θ ^ n` for every `n`. Over `ℂ`, or any algebraically closed field of
characteristic zero, the splitting hypothesis is automatic.

Repeated roots genuinely need polynomial coefficients: `n ↦ n` solves the recurrence with
characteristic polynomial `(X - 1) ^ 2`. The constant-term hypothesis cannot be dropped either:
for the characteristic polynomial `X ^ 2`, the sequence that is `1` at `n = 1` and `0` elsewhere
is a solution, but every `(P 0).eval n * 0 ^ n` vanishes at `n = 1`.

The proof is a dimension count. The characteristic polynomial evaluated at the forward shift
annihilates exactly the solutions (`LinearRecurrence.isSolution_iff_aeval_charPoly_apply`), so
each `n ↦ p.eval n * θ ^ n` with `deg p` below the multiplicity of `θ` is a solution
(`LinearRecurrence.isSolution_eval_mul_pow`). These sequences form a space of dimension
`∑ θ, mult θ = E.order`, mapped injectively into the solution space by the uniqueness theorem
`TauCeti.eq_zero_of_sum_eval_mul_pow_eq_zero`. Since the solution space also has dimension
`E.order`, the map is onto.

## Main results

* `LinearRecurrence.isSolution_iff_aeval_charPoly_apply`: `u` solves `E` iff
  `E.charPoly` evaluated at the forward shift sends `u` to zero.
* `LinearRecurrence.isSolution_eval_mul_pow`: `n ↦ p.eval n * θ ^ n` solves `E` whenever
  `p.degree` is less than the multiplicity of `θ` as a root of `E.charPoly`.
* `LinearRecurrence.exists_eq_sum_eval_mul_pow`: the closed form of a solution.
* `LinearRecurrence.isSolution_iff_exists_eq_sum_eval_mul_pow`: the solutions of `E` are
  exactly these exponential polynomials.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), §8.4, Theorem 8.17.
* R. P. Stanley, *Enumerative Combinatorics*, vol. 1, second edition, Theorem 4.1.1,
  pp. 535–536.
-/

public section

open Polynomial

namespace LinearRecurrence

section CommRing

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

/-- A sequence solves `E` exactly when the characteristic polynomial of `E`, evaluated at the
forward shift `u ↦ (n ↦ u (n + 1))`, annihilates it. -/
theorem isSolution_iff_aeval_charPoly_apply {u : ℕ → R} :
    E.IsSolution u ↔ aeval (LinearMap.funLeft R R Nat.succ) E.charPoly u = 0 := by
  have hpow (k n : ℕ) : ((LinearMap.funLeft R R Nat.succ) ^ k) u n = u (n + k) := by
    induction k generalizing n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.funLeft_apply, ih]
      congr 1
      omega
  have h (n : ℕ) : aeval (LinearMap.funLeft R R Nat.succ) E.charPoly u n =
      u (n + E.order) - ∑ i, E.coeffs i * u (n + i) := by
    simp [charPoly, ← C_mul_X_pow_eq_monomial, Finset.sum_apply, LinearMap.sum_apply,
      Module.algebraMap_end_apply, hpow]
  simp only [IsSolution, funext_iff, Pi.zero_apply, h, sub_eq_zero]

/-- If `p.degree` is less than the multiplicity of `θ` as a root of the characteristic
polynomial, then `n ↦ p.eval n * θ ^ n` solves `E`. This holds over every commutative ring,
including at `θ = 0`. -/
theorem isSolution_eval_mul_pow {p : R[X]} {θ : R}
    (hp : p.degree < E.charPoly.rootMultiplicity θ) :
    E.IsSolution fun n ↦ p.eval (n : R) * θ ^ n := by
  obtain ⟨q, hq⟩ := E.charPoly.pow_rootMultiplicity_dvd θ
  have hker := Module.End.mem_genEigenspace_nat.mp (eval_mul_pow_mem_genEigenspace θ hp)
  rw [LinearMap.mem_ker] at hker
  rw [isSolution_iff_aeval_charPoly_apply, hq, mul_comm, map_mul, Module.End.mul_apply,
    map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, hker, map_zero]

end CommRing

section Field

variable {K : Type*} [Field K] (E : LinearRecurrence K)

/-- The exponential polynomials of the closed form, with the coefficient polynomial at each
root `θ ∈ s` taken of degree less than `m θ`, as a linear map into sequences. -/
private noncomputable def expPolyMap (s : Finset K) (m : K → ℕ) :
    (Π θ : s, degreeLT K (m θ)) →ₗ[K] ℕ → K :=
  ∑ θ : s, LinearMap.pi (fun n : ℕ ↦ (θ : K) ^ n • leval (n : K)) ∘ₗ
    (degreeLT K (m θ)).subtype ∘ₗ LinearMap.proj θ

private theorem expPolyMap_apply (s : Finset K) (m : K → ℕ) (g : Π θ : s, degreeLT K (m θ))
    (n : ℕ) :
    expPolyMap s m g n = ∑ θ : s, (g θ : K[X]).eval (n : K) * (θ : K) ^ n := by
  simp [expPolyMap, LinearMap.sum_apply, Finset.sum_apply, mul_comm]

/-- `expPolyMap` with its coefficient family extended by zero outside `s`. -/
private theorem sum_dite_eval_mul_pow [DecidableEq K] (s : Finset K) (m : K → ℕ)
    (g : Π θ : s, degreeLT K (m θ)) (n : ℕ) :
    ∑ θ ∈ s, (if h : θ ∈ s then (g ⟨θ, h⟩ : K[X]) else 0).eval (n : K) * θ ^ n =
      expPolyMap s m g n := by
  rw [expPolyMap_apply, ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun θ _ ↦ by rw [dite_eq_left θ.2]

variable [CharZero K]

/-- Over nonzero bases, `expPolyMap` is injective: an exponential polynomial determines its
coefficient polynomials. -/
private theorem expPolyMap_injective {s : Finset K} (m : K → ℕ) (hs : ∀ θ ∈ s, θ ≠ 0) :
    Function.Injective (expPolyMap s m) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have hz (n : ℕ) : ∑ θ ∈ s, (if h : θ ∈ s then (g ⟨θ, h⟩ : K[X]) else 0).eval (n : K) *
      θ ^ n = 0 := by
    rw [sum_dite_eval_mul_pow, hg, Pi.zero_apply]
  funext θ
  have := TauCeti.eq_zero_of_sum_eval_mul_pow_eq_zero hs hz θ θ.2
  rw [dite_eq_left θ.2] at this
  exact Subtype.ext this

variable [DecidableEq K]

/-- **Closed form of a linear recurrence.** If the characteristic polynomial of `E` splits and
has nonzero constant term, every solution of `E` is `∑ θ, (P θ).eval n * θ ^ n` over the
distinct characteristic roots `θ`, with `deg (P θ)` less than the multiplicity of `θ`.
Over an algebraically closed field the splitting hypothesis is `IsAlgClosed.splits`. -/
theorem exists_eq_sum_eval_mul_pow (hsplit : E.charPoly.Splits) (h0 : E.charPoly.coeff 0 ≠ 0)
    {u : ℕ → K} (hu : E.IsSolution u) :
    ∃ P : K → K[X],
      (∀ θ ∈ E.charPoly.roots, (P θ).degree < E.charPoly.rootMultiplicity θ) ∧
        ∀ n : ℕ, u n = ∑ θ ∈ E.charPoly.roots.toFinset, (P θ).eval (n : K) * θ ^ n := by
  set s := E.charPoly.roots.toFinset
  set m : K → ℕ := fun θ ↦ E.charPoly.rootMultiplicity θ
  -- The exponential polynomials of the closed form are solutions of `E`.
  have hmem (g : Π θ : s, degreeLT K (m θ)) : expPolyMap s m g ∈ E.solSpace := by
    have : expPolyMap s m g = ∑ θ : s, fun n : ℕ ↦ (g θ : K[X]).eval (n : K) * (θ : K) ^ n := by
      ext n
      simp [expPolyMap_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun θ _ ↦ E.isSolution_eval_mul_pow (mem_degreeLT.mp (g θ).2)
  let Φ := (expPolyMap s m).codRestrict E.solSpace hmem
  -- They are independent, since the characteristic roots are nonzero.
  have hinj : Function.Injective Φ := by
    refine fun g g' h ↦ expPolyMap_injective m (fun θ hθ h0' ↦ h0 ?_) (congrArg Subtype.val h)
    subst h0'
    exact coeff_zero_eq_eval_zero E.charPoly ▸ (mem_roots'.mp (Multiset.mem_toFinset.mp hθ)).2
  -- Both spaces have dimension `E.order = ∑ θ, mult θ`, so every solution is attained.
  have := Module.Finite.of_basis E.basis
  have (θ : s) : Module.Finite K (degreeLT K (m θ)) := .equiv (degreeLTEquiv K (m θ)).symm
  have hdim : Module.finrank K (Π θ : s, degreeLT K (m θ)) = Module.finrank K E.solSpace := by
    rw [Module.finrank_pi_fintype, Module.finrank_eq_card_basis E.basis, Fintype.card_fin,
      ← natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order, hsplit.natDegree_eq_card_roots,
      ← Multiset.toFinset_sum_count_eq, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun θ _ ↦ ?_
    rw [(degreeLTEquiv K (m θ)).finrank_eq, Module.finrank_fin_fun, count_roots]
  have hrange : LinearMap.range Φ = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hinj).trans hdim)
  obtain ⟨g, hg⟩ := LinearMap.range_eq_top.mp hrange ⟨u, (E.is_sol_iff_mem_solSpace u).mp hu⟩
  refine ⟨fun θ ↦ if h : θ ∈ s then (g ⟨θ, h⟩ : K[X]) else 0, fun θ hθ ↦ ?_, fun n ↦ ?_⟩
  · have hθs : θ ∈ s := Multiset.mem_toFinset.mpr hθ
    simpa only [dite_eq_left hθs] using mem_degreeLT.mp (g ⟨θ, hθs⟩).2
  · have := congrArg (fun v : E.solSpace ↦ (v : ℕ → K) n) hg
    simp only [Φ, LinearMap.codRestrict_apply] at this
    beta_reduce
    rw [sum_dite_eval_mul_pow, this]

/-- The solutions of a linear recurrence whose characteristic polynomial splits and has nonzero
constant term are exactly the exponential polynomials `∑ θ, (P θ).eval n * θ ^ n` over the
distinct characteristic roots `θ` with `deg (P θ)` less than the multiplicity of `θ`. -/
theorem isSolution_iff_exists_eq_sum_eval_mul_pow (hsplit : E.charPoly.Splits)
    (h0 : E.charPoly.coeff 0 ≠ 0) {u : ℕ → K} :
    E.IsSolution u ↔ ∃ P : K → K[X],
      (∀ θ ∈ E.charPoly.roots, (P θ).degree < E.charPoly.rootMultiplicity θ) ∧
        ∀ n : ℕ, u n = ∑ θ ∈ E.charPoly.roots.toFinset, (P θ).eval (n : K) * θ ^ n := by
  refine ⟨E.exists_eq_sum_eval_mul_pow hsplit h0, ?_⟩
  rintro ⟨P, hP, hu⟩
  have : u = ∑ θ ∈ E.charPoly.roots.toFinset, fun n : ℕ ↦ (P θ).eval (n : K) * θ ^ n := by
    ext n
    simp [hu n, Finset.sum_apply]
  rw [E.is_sol_iff_mem_solSpace, this]
  exact Submodule.sum_mem _ fun θ hθ ↦
    E.isSolution_eval_mul_pow (hP θ (Multiset.mem_toFinset.mp hθ))

end Field

end LinearRecurrence
