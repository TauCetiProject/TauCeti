/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Intervals
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.TypeAHeckeAlgebra.Embedding

/-!
# The coset basis of a stage over the previous one

Let `Hₙ` be the stage of the first `n` strands of the infinite type-A Hecke algebra
(`TauCeti.InfiniteTypeAHeckeAlgebra.stage`). This file proves that the next stage `Hₙ₊₁` is a free
left `Hₙ`-module of rank `n + 1`, with basis the descending products

`cosetRep q n m = T (n - 1) * T (n - 2) * ⋯ * T m`, for `m = 0, …, n`,

of the generators (the empty product `1` for `m = n`). They are the elements `T_w` attached to
the minimal-length representatives `w = s (n - 1) ⋯ s m` of the cosets of the symmetric group on
`n` letters in the symmetric group on `n + 1` letters, although that identification is not needed
here. Concretely, every element of `Hₙ₊₁` is uniquely a sum `∑ m, a m * cosetRep q n m` with
coefficients `a m` in `Hₙ` (`TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv`), and the
coefficients depend `Hₙ`-linearly on the element
(`TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv_symm_mul`). This is the left-module form of
the decomposition `Hₙ₊₂ = Hₙ₊₁ + Hₙ₊₁ Tₙ Hₙ₊₁`
(`TauCeti.InfiniteTypeAHeckeAlgebra.toSubmodule_stage_add_two`). These coordinates are the ones in
which Jones computes the Ocneanu trace recursively, one strand at a time.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.cosetRep`: the descending product `T (n - 1) * ⋯ * T m`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv`: the `R`-linear isomorphism from
  `Fin (n + 1) → Hₙ` to `Hₙ₊₁` sending `a` to `∑ m, a m * cosetRep q n m`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.coe_cosetEquiv_apply`: the formula for `cosetEquiv`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv_smul` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv_symm_mul`: `cosetEquiv` is `Hₙ`-linear for left
  multiplication, so the representatives form a basis of `Hₙ₊₁` as a left `Hₙ`-module.
* `TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv_symm_inclusion`: an element `b` of `Hₙ` has
  coordinate `b` at the representative `cosetRep q n n = 1`, and coordinate zero at every other
  index.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 4.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

section CosetRep

variable (q) in
/-- The descending product `T (n - 1) * T (n - 2) * ⋯ * T m` of the generators from `T (n - 1)`
down to `T m`, which is `1` when `n ≤ m`. For `m ≤ n` it is the element `T_w` of the
minimal-length representative `w = s (n - 1) ⋯ s m` of a coset of the symmetric group on `n`
letters in the symmetric group on `n + 1` letters. -/
def cosetRep (n m : ℕ) : InfiniteTypeAHeckeAlgebra R q :=
  ((List.Ico m n).reverse.map (T q)).prod

/-- The descending product from `T (n - 1)` down to `T m` is empty when `n ≤ m`. -/
theorem cosetRep_of_le {n m : ℕ} (h : n ≤ m) : cosetRep q n m = 1 := by
  rw [cosetRep, List.Ico.eq_nil_of_le h, List.reverse_nil, List.map_nil, List.prod_nil]

/-- The trivial representative is `1`. -/
@[simp]
theorem cosetRep_self (n : ℕ) : cosetRep q n n = 1 :=
  cosetRep_of_le le_rfl

/-- Raising the top of the descending product adds a generator on the left. -/
theorem cosetRep_succ {n m : ℕ} (h : m ≤ n) : cosetRep q (n + 1) m = T q n * cosetRep q n m := by
  simp only [cosetRep, List.Ico.succ_top h, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons, List.prod_cons]

/-- Lowering the bottom of the descending product adds a generator on the right. -/
theorem cosetRep_succ_mul_T {n m : ℕ} (h : m < n) :
    cosetRep q n (m + 1) * T q m = cosetRep q n m := by
  simp only [cosetRep, List.Ico.eq_cons h, List.reverse_cons, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]

/-- The descending product from `T (n - 1)` lies in the stage of the first `n + 1` strands. -/
theorem cosetRep_mem_stage (n m : ℕ) : cosetRep q n m ∈ stage R q (n + 1) :=
  Subalgebra.list_prod_mem _ fun x hx ↦ by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact T_mem_stage (by grind [List.Ico.mem])

/-- A generator far below the descending product commutes past it. -/
theorem cosetRep_mul_T_of_add_one_lt {n m i : ℕ} (h : i + 1 < m) :
    cosetRep q n m * T q i = T q i * cosetRep q n m :=
  (Commute.list_prod_left _ _ fun x hx ↦ by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact commute_T (Or.inr (by grind [List.Ico.mem]))).eq

/-- For `m < n`, multiplying the descending product on the right by its lowest generator `T m`
gives `(q - q⁻¹) • cosetRep q n m + cosetRep q n (m + 1)`. -/
theorem cosetRep_mul_T_self {n m : ℕ} (h : m < n) :
    cosetRep q n m * T q m = ((q : R) - ↑q⁻¹) • cosetRep q n m + cosetRep q n (m + 1) := by
  rw [← cosetRep_succ_mul_T h, mul_assoc, T_mul_self, mul_add, mul_smul_comm, mul_one]

/-- A generator `T (j + 1)` strictly inside the descending product moves to its left as
`T j`, by the braid relation. -/
theorem cosetRep_mul_T_succ {n m j : ℕ} (hm : m ≤ j) (hj : j + 2 ≤ n) :
    cosetRep q n m * T q (j + 1) = T q j * cosetRep q n m := by
  induction n, hj using Nat.le_induction with
  | base =>
    have hc := (commute_T_of_mem_stage le_rfl (cosetRep_mem_stage (q := q) j m)).eq
    rw [cosetRep_succ (by omega), cosetRep_succ hm]
    calc T q (j + 1) * (T q j * cosetRep q j m) * T q (j + 1)
        = T q (j + 1) * T q j * T q (j + 1) * cosetRep q j m := by
          simp only [mul_assoc, hc]
      _ = T q j * (T q (j + 1) * (T q j * cosetRep q j m)) := by
          rw [← T_braid]
          simp only [mul_assoc]
  | succ n hn ih =>
    rw [cosetRep_succ (by omega), mul_assoc, ih, ← mul_assoc, ← mul_assoc,
      (commute_T (Or.inr (by omega))).eq]

end CosetRep

section CosetEquiv

/- The proof does not use the combinatorics of permutations. Right multiplication by a generator
`T i` of `Hₙ₊₁` takes each representative into the left `Hₙ`-span of the representatives
(`cosetRep_mul_T_of_add_one_lt`, `cosetRep_succ_mul_T`, `cosetRep_mul_T_self` and
`cosetRep_mul_T_succ`), so the sums `∑ m, a m * cosetRep q n m` form a right ideal of `Hₙ₊₁`
containing `1`, hence all of `Hₙ₊₁`. Both sides are free `R`-modules of rank
`(n + 1) * n! = (n + 1)!` (`finrank_stage`), and a surjective linear map between finite free
modules of the same rank over a commutative ring is bijective. -/

variable (R q) in
/-- The sum `∑ m, a m * cosetRep q n m` with coefficients in the stage of the first `n` strands. -/
private def cosetSum (n : ℕ) : (Fin (n + 1) → stage R q n) →ₗ[R] InfiniteTypeAHeckeAlgebra R q :=
  LinearMap.lsum R (fun _ : Fin (n + 1) ↦ stage R q n) R fun m ↦
    LinearMap.mulRight R (cosetRep q n m) ∘ₗ (stage R q n).val.toLinearMap

private theorem cosetSum_apply {n : ℕ} (a : Fin (n + 1) → stage R q n) :
    cosetSum R q n a = ∑ m, (a m : InfiniteTypeAHeckeAlgebra R q) * cosetRep q n m := by
  simp [cosetSum, LinearMap.lsum_apply]

private theorem cosetSum_single {n : ℕ} (m : Fin (n + 1)) (b : stage R q n) :
    cosetSum R q n (Pi.single m b) = (b : InfiniteTypeAHeckeAlgebra R q) * cosetRep q n m := by
  rw [cosetSum, LinearMap.lsum_piSingle]
  rfl

private theorem cosetSum_mem_stage {n : ℕ} (a : Fin (n + 1) → stage R q n) :
    cosetSum R q n a ∈ stage R q (n + 1) := by
  rw [cosetSum_apply]
  exact Subalgebra.sum_mem _ fun m _ ↦
    mul_mem (stage_mono n.le_succ (a m).2) (cosetRep_mem_stage n m)

private theorem mul_cosetRep_mem_range {n m : ℕ} (hm : m ≤ n) {a : InfiniteTypeAHeckeAlgebra R q}
    (ha : a ∈ stage R q n) : a * cosetRep q n m ∈ LinearMap.range (cosetSum R q n) :=
  ⟨Pi.single ⟨m, by omega⟩ ⟨a, ha⟩, cosetSum_single _ _⟩

/-- Right multiplication by a generator of the stage `n + 1` keeps the products `a * cosetRep q n m`
inside the sums `∑ m, a m * cosetRep q n m`. -/
private theorem mul_cosetRep_mul_T_mem_range {n m i : ℕ} (hm : m ≤ n) (hi : i < n)
    {a : InfiniteTypeAHeckeAlgebra R q} (ha : a ∈ stage R q n) :
    a * cosetRep q n m * T q i ∈ LinearMap.range (cosetSum R q n) := by
  rw [mul_assoc]
  rcases lt_trichotomy (i + 1) m with h | h | h
  · rw [cosetRep_mul_T_of_add_one_lt h, ← mul_assoc]
    exact mul_cosetRep_mem_range hm (mul_mem ha (T_mem_stage (by omega)))
  · rw [← h, cosetRep_succ_mul_T (by omega)]
    exact mul_cosetRep_mem_range (by omega) ha
  · obtain rfl | hmi := eq_or_lt_of_le (Nat.lt_succ_iff.1 h)
    · rw [cosetRep_mul_T_self (by omega), mul_add, mul_smul_comm]
      exact add_mem (Submodule.smul_mem _ _ (mul_cosetRep_mem_range hm ha))
        (mul_cosetRep_mem_range (by omega) ha)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hmi
      rw [cosetRep_mul_T_succ (j := m + j) (by omega) (by omega), ← mul_assoc]
      exact mul_cosetRep_mem_range hm (mul_mem ha (T_mem_stage (by omega)))

/-- The sums `∑ m, a m * cosetRep q n m` exhaust the stage of the first `n + 1` strands. -/
private theorem toSubmodule_stage_succ_le_range (n : ℕ) :
    Subalgebra.toSubmodule (stage R q (n + 1)) ≤ LinearMap.range (cosetSum R q n) := by
  set P := LinearMap.range (cosetSum R q n)
  -- The elements multiplying the sums into themselves on the right form a subalgebra.
  let S : Subalgebra R (InfiniteTypeAHeckeAlgebra R q) :=
    { carrier := {x | ∀ p ∈ P, p * x ∈ P}
      mul_mem' := fun hx hy p hp ↦ by
        rw [← mul_assoc]
        exact hy _ (hx p hp)
      add_mem' := fun hx hy p hp ↦ by
        rw [mul_add]
        exact add_mem (hx p hp) (hy p hp)
      algebraMap_mem' := fun r p hp ↦ by
        rw [← Algebra.commutes, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r hp }
  -- It contains the generators of the stage `n + 1`, so the sums form a right ideal of the stage
  -- `n + 1`; they contain `1`, hence the whole stage.
  have hS : stage R q (n + 1) ≤ S := stage_le_iff.2 fun i hi ↦ by
    rintro _ ⟨a, rfl⟩
    rw [cosetSum_apply, Finset.sum_mul]
    exact Submodule.sum_mem _ fun m _ ↦
      mul_cosetRep_mul_T_mem_range (by omega) (by omega) (a m).2
  intro x hx
  simpa only [one_mul] using hS hx 1 (by
    simpa only [cosetRep_self, one_mul] using mul_cosetRep_mem_range le_rfl (one_mem (stage R q n)))

variable (R q) in
/-- The sum `∑ m, a m * cosetRep q n m`, as a linear map into the stage of the first `n + 1`
strands. -/
private def cosetSumStage (n : ℕ) : (Fin (n + 1) → stage R q n) →ₗ[R] stage R q (n + 1) :=
  (cosetSum R q n).codRestrict (Subalgebra.toSubmodule (stage R q (n + 1))) cosetSum_mem_stage

private theorem cosetSumStage_bijective (n : ℕ) : Function.Bijective (cosetSumStage R q n) := by
  refine OrzechProperty.bijective_of_surjective_of_finrank_le _ (fun x ↦ ?_) ?_
  · obtain ⟨a, ha⟩ := toSubmodule_stage_succ_le_range n x.2
    exact ⟨a, Subtype.ext ha⟩
  · nontriviality R
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, finrank_stage, finrank_stage, Nat.factorial_succ]

variable (R q) in
/-- **The coset basis.** The stage of the first `n + 1` strands is a free left module over the stage
of the first `n` strands with basis the descending products `cosetRep q n m`, `m = 0, …, n`: the
`R`-linear map sending coefficients `a : Fin (n + 1) → Hₙ` to `∑ m, a m * cosetRep q n m` is an
isomorphism onto `Hₙ₊₁`. -/
noncomputable def cosetEquiv (n : ℕ) : (Fin (n + 1) → stage R q n) ≃ₗ[R] stage R q (n + 1) :=
  .ofBijective (cosetSumStage R q n) (cosetSumStage_bijective n)

/-- The coset isomorphism sends coefficients `a` to `∑ m, a m * cosetRep q n m`. -/
@[simp]
theorem coe_cosetEquiv_apply {n : ℕ} (a : Fin (n + 1) → stage R q n) :
    (cosetEquiv R q n a : InfiniteTypeAHeckeAlgebra R q) =
      ∑ m, (a m : InfiniteTypeAHeckeAlgebra R q) * cosetRep q n m :=
  cosetSum_apply a

/-- The coset isomorphism is linear for left multiplication by the stage of the first `n`
strands. -/
theorem cosetEquiv_smul {n : ℕ} (b : stage R q n) (a : Fin (n + 1) → stage R q n) :
    cosetEquiv R q n (b • a) = Subalgebra.inclusion (stage_mono n.le_succ) b * cosetEquiv R q n a :=
  Subtype.ext <| by
    simp only [coe_cosetEquiv_apply, Pi.smul_apply, smul_eq_mul, Subalgebra.coe_mul,
      Subalgebra.coe_inclusion, Finset.mul_sum, mul_assoc]

/-- The coefficients of an element of the stage `n + 1` along the representatives
`cosetRep q n m` are linear for left multiplication by the stage `n`. -/
theorem cosetEquiv_symm_mul {n : ℕ} (b : stage R q n) (x : stage R q (n + 1)) :
    (cosetEquiv R q n).symm (Subalgebra.inclusion (stage_mono n.le_succ) b * x) =
      b • (cosetEquiv R q n).symm x := by
  rw [LinearEquiv.symm_apply_eq, cosetEquiv_smul, LinearEquiv.apply_symm_apply]

/-- An element of the stage `n` is its own coefficient at the trivial representative
`cosetRep q n n = 1`, and has no other coefficients. -/
@[simp]
theorem cosetEquiv_symm_inclusion {n : ℕ} (b : stage R q n) :
    (cosetEquiv R q n).symm (Subalgebra.inclusion (stage_mono n.le_succ) b) =
      Pi.single (Fin.last n) b := by
  rw [LinearEquiv.symm_apply_eq]
  refine Subtype.ext ((cosetSum_single (Fin.last n) b).trans ?_).symm
  simp

end CosetEquiv

end InfiniteTypeAHeckeAlgebra

end TauCeti
