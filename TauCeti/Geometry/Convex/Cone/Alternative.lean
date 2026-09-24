/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Order.WellFoundedSet

/-!
# Theorems of the alternative for nonnegative vectors

This file proves the classical theorems of the alternative of Gordan, Stiemke and Tucker over an
arbitrary linearly ordered field and draws their consequences for subgroups of the integer lattice
`ι → ℤ`.

For a finite family of vectors `a j` in a vector space over a linearly ordered field `K`,
*Gordan's theorem* says that either some linear functional is strictly positive on every `a j`,
or the family admits a nontrivial linear relation with nonnegative coefficients, and not both.
Applied to the images of the coordinate vectors in a quotient `(ι → K) ⧸ S`, it becomes
*Stiemke's theorem*: a subspace `S` contains no nonzero nonnegative vector exactly when some
strictly positive vector is orthogonal to all of `S`. Both are consequences of *Tucker's key
lemma*, which for each index `k` produces a nonnegative relation `x` and a functional `y` that is
nonnegative on the family, one of them strictly positive at `k`. Unlike Mathlib's
separation-based Farkas lemma `ProperCone.hyperplane_separation`, these results apply over `ℚ`.

For a subgroup `P` of `ι → ℤ` with `ι` finite, the condition that `P` contains no nonzero
nonnegative vector has two equivalent reformulations proved here:

* some vector of positive integer weights is orthogonal to `P`;
* every coset `D₀ + P` contains only finitely many nonnegative vectors.

The first is an integer-lattice form of Stiemke's theorem. The second is a finiteness consequence
of Dickson's lemma.

This is the combinatorial content of the admissibility lemmas of Heegaard Floer theory. For a
pointed Heegaard diagram, `ι` indexes the regions of the surface cut along the attaching curves,
a domain is a vector `ι → ℤ` of multiplicities, and `P` is the group of periodic domains (which
avoid the basepoint). Weak admissibility, in its form for all `Spin^c` structures at once, asks
that every nonzero periodic domain have both positive and negative multiplicities. Since `P` is
closed under negation, this is exactly the hypothesis of the theorems below. The weights provide
positive target areas for the regions, with zero signed area for every periodic domain.
Applying the finiteness theorem to Whitney disks requires a separate geometric correspondence
between disk classes and their domain vectors, including control of the fibers of that map.
The theorem itself counts nonnegative domain vectors in a coset of `P`.

## Main declarations

* `TauCeti.exists_nonneg_sum_smul_eq_zero_and_dual_nonneg`: Tucker's key lemma.
* `TauCeti.exists_forall_dual_pos_iff`: Gordan's theorem.
* `Submodule.exists_pos_dotProduct_eq_zero_iff`: Stiemke's theorem for a subspace of `ι → K`.
* `AddSubgroup.exists_pos_dotProduct_eq_zero_iff`: a subgroup of `ι → ℤ` has no nonzero
  nonnegative element iff it is orthogonal to a vector of positive integer weights.
* `AddSubgroup.finite_setOf_nonneg_sub_mem_iff`: a subgroup of `ι → ℤ` has no nonzero
  nonnegative element iff each of its cosets has only finitely many nonnegative elements.

## References

* A. W. Tucker, *Dual systems of homogeneous linear relations*, in *Linear Inequalities and
  Related Systems*, Annals of Mathematics Studies 38, 1956, Lemma 1.
* C. G. Broyden, *A simple algebraic proof of Farkas's lemma and related theorems*, Optimization
  Methods and Software 8 (1998).
* P. Ozsváth, Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. 159 (2004), [arXiv:math/0101206](https://arxiv.org/abs/math/0101206),
  Lemmas 4.12 and 4.13.
-/

public section

namespace TauCeti

variable {ι R K V : Type*}

/-- For a vector `c` of strictly positive weights and a nonnegative vector `x`, the pairing
`c ⬝ᵥ x` vanishes only when `x` does. -/
theorem dotProduct_eq_zero_iff_of_pos [Fintype ι] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [NoZeroDivisors R] {c x : ι → R} (hc : ∀ i, 0 < c i) (hx : 0 ≤ x) :
    c ⬝ᵥ x = 0 ↔ x = 0 := by
  refine ⟨fun h => funext fun i => ?_, fun h => by simp [h]⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hc j).le (hx j)).1 h i
    (Finset.mem_univ i)
  exact (mul_eq_zero.1 hterm).resolve_left (hc i).ne'

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V] [Module K V]

/-- Tucker's key lemma for the vectors indexed by `insert k s`. -/
private theorem exists_nonneg_sum_smul_eq_zero_and_dual_nonneg_of_finset [DecidableEq ι] (k : ι)
    (s : Finset ι) (a : ι → V) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, (∀ j ∈ insert k s, 0 ≤ x j ∧ 0 ≤ y (a j)) ∧
      ∑ j ∈ insert k s, x j • a j = 0 ∧ 0 < x k + y (a k) := by
  induction s using Finset.induction_on generalizing a with
  | empty =>
    by_cases ha : a k = 0
    · exact ⟨Pi.single k 1, 0, by simp, by simp [ha], by simp⟩
    · obtain ⟨y, hy⟩ := Module.Projective.exists_dual_eq_one K ha
      exact ⟨0, y, by simp [hy], by simp, by simp [hy]⟩
  | insert n s hn ih =>
    by_cases hnk : n = k
    · subst hnk
      simpa only [Finset.insert_idem] using ih a
    have hn' : n ∉ insert k s := by simp [hn, hnk]
    have hne : ∀ j ∈ insert k s, j ≠ n := fun j hj h => hn' (h ▸ hj)
    rw [Finset.insert_comm]
    obtain ⟨x, y, hxy, hsum, hpos⟩ := ih a
    by_cases hy : 0 ≤ y (a n)
    · -- `y` is already nonnegative on the new vector: extend `x` by zero.
      refine ⟨Function.update x n 0, y, ?_, ?_, ?_⟩
      · rintro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simp [hy]
        · simpa [Function.update_of_ne (hne j hj)] using hxy j hj
      · rw [Finset.sum_insert hn', Function.update_self, zero_smul, zero_add, ← hsum]
        exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
      · rwa [Function.update_of_ne (Ne.symm hnk)]
    · -- Otherwise project the old vectors along `a n` onto `ker y` and apply the induction
      -- hypothesis to the projected family `b j = a j + c j • a n`, where `y (b j) = 0`.
      push Not at hy
      set d := y (a n)
      have hd : d ≠ 0 := hy.ne
      set c : ι → K := fun j => -y (a j) / d
      have hc : ∀ j ∈ insert k s, 0 ≤ c j := fun j hj =>
        div_nonneg_of_nonpos (neg_nonpos.2 (hxy j hj).2) hy.le
      obtain ⟨u, z, huz, hsum', hpos'⟩ := ih fun j => a j + c j • a n
      set w : Module.Dual K V := z + (-z (a n) / d) • y
      have hw : ∀ j, w (a j) = z (a j + c j • a n) := fun j => by
        simp only [w, c, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
          smul_eq_mul]
        field_simp
      refine ⟨Function.update u n (∑ j ∈ insert k s, c j * u j), w, ?_, ?_, ?_⟩
      · rintro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · refine ⟨?_, ?_⟩
          · rw [Function.update_self]
            exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (huz i hi).1
          · simp only [w, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            rw [div_mul_cancel₀ _ hd, add_neg_cancel]
        · rw [Function.update_of_ne (hne j hj), hw]
          exact huz j hj
      · rw [Finset.sum_insert hn', Function.update_self, ← hsum', Finset.sum_smul]
        simp only [smul_add, smul_smul, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        · exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
        · exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
      · rw [Function.update_of_ne (Ne.symm hnk), hw]
        exact hpos'

/-- **Tucker's key lemma.** For a finite family of vectors `a j` and an index `k`, there are a
nonnegative linear relation `x` among the `a j` and a linear functional `y` that is nonnegative on
every `a j`, such that `x k + y (a k) > 0`: either `a k` occurs in a nonnegative relation, or some
functional nonnegative on the family is strictly positive on `a k`. -/
theorem exists_nonneg_sum_smul_eq_zero_and_dual_nonneg [Fintype ι] (a : ι → V) (k : ι) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, 0 ≤ x ∧ ∑ j, x j • a j = 0 ∧ (∀ j, 0 ≤ y (a j)) ∧
      0 < x k + y (a k) := by
  classical
  obtain ⟨x, y, hxy, hsum, hpos⟩ :=
    exists_nonneg_sum_smul_eq_zero_and_dual_nonneg_of_finset (K := K) k (Finset.univ.erase k) a
  rw [Finset.insert_erase (Finset.mem_univ k)] at hxy hsum
  exact ⟨x, y, fun j => (hxy j (Finset.mem_univ j)).1, hsum,
    fun j => (hxy j (Finset.mem_univ j)).2, hpos⟩

/-- **Gordan's theorem.** Some linear functional is strictly positive on every vector of a finite
family exactly when the only nonnegative linear relation among the vectors is the trivial one. -/
theorem exists_forall_dual_pos_iff [Fintype ι] (a : ι → V) :
    (∃ y : Module.Dual K V, ∀ j, 0 < y (a j)) ↔
      ∀ x : ι → K, 0 ≤ x → ∑ j, x j • a j = 0 → x = 0 := by
  constructor
  · rintro ⟨y, hy⟩ x hx hsum
    refine (dotProduct_eq_zero_iff_of_pos hy hx).1 ?_
    simpa [dotProduct, mul_comm] using congrArg y hsum
  · intro h
    choose x y hx hsum hy hpos using exists_nonneg_sum_smul_eq_zero_and_dual_nonneg (K := K) a
    refine ⟨∑ k, y k, fun j => ?_⟩
    rw [LinearMap.sum_apply]
    refine Finset.sum_pos' (fun k _ => hy k j) ⟨j, Finset.mem_univ j, ?_⟩
    simpa [h (x j) (hx j) (hsum j)] using hpos j

end Field

end TauCeti

open TauCeti

section Field

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Stiemke's theorem.** A subspace `S` of `ι → K` contains no nonzero nonnegative vector
exactly when some vector with strictly positive coordinates is orthogonal to all of `S`. -/
theorem Submodule.exists_pos_dotProduct_eq_zero_iff (S : Submodule K (ι → K)) :
    (∃ c : ι → K, (∀ i, 0 < c i) ∧ ∀ x ∈ S, c ⬝ᵥ x = 0) ↔ ∀ x ∈ S, 0 ≤ x → x = 0 := by
  classical
  constructor
  · rintro ⟨c, hc, hS⟩ x hx hx0
    exact (dotProduct_eq_zero_iff_of_pos hc hx0).1 (hS x hx)
  · intro h
    -- Apply Gordan's theorem to the images of the coordinate vectors in `(ι → K) ⧸ S`.
    have hmk : ∀ x : ι → K, ∑ j, x j • S.mkQ (Pi.single j 1) = S.mkQ x := fun x => by
      conv_rhs => rw [pi_eq_sum_univ' x]
      simp only [map_sum, map_smul]
    obtain ⟨y, hy⟩ := (exists_forall_dual_pos_iff fun j => S.mkQ (Pi.single j 1)).2
      fun x hx hsum => h x ((Submodule.Quotient.mk_eq_zero S).1 ((hmk x).symm.trans hsum)) hx
    refine ⟨fun j => y (S.mkQ (Pi.single j 1)), hy, fun x hx => ?_⟩
    have := congrArg y (hmk x)
    simp only [map_sum, map_smul, smul_eq_mul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero S).2 hx, map_zero] at this
    simpa [dotProduct, mul_comm] using this

end Field

section Int

variable {ι : Type*}

/-- An element of the rational span of a subgroup `P` of `ι → ℤ` becomes an element of `P` after
multiplication by some positive integer. -/
private theorem AddSubgroup.exists_nat_mul_eq_intCast_of_mem_span {P : AddSubgroup (ι → ℤ)}
    {x : ι → ℚ} (hx : x ∈ Submodule.span ℚ ((fun p : ι → ℤ => ((↑) : ℤ → ℚ) ∘ p) '' P)) :
    ∃ N : ℕ, 0 < N ∧ ∃ p ∈ P, ∀ i, (p i : ℚ) = N * x i := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨1, one_pos, p, hp, fun i => by simp⟩
  | zero => exact ⟨1, one_pos, 0, zero_mem P, fun i => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨M, hM, p, hp, hpy⟩ := hy
    obtain ⟨N, hN, q, hq, hqz⟩ := hz
    refine ⟨M * N, mul_pos hM hN, N • p + M • q, add_mem (nsmul_mem hp N) (nsmul_mem hq M),
      fun i => ?_⟩
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    push_cast [nsmul_eq_mul, hpy, hqz, Pi.add_apply]
    ring
  | smul r y _ hy =>
    obtain ⟨N, hN, p, hp, hpy⟩ := hy
    refine ⟨r.den * N, mul_pos r.den_pos hN, r.num • p, zsmul_mem hp r.num, fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, hpy, Nat.cast_mul]
    rw [← Rat.mul_den_eq_num]
    ring

/-- A subgroup `P` of `ι → ℤ` contains no nonzero nonnegative vector exactly when some vector of
strictly positive integer weights is orthogonal to all of `P`.

For the group of periodic domains of a pointed Heegaard diagram, the weights are the areas of the
regions for an area form in which every periodic domain has signed area zero; compare
Ozsváth–Szabó, *Holomorphic disks and topological invariants for closed three-manifolds*,
Lemma 4.12. -/
theorem AddSubgroup.exists_pos_dotProduct_eq_zero_iff [Fintype ι] (P : AddSubgroup (ι → ℤ)) :
    (∃ c : ι → ℤ, (∀ i, 0 < c i) ∧ ∀ p ∈ P, c ⬝ᵥ p = 0) ↔ ∀ p ∈ P, 0 ≤ p → p = 0 := by
  constructor
  · rintro ⟨c, hc, hP⟩ p hp hp0
    exact (dotProduct_eq_zero_iff_of_pos hc hp0).1 (hP p hp)
  · intro h
    set S := Submodule.span ℚ ((fun p : ι → ℤ => ((↑) : ℤ → ℚ) ∘ p) '' P)
    -- The rational span of `P` has no nonzero nonnegative vector either.
    have hS : ∀ x ∈ S, 0 ≤ x → x = 0 := by
      intro x hx hx0
      obtain ⟨N, hN, p, hp, hpx⟩ := AddSubgroup.exists_nat_mul_eq_intCast_of_mem_span hx
      have hp0 : p = 0 := h p hp fun i => by
        have : (0 : ℚ) ≤ p i := by
          rw [hpx]
          exact mul_nonneg (Nat.cast_nonneg N) (hx0 i)
        exact_mod_cast this
      funext i
      have := hpx i
      rw [hp0, Pi.zero_apply, Int.cast_zero, eq_comm, mul_eq_zero] at this
      exact this.resolve_left (Nat.cast_ne_zero.2 hN.ne')
    obtain ⟨c, hc, hcS⟩ := (S.exists_pos_dotProduct_eq_zero_iff).2 hS
    -- Clear the denominators of the rational weights.
    set N : ℕ := ∏ i, (c i).den
    have hN : 0 < N := Finset.prod_pos fun i _ => (c i).den_pos
    have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = N * c i := fun i => by
      obtain ⟨m, hm⟩ : (c i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨m * (c i).num, ?_⟩
      rw [hm]
      push_cast
      rw [← Rat.mul_den_eq_num]
      ring
    choose e he using hint
    refine ⟨e, fun i => ?_, fun p hp => ?_⟩
    · have : (0 : ℚ) < e i := by
        rw [he]
        exact mul_pos (Nat.cast_pos.2 hN) (hc i)
      exact_mod_cast this
    · have hcp := hcS _ (Submodule.subset_span ⟨p, hp, rfl⟩)
      have : ((e ⬝ᵥ p : ℤ) : ℚ) = N * (c ⬝ᵥ (((↑) : ℤ → ℚ) ∘ p)) := by
        simp only [dotProduct, Int.cast_sum, Int.cast_mul, he, Finset.mul_sum,
          Function.comp_apply, mul_assoc]
      rw [hcp, mul_zero] at this
      exact_mod_cast this

/-- A subgroup `P` of `ι → ℤ` contains no nonzero nonnegative vector exactly when each coset
`D₀ + P` contains only finitely many nonnegative vectors.

For the group of periodic domains of a pointed Heegaard diagram, this bounds the nonnegative domain
vectors in any coset. Applying the bound to Whitney disk classes also requires a geometric
correspondence between those classes and domain vectors; compare Ozsváth–Szabó, *Holomorphic disks
and topological invariants for closed three-manifolds*, Lemma 4.13. -/
theorem AddSubgroup.finite_setOf_nonneg_sub_mem_iff [Finite ι] (P : AddSubgroup (ι → ℤ)) :
    (∀ D₀ : ι → ℤ, {D | 0 ≤ D ∧ D - D₀ ∈ P}.Finite) ↔ ∀ p ∈ P, 0 ≤ p → p = 0 := by
  constructor
  · intro hfin p hp hp0
    by_contra hne
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℤ) • p)
      (fun m n hmn => Nat.cast_injective (smul_left_injective ℤ hne hmn))
      (fun n => ?_) (hfin 0)
    exact ⟨smul_nonneg (Nat.cast_nonneg n) hp0, by simpa using zsmul_mem hp n⟩
  · intro h D₀
    by_contra hinf
    -- Dickson's lemma: the nonnegative vectors of `ι → ℤ` are partially well-ordered.
    have hpwo : (Set.univ.pi fun _ : ι => Set.Ici (0 : ℤ)).IsPWO :=
      Set.IsPWO.pi fun _ => Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt bddBelow_Ici)
    set f := Set.Infinite.natEmbedding _ hinf
    obtain ⟨m, n, hmn, hle⟩ := hpwo.exists_lt (f := fun n => (f n : ι → ℤ))
      fun n i _ => (f n).2.1 i
    have hsub : (f n : ι → ℤ) - f m ∈ P := by
      simpa using sub_mem (f n).2.2 (f m).2.2
    have := h _ hsub (sub_nonneg.2 hle)
    exact hmn.ne (f.injective (Subtype.ext (sub_eq_zero.1 this).symm))

end Int
