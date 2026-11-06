/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.Algebra.TypeAHeckeAlgebra.SignedCheckedR
public import TauCeti.LinearAlgebra.Finsupp.ProductDensity
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Atomic tensor models of Markov traces on the type-A Hecke algebra

Let `ι` be a finite linearly ordered alphabet whose letters are designated positive or negative
by a predicate `pos`, and let `q : Rˣ`. Rescaling the signed checked R-matrix
`TauCeti.signedCheckedR pos q` by `q⁻¹` gives operators on the word space `(Fin n → ι) →₀ R`
satisfying the relations of the type-A Hecke algebra on `n` strands, in the convention
`T * T = (q - q⁻¹) • T + 1`. This is the representation
`TauCeti.TypeAHeckeAlgebra.signedChecked pos q`; in the generators `gᵢ = q • T i` it is
`gᵢ ↦ signedCheckedR pos q i (i + 1)`.

Given weights `p : ι → R`, the product density `TauCeti.productDensity p` multiplies a basis word
by the product of the weights of its letters. It commutes with the representation, because the
signed checked R-matrix only permutes the letters of a word. The *atomic trace*
`TauCeti.TypeAHeckeAlgebra.atomicTrace pos q p n` is `x ↦ tr (ρ(x) * D)`, the trace of the action
of `x` weighted by the density `D`. It is tracial, and adding an uncrossed last strand multiplies
it by the total weight `∑ a, p a`.

The Markov rule is a condition on the weights. In the diagonal coefficient of `ρ(x * T n)` at a
word ending in the letters `b, c`, only the colour-preserving part of the last crossing survives,
so the last letter `c` is summed against the *right slice* of the R-matrix at `b`,

`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (c > b), p c`.

When the weights sum to `1` and this slice equals `q * z` for every letter `b`, the atomic traces
on all the finite Hecke algebras are the restrictions of the Ocneanu trace with parameter `z`
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace`). For instance, `r + 1` positive letters
with weights proportional to `1, Q, …, Q ^ r`, `Q = q ^ 2`, realize the parameter
`z = q ^ (2 * r + 1) / [r + 1]_Q` (`TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_eq`); for a
single letter this is the index character `z = q`.

Positivity is not considered: everything here is algebraic, over any commutative ring.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.signedChecked`: the representation of the type-A Hecke algebra
  on the word space by the rescaled signed checked R-matrices.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace`: the weighted trace `x ↦ tr (ρ(x) * D)`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.commute_productDensity_signedChecked`: the density commutes with
  the representation.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_mul_comm`, `TauCeti.TypeAHeckeAlgebra.atomicTrace_one`
  and `TauCeti.TypeAHeckeAlgebra.atomicTrace_strandIncl`: the atomic trace is tracial, its value
  at `1`, and its behaviour under adding a strand.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_strandIncl_mul_T_last`: the Markov rule.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace`: **the atomic trace is the Ocneanu
  trace.**

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1, for the signed product model.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553, for weighted traces of enhanced Yang-Baxter operators.

The strand-inclusion and Markov computations follow the corresponding ones for the Jimbo
representation in `TauCeti.KnotTheory.Jimbo.StrandInclusion` and
`TauCeti.KnotTheory.Jimbo.Stabilization`.
-/

public section

open Function Finsupp

namespace TauCeti

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}

namespace TypeAHeckeAlgebra

variable [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ)

/-- The representation of the type-A Hecke algebra on `n` strands on the word space
`(Fin n → ι) →₀ R` in which the generator `T i` acts by `q⁻¹` times the signed checked R-matrix on
the strands `i` and `i + 1`. -/
noncomputable def signedChecked : TypeAHeckeAlgebra R q n →ₐ[R] Module.End R ((Fin n → ι) →₀ R) :=
  lift (fun i ↦ ((q⁻¹ : Rˣ) : R) •
      signedCheckedR pos (q : R) (BraidGroup.strand i) (BraidGroup.strandSucc i))
    (fun _ ↦ inv_smul_signedCheckedR_mul_self pos q _ _)
    (fun {i j} h ↦ by
      have hij : i ≠ j := by
        rintro rfl
        omega
      simp only [smul_mul_smul_comm]
      rw [BraidGroup.strand_eq_strandSucc_of_succ h,
        signedCheckedR_braid pos (q : R) (BraidGroup.strand_ne_strandSucc i)
          (BraidGroup.strandSucc_ne_strandSucc hij) (BraidGroup.strand_ne_strandSucc_of_succ h)])
    (fun h ↦ by
      rw [smul_mul_smul_comm, smul_mul_smul_comm, signedCheckedR_mul_comm pos (q : R)
        (BraidGroup.nodup_strand_strandSucc_strand_strandSucc (.inl h))])

/-- In the signed checked representation, the generator `T i` acts by `q⁻¹` times the signed
checked R-matrix on the strands `i` and `i + 1`. -/
@[simp]
theorem signedChecked_T (i : Fin (n - 1)) :
    signedChecked pos q (T q i) =
      ((q⁻¹ : Rˣ) : R) • signedCheckedR pos (q : R) (BraidGroup.strand i)
        (BraidGroup.strandSucc i) := by
  rw [signedChecked, lift_T]

/-- The product density commutes with every element in the signed checked representation. -/
theorem commute_productDensity_signedChecked (p : ι → R) (x : TypeAHeckeAlgebra R q n) :
    Commute (productDensity p) (signedChecked pos q x) := by
  have hx : signedChecked pos q x ∈
      Algebra.adjoin R (Set.range (signedChecked pos q ∘ T (n := n) q)) := by
    rw [Set.range_comp, ← AlgHom.map_adjoin, adjoin_range_T]
    exact ⟨x, trivial, rfl⟩
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_
  rintro _ ⟨i, rfl⟩
  simpa using (commute_productDensity_signedCheckedR pos p (q : R) _ _).smul_right _

/-- The action of an element after adding an uncrossed last strand is its original action with
the last letter held fixed. -/
@[simp]
theorem signedChecked_strandIncl_mapDomain_snoc (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    signedChecked pos q (strandIncl R q n x) (mapDomain (fun w ↦ Fin.snoc w a) v) =
      mapDomain (fun w ↦ Fin.snoc w a) (signedChecked pos q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.snoc w a : Fin (n + 1) → ι))
  suffices h : (signedChecked pos q (strandIncl R q n x)).comp L = L.comp (signedChecked pos q x)
    by simpa [L] using LinearMap.congr_fun h v
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hj : BraidGroup.strand (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
        (BraidGroup.strand i).castSucc := Fin.ext (by simp)
    have hk : BraidGroup.strandSucc (Fin.castLE (by omega) i : Fin (n + 1 - 1)) =
        (BraidGroup.strandSucc i).castSucc := Fin.ext (by simp)
    rw [strandIncl_T, signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
      hj, hk, signedCheckedR_comp_lmapDomain_snoc]
  | algebraMap r =>
    ext w : 2
    simp [L, Algebra.algebraMap_eq_smul_one]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_assoc, hy, ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc]

/-- Adding an uncrossed last strand preserves the coefficients within each block of words with a
fixed last letter, and has zero coefficients between blocks with different last letters. -/
theorem signedChecked_strandIncl_single_snoc_apply_snoc (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) :
    signedChecked pos q (strandIncl R q n x) (single (Fin.snoc w a) 1) (Fin.snoc u d) =
      if a = d then signedChecked pos q x (single w 1) u else 0 := by
  have h := signedChecked_strandIncl_mapDomain_snoc pos q x a (single w 1)
  rw [mapDomain_single] at h
  rw [h]
  by_cases had : a = d
  · subst d
    simp only [↓reduceIte]
    exact mapDomain_apply_of_injective (@Fin.snoc_left_injective _ (fun _ ↦ ι) a) _ _
  · simp only [had, ↓reduceIte]
    apply mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    apply had
    simpa using congrArg (fun z : Fin (n + 1) → ι ↦ z (Fin.last n)) hv

/-- In the diagonal coefficient of `x * T n`, at a word ending in the letters `w (Fin.last n)` and
`c`, only the colour-preserving part of the last crossing survives. -/
private theorem signedChecked_strandIncl_mul_T_last_single_snoc_apply
    (x : TypeAHeckeAlgebra R q (n + 1)) (w : Fin (n + 1) → ι) (c : ι) :
    signedChecked pos q (strandIncl R q (n + 1) x * T q (Fin.last n))
        (single (Fin.snoc w c) 1) (Fin.snoc w c) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
        (if w (Fin.last n) = c then (if pos c then (q : R) ^ 2 else -1)
          else if w (Fin.last n) < c then (q : R) ^ 2 - 1 else 0) := by
  have hj : BraidGroup.strand (Fin.last n : Fin (n + 2 - 1)) = (Fin.last n).castSucc :=
    Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.last n : Fin (n + 2 - 1)) = Fin.last (n + 1) :=
    Fin.ext (by simp)
  have hswap : Fin.snoc w c ∘ Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1)) =
      Fin.snoc (update w (Fin.last n) c) (w (Fin.last n)) := by
    rw [Equiv.comp_swap_eq_update]
    simp [← Fin.snoc_update, Fin.update_snoc_last]
  simp only [map_mul, mul_apply_eq_comp, signedChecked_T, hj, hk, LinearMap.smul_apply,
    signedCheckedR_single_one, Fin.snoc_castSucc, Fin.snoc_last, hswap]
  rcases lt_trichotomy (w (Fin.last n)) c with h | h | h
  · simp only [h.ne, h, ↓reduceIte, map_sub, map_smul, Finsupp.smul_apply, Finsupp.sub_apply,
      smul_eq_mul, signedChecked_strandIncl_single_snoc_apply_snoc]
    ring
  · subst h
    simp only [↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      signedChecked_strandIncl_single_snoc_apply_snoc]
    ring
  · simp only [h.ne.symm, h.not_gt, ↓reduceIte, map_neg, map_smul, Finsupp.smul_apply,
      Finsupp.neg_apply, smul_eq_mul, signedChecked_strandIncl_single_snoc_apply_snoc]
    ring

section Trace

variable (p : ι → R)

/-- The atomic trace `x ↦ tr (ρ(x) * D)` on the Hecke algebra on `n` strands, where `ρ` is the
signed checked representation and `D` is the product density of the weights `p`. -/
noncomputable def atomicTrace (n : ℕ) : TypeAHeckeAlgebra R q n →ₗ[R] R :=
  LinearMap.trace R ((Fin n → ι) →₀ R) ∘ₗ LinearMap.mulRight R (productDensity p) ∘ₗ
    (signedChecked pos q).toLinearMap

/-- The atomic trace is the trace of the action weighted by the product density. -/
theorem atomicTrace_apply (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n x =
      LinearMap.trace R ((Fin n → ι) →₀ R) (signedChecked pos q x * productDensity p) :=
  (rfl)

/-- The atomic trace is tracial. -/
theorem atomicTrace_mul_comm (x y : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n (x * y) = atomicTrace pos q p n (y * x) := by
  rw [atomicTrace_apply, atomicTrace_apply, map_mul (signedChecked pos q) x y,
    map_mul (signedChecked pos q) y x, mul_assoc,
    ← (commute_productDensity_signedChecked pos q p y).eq, ← mul_assoc,
    LinearMap.trace_mul_comm, mul_assoc]

variable [Fintype ι]

/-- The atomic trace is the sum of the diagonal coefficients times the weights of the words. -/
theorem atomicTrace_eq_sum (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n x =
      ∑ w : Fin n → ι, signedChecked pos q x (single w 1) w * ∏ i, p (w i) := by
  classical
  rw [atomicTrace_apply, LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, mul_apply_eq_comp,
    Finsupp.coe_basisSingleOne, productDensity_single_one, map_smul]
  simp [mul_comm]

/-- The atomic trace of `1` is the `n`-th power of the total weight. -/
@[simp]
theorem atomicTrace_one : atomicTrace pos q p n 1 = (∑ a, p a) ^ n := by
  classical
  rw [atomicTrace_eq_sum]
  simp only [map_one, one_apply_eq_self, single_eq_same, one_mul]
  rw [← Fintype.prod_sum]
  simp

/-- Adding an uncrossed last strand multiplies the atomic trace by the total weight. -/
@[simp]
theorem atomicTrace_strandIncl (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p (n + 1) (strandIncl R q n x) = atomicTrace pos q p n x * ∑ a, p a := by
  rw [atomicTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ι)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    signedChecked_strandIncl_single_snoc_apply_snoc, ite_true, Fin.prod_univ_castSucc (n := n),
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [atomicTrace_eq_sum, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

/-- The right slice of the R-matrix: summing the diagonal coefficient of the last crossing against
the weight of the last letter. -/
private theorem sum_slice (b : ι) :
    (∑ c, (if b = c then (if pos c then (q : R) ^ 2 else -1)
      else if b < c then (q : R) ^ 2 - 1 else 0) * p c) =
      (if pos b then (q : R) ^ 2 else -1) * p b + ((q : R) ^ 2 - 1) * ∑ c with b < c, p c := by
  classical
  have h (c : ι) : (if b = c then (if pos c then (q : R) ^ 2 else -1)
      else if b < c then (q : R) ^ 2 - 1 else 0) * p c =
      (if b = c then (if pos b then (q : R) ^ 2 else -1) * p b else 0) +
        (if b < c then ((q : R) ^ 2 - 1) * p c else 0) := by
    rcases lt_trichotomy b c with hbc | rfl | hbc
    · simp [hbc.ne, hbc]
    · simp
    · simp [hbc.ne', hbc.not_gt]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]

/-- **The Markov rule for the atomic trace.** If the right slice
`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (c > b), p c` equals `q * z` for every
letter `b`, then multiplying by the generator `T n` that adds the new last strand multiplies the
atomic trace by `z`. -/
theorem atomicTrace_strandIncl_mul_T_last {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ c with b < c, p c = q * z) (x : TypeAHeckeAlgebra R q (n + 1)) :
    atomicTrace pos q p (n + 2) (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      z * atomicTrace pos q p (n + 1) x := by
  rw [atomicTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ ι)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    signedChecked_strandIncl_mul_T_last_single_snoc_apply,
    Fin.prod_univ_castSucc (n := n + 1), Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_comm, atomicTrace_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hs := (sum_slice pos q p (w (Fin.last n))).trans (hz _)
  have hq : ((q⁻¹ : Rˣ) : R) * q = 1 := Units.inv_mul q
  calc _ = ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * (∏ i, p (w i)) *
        ∑ c, (if w (Fin.last n) = c then (if pos c then (q : R) ^ 2 else -1)
          else if w (Fin.last n) < c then (q : R) ^ 2 - 1 else 0) * p c := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        ring
    _ = _ := by
        rw [hs]
        linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * hq

/-- **The atomic trace is the Ocneanu trace.** If the weights sum to `1` and the right slice
`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (c > b), p c` equals `q * z` for every
letter `b`, then on the Hecke algebra on any number of strands the atomic trace is the Ocneanu
trace with parameter `z`, along the embedding into the infinite type-A Hecke algebra. -/
theorem atomicTrace_eq_ocneanuTrace {z : R} (hp : ∑ a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ c with b < c, p c = q * z) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  eq_ocneanuTrace_toInfinite (atomicTrace pos q p) (by simp)
    (fun _ _ ↦ by rw [atomicTrace_strandIncl, hp, mul_one]) (fun _ ↦ atomicTrace_mul_comm pos q p)
    (fun _ ↦ atomicTrace_strandIncl_mul_T_last pos q p hz) n x

end Trace

/-- **A geometric atomic model.** On `r + 1` positive letters with weights `c * Q ^ a`,
`Q = q ^ 2`, normalized by `c * [r + 1]_Q = 1`, the atomic trace is the Ocneanu trace with
parameter `z = c * q ^ (2 * r + 1)`. -/
theorem atomicTrace_geometric_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ True) q (fun a ↦ c * ((q : R) ^ 2) ^ (a : ℕ)) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * (q : R) ^ (2 * r + 1))
        (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc, Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a)]
  · -- The letters after `b` carry the geometric weights `Q ^ a`, `b < a ≤ r`.
    have hI : ∑ a : Fin (r + 1) with b < a, c * ((q : R) ^ 2) ^ (a : ℕ) =
        c * ∑ a ∈ Finset.Ico ((b : ℕ) + 1) (r + 1), ((q : R) ^ 2) ^ a := by
      rw [← Finset.mul_sum, Finset.sum_filter]
      congr 1
      simp only [Fin.lt_def]
      refine (Fin.sum_univ_eq_sum_range
        (fun a ↦ if (b : ℕ) < a then ((q : R) ^ 2) ^ a else 0) (r + 1)).trans ?_
      rw [← Finset.sum_filter]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    have hg := geom_sum_Ico_mul ((q : R) ^ 2) (show (b : ℕ) + 1 ≤ r + 1 by omega)
    simp only [↓reduceIte, hI]
    linear_combination c * hg

end TypeAHeckeAlgebra

end TauCeti
