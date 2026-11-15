/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Block
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.Tail
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
public import TauCeti.RingTheory.TraceFunctional.Positive
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Positivity, trace radicals, and first-site Markov rules for atomic models

For a star-fixed parameter `q : Rˣ` in a commutative star ring `R`, the type-A Hecke algebra
carries the real-parameter involution fixing every simple generator `T i` and conjugating scalars
(`TauCeti.TypeAHeckeAlgebra.instStarRing`). Because the signed checked R-matrix has symmetric
self-adjoint matrix entries in the standard word basis, the signed checked representation
`TauCeti.TypeAHeckeAlgebra.signedChecked` is Hermitian in that basis: the `(v, w)` matrix entry of
`star x` is the conjugate of the `(w, v)` entry of `x`
(`TauCeti.TypeAHeckeAlgebra.signedChecked_star_single_apply`). Consequently every diagonal entry of
`star x * x` is a finite sum of Hermitian squares `star c * c`
(`TauCeti.TypeAHeckeAlgebra.signedChecked_star_mul_self_single_apply`), without any finiteness
hypothesis on the alphabet.

On a finite alphabet over a `StarOrderedRing` with nonnegative weights `0 ≤ p a`, it follows that
the atomic trace is nonnegative on all algebraic squares `star x * x`
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg`), giving a `StarPositiveFunctional`
over `ℂ` (`TauCeti.TypeAHeckeAlgebra.atomicPositiveFunctional`). When the weights are strictly
positive and `R` has no zero divisors, a square has zero atomic trace if and only if it lies in the
kernel of the signed checked representation, identifying the finite-stage trace radical with that
representation kernel (`TauCeti.TypeAHeckeAlgebra.traceRadical_atomicTrace_eq_ker_signedChecked`).

This file also develops the first-site (`tailIncl`) counterpart of the last-site (`strandIncl`)
Markov rule of `TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic`. Prepending an uncrossed first
strand acts on words via `Fin.cons`, and summing the first crossing `T 0` against the prepended
letter produces the *left slice*

`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (a < b), p a`.

When the weights sum to `1` and every left slice equals `q * z`, the atomic trace again restricts
the Ocneanu trace with parameter `z`
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace_of_leftSlice`), proved via the cycle-word
recursion `tailIncl (cycleWord (m + 1)) * (q • T 0) = cycleWord (m + 2)` and separated-block
multiplicativity. Applying this to decreasing positive geometric weights `c * Q ^ (r - a)` and
increasing negative geometric weights `c * Q ^ a` realizes both halves `a_(r + 1)(Q)` and
`a_(-(r + 1))(Q)` of Wenzl's discrete series in the first-site R-order.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.atomicPositiveFunctional`: the complex atomic trace bundled as a
  `StarPositiveFunctional` when `0 ≤ p a`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.signedChecked_star_single_apply` and
  `TauCeti.TypeAHeckeAlgebra.signedChecked_star_mul_self_single_apply`: matrix adjointness and
  diagonal sum-of-squares formula for `signedChecked`.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg`: positivity of `atomicTrace` on
  `star x * x` over any commutative `StarOrderedRing`.
* `TauCeti.TypeAHeckeAlgebra.traceRadical_atomicTrace_eq_ker_signedChecked`: for strictly positive
  weights over a domain, the trace radical of `atomicTrace` is `RingHom.ker (signedChecked pos q)`.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_T_zero_mul_tailIncl` and
  `TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace_of_leftSlice`: the left-slice Markov rule
  and Ocneanu-trace identification.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_leftSlice_eq`,
  `TauCeti.TypeAHeckeAlgebra.atomicTrace_negGeometric_eq`, and
  `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_eigenprojection_negGeometric`: the positive
  and negative discrete geometric models in first-site R-order and their Wenzl parameters.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
-/

public section

open Function Finsupp
open scoped ComplexOrder

namespace TauCeti

section SignedCheckedR

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  {n : ℕ}

/-- For a self-adjoint parameter `s`, the matrix entries of `signedCheckedR` in the standard word
basis are Hermitian: conjugating the `(v, w)` entry gives the `(w, v)` entry. -/
theorem star_signedCheckedR_single_apply [StarRing R] {s : R} (hs : IsSelfAdjoint s)
    (j k : Fin n) (v w : Fin n → ι) :
    star (signedCheckedR pos s j k (single w 1) v) = signedCheckedR pos s j k (single v 1) w := by
  have hs₂ : star (s ^ 2) = s ^ 2 := by rw [star_pow, hs.star_eq]
  rw [signedCheckedR_single_apply_comm, signedCheckedR_single_one]
  split_ifs <;> simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.neg_apply, single_apply,
    smul_eq_mul, star_sub, star_neg, star_mul, hs.star_eq, hs₂, star_one] <;> split_ifs <;> simp

/-- Prepending a fixed first letter intertwines the signed checked R-matrix on two strands with
the one on the shifted strands `j.succ` and `k.succ`. -/
theorem signedCheckedR_comp_lmapDomain_cons (s : R) (j k : Fin n) (a : ι) :
    (signedCheckedR pos s j.succ k.succ).comp
        (lmapDomain R R (fun w : Fin n → ι ↦ Fin.cons a w)) =
      (lmapDomain R R (fun w : Fin n → ι ↦ Fin.cons a w)).comp (signedCheckedR pos s j k) :=
  signedCheckedR_comp_lmapDomain pos s _ (fun _ _ ↦ Fin.cons_succ ..) j k fun u ↦ by
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j).symm (Fin.succ_ne_zero k).symm]
    · rw [Function.comp_apply, ← (Fin.succ_injective n).map_swap j k i]
      simp

end SignedCheckedR

namespace TypeAHeckeAlgebra

section AdjointAndPositivity

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

omit [LinearOrder ι] in
private theorem end_apply_eq_finsupp_sum (f : Module.End R ((Fin n → ι) →₀ R))
    (g : (Fin n → ι) →₀ R) (v : Fin n → ι) :
    f g v = g.sum fun u r ↦ r * f (single u 1) v := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ =>
    rw [map_add, Finsupp.add_apply, h₁, h₂,
      Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)]
  | single u r =>
    rw [Finsupp.sum_single_index (zero_mul _), ← smul_single_one, map_smul, Finsupp.smul_apply,
      smul_eq_mul]

/-- **Hermitian matrix symmetry of the signed checked representation.** For a star-fixed unit `q`,
the `(v, w)` matrix entry of `signedChecked pos q (star x)` in the word basis is the conjugate of
the `(w, v)` matrix entry of `signedChecked pos q x`. No finiteness of `ι` is required. -/
theorem signedChecked_star_single_apply [StarRing R] [hq : Fact (IsSelfAdjoint (q : R))]
    (x : TypeAHeckeAlgebra R q n) (v w : Fin n → ι) :
    signedChecked pos q (star x) (single w 1) v =
      star (signedChecked pos q x (single v 1) w) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction generalizing v w with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hq_inv : IsSelfAdjoint ((q⁻¹ : Rˣ) : R) := by
      simpa only [Ring.inverse_unit] using hq.out.ringInverse
    rw [star_T, signedChecked_T, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul, star_mul, hq_inv.star_eq,
      star_signedCheckedR_single_apply pos hq.out, mul_comm]
  | algebraMap r =>
    rw [← algebraMap_star_comm, AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul, star_mul, single_apply, single_apply]
    by_cases hvw : v = w <;> simp [hvw, eq_comm]
  | add x y _ _ hx hy =>
    simp only [star_add, map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hy]
  | mul x y _ _ hx hy =>
    classical
    rw [star_mul, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp,
      end_apply_eq_finsupp_sum, end_apply_eq_finsupp_sum]
    set s := (signedChecked pos q (star x) (single w 1)).support ∪
      (signedChecked pos q y (single v 1)).support
    rw [Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (fun _ _ ↦ zero_mul _),
      Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (fun _ _ ↦ zero_mul _),
      star_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [hx u w, hy v u, star_mul, mul_comm]

/-- **Diagonal sum-of-squares formula.** Every diagonal matrix entry of `star x * x` in the signed
checked representation is the finite sum of `star c * c` over the words appearing in the column of
`x` at `w`. -/
theorem signedChecked_star_mul_self_single_apply [StarRing R] [Fact (IsSelfAdjoint (q : R))]
    (x : TypeAHeckeAlgebra R q n) (w : Fin n → ι) :
    signedChecked pos q (star x * x) (single w 1) w =
      ∑ u ∈ (signedChecked pos q x (single w 1)).support,
        star (signedChecked pos q x (single w 1) u) *
          signedChecked pos q x (single w 1) u := by
  rw [map_mul, mul_apply_eq_comp, end_apply_eq_finsupp_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [signedChecked_star_single_apply, mul_comm]

/-- Every diagonal matrix entry of `star x * x` in the signed checked representation over a
`StarOrderedRing` is nonnegative, on any (possibly infinite) linearly ordered alphabet. -/
theorem signedChecked_star_mul_self_single_apply_nonneg [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [Fact (IsSelfAdjoint (q : R))] (x : TypeAHeckeAlgebra R q n)
    (w : Fin n → ι) :
    0 ≤ signedChecked pos q (star x * x) (single w 1) w := by
  rw [signedChecked_star_mul_self_single_apply]
  exact Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _

/-- Conjugating an atomic trace conjugates the weights and applies the involution to the
argument. -/
theorem star_atomicTrace [StarRing R] [Fact (IsSelfAdjoint (q : R))] [Finite ι] (p : ι → R)
    (x : TypeAHeckeAlgebra R q n) :
    star (atomicTrace pos q p n x) = atomicTrace pos q (star ∘ p) n (star x) := by
  cases nonempty_fintype ι
  rw [atomicTrace_eq_sum, atomicTrace_eq_sum, star_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [star_mul, mul_comm, star_prod, signedChecked_star_single_apply]
  rfl

/-- For self-adjoint weights, the atomic trace preserves the real-parameter involution. -/
@[simp]
theorem atomicTrace_star [StarRing R] [Fact (IsSelfAdjoint (q : R))] [Finite ι] {p : ι → R}
    (hp : ∀ a, IsSelfAdjoint (p a)) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n (star x) = star (atomicTrace pos q p n x) := by
  rw [star_atomicTrace]
  congr 2
  ext a
  exact (hp a).star_eq.symm

private theorem prod_nonneg_of_starOrderedRing [PartialOrder R] [StarRing R] [StarOrderedRing R]
    {α : Type*} (s : Finset α) {f : α → R} (hf : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ ∏ i ∈ s, f i := by
  classical
  let : StarModule R R := ⟨fun r x ↦ by simp [star_mul, mul_comm]⟩
  induction s using Finset.induction with
  | empty => exact zero_le_one
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    exact smul_nonneg (hf a (Finset.mem_insert_self a s))
      (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

/-- **Positivity of finite atomic traces.** Over any commutative `StarOrderedRing` with a
star-fixed parameter `q` and nonnegative weights `0 ≤ p a`, the atomic trace is nonnegative on
every square `star x * x`. -/
theorem atomicTrace_star_mul_self_nonneg [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Fact (IsSelfAdjoint (q : R))] [Finite ι] {p : ι → R} (hp : ∀ a, 0 ≤ p a)
    (x : TypeAHeckeAlgebra R q n) :
    0 ≤ atomicTrace pos q p n (star x * x) := by
  cases nonempty_fintype ι
  let : StarModule R R := ⟨fun r y ↦ by simp [star_mul, mul_comm]⟩
  rw [atomicTrace_eq_sum]
  refine Finset.sum_nonneg fun w _ ↦ ?_
  exact smul_nonneg (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
    (prod_nonneg_of_starOrderedRing Finset.univ fun i _ ↦ hp (w i))

/-- **Null space of a strictly positive atomic trace.** Over a domain that is a `StarOrderedRing`,
if every letter carries strictly positive weight `0 < p a`, then `atomicTrace (star x * x) = 0`
if and only if `x` acts by zero in the signed checked representation. -/
theorem atomicTrace_star_mul_self_eq_zero_iff [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [NoZeroDivisors R] [Fact (IsSelfAdjoint (q : R))] [Finite ι] {p : ι → R}
    (hp : ∀ a, 0 < p a) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n (star x * x) = 0 ↔ signedChecked pos q x = 0 := by
  cases nonempty_fintype ι
  let : StarModule R R := ⟨fun r y ↦ by simp [star_mul, mul_comm]⟩
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rcases subsingleton_or_nontrivial R with _ | _
    · exact Subsingleton.elim _ _
    rw [atomicTrace_eq_sum] at hx
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦
      smul_nonneg (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
        (prod_nonneg_of_starOrderedRing Finset.univ fun i _ ↦ (hp (w i)).le)).mp hx
    ext w u
    simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, LinearMap.zero_apply,
      Finsupp.coe_zero, Pi.zero_apply]
    have hprod : (∏ i, p (w i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hp (w i)).ne'
    have hdiag : signedChecked pos q (star x * x) (single w 1) w = 0 :=
      (mul_eq_zero.mp (hterm w (Finset.mem_univ w))).resolve_right hprod
    rw [signedChecked_star_mul_self_single_apply] at hdiag
    have hcol := (Finset.sum_eq_zero_iff_of_nonneg fun v _ ↦ star_mul_self_nonneg _).mp hdiag
    by_contra hne
    have hsq := hcol u (Finsupp.mem_support_iff.mpr hne)
    exact hne ((mul_eq_zero.mp hsq).elim star_eq_zero.mp id)
  · rw [atomicTrace_apply, map_mul (signedChecked pos q), hx, mul_zero, zero_mul, map_zero]

/-- **Trace radical of a strictly positive atomic model.** When all weights are strictly positive
and `R` has no zero divisors, the two-sided trace radical of the atomic trace on `n` strands is the
kernel of the signed checked representation. -/
theorem traceRadical_atomicTrace_eq_ker_signedChecked [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [NoZeroDivisors R] [Fact (IsSelfAdjoint (q : R))] [Finite ι]
    {p : ι → R} (hp : ∀ a, 0 < p a) (n : ℕ) :
    (atomicTrace pos q p n).traceRadical (atomicTrace_mul_comm pos q p) =
      RingHom.ker (signedChecked pos q) := by
  ext x
  simp only [LinearMap.mem_traceRadical, RingHom.mem_ker]
  refine ⟨fun hx ↦ (atomicTrace_star_mul_self_eq_zero_iff pos q hp x).mp ?_, fun hx y ↦ ?_⟩
  · rw [atomicTrace_mul_comm]
    exact hx (star x)
  · rw [atomicTrace_apply, map_mul (signedChecked pos q), hx, zero_mul, zero_mul, map_zero]

/-- The complex atomic trace on `n` strands bundled as a `StarPositiveFunctional`, for a
star-fixed (real nonzero) parameter `q : ℂˣ` and nonnegative weights `0 ≤ p a`. -/
noncomputable def atomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := atomicTrace pos q p n
  square_nonneg := atomicTrace_star_mul_self_nonneg pos q hp

@[simp]
theorem atomicPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n) :
    atomicPositiveFunctional pos q hp n x = atomicTrace pos q p n x :=
  (rfl)

end AdjointAndPositivity

section LeftSlice

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

/-- Prepending an uncrossed first strand via `tailIncl` acts on words by holding the first letter
fixed and acting on the remaining `n` letters. -/
@[simp]
theorem signedChecked_tailIncl_mapDomain_cons (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    signedChecked pos q (tailIncl q n x) (mapDomain (fun w ↦ Fin.cons a w) v) =
      mapDomain (fun w ↦ Fin.cons a w) (signedChecked pos q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.cons a w : Fin (n + 1) → ι))
  suffices h : (signedChecked pos q (tailIncl q n x)).comp L = L.comp (signedChecked pos q x) by
    simpa [L] using LinearMap.congr_fun h v
  refine signedChecked_comp_eq_of_forall_T pos q _ L (fun i ↦ ?_) x
  have hj : BraidGroup.strand (⟨i + 1, by omega⟩ : Fin (n + 1 - 1)) =
      (BraidGroup.strand i).succ := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (⟨i + 1, by omega⟩ : Fin (n + 1 - 1)) =
      (BraidGroup.strandSucc i).succ := Fin.ext (by simp)
  rw [tailIncl_T, signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
    hj, hk, signedCheckedR_comp_lmapDomain_cons]

/-- Prepending an uncrossed first strand preserves matrix entries within each block of words with a
fixed first letter, and has zero entries between blocks with distinct first letters. -/
theorem signedChecked_tailIncl_single_cons_apply_cons (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) :
    signedChecked pos q (tailIncl q n x) (single (Fin.cons a w) 1) (Fin.cons d u) =
      if a = d then signedChecked pos q x (single w 1) u else 0 := by
  have h := signedChecked_tailIncl_mapDomain_cons pos q x a (single w 1)
  rw [mapDomain_single] at h
  rw [h]
  by_cases had : a = d
  · subst d
    simp only [↓reduceIte]
    exact mapDomain_apply_of_injective (@Fin.cons_right_injective _ (fun _ ↦ ι) a) _ _
  · simp only [had, ↓reduceIte]
    apply mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    exact had (by simpa using congrArg (fun z : Fin (n + 1) → ι ↦ z 0) hv)

/-- In the diagonal coefficient of `tailIncl x * T 0` at a word `Fin.cons a w` starting with `a`
and `w 0`, only the first-letter-preserving part of `T 0` survives. -/
theorem signedChecked_tailIncl_mul_T_zero_single_cons_apply
    (x : TypeAHeckeAlgebra R q (n + 1)) (a : ι) (w : Fin (n + 1) → ι) :
    signedChecked pos q (tailIncl q (n + 1) x * T q (0 : Fin (n + 1)))
        (single (Fin.cons a w) 1) (Fin.cons a w) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
        (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) := by
  have hj : BraidGroup.strand (n := n + 2) (0 : Fin (n + 1)) = 0 := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (n := n + 2) (0 : Fin (n + 1)) = (0 : Fin (n + 1)).succ :=
    Fin.ext (by simp)
  have hswap : Fin.cons a w ∘ Equiv.swap (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ =
      Fin.cons (w 0) (update w 0 a) := by
    funext i
    refine Fin.cases (by simp) (fun i ↦ ?_) i
    rcases eq_or_ne i 0 with rfl | hi
    · simp
    · have his : i.succ ≠ (0 : Fin (n + 1)).succ := Fin.succ_injective _ |>.ne hi
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) his]
      simp [hi]
  simp only [map_mul, mul_apply_eq_comp, signedChecked_T, hj, hk, LinearMap.smul_apply,
    signedCheckedR_single_one, Fin.cons_zero, Fin.cons_succ, hswap]
  rcases lt_trichotomy a (w 0) with h | h | h
  · simp only [h.ne, h.ne', h, ↓reduceIte, map_sub, map_smul, Finsupp.smul_apply,
      Finsupp.sub_apply, smul_eq_mul, signedChecked_tailIncl_single_cons_apply_cons]
    ring
  · subst h
    simp only [↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      signedChecked_tailIncl_single_cons_apply_cons]
    ring
  · simp only [h.ne, h.ne', h.not_gt, ↓reduceIte, map_neg, map_smul, Finsupp.smul_apply,
      Finsupp.neg_apply, smul_eq_mul, signedChecked_tailIncl_single_cons_apply_cons]
    ring

/-- Adding an uncrossed first strand multiplies the atomic trace by the total weight. -/
@[simp]
theorem atomicTrace_tailIncl [Fintype ι] (p : ι → R) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p (n + 1) (tailIncl q n x) = atomicTrace pos q p n x * ∑ a, p a := by
  rw [← strandCycleConj_strandIncl, strandCycleConj_apply, mul_assoc, atomicTrace_mul_comm,
    mul_assoc, Units.inv_mul, mul_one, atomicTrace_strandIncl]

private theorem sum_leftSlice [Fintype ι] (p : ι → R) (b : ι) :
    (∑ a, (if a = b then (if pos b then (q : R) ^ 2 else -1)
      else if a < b then (q : R) ^ 2 - 1 else 0) * p a) =
      (if pos b then (q : R) ^ 2 else -1) * p b + ((q : R) ^ 2 - 1) * ∑ a with a < b, p a := by
  classical
  have h (a : ι) : (if a = b then (if pos b then (q : R) ^ 2 else -1)
      else if a < b then (q : R) ^ 2 - 1 else 0) * p a =
      (if a = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0) +
        (if a < b then ((q : R) ^ 2 - 1) * p a else 0) := by
    rcases lt_trichotomy a b with hab | rfl | hab
    · simp [hab.ne, hab]
    · simp
    · simp [hab.ne', hab.not_gt]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]

/-- **The first-site (left-slice) Markov rule for the atomic trace.** If the left slice
`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (a < b), p a` equals `q * z` for every
letter `b`, then multiplying a shifted-tail element by `T 0` multiplies the atomic trace by `z`. -/
theorem atomicTrace_T_zero_mul_tailIncl [Fintype ι] (p : ι → R) {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ a with a < b, p a = q * z)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    atomicTrace pos q p (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) =
      z * atomicTrace pos q p (n + 1) x := by
  rw [atomicTrace_mul_comm, atomicTrace_eq_sum,
    ← (Fin.consEquiv (fun _ : Fin (n + 2) ↦ ι)).sum_comp]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    signedChecked_tailIncl_mul_T_zero_single_cons_apply]
  simp_rw [Fin.prod_univ_succ (n := n + 1), Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_comm, atomicTrace_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hs := (sum_leftSlice pos q p (w 0)).trans (hz _)
  have hq : ((q⁻¹ : Rˣ) : R) * q = 1 := Units.inv_mul q
  calc _ = ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * (∏ i, p (w i)) *
        ∑ a, (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) * p a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = _ := by
        rw [hs]
        linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * hq

/-- Appending `g_0 = q • T 0` on the right of the shifted cycle word `tailIncl (cycleWord (m + 1))`
produces `cycleWord (m + 2)`. -/
theorem tailIncl_cycleWord_mul_smul_T_zero {q : Rˣ} (m : ℕ) :
    tailIncl q (m + 1) (cycleWord q (m + 1)) * ((q : R) • T q (0 : Fin (m + 1))) =
      cycleWord q (m + 2) := by
  refine toInfinite_injective R q (m + 2) ?_
  rw [map_mul, toInfinite_tailIncl, toInfinite_cycleWord, toInfinite_cycleWord, map_smul,
    toInfinite_T, Fin.val_zero, InfiniteTypeAHeckeAlgebra.cycleWord_def,
    InfiniteTypeAHeckeAlgebra.cycleWord_def]
  simp [InfiniteTypeAHeckeAlgebra.shift_cosetRep,
    InfiniteTypeAHeckeAlgebra.cosetRep_succ_mul_T (Nat.zero_lt_succ m), pow_succ, mul_smul,
    mul_comm]

/-- **First-site Markov towers are restrictions of the Ocneanu trace.** A tracial,
block-multiplicative family of functionals `φ n` normalized on `0` and `1` strands and satisfying
`φ (n + 2) (T 0 * tailIncl x) = z * φ (n + 1) x` agrees with `ocneanuTrace R q z` along
`toInfinite` on every finite Hecke algebra. -/
theorem eq_ocneanuTrace_toInfinite_of_T_zero_mul_tailIncl {q : Rˣ} {z : R}
    (φ : ∀ n, TypeAHeckeAlgebra R q n →ₗ[R] R)
    (h_zero : φ 0 1 = 1) (h_one : φ 1 1 = 1)
    (h_comm : ∀ n x y, φ n (x * y) = φ n (y * x))
    (h_block : ∀ a b x y, φ (a + b) (castAdd R q a b x * natAdd R q a b y) = φ a x * φ b y)
    (h_left : ∀ n x, φ (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) = z * φ (n + 1) x)
    (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    φ n x = InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) := by
  have hτ := InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace (R := R) (q := q) z
  let ψ : ∀ m, TypeAHeckeAlgebra R q m →ₗ[R] R := fun m ↦
    (InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z).comp (toInfinite R q m).toLinearMap
  have hψm (a b : ℕ) (u : TypeAHeckeAlgebra R q a) (v : TypeAHeckeAlgebra R q b) :
      ψ (a + b) (castAdd R q a b u * natAdd R q a b v) = ψ a u * ψ b v := by
    simp only [ψ, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, toInfinite_castAdd,
      toInfinite_natAdd]
    exact hτ.map_mul_shift (by rw [← range_toInfinite]; exact ⟨u, rfl⟩) _
  have hcyc : ∀ m, φ m (cycleWord q m) = ψ m (cycleWord q m) := by
    intro m
    induction m with
    | zero => simpa [ψ] using h_zero
    | succ m ih =>
      rcases m with _ | m
      · simpa [ψ] using h_one
      · simp only [ψ, LinearMap.comp_apply, AlgHom.toLinearMap_apply, toInfinite_cycleWord,
          hτ.map_cycleWord, Nat.add_sub_cancel] at ih ⊢
        rw [← tailIncl_cycleWord_mul_smul_T_zero m, mul_smul_comm, map_smul, h_comm, h_left, ih,
          smul_eq_mul]
        ring
  exact DFunLike.congr_fun (trace_eq_of_cycleWord_values h_comm
    (fun m u v ↦ by simp [ψ, hτ.map_mul_comm]) h_block hψm hcyc n) x

/-- **The atomic trace with scalar left slice is the Ocneanu trace.** If `∑ a, p a = 1` and every
left slice equals `q * z`, then on every finite Hecke algebra the atomic trace restricts the
Ocneanu trace with parameter `z`. -/
theorem atomicTrace_eq_ocneanuTrace_of_leftSlice [Fintype ι] (p : ι → R) {z : R}
    (hp : ∑ a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ a with a < b, p a = q * z)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  eq_ocneanuTrace_toInfinite_of_T_zero_mul_tailIncl (atomicTrace pos q p)
    (by simp) (by simp [hp]) (fun _ ↦ atomicTrace_mul_comm pos q p)
    (fun _ _ ↦ atomicTrace_castAdd_mul_natAdd pos q p)
    (fun _ ↦ atomicTrace_T_zero_mul_tailIncl pos q p hz) n x

/-- **Positive discrete geometric model in first-site R-order.** On `r + 1` positive letters with
decreasing geometric weights `p a = c * Q ^ (r - a)`, `Q = q ^ 2`, normalized by
`c * [r + 1]_Q = 1`, every left slice equals `c * Q ^ (r + 1)` and the atomic trace is the Ocneanu
trace with parameter `z = c * q ^ (2 * r + 1)`. -/
theorem atomicTrace_geometric_leftSlice_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ True) q (fun a ↦ c * ((q : R) ^ 2) ^ (r - (a : ℕ))) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * (q : R) ^ (2 * r + 1))
        (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace_of_leftSlice _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc]
    congr 1
    refine (Fintype.sum_equiv Fin.revPerm _ (fun a : Fin (r + 1) ↦ ((q : R) ^ 2) ^ (a : ℕ))
      fun a ↦ ?_).trans (Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a) (r + 1))
    simp only [Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  · have hI : ∑ a : Fin (r + 1) with a < b, c * ((q : R) ^ 2) ^ (r - (a : ℕ)) =
        c * ∑ k ∈ Finset.Ico ((r - (b : ℕ)) + 1) (r + 1), ((q : R) ^ 2) ^ k := by
      rw [← Finset.mul_sum, Finset.sum_filter]
      congr 1
      refine (Fintype.sum_equiv Fin.revPerm _
        (fun k : Fin (r + 1) ↦ if r - (k : ℕ) < (b : ℕ) then ((q : R) ^ 2) ^ (k : ℕ) else 0)
        fun a ↦ ?_).trans ?_
      · simp only [Fin.revPerm_apply, Fin.lt_def, Fin.val_rev]
        have h1 : r + 1 - ((a : ℕ) + 1) = r - (a : ℕ) := by omega
        have h2 : r - (r - (a : ℕ)) = (a : ℕ) := by omega
        simp only [h1, h2]
      · refine (Fin.sum_univ_eq_sum_range
          (fun k ↦ if r - k < (b : ℕ) then ((q : R) ^ 2) ^ k else 0) (r + 1)).trans ?_
        rw [← Finset.sum_filter]
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
    have hg := geom_sum_Ico_mul ((q : R) ^ 2) (show (r - (b : ℕ)) + 1 ≤ r + 1 by omega)
    rw [pow_succ' ((q : R) ^ 2) (r - (b : ℕ))] at hg
    have hpow : (q : R) * ((q : R) ^ (2 * r + 1)) = ((q : R) ^ 2) ^ (r + 1) := by ring
    simp only [↓reduceIte, hI]
    linear_combination c * hg - c * hpow

/-- **Negative discrete geometric model in first-site R-order.** On `r + 1` negative letters with
increasing geometric weights `p a = c * Q ^ a`, `Q = q ^ 2`, normalized by `c * [r + 1]_Q = 1`,
every left slice equals `-c` and the atomic trace is the Ocneanu trace with parameter
`z = -(c * q⁻¹)`. -/
theorem atomicTrace_negGeometric_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ False) q (fun a ↦ c * ((q : R) ^ 2) ^ (a : ℕ)) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (-(c * ↑q⁻¹)) (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace_of_leftSlice _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc, Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a)]
  · have hI : ∑ a : Fin (r + 1) with a < b, c * ((q : R) ^ 2) ^ (a : ℕ) =
        c * ∑ a ∈ Finset.range (b : ℕ), ((q : R) ^ 2) ^ a := by
      rw [← Finset.mul_sum, Finset.sum_filter]
      congr 1
      refine (Fin.sum_univ_eq_sum_range
        (fun a ↦ if a < (b : ℕ) then ((q : R) ^ 2) ^ a else 0) (r + 1)).trans ?_
      rw [← Finset.sum_filter]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    have hg := geom_sum_mul ((q : R) ^ 2) (b : ℕ)
    have hq : (q : R) * ↑q⁻¹ = 1 := Units.mul_inv q
    simp only [↓reduceIte, hI]
    linear_combination c * hg + c * hq

end LeftSlice

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

/-- **The projection parameter of a negative geometric atomic model.** Let `Q = q ^ 2` and
`c * [r + 1]_Q = 1`. The Ocneanu trace with parameter `z = -(c * q⁻¹)`, which the atomic model on
`r + 1` negative letters with weights `c * Q ^ a` realizes
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_negGeometric_eq`), has native projection parameter
`a_(-(r + 1))(Q)` (so Wenzl's complementary projection parameter is `a_(r + 1)(Q)`). -/
theorem ocneanuTrace_mul_eigenprojection_negGeometric {K : Type*} [Field K] {q : Kˣ} (s : Kˣ)
    (hs : (s : K) = q + ↑q⁻¹) {r : ℕ} {c : K}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : K) ^ 2) ^ a = 1) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra K q} (hx : x ∈ stage K q (n + 1)) :
    ocneanuTrace K q (-(c * ↑q⁻¹))
        (x * (↑s⁻¹ : K) • (T q n + algebraMap K _ (↑q⁻¹ : K))) =
      wenzlParam (-((r + 1 : ℕ) : ℤ)) ((q : K) ^ 2) *
        ocneanuTrace K q (-(c * ↑q⁻¹)) x := by
  refine (isMarkovTrace_ocneanuTrace _).map_mul_eigenprojection s hs ?_ hx
  have hq : (q : K) ≠ 0 := q.ne_zero
  have hZ : ∑ a ∈ Finset.range (r + 1), ((q : K) ^ 2) ^ a ≠ 0 := right_ne_zero_of_mul_eq_one hc
  have hQ : 1 + (q : K) ^ 2 ≠ 0 := by
    rw [show 1 + (q : K) ^ 2 = q * s by rw [hs, Units.val_inv_eq_inv_val]; field_simp; ring]
    exact mul_ne_zero hq s.ne_zero
  rw [wenzlParam_neg_natCast, Nat.add_sub_cancel, Units.val_inv_eq_inv_val]
  have hg : ∑ a ∈ Finset.range (r + 1), ((q : K) ^ 2) ^ a =
      (q : K) ^ 2 * ∑ a ∈ Finset.range r, ((q : K) ^ 2) ^ a + 1 := by
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
    congr 1
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  field_simp
  linear_combination (1 + (q : K) ^ 2) * hg - (1 + (q : K) ^ 2) * hc

end InfiniteTypeAHeckeAlgebra

end TauCeti
