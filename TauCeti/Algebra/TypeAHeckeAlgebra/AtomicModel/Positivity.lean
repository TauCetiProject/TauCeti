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
import TauCeti.Algebra.Order.Star.Basic
import TauCeti.LinearAlgebra.Finsupp.LSum

/-!
# Positivity, trace radicals, and first-site Markov rules for atomic models

For a star-fixed parameter `q : Rˣ` in a commutative star ring `R`, `signedChecked` is Hermitian
in the word basis (`signedChecked_star_single_apply`), so every diagonal entry of `star x * x` is a
finite sum of squares `star c * c` (`signedChecked_star_mul_self_single_apply`). Over a
`StarOrderedRing` with `0 ≤ p a`, the atomic trace is `⋆`-positive
(`atomicTrace_star_mul_self_nonneg`, bundled over `ℂ` as `atomicPositiveFunctional`), and for
strictly positive weights over a domain its trace radical is `RingHom.ker (signedChecked pos q)`
(`traceRadical_atomicTrace_eq_ker_signedChecked`).

We also prove the first-site (`tailIncl`) Markov rule (`atomicTrace_T_zero_mul_tailIncl`): if the
*left slice* `(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (a < b), p a` equals `q * z`
and `∑ a, p a = 1`, then `atomicTrace` restricts `ocneanuTrace R q z`
(`atomicTrace_eq_ocneanuTrace_of_leftSlice`). Decreasing positive and increasing negative geometric
weights (`atomicTrace_geometric_leftSlice_eq`, `atomicTrace_negGeometric_eq`,
`ocneanuTrace_mul_eigenprojection_negGeometric`) realize both halves `a_(±(r + 1))(Q)` of Wenzl's
discrete series.

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

/-- For self-adjoint `s`, `signedCheckedR pos s j k` is Hermitian in the word basis. -/
theorem star_signedCheckedR_single_apply [StarRing R] {s : R} (hs : IsSelfAdjoint s)
    (j k : Fin n) (v w : Fin n → ι) :
    star (signedCheckedR pos s j k (single w 1) v) = signedCheckedR pos s j k (single v 1) w := by
  have hs₂ : star (s ^ 2) = s ^ 2 := by rw [star_pow, hs.star_eq]
  rw [signedCheckedR_single_apply_comm, signedCheckedR_single_one]
  split_ifs <;> simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.neg_apply, single_apply,
    smul_eq_mul, star_sub, star_neg, star_mul, hs.star_eq, hs₂, star_one] <;> split_ifs <;> simp

/-- Prepending a fixed first letter intertwines `signedCheckedR` with its shifted counterpart. -/
theorem signedCheckedR_comp_lmapDomain_cons (s : R) (j k : Fin n) (a : ι) :
    (signedCheckedR pos s j.succ k.succ).comp
        (lmapDomain R R (fun w : Fin n → ι ↦ Fin.cons a w)) =
      (lmapDomain R R (fun w : Fin n → ι ↦ Fin.cons a w)).comp (signedCheckedR pos s j k) :=
  signedCheckedR_comp_lmapDomain pos s _ (fun _ _ ↦ Fin.cons_succ ..) j k fun u ↦ funext <|
    Fin.cases (by simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j).symm
      (Fin.succ_ne_zero k).symm]) fun i ↦ by
      rw [comp_apply, ← (Fin.succ_injective n).map_swap j k i]; simp

end SignedCheckedR

namespace TypeAHeckeAlgebra

section AdjointAndPositivity

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

/-- **Hermitian matrix symmetry of `signedChecked`** for a star-fixed unit `q`. -/
theorem signedChecked_star_single_apply [StarRing R] [hq : Fact (IsSelfAdjoint (q : R))]
    (x : TypeAHeckeAlgebra R q n) (v w : Fin n → ι) :
    signedChecked pos q (star x) (single w 1) v =
      star (signedChecked pos q x (single v 1) w) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by rw [adjoin_range_T]; trivial
  induction hx using Algebra.adjoin_induction generalizing v w with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hq_inv : IsSelfAdjoint ((q⁻¹ : Rˣ) : R) := by
      simpa only [Ring.inverse_unit] using hq.out.ringInverse
    simp only [star_T, signedChecked_T, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      star_mul, hq_inv.star_eq, star_signedCheckedR_single_apply pos hq.out, mul_comm]
  | algebraMap r =>
    simp only [← algebraMap_star_comm, AlgHom.commutes, Module.algebraMap_end_apply,
      Finsupp.smul_apply, smul_eq_mul, star_mul, single_apply]
    by_cases hvw : v = w <;> simp [hvw, eq_comm]
  | add _ _ _ _ hx hy =>
    simp only [star_add, map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hy]
  | mul x y _ _ hx hy =>
    classical
    rw [star_mul, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp,
      LinearMap.apply_apply_eq_finsuppSum_mul, LinearMap.apply_apply_eq_finsuppSum_mul]
    simp_rw [RingHom.id_apply]
    set s := (signedChecked pos q (star x) (single w 1)).support ∪
      (signedChecked pos q y (single v 1)).support
    rw [Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (fun _ _ ↦ zero_mul _),
      Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (fun _ _ ↦ zero_mul _), star_sum]
    exact Finset.sum_congr rfl fun u _ ↦ by rw [hx u w, hy v u, star_mul, mul_comm]

/-- **Diagonal sum-of-squares formula** for `signedChecked pos q (star x * x)`. -/
theorem signedChecked_star_mul_self_single_apply [StarRing R] [Fact (IsSelfAdjoint (q : R))]
    (x : TypeAHeckeAlgebra R q n) (w : Fin n → ι) :
    signedChecked pos q (star x * x) (single w 1) w =
      ∑ u ∈ (signedChecked pos q x (single w 1)).support,
        star (signedChecked pos q x (single w 1) u) *
          signedChecked pos q x (single w 1) u := by
  rw [map_mul, mul_apply_eq_comp, LinearMap.apply_apply_eq_finsuppSum_mul, Finsupp.sum]
  exact Finset.sum_congr rfl fun u _ ↦ by
    rw [RingHom.id_apply, signedChecked_star_single_apply, mul_comm]

/-- Every diagonal entry of `signedChecked pos q (star x * x)` is nonnegative. -/
theorem signedChecked_star_mul_self_single_apply_nonneg [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [Fact (IsSelfAdjoint (q : R))] (x : TypeAHeckeAlgebra R q n)
    (w : Fin n → ι) :
    0 ≤ signedChecked pos q (star x * x) (single w 1) w := by
  rw [signedChecked_star_mul_self_single_apply]
  exact Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _

/-- Conjugating `atomicTrace` conjugates both the weights and the argument. -/
theorem star_atomicTrace [StarRing R] [Fact (IsSelfAdjoint (q : R))] [Finite ι] (p : ι → R)
    (x : TypeAHeckeAlgebra R q n) :
    star (atomicTrace pos q p n x) = atomicTrace pos q (star ∘ p) n (star x) := by
  cases nonempty_fintype ι
  rw [atomicTrace_eq_sum, atomicTrace_eq_sum, star_sum]
  exact Finset.sum_congr rfl fun w _ ↦ by
    rw [star_mul, mul_comm, star_prod, signedChecked_star_single_apply]; rfl

/-- For self-adjoint weights, `atomicTrace` commutes with `star`. -/
@[simp]
theorem atomicTrace_star [StarRing R] [Fact (IsSelfAdjoint (q : R))] [Finite ι] {p : ι → R}
    (hp : ∀ a, IsSelfAdjoint (p a)) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n (star x) = star (atomicTrace pos q p n x) := by
  rw [star_atomicTrace]; congr 2; ext a; exact (hp a).star_eq.symm

/-- **Positivity of finite atomic traces** for nonnegative weights over a `StarOrderedRing`. -/
theorem atomicTrace_star_mul_self_nonneg [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Fact (IsSelfAdjoint (q : R))] [Finite ι] {p : ι → R} (hp : ∀ a, 0 ≤ p a)
    (x : TypeAHeckeAlgebra R q n) :
    0 ≤ atomicTrace pos q p n (star x * x) := by
  cases nonempty_fintype ι
  rw [atomicTrace_eq_sum]
  exact Finset.sum_nonneg fun w _ ↦ StarOrderedRing.mul_nonneg
    (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
    (Finset.prod_nonneg_of_starOrderedRing fun i _ ↦ hp (w i))

/-- **Null space of a strictly positive atomic trace** over a `StarOrderedRing` without zero
divisors: `atomicTrace (star x * x) = 0 ↔ signedChecked pos q x = 0`. -/
theorem atomicTrace_star_mul_self_eq_zero_iff [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [NoZeroDivisors R] [Fact (IsSelfAdjoint (q : R))] [Finite ι] {p : ι → R}
    (hp : ∀ a, 0 < p a) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n (star x * x) = 0 ↔ signedChecked pos q x = 0 := by
  cases nonempty_fintype ι
  refine ⟨fun hx ↦ ?_, fun hx ↦ by
    rw [atomicTrace_apply, map_mul (signedChecked pos q), hx, mul_zero, zero_mul, map_zero]⟩
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  rw [atomicTrace_eq_sum] at hx
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦
    StarOrderedRing.mul_nonneg (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
      (Finset.prod_nonneg_of_starOrderedRing fun i _ ↦ (hp (w i)).le)).mp hx
  ext w u
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  have hdiag : signedChecked pos q (star x * x) (single w 1) w = 0 :=
    (mul_eq_zero.mp (hterm w (Finset.mem_univ w))).resolve_right
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hp (w i)).ne')
  rw [signedChecked_star_mul_self_single_apply] at hdiag
  have hcol := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ star_mul_self_nonneg _).mp hdiag
  by_contra hne
  exact hne ((mul_eq_zero.mp (hcol u (Finsupp.mem_support_iff.mpr hne))).elim star_eq_zero.mp id)

/-- **Trace radical of a strictly positive atomic model** equals `RingHom.ker (signedChecked)`. -/
theorem traceRadical_atomicTrace_eq_ker_signedChecked [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [NoZeroDivisors R] [Fact (IsSelfAdjoint (q : R))] [Finite ι]
    {p : ι → R} (hp : ∀ a, 0 < p a) (n : ℕ) :
    (atomicTrace pos q p n).traceRadical (atomicTrace_mul_comm pos q p) =
      RingHom.ker (signedChecked pos q) := by
  ext x
  simp only [LinearMap.mem_traceRadical, RingHom.mem_ker]
  refine ⟨fun hx ↦ (atomicTrace_star_mul_self_eq_zero_iff pos q hp x).mp
    (by rw [atomicTrace_mul_comm]; exact hx (star x)), fun hx y ↦ ?_⟩
  rw [atomicTrace_apply, map_mul (signedChecked pos q), hx, zero_mul, zero_mul, map_zero]

/-- The complex atomic trace on `n` strands bundled as a `StarPositiveFunctional`. -/
noncomputable def atomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := atomicTrace pos q p n
  square_nonneg := atomicTrace_star_mul_self_nonneg pos q hp

@[simp]
theorem atomicPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n) :
    atomicPositiveFunctional pos q hp n x = atomicTrace pos q p n x := (rfl)

end AdjointAndPositivity

section LeftSlice

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

/-- `tailIncl` fixes the prepended first letter and acts on the remaining `n` letters. -/
@[simp]
theorem signedChecked_tailIncl_mapDomain_cons (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    signedChecked pos q (tailIncl q n x) (mapDomain (fun w ↦ Fin.cons a w) v) =
      mapDomain (fun w ↦ Fin.cons a w) (signedChecked pos q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.cons a w : Fin (n + 1) → ι))
  suffices h : (signedChecked pos q (tailIncl q n x)).comp L = L.comp (signedChecked pos q x) by
    simpa [L] using LinearMap.congr_fun h v
  refine signedChecked_comp_eq_of_forall_T pos q _ L (fun i ↦ ?_) x
  rw [tailIncl_T, signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
    show BraidGroup.strand (⟨i + 1, by omega⟩ : Fin (n + 1 - 1)) = (BraidGroup.strand i).succ from
      Fin.ext (by simp),
    show BraidGroup.strandSucc (⟨i + 1, by omega⟩ : Fin (n + 1 - 1)) =
      (BraidGroup.strandSucc i).succ from Fin.ext (by simp),
    signedCheckedR_comp_lmapDomain_cons]

/-- `tailIncl` acts block-diagonally on words grouped by their first letter. -/
theorem signedChecked_tailIncl_single_cons_apply_cons (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) :
    signedChecked pos q (tailIncl q n x) (single (Fin.cons a w) 1) (Fin.cons d u) =
      if a = d then signedChecked pos q x (single w 1) u else 0 := by
  have h := signedChecked_tailIncl_mapDomain_cons pos q x a (single w 1)
  rw [mapDomain_single] at h; rw [h]
  split_ifs with had
  · subst d; exact mapDomain_apply_of_injective (@Fin.cons_right_injective _ (fun _ ↦ ι) a) _ _
  · apply mapDomain_of_notMem_range; rintro ⟨_, hv⟩
    exact had (by simpa using congrArg (fun z : Fin (n + 1) → ι ↦ z 0) hv)

/-- Diagonal entry of `tailIncl x * T 0` at `Fin.cons a w`. -/
theorem signedChecked_tailIncl_mul_T_zero_single_cons_apply
    (x : TypeAHeckeAlgebra R q (n + 1)) (a : ι) (w : Fin (n + 1) → ι) :
    signedChecked pos q (tailIncl q (n + 1) x * T q (0 : Fin (n + 1)))
        (single (Fin.cons a w) 1) (Fin.cons a w) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
        (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) := by
  have hswap : Fin.cons a w ∘ Equiv.swap (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ =
      Fin.cons (w 0) (update w 0 a) := by
    rw [Equiv.comp_swap_eq_update, update_comm (Fin.succ_ne_zero _)]; simp
  simp only [map_mul, mul_apply_eq_comp, signedChecked_T,
    show BraidGroup.strand (n := n + 2) (0 : Fin (n + 1)) = 0 from Fin.ext (by simp),
    show BraidGroup.strandSucc (n := n + 2) (0 : Fin (n + 1)) = (0 : Fin (n + 1)).succ from
      Fin.ext (by simp),
    LinearMap.smul_apply, signedCheckedR_single_one, Fin.cons_zero, Fin.cons_succ, hswap]
  rcases lt_trichotomy a (w 0) with h | rfl | h
  · simp only [h.ne, h.ne', h, ↓reduceIte, map_sub, map_smul, Finsupp.smul_apply,
      Finsupp.sub_apply, smul_eq_mul, signedChecked_tailIncl_single_cons_apply_cons]; ring
  · simp only [↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      signedChecked_tailIncl_single_cons_apply_cons]; ring
  · simp only [h.ne, h.ne', h.not_gt, ↓reduceIte, map_neg, map_smul, Finsupp.smul_apply,
      Finsupp.neg_apply, smul_eq_mul, signedChecked_tailIncl_single_cons_apply_cons]; ring

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
    split_ifs <;> simp_all
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]

/-- **First-site (left-slice) Markov rule** for `atomicTrace`. -/
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
  rw [show (∑ a, _) = ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * (∏ i, p (w i)) *
        ∑ a, (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) * p a by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring,
    sum_leftSlice, hz]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * Units.inv_mul q

/-- **The atomic trace with scalar left slice is the Ocneanu trace.** -/
theorem atomicTrace_eq_ocneanuTrace_of_leftSlice [Fintype ι] (p : ι → R) {z : R}
    (hp : ∑ a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ a with a < b, p a = q * z)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace z).eq_toInfinite_of_T_zero_mul_tailIncl
    (atomicTrace pos q p) (by simp) (by simp [hp]) (fun _ ↦ atomicTrace_mul_comm pos q p)
    (fun _ _ ↦ atomicTrace_castAdd_mul_natAdd pos q p)
    (fun _ ↦ atomicTrace_T_zero_mul_tailIncl pos q p hz) n x

/-- **Positive discrete geometric model in first-site R-order** (`z = c * q ^ (2 * r + 1)`). -/
theorem atomicTrace_geometric_leftSlice_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ True) q (fun a ↦ c * ((q : R) ^ 2) ^ (r - (a : ℕ))) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * (q : R) ^ (2 * r + 1))
        (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace_of_leftSlice _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc]; congr 1
    exact (Fintype.sum_equiv Fin.revPerm _ (fun a : Fin (r + 1) ↦ ((q : R) ^ 2) ^ (a : ℕ))
      fun a ↦ by simp only [Fin.revPerm_apply, Fin.val_rev]; congr 1; omega).trans
      (Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a) (r + 1))
  · have hI : ∑ a : Fin (r + 1) with a < b, c * ((q : R) ^ 2) ^ (r - (a : ℕ)) =
        c * ∑ k ∈ Finset.Ico ((r - (b : ℕ)) + 1) (r + 1), ((q : R) ^ 2) ^ k := by
      rw [← Finset.mul_sum]; congr 1
      refine Finset.sum_bij' (fun a _ ↦ r - (a : ℕ))
        (fun k hk ↦ ⟨r - k, by rw [Finset.mem_Ico] at hk; omega⟩)
        (fun a ha ↦ by simp only [Finset.mem_filter, Fin.lt_def, Finset.mem_Ico] at ha ⊢; omega)
        (fun k hk ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
          Finset.mem_Ico] at hk ⊢; omega)
        (fun a _ ↦ Fin.ext (by dsimp; omega))
        (fun k hk ↦ by rw [Finset.mem_Ico] at hk; dsimp; omega)
        (fun _ _ ↦ rfl)
    have hg := geom_sum_Ico_mul ((q : R) ^ 2) (show (r - (b : ℕ)) + 1 ≤ r + 1 by omega)
    rw [pow_succ' ((q : R) ^ 2) (r - (b : ℕ))] at hg
    have hpow : (q : R) * (q : R) ^ (2 * r + 1) = ((q : R) ^ 2) ^ (r + 1) := by ring
    simp only [↓reduceIte, hI]; linear_combination c * hg - c * hpow

/-- **Negative discrete geometric model in first-site R-order** (`z = -(c * q⁻¹)`). -/
theorem atomicTrace_negGeometric_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ False) q (fun a ↦ c * ((q : R) ^ 2) ^ (a : ℕ)) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (-(c * ↑q⁻¹)) (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace_of_leftSlice _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc, Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a)]
  · have hI : ∑ a : Fin (r + 1) with a < b, c * ((q : R) ^ 2) ^ (a : ℕ) =
        c * ∑ a ∈ Finset.range (b : ℕ), ((q : R) ^ 2) ^ a := by
      rw [← Finset.mul_sum, Finset.sum_filter]; congr 1; simp_rw [Fin.lt_def]
      rw [Fin.sum_univ_eq_sum_range
        (fun a ↦ if a < (b : ℕ) then ((q : R) ^ 2) ^ a else 0) (r + 1), ← Finset.sum_filter]
      congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
    simp only [↓reduceIte, hI]
    linear_combination c * geom_sum_mul ((q : R) ^ 2) (b : ℕ) + c * Units.mul_inv q

end LeftSlice

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

/-- **The projection parameter of a negative geometric atomic model** is `wenzlParam (-(r + 1)) Q`
(`Q = q ^ 2`, `c * [r + 1]_Q = 1`). -/
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
  have hg : ∑ a ∈ Finset.range (r + 1), ((q : K) ^ 2) ^ a =
      (q : K) ^ 2 * ∑ a ∈ Finset.range r, ((q : K) ^ 2) ^ a + 1 := by
    simp [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum]
  rw [wenzlParam_neg_natCast, Nat.add_sub_cancel, Units.val_inv_eq_inv_val]
  field_simp; linear_combination (1 + (q : K) ^ 2) * hg - (1 + (q : K) ^ 2) * hc

end InfiniteTypeAHeckeAlgebra

end TauCeti
