/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical
import Mathlib.Analysis.Complex.Order
import TauCeti.Algebra.Order.Star.Basic
import TauCeti.LinearAlgebra.Finsupp.LSum

/-!
# Positivity and trace radicals for atomic models

For a star-fixed parameter `q : Rˣ` in a commutative star ring `R`, `signedChecked` is Hermitian
in the word basis (`signedChecked_star_single_apply`), so every diagonal entry of `star x * x` is a
finite sum of squares `star c * c` (`signedChecked_star_mul_self_single_apply`). Over a
`StarOrderedRing` with `0 ≤ p a`, the atomic trace is `⋆`-positive
(`atomicTrace_star_mul_self_nonneg`, bundled over `ℂ` as `atomicPositiveFunctional`), and for
strictly positive weights over a domain its trace radical is `RingHom.ker (signedChecked pos q)`
(`traceRadical_atomicTrace_eq_ker_signedChecked`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.atomicPositiveFunctional`: the complex finite atomic trace bundled as
  a `StarPositiveFunctional`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.signedChecked_star_single_apply` and
  `TauCeti.TypeAHeckeAlgebra.signedChecked_star_mul_self_single_apply`: Hermitian symmetry and
  diagonal sum-of-squares formula for `signedChecked`.
* `TauCeti.TypeAHeckeAlgebra.star_atomicTrace` and `TauCeti.TypeAHeckeAlgebra.atomicTrace_star`:
  star compatibility of finite atomic traces.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg`: positivity of finite atomic traces
  over a `StarOrderedRing`.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_eq_zero_iff` and
  `TauCeti.TypeAHeckeAlgebra.traceRadical_atomicTrace_eq_ker_signedChecked`: null space and trace
  radical for strictly positive weights.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
-/

public section

open Function Finsupp
open scoped ComplexOrder

namespace TauCeti.TypeAHeckeAlgebra

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

/-- Forgetting positivity recovers the underlying atomic trace. -/
@[simp]
theorem toLinearMap_atomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) :
    (atomicPositiveFunctional pos q hp n).toLinearMap = atomicTrace pos q p n := (rfl)

/-- Evaluating `atomicPositiveFunctional` at an element recovers `atomicTrace`. -/
@[simp]
theorem atomicPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n) :
    atomicPositiveFunctional pos q hp n x = atomicTrace pos q p n x := (rfl)

end AdjointAndPositivity

end TauCeti.TypeAHeckeAlgebra
