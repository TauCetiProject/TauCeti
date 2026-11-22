/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord.Analytic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.LeftSlice
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Positivity.Basic
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TauCeti.Algebra.Order.Star.Basic
import TauCeti.Analysis.Normed.Ring.InfiniteSum

/-!
# Countable atomic models and infinite cycle-trace products

For a linearly ordered alphabet `ι` and an absolutely summable weight family `p : ι → R` in a
complete normed commutative ring `R`, the matrix entries of `signedChecked pos q x` are uniformly
bounded (`exists_norm_signedChecked_single_apply_le`), so the diagonal series converges absolutely
and defines `countableAtomicTrace` (bundled over `ℂ` as `countableAtomicPositiveFunctional`).
It is invariant under dropping zero-weight letters (`countableAtomicTrace_subtype_eq_of_eq_zero`,
`countableAtomicTrace_subtype_ne_zero`).

Exhaustion by finite `atomicTrace`s (`tendsto_atomicTrace_finset`) passes traciality, scaling on
`1` / `strandIncl` / `tailIncl`, block multiplicativity, star compatibility
(`star_countableAtomicTrace`, `countableAtomicTrace_star`), `⋆`-positivity
(`countableAtomicTrace_star_mul_self_nonneg`), null space and trace radical for strictly positive
weights (`countableAtomicTrace_star_mul_self_eq_zero_iff`,
`traceRadical_countableAtomicTrace_eq_ker_signedChecked`), and the left- and right-slice Ocneanu
identifications (`countableAtomicTrace_eq_ocneanuTrace_of_leftSlice`,
`countableAtomicTrace_eq_ocneanuTrace_of_rightSlice`) to countable alphabets.

We also lift the cycle-word generating identity to infinite alphabets over a complete normed field
`K` (`countableAtomicTrace_cycleWord_hasProd`) and evaluate the `Q = 1` signed power sums
(`countableAtomicTrace_cycleWord_of_sq_eq_one`).

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
-/

public section

open Filter Function Finsupp
open scoped Topology ComplexOrder

namespace TauCeti.TypeAHeckeAlgebra

section CountableTrace

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {ι : Type*} [LinearOrder ι]
  (pos : ι → Prop) [DecidablePred pos] (q : Rˣ)

omit [CompleteSpace R] in
/-- Absolute summability of the weighted diagonal coefficients of `signedChecked pos q x`. -/
theorem summable_norm_signedChecked_mul_prod {p : ι → R} (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    Summable fun w : Fin n → ι ↦ ‖signedChecked pos q x (single w 1) w * ∏ i, p (w i)‖ := by
  obtain ⟨C, _, hC⟩ := exists_norm_signedChecked_single_apply_le pos q x
  refine ((summable_norm_prod_of_summable_norm (f := fun _ : Fin n ↦ p) fun _ ↦ hp).mul_left
    C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun w ↦
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hC w w) (norm_nonneg _))

/-- **The countable atomic trace** on `TypeAHeckeAlgebra R q n` for an absolutely summable weight
family `p : ι → R`. -/
noncomputable def countableAtomicTrace (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ) :
    TypeAHeckeAlgebra R q n →ₗ[R] R where
  toFun x := ∑' w : Fin n → ι, signedChecked pos q x (single w 1) w * ∏ i, p (w i)
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, add_mul]
    exact (summable_norm_signedChecked_mul_prod pos q hp n x).of_norm.tsum_add
      (summable_norm_signedChecked_mul_prod pos q hp n y).of_norm
  map_smul' r x := by
    simp only [map_smul, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul, mul_assoc,
      RingHom.id_apply]
    exact (summable_norm_signedChecked_mul_prod pos q hp n x).of_norm.tsum_mul_left r

theorem countableAtomicTrace_apply (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      ∑' w : Fin n → ι, signedChecked pos q x (single w 1) w * ∏ i, p (w i) := (rfl)

/-- On a finite alphabet, `countableAtomicTrace` agrees with `atomicTrace`. -/
theorem countableAtomicTrace_eq_atomicTrace [Finite ι] (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (n : ℕ) (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x = atomicTrace pos q p n x := by
  cases nonempty_fintype ι
  rw [countableAtomicTrace_apply, tsum_fintype, atomicTrace_eq_sum]

/-- Restricting the alphabet of a countable atomic model to a predicate outside which all weights
vanish does not change `countableAtomicTrace`. -/
theorem countableAtomicTrace_subtype_eq_of_eq_zero (P : ι → Prop) (p : ι → R)
    (hp_sum : Summable fun a ↦ ‖p a‖) (hp : ∀ a, ¬ P a → p a = 0) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace (fun a : {a : ι // P a} ↦ pos a) q (fun a ↦ p a)
        (hp_sum.comp_injective Subtype.val_injective) n x =
      countableAtomicTrace pos q p hp_sum n x := by
  rw [countableAtomicTrace_apply, countableAtomicTrace_apply]
  have htsum :
      (∑' w : Fin n → {a : ι // P a},
        signedChecked pos q x (single (Subtype.val ∘ w) 1) (Subtype.val ∘ w) *
          ∏ i, p (w i)) =
      ∑' w : Fin n → ι, signedChecked pos q x (single w 1) w * ∏ i, p (w i) := by
    exact (Subtype.val_injective.comp_left (α := Fin n)).tsum_eq
      (f := fun w : Fin n → ι ↦ signedChecked pos q x (single w 1) w * ∏ i, p (w i))
      fun w hw ↦ by
        by_contra hrange
        apply hw
        dsimp only
        have hnot : ¬ ∀ i, P (w i) := fun hP ↦ hrange ⟨fun i ↦ ⟨w i, hP i⟩, rfl⟩
        obtain ⟨i, hi⟩ := not_forall.mp hnot
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (hp (w i) hi), mul_zero]
  rw [← htsum]
  refine tsum_congr fun w ↦ ?_
  rw [signedChecked_strictMono_single_apply pos q (fun a : {a : ι // P a} ↦ pos a)
    (Subtype.strictMono_coe P) (fun _ ↦ Iff.rfl)]

/-- Dropping zero-weight letters from a countable alphabet does not change
`countableAtomicTrace`. -/
theorem countableAtomicTrace_subtype_ne_zero (p : ι → R) (hp_sum : Summable fun a ↦ ‖p a‖)
    {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace (fun a : {a : ι // p a ≠ 0} ↦ pos a) q (fun a ↦ p a)
        (hp_sum.comp_injective Subtype.val_injective) n x =
      countableAtomicTrace pos q p hp_sum n x :=
  countableAtomicTrace_subtype_eq_of_eq_zero pos q (fun a ↦ p a ≠ 0) p hp_sum
    (fun _ h ↦ not_not.mp h) x

/-- **Exhaustion of `countableAtomicTrace` by finite sub-alphabets** along `atTop`. -/
theorem tendsto_atomicTrace_finset (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    Tendsto (fun s : Finset ι ↦ atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) n x)
      atTop (𝓝 (countableAtomicTrace pos q p hp n x)) := by
  classical
  have hpi : Tendsto (fun s : Finset ι ↦ Fintype.piFinset fun _ : Fin n ↦ s) atTop atTop :=
    tendsto_atTop_atTop.mpr fun T ↦ ⟨T.biUnion fun w ↦ Finset.univ.image w,
      fun s hs w hw ↦ Fintype.mem_piFinset.mpr fun i ↦
        hs (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_image_of_mem w (Finset.mem_univ i)⟩)⟩
  refine ((summable_norm_signedChecked_mul_prod pos q hp n x).of_norm.hasSum.comp hpi).congr
    fun s ↦ ?_
  rw [comp_apply, atomicTrace_eq_sum]; symm
  refine Finset.sum_bij (fun (w : Fin n → s) _ ↦ Subtype.val ∘ w)
    (fun w _ ↦ Fintype.mem_piFinset.mpr fun i ↦ (w i).property)
    (fun _ _ _ _ h ↦ funext fun i ↦ Subtype.ext (congrFun h i))
    (fun w hw ↦ ⟨fun i ↦ ⟨w i, Fintype.mem_piFinset.mp hw i⟩, Finset.mem_univ _, rfl⟩) fun w _ ↦ ?_
  rw [signedChecked_strictMono_single_apply pos q (fun a : s ↦ pos a)
    (fun _ _ h ↦ h) (fun _ ↦ Iff.rfl)]; rfl

/-- The countable atomic trace is tracial. -/
theorem countableAtomicTrace_mul_comm (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x y : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n (x * y) = countableAtomicTrace pos q p hp n (y * x) :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp n (x * y)) <|
    (tendsto_atomicTrace_finset pos q p hp n (y * x)).congr fun s ↦
      (atomicTrace_mul_comm (fun a : s ↦ pos a) q (fun a : s ↦ p a) x y).symm

/-- The countable atomic trace of `1` on `n` strands is `(∑' a, p a) ^ n`. -/
@[simp]
theorem countableAtomicTrace_one (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) (n : ℕ) :
    countableAtomicTrace pos q p hp n 1 = (∑' a, p a) ^ n :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp n 1) <|
    (hp.of_norm.hasSum.pow n).congr fun s ↦ by
      rw [atomicTrace_one, Finset.univ_eq_attach, s.sum_attach p]

/-- Adding an uncrossed last strand multiplies `countableAtomicTrace` by `∑' a, p a`. -/
@[simp]
theorem countableAtomicTrace_strandIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (n + 1) (strandIncl R q n x) =
      countableAtomicTrace pos q p hp n x * ∑' a, p a :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp (n + 1) (strandIncl R q n x)) <|
    ((tendsto_atomicTrace_finset pos q p hp n x).mul hp.of_norm.hasSum).congr fun s ↦ by
      rw [← Finset.sum_attach s p, ← Finset.univ_eq_attach, ← atomicTrace_strandIncl]

/-- Adding an uncrossed first strand multiplies `countableAtomicTrace` by `∑' a, p a`. -/
@[simp]
theorem countableAtomicTrace_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (n + 1) (tailIncl q n x) =
      countableAtomicTrace pos q p hp n x * ∑' a, p a :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp (n + 1) (tailIncl q n x)) <|
    ((tendsto_atomicTrace_finset pos q p hp n x).mul hp.of_norm.hasSum).congr fun s ↦ by
      rw [← Finset.sum_attach s p, ← Finset.univ_eq_attach, ← atomicTrace_tailIncl]

/-- **Block multiplicativity of `countableAtomicTrace`** on disjoint consecutive strand blocks. -/
theorem countableAtomicTrace_castAdd_mul_natAdd (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {m n : ℕ} (x : TypeAHeckeAlgebra R q m) (y : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (m + n) (castAdd R q m n x * natAdd R q m n y) =
      countableAtomicTrace pos q p hp m x * countableAtomicTrace pos q p hp n y :=
  tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + n) (castAdd R q m n x * natAdd R q m n y)) <|
    ((tendsto_atomicTrace_finset pos q p hp m x).mul
      (tendsto_atomicTrace_finset pos q p hp n y)).congr fun s ↦
        (atomicTrace_castAdd_mul_natAdd (fun a : s ↦ pos a) q (fun a : s ↦ p a) x y).symm

/-- **Positivity of countable atomic traces** for nonnegative weights over a complete normed
`StarOrderedRing` with `OrderClosedTopology`. -/
theorem countableAtomicTrace_star_mul_self_nonneg [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [OrderClosedTopology R] [Fact (IsSelfAdjoint (q : R))] {p : ι → R}
    (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    0 ≤ countableAtomicTrace pos q p hp n (star x * x) :=
  ge_of_tendsto (tendsto_atomicTrace_finset pos q p hp n (star x * x)) <|
    Eventually.of_forall fun s ↦
      atomicTrace_star_mul_self_nonneg (fun a : s ↦ pos a) q (fun a : s ↦ p a)
        (fun a : s ↦ hp0 a) x

/-- Conjugating `countableAtomicTrace` conjugates both the weights and the argument. -/
theorem star_countableAtomicTrace [StarRing R] [NormedStarGroup R]
    [Fact (IsSelfAdjoint (q : R))] (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    star (countableAtomicTrace pos q p hp n x) =
      countableAtomicTrace pos q (star ∘ p) (hp.congr fun _ ↦ (norm_star _).symm) n (star x) :=
  tendsto_nhds_unique
    ((continuous_star.tendsto _).comp (tendsto_atomicTrace_finset pos q p hp n x)) <|
    (tendsto_atomicTrace_finset pos q (star ∘ p) (hp.congr fun _ ↦ (norm_star _).symm) n
      (star x)).congr fun s ↦ (star_atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) x).symm

/-- For self-adjoint weights, `countableAtomicTrace` commutes with `star`. -/
@[simp]
theorem countableAtomicTrace_star [StarRing R] [ContinuousStar R]
    [Fact (IsSelfAdjoint (q : R))] {p : ι → R} (hp_sum : Summable fun a ↦ ‖p a‖)
    (hp : ∀ a, IsSelfAdjoint (p a)) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp_sum n (star x) =
      star (countableAtomicTrace pos q p hp_sum n x) :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp_sum n (star x)) <|
    ((continuous_star.tendsto _).comp (tendsto_atomicTrace_finset pos q p hp_sum n x)).congr
      fun s ↦ (atomicTrace_star (fun a : s ↦ pos a) q (fun a : s ↦ p a)
        (fun a : s ↦ hp a) x).symm

/-- **Null space of a strictly positive countable atomic trace** over a complete normed
`StarOrderedRing` with `OrderClosedTopology` and no zero divisors:
`countableAtomicTrace (star x * x) = 0 ↔ signedChecked pos q x = 0`. -/
theorem countableAtomicTrace_star_mul_self_eq_zero_iff [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [OrderClosedTopology R] [NoZeroDivisors R]
    [Fact (IsSelfAdjoint (q : R))] {p : ι → R} (hp : Summable fun a ↦ ‖p a‖)
    (hp0 : ∀ a, 0 < p a) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n (star x * x) = 0 ↔ signedChecked pos q x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by
    rw [countableAtomicTrace_apply, map_mul (signedChecked pos q), hx]; simp⟩
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  rw [countableAtomicTrace_apply] at hx
  have hsum : Summable fun w : Fin n → ι ↦
      signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) :=
    (summable_norm_signedChecked_mul_prod pos q hp n (star x * x)).of_norm
  have hnonneg (w : Fin n → ι) :
      0 ≤ signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) :=
    StarOrderedRing.mul_nonneg (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
      (Finset.prod_nonneg_of_starOrderedRing fun i _ ↦ (hp0 (w i)).le)
  ext w u
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  have hw : signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) = 0 :=
    le_antisymm ((hsum.le_tsum w fun _ _ ↦ hnonneg _).trans_eq hx) (hnonneg w)
  have hdiag : signedChecked pos q (star x * x) (single w 1) w = 0 :=
    (mul_eq_zero.mp hw).resolve_right (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hp0 (w i)).ne')
  exact signedChecked_single_apply_eq_zero_of_star_mul_self pos q x hdiag u

/-- **Trace radical of a strictly positive countable atomic model** equals
`RingHom.ker (signedChecked)`. -/
theorem traceRadical_countableAtomicTrace_eq_ker_signedChecked [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [OrderClosedTopology R] [NoZeroDivisors R]
    [Fact (IsSelfAdjoint (q : R))] {p : ι → R} (hp : Summable fun a ↦ ‖p a‖)
    (hp0 : ∀ a, 0 < p a) (n : ℕ) :
    (countableAtomicTrace pos q p hp n).traceRadical
        (countableAtomicTrace_mul_comm pos q p hp) =
      RingHom.ker (signedChecked pos q) := by
  ext x
  simp only [LinearMap.mem_traceRadical, RingHom.mem_ker]
  refine ⟨fun hx ↦ (countableAtomicTrace_star_mul_self_eq_zero_iff pos q hp hp0 x).mp
    (by rw [countableAtomicTrace_mul_comm]; exact hx (star x)), fun hx y ↦ ?_⟩
  rw [countableAtomicTrace_apply, map_mul (signedChecked pos q), hx]
  simp

/-- The complex countable atomic trace on `n` strands bundled as a `StarPositiveFunctional`. -/
noncomputable def countableAtomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := countableAtomicTrace pos q p hp n
  square_nonneg := countableAtomicTrace_star_mul_self_nonneg pos q hp hp0

/-- Forgetting positivity recovers the underlying countable atomic trace. -/
@[simp]
theorem toLinearMap_countableAtomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ) :
    (countableAtomicPositiveFunctional pos q hp hp0 n).toLinearMap =
      countableAtomicTrace pos q p hp n := (rfl)

/-- Evaluating `countableAtomicPositiveFunctional` at an element recovers `countableAtomicTrace`. -/
@[simp]
theorem countableAtomicPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ)
    (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicPositiveFunctional pos q hp hp0 n x =
      countableAtomicTrace pos q p hp n x := (rfl)

/-- **Cycle-word countable atomic trace at `Q = 1`** equals the signed `(m + 1)`-th power sum. -/
theorem countableAtomicTrace_cycleWord_of_sq_eq_one (hq : (q : R) ^ 2 = 1) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) =
      ∑' a, (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1) := by
  have hsign (a : ι) : ‖(if pos a then (1 : R) else -1) ^ m‖ = ‖(1 : R)‖ := by
    split_ifs <;> simp
  have hpow : Summable fun a ↦ ‖(if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)‖ :=
    (hp.mul_left (‖(1 : R)‖ * (∑' b, ‖p b‖) ^ m)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun a ↦ (norm_mul_le _ _).trans <| by
        rw [hsign a, mul_assoc]
        refine mul_le_mul_of_nonneg_left ((norm_pow_le' (p a) (Nat.succ_pos m)).trans ?_)
          (norm_nonneg _)
        rw [pow_succ]; gcongr; exact hp.le_tsum a fun _ _ ↦ norm_nonneg _
  refine tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))) <|
    hpow.of_norm.hasSum.congr fun s ↦ ?_
  rw [← Finset.sum_attach s (fun a ↦ (if pos a then (1 : R) else -1) ^ m * p a ^ (m + 1)),
    ← Finset.univ_eq_attach, ← atomicTrace_cycleWord_of_sq_eq_one (fun a : s ↦ pos a) q hq]

private theorem countableAtomicTrace_eq_mul_of_slice (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R} {n : ℕ} {x : TypeAHeckeAlgebra R q (n + 1)} {y : TypeAHeckeAlgebra R q (n + 2)}
    (e : (Fin (n + 1) → ι) × ι ≃ (Fin (n + 2) → ι)) (b : (Fin (n + 1) → ι) → ι)
    (P : ι → ι → Prop) [∀ u, DecidablePred (P u)] (hP : ∀ u, ¬ P u u)
    (hprod : ∀ w a, ∏ i, p (e (w, a) i) = p a * ∏ i, p (w i))
    (hdiag : ∀ w a, signedChecked pos q y (single (e (w, a)) 1) (e (w, a)) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
        (if a = b w then (if pos (b w) then (q : R) ^ 2 else -1)
          else if P (b w) a then (q : R) ^ 2 - 1 else 0))
    (hz : ∀ u, (if pos u then (q : R) ^ 2 else -1) * p u +
      ((q : R) ^ 2 - 1) * (∑' a, if P u a then p a else 0) = q * z) :
    countableAtomicTrace pos q p hp (n + 2) y = z * countableAtomicTrace pos q p hp (n + 1) x := by
  classical
  rw [countableAtomicTrace_apply,
    (e.tsum_eq _).symm.trans (Summable.tsum_prod (e.summable_iff.mpr
      (summable_norm_signedChecked_mul_prod pos q hp (n + 2) y).of_norm)),
    countableAtomicTrace_apply,
    ← (summable_norm_signedChecked_mul_prod pos q hp (n + 1) x).of_norm.tsum_mul_left]
  congr 1 with w
  set u := b w
  have h₁ : Summable fun a ↦ if a = u then (if pos u then (q : R) ^ 2 else -1) * p u else 0 :=
    summable_of_ne_finset_zero (s := {u}) fun _ ha ↦ by simp [Finset.notMem_singleton.mp ha]
  have h_ite : Summable fun a ↦ ‖if P u a then p a else 0‖ :=
    hp.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun _ ↦ by split_ifs <;> simp
  have h₂ := h_ite.of_norm.mul_left ((q : R) ^ 2 - 1)
  have hdecomp (a : ι) :
      signedChecked pos q y (single (e (w, a)) 1) (e (w, a)) * ∏ i, p (e (w, a) i) =
        (((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) *
          ((if a = u then (if pos u then (q : R) ^ 2 else -1) * p u else 0) +
            ((q : R) ^ 2 - 1) * (if P u a then p a else 0)) := by
    rw [hdiag w a, hprod w a]
    split_ifs <;> simp_all [u] <;> ring
  rw [funext hdecomp, (h₁.add h₂).tsum_mul_left, h₁.tsum_add h₂, tsum_ite_eq,
    h_ite.of_norm.tsum_mul_left, hz u]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * Units.inv_mul q

/-- **Countable first-site (left-slice) Markov rule** for `countableAtomicTrace`. -/
theorem countableAtomicTrace_T_zero_mul_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q (n + 1)) :
    countableAtomicTrace pos q p hp (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) =
      z * countableAtomicTrace pos q p hp (n + 1) x := by
  rw [countableAtomicTrace_mul_comm]
  exact countableAtomicTrace_eq_mul_of_slice pos q p hp
    ((Equiv.prodComm (Fin (n + 1) → ι) ι).trans (Fin.consEquiv fun _ : Fin (n + 2) ↦ ι))
    (· 0) (fun u a ↦ a < u) lt_irrefl
    (fun w a ↦ by simp [Fin.prod_univ_succ (n := n + 1)])
    (fun w a ↦ signedChecked_tailIncl_mul_T_zero_single_cons_apply pos q x a w) hz

/-- **Countable atomic trace with scalar left slice is the Ocneanu trace.** -/
theorem countableAtomicTrace_eq_ocneanuTrace_of_leftSlice (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) {z : R} (hp1 : ∑' a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace z).eq_toInfinite_of_T_zero_mul_tailIncl
    (countableAtomicTrace pos q p hp) (by simp [hp1])
    (fun _ ↦ countableAtomicTrace_mul_comm pos q p hp)
    (fun _ _ ↦ countableAtomicTrace_castAdd_mul_natAdd pos q p hp)
    (fun _ ↦ countableAtomicTrace_T_zero_mul_tailIncl pos q p hp hz) n x

/-- **Countable last-site (right-slice) Markov rule** for `countableAtomicTrace`. -/
theorem countableAtomicTrace_strandIncl_mul_T_last (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' c, if b < c then p c else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q (n + 1)) :
    countableAtomicTrace pos q p hp (n + 2)
        (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      z * countableAtomicTrace pos q p hp (n + 1) x := by
  refine countableAtomicTrace_eq_mul_of_slice pos q p hp
    ((Equiv.prodComm (Fin (n + 1) → ι) ι).trans (Fin.snocEquiv fun _ : Fin (n + 2) ↦ ι))
    (· (Fin.last n)) (· < ·) lt_irrefl
    (fun w c ↦ by simp [Fin.prod_univ_castSucc (n := n + 1), mul_comm]) (fun w c ↦ ?_) hz
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Fin.snocEquiv_apply,
    signedChecked_strandIncl_mul_T_last_single_snoc_apply]
  congr 1
  by_cases h : c = w (Fin.last n) <;> simp [h, eq_comm]

/-- **Countable atomic trace with scalar right slice is the Ocneanu trace.** -/
theorem countableAtomicTrace_eq_ocneanuTrace_of_rightSlice (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) {z : R} (hp1 : ∑' a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' c, if b < c then p c else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  eq_ocneanuTrace_toInfinite (countableAtomicTrace pos q p hp) (by simp)
    (fun _ _ ↦ by rw [countableAtomicTrace_strandIncl, hp1, mul_one])
    (fun _ ↦ countableAtomicTrace_mul_comm pos q p hp)
    (fun _ ↦ countableAtomicTrace_strandIncl_mul_T_last pos q p hp hz) n x

end CountableTrace

section GeneratingProduct

/-- Norm bound on the countable atomic trace of a cycle word `cycleWord (m + 1)`. -/
theorem norm_countableAtomicTrace_cycleWord_le {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1))‖ ≤
      ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m *
        (∑' a, ‖p a‖) ^ (m + 1) := by
  have hp_norm : ∀ _ : Fin (m + 1), Summable fun a ↦ ‖‖p a‖‖ := fun _ ↦ by simpa using hp
  have hprod : Summable fun w : Fin (m + 1) → ι ↦ ∏ i, ‖p (w i)‖ := by
    simpa only [Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)] using
      summable_norm_prod_of_summable_norm hp_norm
  rw [countableAtomicTrace_apply]
  refine (norm_tsum_le_tsum_norm
    (summable_norm_signedChecked_mul_prod pos q hp (m + 1) (cycleWord q (m + 1)))).trans ?_
  refine ((summable_norm_signedChecked_mul_prod pos q hp (m + 1) _).tsum_le_tsum (fun w ↦
    (norm_mul_le _ _).trans (mul_le_mul (norm_signedChecked_cycleWord_single_apply_le pos q w)
      (Finset.norm_prod_le' _ Finset.univ_nonempty _) (norm_nonneg _) (by positivity)))
    (hprod.mul_left _)).trans_eq ?_
  rw [hprod.tsum_mul_left, ← prod_tsum_of_summable_norm hp_norm, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

private theorem norm_countableAtomicTrace_cycleWord_mul_pow_le {K : Type*}
    [NormedField K] [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
    [DecidablePred pos] (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) (x : K) (m : ℕ) :
    ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ ≤
      ((∑' a, ‖p a‖) * ‖x‖) *
        (max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖) ^ m := by
  rw [norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_right (norm_countableAtomicTrace_cycleWord_le pos q p hp m)
    (pow_nonneg (norm_nonneg x) _)).trans ?_
  rw [norm_one, one_mul]; exact le_of_eq (by ring)

/-- Absolute summability of the countable cycle-trace generating series on the convergence disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem summable_norm_countableAtomicTrace_cycleWord_mul_pow {K : Type*} [NormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1) :
    Summable fun m : ℕ ↦
      ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ :=
  have : 0 ≤ ∑' a, ‖p a‖ := tsum_nonneg fun _ ↦ norm_nonneg _
  ((summable_geometric_of_lt_one (by positivity) hx).mul_left
      ((∑' a, ‖p a‖) * ‖x‖)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_countableAtomicTrace_cycleWord_mul_pow_le pos q p hp x)

/-- **Countable cycle-trace generating product** over any complete normed field `K` on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem countableAtomicTrace_cycleWord_hasProd {K : Type*} [NormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1) :
    (Summable fun m : ℕ ↦
        ‖countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖) ∧
      HasProd (fun a : ι ↦
          if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))
        (1 + ((q : K) ^ 2 - 1) * ∑' m : ℕ,
          countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)) := by
  refine ⟨summable_norm_countableAtomicTrace_cycleWord_mul_pow pos q p hp hx, ?_⟩
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  set S : ℝ := ∑' a, ‖p a‖
  have : 0 ≤ S := tsum_nonneg fun _ ↦ norm_nonneg _
  have hmaj := (summable_geometric_of_lt_one (by positivity) hx).mul_left (S * ‖x‖)
  have hs_le (s : Finset ι) : ∑ a : s, ‖p a‖ ≤ S := by
    rw [Finset.univ_eq_attach, s.sum_attach fun a ↦ ‖p a‖]
    exact hp.sum_le_tsum s fun _ _ ↦ norm_nonneg _
  have hdom : Tendsto (fun s : Finset ι ↦ ∑' m : ℕ,
      atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1)) atTop
      (𝓝 (∑' m : ℕ, countableAtomicTrace pos q p hp (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1))) :=
    tendsto_tsum_of_dominated_convergence hmaj
      (fun m ↦ (tendsto_atomicTrace_finset pos q p hp (m + 1) (cycleWord q (m + 1))).mul_const _)
      (Eventually.of_forall fun s m ↦ by
        have hps : Summable fun a : s ↦ ‖p a‖ := (hasSum_fintype _).summable
        rw [← countableAtomicTrace_eq_atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) hps]
        refine (norm_countableAtomicTrace_cycleWord_mul_pow_le _ q _ hps x m).trans ?_
        rw [tsum_fintype]; have := hs_le s; gcongr)
  refine (tendsto_const_nhds.add (hdom.const_mul _)).congr fun s ↦ ?_
  have hxs : M * (∑ a : s, ‖p a‖) * ‖x‖ < 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs_le s) (by positivity))
      (norm_nonneg x)).trans_lt hx
  rw [(atomicTrace_cycleWord_generating_eval (fun a : s ↦ pos a) q (fun a : s ↦ p a) hxs).2,
    Finset.univ_eq_attach, s.prod_attach (fun a ↦
      if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
      else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x))]

end GeneratingProduct

end TauCeti.TypeAHeckeAlgebra
