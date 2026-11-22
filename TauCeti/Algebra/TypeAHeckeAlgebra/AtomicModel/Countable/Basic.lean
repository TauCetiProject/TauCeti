/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.NormBounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TauCeti.Analysis.Normed.Ring.InfiniteSum

/-!
# Countable atomic models and finite exhaustion

For a linearly ordered alphabet `ι` and an absolutely summable weight family `p : ι → R` in a
complete normed commutative ring `R`, the matrix entries of `signedChecked pos q x` are uniformly
bounded (`TauCeti.TypeAHeckeAlgebra.exists_norm_signedChecked_single_apply_le`), so the diagonal
series converges absolutely and defines `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace`. It is
invariant under dropping zero-weight letters
(`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_subtype_eq_of_eq_zero`,
`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_subtype_ne_zero`).

Exhaustion by finite `atomicTrace`s (`TauCeti.TypeAHeckeAlgebra.tendsto_atomicTrace_finset`) passes
traciality and scaling on `1` and `strandIncl` to countable alphabets.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace`: the weighted diagonal series trace on
  `TypeAHeckeAlgebra R q n` for an absolutely summable weight family.

## Main results

* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_atomicTrace`: agreement with `atomicTrace` on
  finite alphabets.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_subtype_eq_of_eq_zero` and
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_subtype_ne_zero`: invariance under dropping
  zero-weight letters.
* `TauCeti.TypeAHeckeAlgebra.tendsto_atomicTrace_finset`: exhaustion by finite sub-alphabets.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_mul_comm`,
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_one`, and
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_strandIncl`: traciality, value at `1`, and
  behaviour under adding a last strand.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
-/

public section

open Filter Function Finsupp
open scoped Topology

namespace TauCeti.TypeAHeckeAlgebra

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

/-- Evaluating `countableAtomicTrace` as a diagonal series over words. -/
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
      ∑' w : Fin n → ι, signedChecked pos q x (single w 1) w * ∏ i, p (w i) :=
    (Subtype.val_injective.comp_left (α := Fin n)).tsum_eq
      (f := fun w : Fin n → ι ↦ signedChecked pos q x (single w 1) w * ∏ i, p (w i))
      fun w hw ↦ by
        by_contra hrange
        exact hw (by dsimp only; rw [prod_eq_zero_of_notMem_range_subtype p P hp hrange, mul_zero])
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

end TauCeti.TypeAHeckeAlgebra
