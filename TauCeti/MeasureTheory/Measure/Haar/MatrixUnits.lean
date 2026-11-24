/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Haar measure of the invertible matrices over a local ring

Let `R` be a commutative local ring with finite residue field of `q` elements, whose maximal
ideal is measurable (for instance the ring of integers of a nonarchimedean local field, with its
Borel σ-algebra). For every left-invariant measure `μ` on `M_n(R)`, such as the additive Haar
probability measure when `R` is compact,
`μ(GL_n(R)) = #GL_n(F_q) / q^{n²} · μ(M_n(R)) = ∏_{i=1}^n (1 - q^{-i}) · μ(M_n(R))`.

Indeed a matrix is invertible exactly when its reduction modulo the maximal ideal is, so
`GL_n(R)` is the preimage of `GL_n(F_q)` under reduction. The fibres of reduction are the cosets
of its kernel, which all have the same measure by translation invariance, and there are `q^{n²}`
of them. The count `#GL_n(F_q) = ∏_{i=0}^{n-1} (q^n - q^i)` is Mathlib's `Matrix.card_GL_field`.

## Main results

* `MeasureTheory.measure_preimage_addMonoidHom`: for a surjective additive map `φ : G → F` onto a
  finite group with measurable kernel and a left-invariant measure `μ` on `G`, the preimage of
  `T ⊆ F` has measure `#T / #F · μ G`.
* `Matrix.measure_setOf_isUnit`: `μ(GL_n(R)) = #GL_n(F_q) / q^{n²} · μ(M_n(R))`.
* `Matrix.measureReal_setOf_isUnit`: for a probability measure,
  `μ(GL_n(R)) = ∏_{i=1}^n (1 - q^{-i})`.
-/

public section

open MeasureTheory Set IsLocalRing
open scoped ENNReal

namespace MeasureTheory

variable {G F : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] [AddGroup F] [Finite F]

/-- **Measure of a preimage under a map onto a finite group.** If `φ : G →+ F` is surjective onto
a finite group and has measurable kernel, then for every left-invariant measure `μ` on `G` the
preimage of `T ⊆ F` has measure `#T / #F · μ univ`: the fibres of `φ` are the translates of its
kernel, which all have the same measure. -/
theorem measure_preimage_addMonoidHom (μ : Measure G) [μ.IsAddLeftInvariant] (φ : G →+ F)
    (hφ : Function.Surjective φ) (hker : MeasurableSet (φ.ker : Set G)) (T : Set F) :
    μ (φ ⁻¹' T) = Nat.card T / Nat.card F * μ univ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hfib (t : F) : ∃ a, φ ⁻¹' {t} = (fun h => -a + h) ⁻¹' (φ.ker : Set G) := by
    obtain ⟨a, rfl⟩ := hφ t
    exact ⟨a, by ext x; simp only [mem_preimage, mem_singleton_iff, SetLike.mem_coe,
      AddMonoidHom.mem_ker, map_add, map_neg, neg_add_eq_zero]; exact eq_comm⟩
  have hfibm (t : F) : MeasurableSet (φ ⁻¹' {t}) := by
    obtain ⟨a, ha⟩ := hfib t
    rw [ha]
    exact hker.preimage (measurable_const_add _)
  have hfibμ (t : F) : μ (φ ⁻¹' {t}) = μ φ.ker := by
    obtain ⟨a, ha⟩ := hfib t
    rw [ha, measure_preimage_add]
  have hpre (S : Set F) : μ (φ ⁻¹' S) = Nat.card S * μ φ.ker := by
    have hS : φ ⁻¹' S = ⋃ t ∈ S.toFinset, φ ⁻¹' {t} := by ext; simp
    rw [hS, measure_biUnion_finset (fun s _ t _ hst => (disjoint_singleton.2 hst).preimage φ)
      fun t _ => hfibm t]
    simp [hfibμ]
  have hindex : φ.ker.index = Nat.card F := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hφ]
    exact Nat.card_congr (Equiv.Set.univ F)
  have : φ.ker.FiniteIndex := ⟨by rw [hindex]; exact Nat.card_pos.ne'⟩
  have huniv := AddSubgroup.index_mul_measure φ.ker hker μ
  rw [hindex] at huniv
  have hF0 : (Nat.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [hpre, ← huniv, ← mul_assoc, ENNReal.div_mul_cancel hF0 (ENNReal.natCast_ne_top _)]

end MeasureTheory

namespace Matrix

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Entrywise addition of matrices is measurable when addition of the entries is. -/
instance instMeasurableAddMatrix {m p α : Type*} [MeasurableSpace α] [Add α] [MeasurableAdd α] :
    MeasurableAdd (Matrix m p α) :=
  inferInstanceAs (MeasurableAdd (m → p → α))

/-- A square matrix over a local ring is invertible if and only if its reduction modulo the
maximal ideal is. -/
theorem isUnit_map_residue_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    IsUnit (M.map (residue R)) ↔ IsUnit M := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, isUnit_map_iff]

variable [MeasurableSpace R] [MeasurableAdd R] [Finite (ResidueField R)] (n : ℕ)

/-- **Measure of the invertible matrices over a local ring.** If `R` is a commutative local ring
with measurable maximal ideal and finite residue field of `q` elements, then every left-invariant
measure `μ` on `M_n(R)` gives the invertible matrices measure
`#GL_n(F_q) / q^{n²} · μ(M_n(R)) = ∏_{i=0}^{n-1} (q^n - q^i) / q^{n²} · μ(M_n(R))`. -/
theorem measure_setOf_isUnit (hm : MeasurableSet (maximalIdeal R : Set R))
    (μ : Measure (Matrix (Fin n) (Fin n) R)) [μ.IsAddLeftInvariant] :
    μ {M | IsUnit M} = ((∏ i : Fin n, (Nat.card (ResidueField R) ^ n -
      Nat.card (ResidueField R) ^ (i : ℕ)) : ℕ) : ℝ≥0∞) /
        (Nat.card (ResidueField R) ^ (n * n) : ℕ) * μ univ := by
  let k := ResidueField R
  have : Fintype k := Fintype.ofFinite k
  let φ : Matrix (Fin n) (Fin n) R →+ Matrix (Fin n) (Fin n) k :=
    (residue R).mapMatrix.toAddMonoidHom
  have hφ : Function.Surjective φ := fun N =>
    ⟨N.map (Function.surjInv (residue_surjective (R := R))), by
      ext i j; simp [φ, Function.surjInv_eq]⟩
  have hker : MeasurableSet (φ.ker : Set (Matrix (Fin n) (Fin n) R)) := by
    have : (φ.ker : Set (Matrix (Fin n) (Fin n) R)) =
        ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) R => M i j) ⁻¹' (maximalIdeal R : Set R) := by
      ext M
      simp [φ, AddMonoidHom.mem_ker, ← Matrix.ext_iff, residue_eq_zero_iff]
    rw [this]
    exact .iInter fun i => .iInter fun j => hm.preimage Matrix.measurable_apply
  have hset : {M : Matrix (Fin n) (Fin n) R | IsUnit M} = φ ⁻¹' {N | IsUnit N} := by
    ext M
    exact (isUnit_map_residue_iff M).symm
  have hGL : Nat.card {N : Matrix (Fin n) (Fin n) k | IsUnit N} =
      ∏ i : Fin n, (Nat.card k ^ n - Nat.card k ^ (i : ℕ)) := by
    rw [show Nat.card {N : Matrix (Fin n) (Fin n) k | IsUnit N} = Nat.card (GL (Fin n) k) from
      (Nat.card_congr (Equiv.ofInjective _ Units.val_injective)).symm, card_GL_field,
      Nat.card_eq_fintype_card (α := k)]
  have hM : Nat.card (Matrix (Fin n) (Fin n) k) = Nat.card k ^ (n * n) := by
    rw [show Nat.card (Matrix (Fin n) (Fin n) k) = Nat.card (Fin n → Fin n → k) from rfl]
    simp [← pow_mul]
  rw [hset, measure_preimage_addMonoidHom μ φ hφ hker, hGL, hM]

/-- **Haar probability of the invertible matrices over a local ring.** If `R` is a commutative
local ring with measurable maximal ideal and finite residue field of `q` elements, then every
left-invariant probability measure on `M_n(R)`, such as its additive Haar probability measure,
gives the invertible matrices measure `∏_{i=1}^n (1 - q^{-i})`. -/
theorem measureReal_setOf_isUnit (hm : MeasurableSet (maximalIdeal R : Set R))
    (μ : Measure (Matrix (Fin n) (Fin n) R)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    μ.real {M | IsUnit M} =
      ∏ i ∈ Finset.range n, (1 - ((Nat.card (ResidueField R) : ℝ)⁻¹) ^ (i + 1)) := by
  rw [measureReal_def, measure_setOf_isUnit n hm μ, measure_univ, mul_one, ENNReal.toReal_div]
  set q := Nat.card (ResidueField R)
  have hq : (q : ℝ) ≠ 0 := by
    have : Fintype (ResidueField R) := Fintype.ofFinite _
    exact_mod_cast Nat.card_pos.ne'
  have hcast : ((∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) : ℕ) : ℝ) =
      ∏ i : Fin n, ((q : ℝ) ^ n - (q : ℝ) ^ (i : ℕ)) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.pow_le_pow_right Nat.card_pos i.isLt.le)]
    push_cast
    rfl
  simp only [ENNReal.toReal_natCast]
  rw [hcast, Nat.cast_pow]
  have hden : ((q : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (q : ℝ) ^ n := by simp
  rw [Fin.prod_univ_eq_prod_range (fun i => (q : ℝ) ^ n - (q : ℝ) ^ i), mul_comm n n, pow_mul,
    hden, ← Finset.prod_div_distrib]
  refine Eq.trans ?_ (Finset.prod_range_reflect (fun i => 1 - ((q : ℝ)⁻¹) ^ (i + 1)) n)
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj : j < n := Finset.mem_range.1 hj
  rw [show n - 1 - j + 1 = n - j by omega, inv_pow, pow_sub₀ _ hq hj.le, sub_div,
    div_self (pow_ne_zero _ hq), mul_inv, inv_inv, div_eq_mul_inv, mul_comm]

end Matrix
