/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.Ring.QPochhammer.Basic
public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.MeasureTheory.Group.Measure
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse

/-!
# Haar measure of the invertible matrices over a local ring

Let `R` be a commutative local ring with finite residue field of `q` elements, whose maximal
ideal is measurable (for instance the ring of integers of a nonarchimedean local field, with its
Borel σ-algebra). For every left-invariant measure `μ` on `M_n(R)`, such as the additive Haar
probability measure when `R` is compact,
`μ(GL_n(R)) = #GL_n(F_q) / q^{n²} · μ(M_n(R)) = (q⁻¹; q⁻¹)_n · μ(M_n(R))`, where the q-Pochhammer
product `(q⁻¹; q⁻¹)_n` is `∏_{i=1}^n (1 - q^{-i})`.

Indeed a matrix is invertible exactly when its reduction modulo the maximal ideal is
(`Matrix.isUnit_map_iff`), so `GL_n(R)` is the preimage of `GL_n(F_q)` under reduction. The fibres
of reduction are the cosets of its kernel, which all have the same measure by translation
invariance (`MeasureTheory.measure_preimage_addMonoidHom`), and there are `q^{n²}` of them. The
count `#GL_n(F_q) = ∏_{i=0}^{n-1} (q^n - q^i)` is Mathlib's `Matrix.card_GL_field`, and
`TauCeti.prod_range_pow_sub_pow_div_pow` rewrites `#GL_n(F_q) / q^{n²}` as `(q⁻¹; q⁻¹)_n`.

## Main results

* `Matrix.measure_setOf_isUnit`: `μ(GL_n(R)) = #GL_n(F_q) / q^{n²} · μ(M_n(R))`.
* `Matrix.measureReal_setOf_isUnit`: for a probability measure,
  `μ(GL_n(R)) = (q⁻¹; q⁻¹)_n = ∏_{i=1}^n (1 - q^{-i})`.
* `IsLocalRing.measureReal_setOf_isUnit`: the case `n = 1`, transported along `R ≃ M_1(R)`: the
  units of `R` have measure `1 - q⁻¹` for every left-invariant probability measure on `R`.
-/

public section

open MeasureTheory Set IsLocalRing
open scoped ENNReal

namespace Matrix

variable {R : Type*} [CommRing R] [IsLocalRing R] [MeasurableSpace R] [MeasurableAdd R]
  [Finite (ResidueField R)] (n : ℕ)

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
    simp [φ, RingHom.mapMatrix_apply]
  have hGL : Nat.card {N : Matrix (Fin n) (Fin n) k | IsUnit N} =
      ∏ i : Fin n, (Nat.card k ^ n - Nat.card k ^ (i : ℕ)) := by
    have e : GL (Fin n) k ≃ {N : Matrix (Fin n) (Fin n) k | IsUnit N} :=
      Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv.trans <|
        Equiv.subtypeEquivRight fun N ↦ IsUnit.mem_submonoid_iff N
    rw [← Nat.card_congr e, card_GL_field, Nat.card_eq_fintype_card (α := k)]
  have hM : Nat.card (Matrix (Fin n) (Fin n) k) = Nat.card k ^ (n * n) := by
    rw [card_matrix, Nat.card_fin]
  rw [hset, measure_preimage_addMonoidHom μ φ hφ hker, hGL, hM]

/-- **Haar probability of the invertible matrices over a local ring.** If `R` is a commutative
local ring with measurable maximal ideal and finite residue field of `q` elements, then every
left-invariant probability measure on `M_n(R)`, such as its additive Haar probability measure,
gives the invertible matrices measure the q-Pochhammer product
`(q⁻¹; q⁻¹)_n = ∏_{i=1}^n (1 - q^{-i})`. -/
theorem measureReal_setOf_isUnit (hm : MeasurableSet (maximalIdeal R : Set R))
    (μ : Measure (Matrix (Fin n) (Fin n) R)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    μ.real {M | IsUnit M} = TauCeti.qPochhammer ((Nat.card (ResidueField R) : ℝ)⁻¹)
      (Nat.card (ResidueField R) : ℝ)⁻¹ n := by
  rw [measureReal_def, measure_setOf_isUnit n hm μ, measure_univ, mul_one, ENNReal.toReal_div]
  set q := Nat.card (ResidueField R)
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hcast : ((∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) : ℕ) : ℝ) =
      ∏ i : Fin n, ((q : ℝ) ^ n - (q : ℝ) ^ (i : ℕ)) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.pow_le_pow_right Nat.card_pos i.isLt.le), Nat.cast_pow, Nat.cast_pow]
  simp only [ENNReal.toReal_natCast]
  rw [hcast, Nat.cast_pow, Fin.prod_univ_eq_prod_range (fun i => (q : ℝ) ^ n - (q : ℝ) ^ i),
    TauCeti.prod_range_pow_sub_pow_div_pow hq]

end Matrix

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [MeasurableSpace R] [MeasurableAdd R]
  [Finite (ResidueField R)]

/-- **Haar probability of the units of a local ring.** If `R` is a commutative local ring with
measurable maximal ideal and finite residue field of `q` elements, then every left-invariant
probability measure on `R`, such as its additive Haar probability measure, gives the units
measure `1 - q⁻¹`. This is the case `n = 1` of `Matrix.measureReal_setOf_isUnit`, transported
along `R ≃ M_1(R)`. -/
theorem measureReal_setOf_isUnit (hm : MeasurableSet (maximalIdeal R : Set R)) (μ : Measure R)
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    μ.real {x | IsUnit x} = 1 - (Nat.card (ResidueField R) : ℝ)⁻¹ := by
  let e : R ≃ᵐ Matrix (Fin 1) (Fin 1) R :=
    (MeasurableEquiv.funUnique (Fin 1) R).symm.trans <|
      (MeasurableEquiv.funUnique (Fin 1) (Fin 1 → R)).symm.trans (Matrix.ofMeasurableEquiv _ _ _)
  let f : R →ₙ+ Matrix (Fin 1) (Fin 1) R :=
    { toFun := e
      map_add' := fun x y ↦ by ext i j; simp [e] }
  have : (μ.map e).IsAddLeftInvariant := isAddLeftInvariant_map f e.measurable e.surjective
  have hset : e ⁻¹' {M | IsUnit M} = {x | IsUnit x} := by
    ext x
    simp [e, Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
  have h := Matrix.measureReal_setOf_isUnit 1 hm (μ.map e)
  rwa [measureReal_def, e.map_apply, hset, ← measureReal_def, TauCeti.qPochhammer_one] at h

end IsLocalRing
