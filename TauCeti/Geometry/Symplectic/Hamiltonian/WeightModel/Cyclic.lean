/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Cyclic groups of rotations of `ℂ^ι` and their fixed loci

A single rotation `R = TauCeti.weightRotation θ`, `z_i ↦ exp(i θ_i) z_i`, of `ℂ^ι` generates the
cyclic group of rotations `R^n = weightRotation (n • θ)`, `n : ℤ`, which preserve the standard
symplectic form (`TauCeti.stdSymplecticForm_weightRotation`) and the Euclidean metric. This file
computes its fixed locus and its order.

* A point is fixed by every `R^n` exactly when it is fixed by `R`
  (`TauCeti.forall_weightRotation_zsmul_apply_eq_self_iff`), exactly when it vanishes in every
  coordinate `i` whose angle `θ_i` is not in `2πℤ`
  (`TauCeti.mem_fixedSubmodule_weightRotation_iff`). The fixed locus is a complex subspace, of real
  dimension twice the number of angles in `2πℤ`
  (`TauCeti.finrank_fixedSubmodule_weightRotation`).
* The group is infinite cyclic, that is `n ↦ R^n` is injective, exactly when some `θ_i / 2π` is
  irrational (`TauCeti.weightRotation_zsmul_injective_iff`).

For an irrational `a`, the rotation `(z₁, z₂) ↦ (exp(2πia) z₁, z₂)` of `ℂ²` thus generates an
infinite cyclic group of symplectic isometries, dense in a circle but not closed, whose fixed locus
is the complex line `{0} × ℂ`, of real dimension `2`
(`TauCeti.weightRotation_zsmul_injective_of_irrational`,
`TauCeti.forall_weightRotation_zsmul_apply_eq_self_iff_of_irrational`,
`TauCeti.finrank_fixedSubmodule_weightRotation_of_irrational`). This is the standard example for
fixed loci of groups of symplectomorphisms preserving a metric, a theorem that needs no
compactness or topology on the group.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed loci of groups of symplectomorphisms preserving
  a metric).
-/

public section

noncomputable section

namespace TauCeti

open Real

variable {ι : Type*} [Fintype ι]

/-- A point of `ℂ^ι` is fixed by the rotation by `θ` exactly when its coordinates vanish wherever
the angle `θ_i` is not a multiple of `2π`. -/
theorem mem_fixedSubmodule_weightRotation_iff (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    x ∈ LinearMap.fixedSubmodule (weightRotation θ).toLinearMap ↔
      ∀ i, (¬ ∃ k : ℤ, k * (2 * π) = θ i) → x.1 i = 0 ∧ x.2 i = 0 := by
  rw [LinearMap.mem_fixedSubmodule_iff, ContinuousLinearMap.coe_coe,
    weightRotation_apply_eq_self_iff]
  exact forall_congr' fun i ↦ by tauto

/-- **The dimension of the fixed locus of a rotation.** The fixed subspace of the rotation by `θ`
has real dimension twice the number of angles `θ_i` in `2πℤ`. -/
theorem finrank_fixedSubmodule_weightRotation (θ : ι → ℝ) :
    Module.finrank ℝ (LinearMap.fixedSubmodule (weightRotation θ).toLinearMap) =
      2 * {i | ∃ k : ℤ, k * (2 * π) = θ i}.ncard := by
  classical
  -- The fixed subspace is the kernel of the generator with angle `0` on the coordinates whose
  -- angle lies in `2πℤ` and `1` on the others.
  let θ' : ι → ℝ := fun i ↦ if ∃ k : ℤ, k * (2 * π) = θ i then 0 else 1
  have hθ' : ∀ i, θ' i = 0 ↔ ∃ k : ℤ, k * (2 * π) = θ i := fun i ↦ by
    by_cases h : ∃ k : ℤ, k * (2 * π) = θ i <;> simp [θ', h]
  have hker : LinearMap.fixedSubmodule (weightRotation θ).toLinearMap =
      LinearMap.ker (weightGenerator θ').toLinearMap := by
    ext x
    rw [mem_fixedSubmodule_weightRotation_iff, mem_ker_weightGenerator_iff]
    exact forall_congr' fun i ↦ by rw [Ne, hθ']
  rw [hker, finrank_ker_weightGenerator]
  simp only [hθ']

/-- A point is fixed by every power of a rotation exactly when it is fixed by the rotation. -/
theorem forall_weightRotation_zsmul_apply_eq_self_iff (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ n : ℤ, weightRotation (n • θ) x = x) ↔ weightRotation θ x = x := by
  refine ⟨fun h ↦ by simpa using h 1, fun h n ↦ ?_⟩
  rw [weightRotation_apply_eq_self_iff] at h ⊢
  intro i hi
  obtain ⟨k, hk⟩ := h i hi
  exact ⟨n * k, by simp [← hk]; ring⟩

/-- **When a rotation has infinite order.** The powers `weightRotation (n • θ)`, `n : ℤ`, of the
rotation by `θ` are pairwise distinct exactly when some `θ_i / 2π` is irrational. -/
theorem weightRotation_zsmul_injective_iff (θ : ι → ℝ) :
    Function.Injective (fun n : ℤ ↦ weightRotation (n • θ)) ↔
      ∃ i, Irrational (θ i / (2 * π)) := by
  have hπ : (2 * π) ≠ 0 := by positivity
  -- `R^n = R^m` exactly when `R^(n - m)` is the identity.
  have hpow (n m : ℤ) : weightRotation (n • θ) = weightRotation (m • θ) ↔
      ∀ j, ∃ k : ℤ, k * (2 * π) = (n - m) * θ j := by
    have hid : weightRotation ((n - m) • θ) = ContinuousLinearMap.id ℝ _ ↔
        ∀ j, ∃ k : ℤ, k * (2 * π) = (n - m) * θ j := by
      rw [weightRotation_eq_id_iff]
      simp [zsmul_eq_mul]
    rw [← hid]
    constructor
    · intro h
      rw [sub_smul, sub_eq_add_neg, weightRotation_add, h, ← weightRotation_add, add_neg_cancel,
        weightRotation_zero]
    · intro h
      rw [← sub_add_cancel n m, add_smul, weightRotation_add, h, ContinuousLinearMap.id_comp]
  constructor
  · intro hinj
    by_contra! hrat
    -- Every `θ_j / 2π` is rational; a common denominator `N` gives `R^N = R^0`.
    have hq : ∀ j, ∃ q : ℚ, (q : ℝ) = θ j / (2 * π) := fun j ↦ by
      simpa [Irrational] using hrat j
    choose q hq using hq
    set N : ℕ := ∏ j, (q j).den
    have hN : (N : ℤ) ≠ 0 := by
      exact_mod_cast Finset.prod_ne_zero_iff.2 fun j _ ↦ (q j).den_nz
    refine hN (hinj ((hpow N 0).2 fun j ↦ ?_))
    obtain ⟨c, hc⟩ : ((q j).den : ℤ) ∣ N := by
      exact_mod_cast Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (Finset.mem_univ j)
    refine ⟨(q j).num * c, ?_⟩
    have hθ : θ j = q j * (2 * π) := by rw [hq j]; field_simp
    have hqd : ((q j).num : ℝ) = q j * (q j).den := by
      exact_mod_cast (Rat.mul_den_eq_num (q j)).symm
    have hNc : ((N : ℤ) : ℝ) = (q j).den * c := by exact_mod_cast hc
    rw [hθ, Int.cast_zero, sub_zero, hNc]
    push_cast
    linear_combination (c * (2 * π)) * hqd
  · rintro ⟨i, hi⟩ n m hnm
    obtain ⟨k, hk⟩ := (hpow n m).1 hnm i
    by_contra hne
    have hsub : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
    refine hi ⟨k / (n - m : ℤ), ?_⟩
    push_cast at hsub ⊢
    rw [eq_div_iff hπ, div_mul_eq_mul_div, div_eq_iff hsub, hk]
    ring

/-! ### An irrational rotation of the first factor of `ℂ²` -/

section Irrational

variable {a : ℝ}

/-- An irrational rotation `(z₁, z₂) ↦ (exp(2πia) z₁, z₂)` of `ℂ²` generates an infinite cyclic
group. -/
theorem weightRotation_zsmul_injective_of_irrational (ha : Irrational a) :
    Function.Injective (fun n : ℤ ↦ weightRotation (n • ![2 * π * a, 0])) :=
  (weightRotation_zsmul_injective_iff _).2 ⟨0, by
    rw [Matrix.cons_val_zero, mul_comm, mul_div_cancel_right₀ _ (by positivity)]
    exact ha⟩

/-- The common fixed locus of the infinite cyclic group generated by the irrational rotation
`(z₁, z₂) ↦ (exp(2πia) z₁, z₂)` of `ℂ²` is the complex line `{0} × ℂ`. -/
theorem forall_weightRotation_zsmul_apply_eq_self_iff_of_irrational (ha : Irrational a)
    (x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    (∀ n : ℤ, weightRotation (n • ![2 * π * a, 0]) x = x) ↔ x.1 0 = 0 ∧ x.2 0 = 0 := by
  rw [forall_weightRotation_zsmul_apply_eq_self_iff, ← ContinuousLinearMap.coe_coe,
    ← LinearMap.mem_fixedSubmodule_iff, mem_fixedSubmodule_weightRotation_iff, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨fun h ↦ h.1 fun ⟨k, hk⟩ ↦ ha ⟨k, ?_⟩,
    fun h ↦ ⟨fun _ ↦ h, fun h0 ↦ (h0 ⟨0, by simp⟩).elim⟩⟩
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp at hk
  exact_mod_cast hk

/-- The fixed locus `{0} × ℂ` of an irrational rotation of the first factor of `ℂ²` has real
dimension `2`. -/
theorem finrank_fixedSubmodule_weightRotation_of_irrational (ha : Irrational a) :
    Module.finrank ℝ
      (LinearMap.fixedSubmodule (weightRotation ![2 * π * a, 0]).toLinearMap) = 2 := by
  rw [finrank_fixedSubmodule_weightRotation]
  have hset : {i : Fin 2 | ∃ k : ℤ, k * (2 * π) = ![2 * π * a, 0] i} = {1} := by
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Set.mem_ofPred_eq,
        Set.mem_singleton_iff, zero_ne_one, iff_false, not_exists]
      intro k hk
      refine ha ⟨k, ?_⟩
      have hπ : π ≠ 0 := pi_ne_zero
      field_simp at hk
      exact_mod_cast hk
    · simp
  rw [hset, Set.ncard_singleton]

end Irrational

end TauCeti
