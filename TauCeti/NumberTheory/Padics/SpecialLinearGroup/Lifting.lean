/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Group.Matrix

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Ring.SubOnePow
import TauCeti.Data.ZMod.Ico
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Adjoint
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.Padics.Matrix

/-!
# Serre's lifting lemma for `SL₂(ℤ_ℓ)` and `GL₂(ℤ_ℓ)`

For a prime `ℓ ≥ 5`, a closed subgroup `H` of `SL₂(ℤ_ℓ)` whose reduction modulo `ℓ` is all of
`SL₂(𝔽_ℓ)` is all of `SL₂(ℤ_ℓ)`. This is the group-theoretic input of Serre's open image theorem:
an `ℓ`-adic Galois image is controlled by its residual image.

In the `GL₂` form, a closed subgroup `H` of `GL₂(ℤ_ℓ)` whose reduction modulo `ℓ` contains
`SL₂(𝔽_ℓ)` contains `SL₂(ℤ_ℓ)`: the closure of its commutator subgroup is a closed subgroup of
`SL₂(ℤ_ℓ)` reducing onto the perfect group `SL₂(𝔽_ℓ)`. So `H` is the full preimage of its image
under the determinant, and `H = GL₂(ℤ_ℓ)` exactly when `det H = ℤ_ℓˣ`. The residual condition alone
does not decide this: `ℤ_ℓˣ = μ_{ℓ - 1} × (1 + ℓ ℤ_ℓ)`, and the second factor is invisible modulo
`ℓ`.

## The proof

For `k ≥ 1` let `L_k ⊆ M₂(𝔽_ℓ)` be the set of reductions modulo `ℓ` of the matrices `X` with
`1 + ℓᵏ X ∈ H`, the `k`-th layer of `H`. Since `(1 + ℓᵏ X)(1 + ℓᵏ Y) ≡ 1 + ℓᵏ (X + Y)` modulo
`ℓᵏ⁺¹`, each `L_k` is an `𝔽_ℓ`-subspace; the determinant condition makes it trace-zero, and
conjugating by elements of `H` lifting `SL₂(𝔽_ℓ)` makes it stable under conjugation by
`SL₂(𝔽_ℓ)`. The adjoint representation `𝔰𝔩₂(𝔽_ℓ)` being irreducible for odd `ℓ`
(`TauCeti.eq_ker_traceLinearMap_of_conj_mem`), each `L_k` is `0` or all of `𝔰𝔩₂(𝔽_ℓ)`.

* `L_1 ≠ 0`: take `x ∈ H` lifting `u = [[1, 1], [0, 1]]` and write `x = 1 + A`, so that `ℓ ∣ A²`.
  Expanding `(1 + A)ˡ` to third order, the binomial coefficients `C(ℓ, 2)` and `C(ℓ, 3)` are
  divisible by `ℓ` when `ℓ ≥ 5`, so `xˡ = 1 + ℓ A` modulo `ℓ²`, and `xˡ ∈ H` puts the reduction
  `[[0, 1], [0, 0]]` of `A` into `L_1`. At `ℓ = 3` this fails, since `C(3, 3) = 1`.
* `L_k ⊆ L_{k+1}`: the `ℓ`-th power of `1 + ℓᵏ X` is `1 + ℓᵏ⁺¹ X` modulo `ℓᵏ⁺²`.

Hence `L_k = 𝔰𝔩₂(𝔽_ℓ)` for every `k ≥ 1`. By induction on `k`, every `g ∈ SL₂(ℤ_ℓ)` is then
congruent modulo `ℓᵏ` to an element of `H`: the error term of an approximation modulo `ℓᵏ` has
trace zero modulo `ℓ`, so it is absorbed by an element of `H` from the layer `L_k`. So `H` is dense,
and being closed it is everything.

## Main results

* `TauCeti.eq_top_of_isClosed_of_map_toZMod_eq_top`: for a prime `ℓ ≥ 5`, a closed subgroup of
  `SL₂(ℤ_ℓ)` that surjects onto `SL₂(𝔽_ℓ)` is all of `SL₂(ℤ_ℓ)`.
* `TauCeti.eq_comap_map_det_of_isClosed`: for a prime `ℓ ≥ 5`, a closed subgroup of `GL₂(ℤ_ℓ)`
  whose reduction contains `SL₂(𝔽_ℓ)` is the preimage of its determinant image.
* `TauCeti.eq_top_of_isClosed_of_map_det_eq_top`: if moreover its determinant is surjective, it is
  all of `GL₂(ℤ_ℓ)`.

## References

* J.-P. Serre, *Abelian ℓ-adic representations and elliptic curves*, W. A. Benjamin, 1968,
  IV-23, Lemma 3.
-/

public section

namespace TauCeti

open Matrix PadicInt Filter Topology

open scoped MatrixGroups commutatorElement

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### Reduction of matrices modulo `ℓ` -/

/-- If `1 + ℓ ^ (k + 1) X` has determinant `1`, the reduction of `X` modulo `ℓ` has trace zero. -/
private theorem trace_mapMatrix_eq_zero {k : ℕ} {X : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]}
    (hX : (1 + ℓ ^ (k + 1) • X).det = 1) : (toZMod.mapMatrix X).trace = 0 := by
  set c : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) ^ (k + 1) with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hℓ.out.ne_zero)
  rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], Nat.cast_pow, ← hc, det_fin_two] at hX
  simp only [Matrix.add_apply, one_apply_eq, Matrix.smul_apply, smul_eq_mul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_add, one_ne_zero] at hX
  have htr : X 0 0 + X 1 1 = -(c * (X 0 0 * X 1 1 - X 0 1 * X 1 0)) :=
    mul_left_cancel₀ hc0 (by linear_combination hX)
  have hred : toZMod c = 0 := by simp [hc, pow_succ]
  rw [trace_fin_two, RingHom.mapMatrix_apply, map_apply, map_apply, ← map_add, htr]
  simp [hred]

/-! ### The layers of a subgroup of `SL₂(ℤ_ℓ)` -/

/-- The reductions modulo `ℓ` of the matrices `X` with `1 + ℓ ^ (k + 1) X ∈ H`, as an additive
submonoid of `M₂(𝔽_ℓ)`. -/
private def layerAddSubmonoid (H : Subgroup SL(2, ℤ_[ℓ])) (k : ℕ) :
    AddSubmonoid (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {Y | ∃ X, toZMod.mapMatrix X = Y ∧
    ∃ h ∈ H, (h : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = 1 + ℓ ^ (k + 1) • X}
  zero_mem' := ⟨0, map_zero _, 1, H.one_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨X₁, rfl, h₁, hh₁, e₁⟩ ⟨X₂, rfl, h₂, hh₂, e₂⟩
    refine ⟨X₁ + X₂ + ℓ ^ (k + 1) • (X₁ * X₂), ?_, h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
    · have h0 := map_toZMod_nsmul_eq_zero (dvd_pow_self ℓ k.succ_ne_zero) (X₁ * X₂)
      rw [← RingHom.mapMatrix_apply] at h0
      rw [map_add, h0, add_zero, map_add]
    · rw [SpecialLinearGroup.coe_mul, e₁, e₂]
      simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, smul_add,
        smul_smul]
      abel

/-- The `k + 1`-st layer of `H`: the reductions modulo `ℓ` of the matrices `X` with
`1 + ℓ ^ (k + 1) X ∈ H`, an `𝔽_ℓ`-subspace of `M₂(𝔽_ℓ)`. -/
private def layer (H : Subgroup SL(2, ℤ_[ℓ])) (k : ℕ) :
    Submodule (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  __ := layerAddSubmonoid H k
  smul_mem' a Y hY := by
    rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul]
    exact AddSubmonoid.nsmul_mem _ hY _

/-- The layers consist of trace-zero matrices. -/
private theorem layer_le_ker_trace (H : Subgroup SL(2, ℤ_[ℓ])) (k : ℕ) :
    layer H k ≤ LinearMap.ker (traceLinearMap (Fin 2) (ZMod ℓ) (ZMod ℓ)) := by
  rintro _ ⟨X, rfl, h, -, e⟩
  rw [LinearMap.mem_ker, traceLinearMap_apply]
  exact trace_mapMatrix_eq_zero (e ▸ h.prop)

/-- If `H` surjects onto `SL₂(𝔽_ℓ)`, its layers are stable under conjugation by `SL₂(𝔽_ℓ)`. -/
private theorem conj_mem_layer {H : Subgroup SL(2, ℤ_[ℓ])}
    (hmap : H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤) (k : ℕ)
    (g : SL(2, ZMod ℓ)) (Y : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (hY : Y ∈ layer H k) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * Y * ((g⁻¹ : SL(2, ZMod ℓ)) :
      Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ∈ layer H k := by
  obtain ⟨X, rfl, h, hh, e⟩ := hY
  obtain ⟨h₀, hh₀, rfl⟩ : g ∈ H.map (SpecialLinearGroup.map toZMod) := hmap ▸ Subgroup.mem_top g
  refine ⟨h₀ * X * ((h₀⁻¹ : SL(2, ℤ_[ℓ])) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]), ?_,
    h₀ * h * h₀⁻¹, H.mul_mem (H.mul_mem hh₀ hh) (H.inv_mem hh₀), ?_⟩
  · simp [← map_inv]
  · have hinv : (h₀ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) *
        ((h₀⁻¹ : SL(2, ℤ_[ℓ])) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, e, mul_add, mul_one, add_mul,
      hinv, mul_smul_comm, smul_mul_assoc]

/-- The `ℓ`-th power map sends each layer into the next one. -/
private theorem layer_le_layer_succ (hℓ5 : 5 ≤ ℓ) (H : Subgroup SL(2, ℤ_[ℓ])) (k : ℕ) :
    layer H k ≤ layer H (k + 1) := by
  rintro _ ⟨X, rfl, h, hh, e⟩
  have hA : (ℓ ^ (k + 1) • X) ^ 2 = (ℓ ^ (k + 1) * ℓ) • (ℓ ^ k • X ^ 2) := by
    rw [smul_pow, smul_smul]
    ring_nf
  obtain ⟨W, hW⟩ := exists_one_add_pow_prime_eq_of_sq_eq_nsmul hℓ.out (by omega) hA
  refine ⟨X + ℓ • W, ?_, h ^ ℓ, H.pow_mem hh ℓ, ?_⟩
  · have h0 := map_toZMod_nsmul_eq_zero dvd_rfl W
    rw [← RingHom.mapMatrix_apply] at h0
    rw [map_add, h0, add_zero]
  · rw [SpecialLinearGroup.coe_pow, e, hW]
    module

/-- If `H` surjects onto `SL₂(𝔽_ℓ)` and `ℓ ≥ 5`, the first layer of `H` is nonzero: the `ℓ`-th
power of a lift in `H` of `[[1, 1], [0, 1]]` is `1 + ℓ A` with `A` reducing to
`[[0, 1], [0, 0]]`. -/
private theorem layer_zero_ne_bot (hℓ5 : 5 ≤ ℓ) {H : Subgroup SL(2, ℤ_[ℓ])}
    (hmap : H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤) : layer H 0 ≠ ⊥ := by
  let u : SL(2, ZMod ℓ) := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  obtain ⟨x, hx, hxu⟩ : u ∈ H.map (SpecialLinearGroup.map toZMod) := hmap ▸ Subgroup.mem_top u
  set A : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] := (x : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) - 1 with hA
  have hredA : toZMod.mapMatrix A = !![0, 1; 0, 0] := by
    have hxu' : toZMod.mapMatrix (x : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = u := by
      rw [← hxu, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rw [hA, map_sub, hxu', map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u]
  obtain ⟨B, hB⟩ : ∃ B, A ^ 2 = ℓ • B := by
    refine exists_eq_nsmul_of_map_toZMod_eq_zero ?_
    rw [← RingHom.mapMatrix_apply, map_pow, hredA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq]
  obtain ⟨W, hW⟩ := exists_one_add_pow_prime_eq_of_sq_eq_nsmul (c := 1) hℓ.out (by omega)
    (by rwa [one_mul])
  refine (Submodule.ne_bot_iff _).2 ⟨_, ⟨A + ℓ • W, rfl, x ^ ℓ, H.pow_mem hx ℓ, ?_⟩, ?_⟩
  · rw [SpecialLinearGroup.coe_pow, show (x : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = 1 + A by
      rw [hA, add_sub_cancel], hW]
    module
  · have h0 := map_toZMod_nsmul_eq_zero dvd_rfl W
    rw [← RingHom.mapMatrix_apply] at h0
    rw [map_add, h0, add_zero, hredA]
    intro h
    simpa using congrFun (congrFun h 0) 1

/-- If `H` surjects onto `SL₂(𝔽_ℓ)` and `ℓ ≥ 5`, every layer of `H` is all of `𝔰𝔩₂(𝔽_ℓ)`. -/
private theorem layer_eq_ker_trace (hℓ5 : 5 ≤ ℓ) {H : Subgroup SL(2, ℤ_[ℓ])}
    (hmap : H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤) (k : ℕ) :
    layer H k = LinearMap.ker (traceLinearMap (Fin 2) (ZMod ℓ) (ZMod ℓ)) := by
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    exact_mod_cast ZMod.natCast_ne_zero_of_mem_Ico (k := 2)
      (Finset.mem_Ico.2 ⟨by norm_num, by omega⟩)
  have h0 := eq_ker_traceLinearMap_of_conj_mem h2 (layer_le_ker_trace H 0)
    (layer_zero_ne_bot hℓ5 hmap) (conj_mem_layer hmap 0)
  refine le_antisymm (layer_le_ker_trace H k) ?_
  rw [← h0]
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (layer_le_layer_succ hℓ5 H k)

/-! ### Approximation and density -/

/-- If `H` surjects onto `SL₂(𝔽_ℓ)` and `ℓ ≥ 5`, every element of `SL₂(ℤ_ℓ)` is congruent modulo
`ℓ ^ (k + 1)` to an element of `H`. -/
private theorem exists_mem_eq_add_pow_smul (hℓ5 : 5 ≤ ℓ) {H : Subgroup SL(2, ℤ_[ℓ])}
    (hmap : H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤) (k : ℕ) (g : SL(2, ℤ_[ℓ])) :
    ∃ h ∈ H, ∃ Z, (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h + ℓ ^ (k + 1) • Z := by
  induction k with
  | zero =>
    obtain ⟨h, hh, hgh⟩ : SpecialLinearGroup.map toZMod g ∈ H.map (SpecialLinearGroup.map toZMod) :=
      hmap ▸ Subgroup.mem_top _
    obtain ⟨Z, hZ⟩ := exists_eq_nsmul_of_map_toZMod_eq_zero
      (X := (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) - (h : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])) (by
        rw [Matrix.map_sub _ (map_sub toZMod), ← SpecialLinearGroup.map_apply_coe,
          ← SpecialLinearGroup.map_apply_coe, hgh, sub_self])
    exact ⟨h, hh, Z, by rw [zero_add, pow_one, ← hZ, add_sub_cancel]⟩
  | succ k ih =>
    obtain ⟨h, hh, Z, hZ⟩ := ih
    set hinv : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] := ((h⁻¹ : SL(2, ℤ_[ℓ])) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])
    have hhinv : (h : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) * hinv = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    -- The error term `h⁻¹ g = 1 + ℓ ^ (k + 1) h⁻¹ Z` has trace zero modulo `ℓ`.
    have hdet : (1 + ℓ ^ (k + 1) • (hinv * Z)).det = 1 := by
      have : (1 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) + ℓ ^ (k + 1) • (hinv * Z) =
          ((h⁻¹ * g : SL(2, ℤ_[ℓ])) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) := by
        rw [SpecialLinearGroup.coe_mul, hZ, mul_add, mul_smul_comm, ← SpecialLinearGroup.coe_mul,
          inv_mul_cancel, SpecialLinearGroup.coe_one]
      rw [this]
      exact (h⁻¹ * g).prop
    have hmem : toZMod.mapMatrix (hinv * Z) ∈ layer H k := by
      rw [layer_eq_ker_trace hℓ5 hmap, LinearMap.mem_ker, traceLinearMap_apply]
      exact trace_mapMatrix_eq_zero hdet
    obtain ⟨X, hX, h', hh', e'⟩ := hmem
    obtain ⟨W, hW⟩ := exists_eq_nsmul_of_map_toZMod_eq_zero (X := hinv * Z - X)
      (by rw [← RingHom.mapMatrix_apply, map_sub, hX, sub_self])
    refine ⟨h * h', H.mul_mem hh hh', h * W, ?_⟩
    calc (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])
        = h + ℓ ^ (k + 1) • (h * (hinv * Z)) := by rw [hZ, ← mul_assoc, hhinv, one_mul]
      _ = h + ℓ ^ (k + 1) • (h * (X + ℓ • W)) := by rw [← hW, add_sub_cancel]
      _ = h * (1 + ℓ ^ (k + 1) • X) + ℓ ^ (k + 1 + 1) • (h * W) := by
        simp only [mul_add, mul_one, mul_smul_comm, smul_add, smul_smul, ← pow_succ]
        abel
      _ = ((h * h' : SL(2, ℤ_[ℓ])) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) + ℓ ^ (k + 1 + 1) • (h * W) := by
        rw [SpecialLinearGroup.coe_mul, e']

/-- Elements `h k` congruent to `g` modulo `ℓ ^ (k + 1)` converge to `g`. -/
private theorem tendsto_of_eq_add_pow_smul {g : SL(2, ℤ_[ℓ])} {h : ℕ → SL(2, ℤ_[ℓ])}
    {Z : ℕ → Matrix (Fin 2) (Fin 2) ℤ_[ℓ]}
    (hZ : ∀ k, (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h k + ℓ ^ (k + 1) • Z k) :
    Tendsto h atTop (𝓝 g) := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.out.pos
  have hlim : Tendsto (fun k : ℕ ↦ ((ℓ : ℝ)⁻¹) ^ (k + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hℓ0.le)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt))).comp (tendsto_add_atTop_nat 1)
  have hmat : Tendsto (fun k ↦ (h k : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])) atTop
      (𝓝 (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])) := by
    refine tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hlim)
    have hk := congrFun (congrFun (hZ k) i) j
    rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Nat.cast_pow] at hk
    rw [hk, sub_add_cancel_left, norm_neg, norm_mul, norm_pow, norm_p]
    exact mul_le_of_le_one_right (by positivity) (norm_le_one _)
  exact SpecialLinearGroup.isClosedEmbedding_val.isInducing.tendsto_nhds_iff.2 hmat

/-- **Serre's lifting lemma.** For a prime `ℓ ≥ 5`, a closed subgroup of `SL₂(ℤ_ℓ)` whose
reduction modulo `ℓ` is all of `SL₂(𝔽_ℓ)` is all of `SL₂(ℤ_ℓ)`. -/
theorem eq_top_of_isClosed_of_map_toZMod_eq_top (hℓ5 : 5 ≤ ℓ) {H : Subgroup SL(2, ℤ_[ℓ])}
    (hH : IsClosed (H : Set SL(2, ℤ_[ℓ])))
    (hmap : H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤) : H = ⊤ := by
  refine eq_top_iff.2 fun g _ ↦ ?_
  choose h hh Z hZ using fun k ↦ exists_mem_eq_add_pow_smul hℓ5 hmap k g
  rw [← SetLike.mem_coe, ← hH.closure_eq]
  exact mem_closure_of_tendsto (tendsto_of_eq_add_pow_smul hZ) (Eventually.of_forall hh)

/-! ### The `GL₂` form -/

/-- **Serre's lifting lemma, the `GL₂` form.** For a prime `ℓ ≥ 5`, a closed subgroup `H` of
`GL₂(ℤ_ℓ)` whose reduction modulo `ℓ` contains `SL₂(𝔽_ℓ)` contains `SL₂(ℤ_ℓ)`, so it is the full
preimage of its image under the determinant. -/
theorem eq_comap_map_det_of_isClosed (hℓ5 : 5 ≤ ℓ) {H : Subgroup (GL (Fin 2) ℤ_[ℓ])}
    (hH : IsClosed (H : Set (GL (Fin 2) ℤ_[ℓ])))
    (hsl : (SpecialLinearGroup.toGL : SL(2, ZMod ℓ) →* GL (Fin 2) (ZMod ℓ)).range ≤
      H.map (GeneralLinearGroup.map (toZMod (p := ℓ)))) :
    H = (H.map GeneralLinearGroup.det).comap GeneralLinearGroup.det := by
  -- The closure `C` of the commutator subgroup of `H` lies in `H`, and its determinant-one part
  -- `K`, a closed subgroup of `SL₂(ℤ_ℓ)`, reduces onto the perfect group `SL₂(𝔽_ℓ)`.
  set C := ⁅H, H⁆.topologicalClosure
  have hCH : C ≤ H := Subgroup.topologicalClosure_minimal _
    (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ ↦ by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)) hH
  set K := C.comap SpecialLinearGroup.toGL
  have hK : IsClosed (K : Set SL(2, ℤ_[ℓ])) :=
    (Subgroup.isClosed_topologicalClosure ⁅H, H⁆).preimage SpecialLinearGroup.continuous_toGL
  have hKmap : K.map (SpecialLinearGroup.map toZMod) = ⊤ := by
    have h2 : (2 : ZMod ℓ) ≠ 0 := by
      exact_mod_cast ZMod.natCast_ne_zero_of_mem_Ico (k := 2)
        (Finset.mem_Ico.2 ⟨by norm_num, by omega⟩)
    have h3 : (3 : ZMod ℓ) ≠ 0 := by
      exact_mod_cast ZMod.natCast_ne_zero_of_mem_Ico (k := 3)
        (Finset.mem_Ico.2 ⟨by norm_num, by omega⟩)
    have h4 : (2 : ZMod ℓ) ^ 2 ≠ 1 := fun h ↦ h3 (by linear_combination h)
    rw [eq_top_iff, ← SL2.commutator_eq_top h2 h4, commutator_def, Subgroup.commutator_le]
    rintro t₁ - t₂ -
    obtain ⟨g₁, hg₁, e₁⟩ := hsl ⟨t₁, rfl⟩
    obtain ⟨g₂, hg₂, e₂⟩ := hsl ⟨t₂, rfl⟩
    obtain ⟨k, hk⟩ :
        ⁅g₁, g₂⁆ ∈ (SpecialLinearGroup.toGL : SL(2, ℤ_[ℓ]) →* GL (Fin 2) ℤ_[ℓ]).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, commutatorElement_def]
      simp
    refine ⟨k, ?_, SpecialLinearGroup.toGL_injective ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, hk]
      exact Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator hg₁ hg₂)
    · rw [SpecialLinearGroup.toGL_map, hk, map_commutatorElement, e₁, e₂, map_commutatorElement]
  have hSL : (SpecialLinearGroup.toGL : SL(2, ℤ_[ℓ]) →* GL (Fin 2) ℤ_[ℓ]).range ≤ H := by
    rintro _ ⟨s, rfl⟩
    have hs : s ∈ K := eq_top_of_isClosed_of_map_toZMod_eq_top hℓ5 hK hKmap ▸ Subgroup.mem_top s
    exact hCH hs
  refine le_antisymm (Subgroup.le_comap_map _ _) fun g ⟨h, hh, hdet⟩ ↦ ?_
  have hhg : h⁻¹ * g ∈ H := hSL <| by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, map_mul, map_inv, hdet,
      inv_mul_cancel]
  simpa using H.mul_mem hh hhg

/-- For a prime `ℓ ≥ 5`, a closed subgroup of `GL₂(ℤ_ℓ)` whose reduction modulo `ℓ` contains
`SL₂(𝔽_ℓ)` and whose determinant is surjective onto `ℤ_ℓˣ` is all of `GL₂(ℤ_ℓ)`. -/
theorem eq_top_of_isClosed_of_map_det_eq_top (hℓ5 : 5 ≤ ℓ) {H : Subgroup (GL (Fin 2) ℤ_[ℓ])}
    (hH : IsClosed (H : Set (GL (Fin 2) ℤ_[ℓ])))
    (hsl : (SpecialLinearGroup.toGL : SL(2, ZMod ℓ) →* GL (Fin 2) (ZMod ℓ)).range ≤
      H.map (GeneralLinearGroup.map (toZMod (p := ℓ))))
    (hdet : H.map GeneralLinearGroup.det = ⊤) : H = ⊤ := by
  rw [eq_comap_map_det_of_isClosed hℓ5 hH hsl, hdet, Subgroup.comap_top]

end TauCeti
