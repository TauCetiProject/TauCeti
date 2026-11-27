/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Group.Matrix

import Mathlib.RingTheory.ZMod.LocalRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Ring.SubOnePow
import TauCeti.Data.ZMod.Ico
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Commutator
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Adjoint
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Lift
import TauCeti.NumberTheory.Padics.Matrix
import TauCeti.NumberTheory.Padics.PrincipalUnits
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Diagonal

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

For `ℓ = 3` the residual statement is false, because `SL₂(ℤ/9) → SL₂(𝔽₃)` has a section; the
correct threshold is `9`. For every odd prime `ℓ`, a closed subgroup of `SL₂(ℤ_ℓ)` that surjects
onto `SL₂(ℤ/ℓ²)` is all of `SL₂(ℤ_ℓ)`, and a closed subgroup of `GL₂(ℤ_ℓ)` that surjects onto
`GL₂(ℤ/ℓ²)` is all of `GL₂(ℤ_ℓ)`. In the `GL₂` case the determinant needs no separate hypothesis:
modulo `ℓ²` the determinant image contains a unit of exact level `1`, which topologically generates
`1 + ℓ ℤ_ℓ`.

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
  `[[0, 1], [0, 0]]` of `A` into `L_1`. At `ℓ = 3` this fails, since `C(3, 3) = 1`. If instead
  `H` surjects onto `SL₂(ℤ/ℓ²)`, some element of `H` is congruent to `[[1, ℓ], [0, 1]]` modulo
  `ℓ²`, which again puts `[[0, 1], [0, 0]]` into `L_1`, for every odd `ℓ`.
* `L_k ⊆ L_{k+1}` for odd `ℓ`: the `ℓ`-th power of `1 + ℓᵏ X` is `1 + ℓᵏ⁺¹ X` modulo `ℓᵏ⁺²`.

Hence `L_k = 𝔰𝔩₂(𝔽_ℓ)` for every `k ≥ 1`. By induction on `k`, every `g ∈ SL₂(ℤ_ℓ)` is then
congruent modulo `ℓᵏ` to an element of `H`: the error term of an approximation modulo `ℓᵏ` has
trace zero modulo `ℓ`, so it is absorbed by an element of `H` from the layer `L_k`. So `H` is dense,
and being closed it is everything. This approximation and density step is stated separately, from
an arbitrary starting level `ℓ ^ (k₀ + 1)`: the version modulo `ℓ²` runs it from `k₀ = 1`.

The `GL₂` forms apply the `SL₂` statements to the determinant-one part of the closure of `⁅H, H⁆`.
Modulo `ℓ` its reduction is onto because `SL₂(𝔽_ℓ)` is perfect for `ℓ ≥ 5`; modulo `ℓ²` because the
commutator subgroup of `GL₂(ℤ/ℓ²)` is `SL₂(ℤ/ℓ²)` for odd `ℓ`
(`Matrix.GeneralLinearGroup.commutator_eq_ker_det_fin_two_of_isLocalRing`).

## Main results

* `TauCeti.eq_top_of_isClosed_of_map_toZMod_eq_top`: for a prime `ℓ ≥ 5`, a closed subgroup of
  `SL₂(ℤ_ℓ)` that surjects onto `SL₂(𝔽_ℓ)` is all of `SL₂(ℤ_ℓ)`.
* `TauCeti.exists_mem_eq_add_pow_smul_of_le` and
  `TauCeti.eq_top_of_isClosed_of_exists_mem_eq_add_pow_smul`: if every element of `SL₂(ℤ_ℓ)` is
  approximated modulo `ℓ ^ (k₀ + 1)` by elements of `H`, and every layer from `L_{k₀+1}` on is all
  of `𝔰𝔩₂(𝔽_ℓ)`, then every element is approximated modulo every `ℓ ^ (k + 1)`, `k ≥ k₀`; so a
  closed such `H` is all of `SL₂(ℤ_ℓ)`.
* `TauCeti.eq_comap_map_det_of_isClosed`: for a prime `ℓ ≥ 5`, a closed subgroup of `GL₂(ℤ_ℓ)`
  whose reduction contains `SL₂(𝔽_ℓ)` is the preimage of its determinant image.
* `TauCeti.eq_top_of_isClosed_of_map_det_eq_top`: if moreover its determinant is surjective, it is
  all of `GL₂(ℤ_ℓ)`.
* `TauCeti.exists_mem_eq_add_pow_smul_of_map_eq_top`: if `H` surjects onto `SL₂(R)` along a ring
  homomorphism `ℤ_ℓ →+* R` with kernel inside `ℓⁿ ℤ_ℓ`, every element of `SL₂(ℤ_ℓ)` is congruent
  modulo `ℓⁿ` to an element of `H`.
* `TauCeti.eq_top_of_isClosed_of_map_toZModPow_two_eq_top`: for an odd prime `ℓ`, a closed subgroup
  of `SL₂(ℤ_ℓ)` that surjects onto `SL₂(ℤ/ℓ²)` is all of `SL₂(ℤ_ℓ)`.
* `TauCeti.eq_top_of_isClosed_of_map_generalLinearGroupMap_toZModPow_two_eq_top`: for an odd prime
  `ℓ`, a closed subgroup of `GL₂(ℤ_ℓ)` that surjects onto `GL₂(ℤ/ℓ²)` is all of `GL₂(ℤ_ℓ)`.

## References

* J.-P. Serre, *Abelian ℓ-adic representations and elliptic curves*, W. A. Benjamin, 1968,
  IV-23, Lemma 3.
-/

public section

namespace TauCeti

open Matrix PadicInt Filter Topology

open scoped MatrixGroups commutatorElement

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### The layers of a subgroup of `SL₂(ℤ_ℓ)` -/

/-- The reductions modulo `ℓ` of the matrices `X` with `1 + ℓ ^ (k + 1) X ∈ H`, as an additive
submonoid of `M₂(𝔽_ℓ)`. -/
private def layerAddSubmonoid (H : Subgroup SL(2, ℤ_[ℓ])) (k : ℕ) :
    AddSubmonoid (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {Y | ∃ X, X.map toZMod = Y ∧
    ∃ h ∈ H, (h : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = 1 + ℓ ^ (k + 1) • X}
  zero_mem' := ⟨0, Matrix.map_zero _ (map_zero _), 1, H.one_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨X₁, rfl, h₁, hh₁, e₁⟩ ⟨X₂, rfl, h₂, hh₂, e₂⟩
    refine ⟨X₁ + X₂ + ℓ ^ (k + 1) • (X₁ * X₂), ?_, h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
    · exact (map_toZMod_add_nsmul (dvd_pow_self ℓ k.succ_ne_zero) _ _).trans
        (Matrix.map_add _ (map_add _) X₁ X₂)
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
  exact trace_map_toZMod_eq_zero_of_det_one_add_nsmul (dvd_pow_self ℓ k.succ_ne_zero)
    (pow_ne_zero _ hℓ.out.ne_zero) (e ▸ h.prop)

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
  · rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, e, mul_add, mul_one, add_mul,
      SpecialLinearGroup.coe_mul_coe_inv, mul_smul_comm, smul_mul_assoc]

/-- For odd `ℓ`, the `ℓ`-th power map sends each layer into the next one. -/
private theorem layer_le_layer_succ (hℓ2 : ℓ ≠ 2) (H : Subgroup SL(2, ℤ_[ℓ])) (k : ℕ) :
    layer H k ≤ layer H (k + 1) := by
  rintro _ ⟨X, rfl, h, hh, e⟩
  obtain ⟨W, hW⟩ := exists_one_add_prime_pow_succ_nsmul_pow_eq hℓ.out (.inl hℓ2) X
  refine ⟨X + ℓ • W, map_toZMod_add_nsmul dvd_rfl X W, h ^ ℓ, H.pow_mem hh ℓ, ?_⟩
  rw [SpecialLinearGroup.coe_pow, e, hW]

/-- If `H` surjects onto `SL₂(𝔽_ℓ)` and `ℓ ≥ 5`, the first layer of `H` is nonzero: the `ℓ`-th
power of a lift in `H` of `[[1, 1], [0, 1]]` is `1 + ℓ A` with `A` reducing to
`[[0, 1], [0, 0]]`. -/
private theorem layer_zero_ne_bot (hℓ5 : 5 ≤ ℓ) {H : Subgroup SL(2, ℤ_[ℓ])}
    (hmap : H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤) : layer H 0 ≠ ⊥ := by
  let u : SL(2, ZMod ℓ) := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  obtain ⟨x, hx, hxu⟩ : u ∈ H.map (SpecialLinearGroup.map toZMod) := hmap ▸ Subgroup.mem_top u
  set A : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] := (x : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) - 1 with hA
  have hredA : A.map toZMod = !![0, 1; 0, 0] := by
    rw [hA, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      ← SpecialLinearGroup.map_apply_coe, hxu]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u]
  obtain ⟨B, hB⟩ : ∃ B, A ^ 2 = ℓ • B := by
    refine exists_eq_nsmul_of_map_toZMod_eq_zero ?_
    rw [Matrix.map_pow, hredA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq]
  obtain ⟨W, hW⟩ := exists_one_add_pow_prime_eq_of_sq_eq_nsmul (c := 1) hℓ.out (by omega)
    (by rwa [one_mul])
  refine (Submodule.ne_bot_iff _).2 ⟨A.map toZMod,
    ⟨A + ℓ • W, map_toZMod_add_nsmul dvd_rfl A W, x ^ ℓ, H.pow_mem hx ℓ, ?_⟩, ?_⟩
  · rw [SpecialLinearGroup.coe_pow, show (x : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = 1 + A by
      rw [hA, add_sub_cancel], hW]
    module
  · rw [hredA]
    intro h
    simpa using congrFun (congrFun h 0) 1

/-- If `ℓ` is odd, `H` surjects onto `SL₂(𝔽_ℓ)` and the first layer of `H` is nonzero, every layer
of `H` is all of `𝔰𝔩₂(𝔽_ℓ)`. -/
private theorem layer_eq_ker_trace (hℓ2 : ℓ ≠ 2) {H : Subgroup SL(2, ℤ_[ℓ])}
    (hmap : H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤) (h0 : layer H 0 ≠ ⊥) (k : ℕ) :
    layer H k = LinearMap.ker (traceLinearMap (Fin 2) (ZMod ℓ) (ZMod ℓ)) := by
  have h0 := eq_ker_traceLinearMap_of_conj_mem
    (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])) (layer_le_ker_trace H 0) h0
    (conj_mem_layer hmap 0)
  refine le_antisymm (layer_le_ker_trace H k) ?_
  rw [← h0]
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (layer_le_layer_succ hℓ2 H k)

/-! ### Approximation and density -/

/-- Let `f : ℤ_ℓ →+* R` be a ring homomorphism whose kernel consists of multiples of `ℓ ^ n`, such
as reduction modulo `ℓ` (`n = 1`) or truncation modulo `ℓ ^ n`. If `H` surjects onto `SL₂(R)`
along `f`, every element of `SL₂(ℤ_ℓ)` is congruent modulo `ℓ ^ n` to an element of `H`. -/
theorem exists_mem_eq_add_pow_smul_of_map_eq_top {R : Type*} [CommRing R] (f : ℤ_[ℓ] →+* R)
    {n : ℕ} (hf : ∀ x, f x = 0 → (ℓ : ℤ_[ℓ]) ^ n ∣ x) {H : Subgroup SL(2, ℤ_[ℓ])}
    (hmap : H.map (SpecialLinearGroup.map f) = ⊤) (g : SL(2, ℤ_[ℓ])) :
    ∃ h ∈ H, ∃ Z, (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h + ℓ ^ n • Z := by
  obtain ⟨h, hh, hgh⟩ : SpecialLinearGroup.map f g ∈ H.map (SpecialLinearGroup.map f) :=
    hmap ▸ Subgroup.mem_top _
  have hdvd (i j : Fin 2) : (ℓ : ℤ_[ℓ]) ^ n ∣ (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) i j - h i j := by
    refine hf _ ?_
    have := congrFun (congrFun (congrArg Subtype.val hgh) i) j
    simp only [SpecialLinearGroup.map_apply_coe, Matrix.map_apply] at this
    rw [map_sub, this, sub_self]
  choose Z hZ using hdvd
  refine ⟨h, hh, of Z, ?_⟩
  ext i j
  simp [← hZ i j, nsmul_eq_mul]

/-- If every element of `SL₂(ℤ_ℓ)` is congruent modulo `ℓ ^ (k + 1)` to an element of `H`, then `H`
surjects onto `SL₂(𝔽_ℓ)`. -/
private theorem map_toZMod_eq_top_of_forall_exists_mem {H : Subgroup SL(2, ℤ_[ℓ])} {k : ℕ}
    (hbase : ∀ g : SL(2, ℤ_[ℓ]), ∃ h ∈ H, ∃ Z,
      (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h + ℓ ^ (k + 1) • Z) :
    H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤ := by
  refine eq_top_iff.2 fun g' _ ↦ ?_
  obtain ⟨g, rfl⟩ := SpecialLinearGroup.map_surjective toZMod (ZMod.ringHom_surjective _) g'
  obtain ⟨h, hh, Z, hZ⟩ := hbase g
  refine ⟨h, hh, Subtype.ext ?_⟩
  simp only [SpecialLinearGroup.map_apply_coe, hZ,
    map_toZMod_add_nsmul (dvd_pow_self ℓ k.succ_ne_zero)]

/-- If every element of `SL₂(ℤ_ℓ)` is congruent modulo `ℓ²` to an element of `H`, the first layer
of `H` is nonzero: it contains the reduction of `[[0, 1], [0, 0]]`, from `[[1, ℓ], [0, 1]]`. -/
private theorem layer_zero_ne_bot_of_forall_exists_mem {H : Subgroup SL(2, ℤ_[ℓ])}
    (hbase : ∀ g : SL(2, ℤ_[ℓ]), ∃ h ∈ H, ∃ Z,
      (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h + ℓ ^ (1 + 1) • Z) :
    layer H 0 ≠ ⊥ := by
  let N : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] := !![0, 1; 0, 0]
  let t : SL(2, ℤ_[ℓ]) := ⟨1 + ℓ • N, by simp [N, det_fin_two]⟩
  obtain ⟨h, hh, Z, hZ⟩ := hbase t
  refine (Submodule.ne_bot_iff _).2 ⟨N.map toZMod,
    ⟨N + ℓ • -Z, map_toZMod_add_nsmul dvd_rfl N _, h, hh, ?_⟩, ?_⟩
  · have ht : (t : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = 1 + ℓ • N := rfl
    rw [ht] at hZ
    rw [zero_add, pow_one, eq_sub_of_add_eq hZ.symm]
    module
  · intro h
    simpa [N] using congrFun (congrFun h 0) 1

/-- The approximation step of Serre's lifting lemma, from level `ℓ ^ (k₀ + 1)` on. Suppose every
element of `SL₂(ℤ_ℓ)` is congruent modulo `ℓ ^ (k₀ + 1)` to an element of `H`, and for every
`k ≥ k₀` each trace-zero `Y ∈ M₂(𝔽_ℓ)` is the reduction of some `X` with `1 + ℓ ^ (k + 1) X ∈ H`.
Then every element of `SL₂(ℤ_ℓ)` is congruent modulo `ℓ ^ (k + 1)` to an element of `H`, for
every `k ≥ k₀`. -/
theorem exists_mem_eq_add_pow_smul_of_le {H : Subgroup SL(2, ℤ_[ℓ])} {k₀ : ℕ}
    (hbase : ∀ g : SL(2, ℤ_[ℓ]), ∃ h ∈ H, ∃ Z,
      (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h + ℓ ^ (k₀ + 1) • Z)
    (hlayer : ∀ k, k₀ ≤ k → ∀ Y : Matrix (Fin 2) (Fin 2) (ZMod ℓ), Y.trace = 0 →
      ∃ X, X.map toZMod = Y ∧
        ∃ h ∈ H, (h : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = 1 + ℓ ^ (k + 1) • X)
    {k : ℕ} (hk : k₀ ≤ k) (g : SL(2, ℤ_[ℓ])) :
    ∃ h ∈ H, ∃ Z, (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h + ℓ ^ (k + 1) • Z := by
  induction k, hk using Nat.le_induction with
  | base => exact hbase g
  | succ k hk ih =>
    obtain ⟨h, hh, Z, hZ⟩ := ih
    set hinv : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] := ((h⁻¹ : SL(2, ℤ_[ℓ])) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])
    -- The error term `h⁻¹ g = 1 + ℓ ^ (k + 1) h⁻¹ Z` has trace zero modulo `ℓ`.
    have hdet : (1 + ℓ ^ (k + 1) • (hinv * Z)).det = 1 := by
      have : (1 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) + ℓ ^ (k + 1) • (hinv * Z) =
          ((h⁻¹ * g : SL(2, ℤ_[ℓ])) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) := by
        rw [SpecialLinearGroup.coe_mul, hZ, mul_add, mul_smul_comm,
          SpecialLinearGroup.coe_inv_mul_coe]
      rw [this]
      exact (h⁻¹ * g).prop
    obtain ⟨X, hX, h', hh', e'⟩ := hlayer k hk ((hinv * Z).map toZMod) <|
      trace_map_toZMod_eq_zero_of_det_one_add_nsmul (dvd_pow_self ℓ k.succ_ne_zero)
        (pow_ne_zero _ hℓ.out.ne_zero) hdet
    obtain ⟨W, hW⟩ := exists_eq_nsmul_of_map_toZMod_eq_zero (X := hinv * Z - X)
      (by rw [Matrix.map_sub _ (map_sub _), hX, sub_self])
    refine ⟨h * h', H.mul_mem hh hh', h * W, ?_⟩
    calc (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])
        = h + ℓ ^ (k + 1) • (h * (hinv * Z)) := by
          rw [hZ, ← mul_assoc, SpecialLinearGroup.coe_mul_coe_inv, one_mul]
      _ = h + ℓ ^ (k + 1) • (h * (X + ℓ • W)) := by rw [← hW, add_sub_cancel]
      _ = h * (1 + ℓ ^ (k + 1) • X) + ℓ ^ (k + 1 + 1) • (h * W) := by
        simp only [mul_add, mul_one, mul_smul_comm, smul_add, smul_smul, ← pow_succ]
        abel
      _ = ((h * h' : SL(2, ℤ_[ℓ])) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) + ℓ ^ (k + 1 + 1) • (h * W) := by
        rw [SpecialLinearGroup.coe_mul, e']

/-- The density step of Serre's lifting lemma, from level `ℓ ^ (k₀ + 1)` on. Suppose every
element of `SL₂(ℤ_ℓ)` is congruent modulo `ℓ ^ (k₀ + 1)` to an element of the closed subgroup `H`,
and for every `k ≥ k₀` each trace-zero `Y ∈ M₂(𝔽_ℓ)` is the reduction of some `X` with
`1 + ℓ ^ (k + 1) X ∈ H`. Then `H` is all of `SL₂(ℤ_ℓ)`. -/
theorem eq_top_of_isClosed_of_exists_mem_eq_add_pow_smul {H : Subgroup SL(2, ℤ_[ℓ])}
    (hH : IsClosed (H : Set SL(2, ℤ_[ℓ]))) {k₀ : ℕ}
    (hbase : ∀ g : SL(2, ℤ_[ℓ]), ∃ h ∈ H, ∃ Z,
      (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h + ℓ ^ (k₀ + 1) • Z)
    (hlayer : ∀ k, k₀ ≤ k → ∀ Y : Matrix (Fin 2) (Fin 2) (ZMod ℓ), Y.trace = 0 →
      ∃ X, X.map toZMod = Y ∧
        ∃ h ∈ H, (h : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = 1 + ℓ ^ (k + 1) • X) :
    H = ⊤ := by
  refine eq_top_iff.2 fun g _ ↦ ?_
  choose h hh Z hZ using fun k ↦
    exists_mem_eq_add_pow_smul_of_le hbase hlayer (Nat.le_add_left k₀ k) g
  have hZ' (k : ℕ) : (g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = h k + ℓ ^ (k + 1) • (ℓ ^ k₀ • Z k) := by
    rw [hZ k, smul_smul, ← pow_add, add_right_comm]
  rw [← SetLike.mem_coe, ← hH.closure_eq]
  exact mem_closure_of_tendsto
    (SpecialLinearGroup.isClosedEmbedding_val.isInducing.tendsto_nhds_iff.2
      (tendsto_of_eq_add_pow_nsmul hZ')) (Eventually.of_forall hh)

/-- **Serre's lifting lemma.** For a prime `ℓ ≥ 5`, a closed subgroup of `SL₂(ℤ_ℓ)` whose
reduction modulo `ℓ` is all of `SL₂(𝔽_ℓ)` is all of `SL₂(ℤ_ℓ)`. -/
theorem eq_top_of_isClosed_of_map_toZMod_eq_top (hℓ5 : 5 ≤ ℓ) {H : Subgroup SL(2, ℤ_[ℓ])}
    (hH : IsClosed (H : Set SL(2, ℤ_[ℓ])))
    (hmap : H.map (SpecialLinearGroup.map (toZMod (p := ℓ))) = ⊤) : H = ⊤ :=
  eq_top_of_isClosed_of_exists_mem_eq_add_pow_smul hH
    (exists_mem_eq_add_pow_smul_of_map_eq_top toZMod
      (fun x hx ↦ by rwa [zero_add, pow_one, ← toZMod_eq_zero_iff_dvd]) hmap)
    fun k _ Y hY ↦ (layer_eq_ker_trace (by omega) hmap (layer_zero_ne_bot hℓ5 hmap) k).ge <| by
      rwa [LinearMap.mem_ker, traceLinearMap_apply]

/-- **The lifting lemma modulo `ℓ²`.** For an odd prime `ℓ`, a closed subgroup of `SL₂(ℤ_ℓ)` whose
truncation modulo `ℓ²` is all of `SL₂(ℤ/ℓ²)` is all of `SL₂(ℤ_ℓ)`. For `ℓ ≥ 5` this is weaker than
`TauCeti.eq_top_of_isClosed_of_map_toZMod_eq_top`; for `ℓ = 3` it is the correct statement, since
`SL₂(ℤ/9) → SL₂(𝔽₃)` has a section, so surjectivity modulo `3` alone does not suffice. -/
theorem eq_top_of_isClosed_of_map_toZModPow_two_eq_top (hℓ2 : ℓ ≠ 2)
    {H : Subgroup SL(2, ℤ_[ℓ])} (hH : IsClosed (H : Set SL(2, ℤ_[ℓ])))
    (hmap : H.map (SpecialLinearGroup.map (toZModPow (p := ℓ) 2)) = ⊤) : H = ⊤ := by
  have hbase := exists_mem_eq_add_pow_smul_of_map_eq_top (toZModPow 2)
    (fun x hx ↦ (toZModPow_eq_zero_iff_dvd 2 x).1 hx) hmap
  have hmod := map_toZMod_eq_top_of_forall_exists_mem (k := 1) hbase
  exact eq_top_of_isClosed_of_exists_mem_eq_add_pow_smul (k₀ := 1) hH hbase
    fun k _ Y hY ↦ (layer_eq_ker_trace hℓ2 hmod
      (layer_zero_ne_bot_of_forall_exists_mem hbase) k).ge <| by
      rwa [LinearMap.mem_ker, traceLinearMap_apply]

/-! ### The `GL₂` form -/

/-- An element `s ∈ SL₂(R)` whose image in `GL₂(R)` is a commutator of the image of `H` along a
ring homomorphism `f : ℤ_ℓ →+* R` lifts along `f` to the determinant-one part of the closure of
`⁅H, H⁆`. -/
private theorem mem_map_comap_toGL_topologicalClosure_commutator {R : Type*} [CommRing R]
    (f : ℤ_[ℓ] →+* R) (H : Subgroup (GL (Fin 2) ℤ_[ℓ])) {s : SL(2, R)}
    (hs : SpecialLinearGroup.toGL s ∈
      ⁅H.map (GeneralLinearGroup.map f), H.map (GeneralLinearGroup.map f)⁆) :
    s ∈ (⁅H, H⁆.topologicalClosure.comap SpecialLinearGroup.toGL).map
      (SpecialLinearGroup.map f) := by
  rw [← Subgroup.map_commutator] at hs
  obtain ⟨c, hc, hcs⟩ := hs
  obtain ⟨k, rfl⟩ : c ∈ (SpecialLinearGroup.toGL : SL(2, ℤ_[ℓ]) →* GL (Fin 2) ℤ_[ℓ]).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (Group.Abelianization.commutator_le_ker GeneralLinearGroup.det) hc
  refine ⟨k, Subgroup.le_topologicalClosure _ hc, SpecialLinearGroup.toGL_injective ?_⟩
  rw [SpecialLinearGroup.toGL_map, hcs]

/-- A closed subgroup `H` of `GL₂(ℤ_ℓ)` contains `SL₂(ℤ_ℓ)` as soon as the determinant-one part of
the closure of `⁅H, H⁆` is all of `SL₂(ℤ_ℓ)`. -/
private theorem range_toGL_le_of_comap_toGL_eq_top {H : Subgroup (GL (Fin 2) ℤ_[ℓ])}
    (hH : IsClosed (H : Set (GL (Fin 2) ℤ_[ℓ])))
    (hK : ⁅H, H⁆.topologicalClosure.comap SpecialLinearGroup.toGL = ⊤) :
    (SpecialLinearGroup.toGL : SL(2, ℤ_[ℓ]) →* GL (Fin 2) ℤ_[ℓ]).range ≤ H := by
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ ⁅H, H⁆.topologicalClosure.comap SpecialLinearGroup.toGL := hK ▸ Subgroup.mem_top s
  exact Subgroup.topologicalClosure_minimal _ H.commutator_le_self hH hs

/-- The determinant-one part of the closure of `⁅H, H⁆` is closed in `SL₂(ℤ_ℓ)`. -/
private theorem isClosed_comap_toGL_topologicalClosure (H : Subgroup (GL (Fin 2) ℤ_[ℓ])) :
    IsClosed ((⁅H, H⁆.topologicalClosure.comap SpecialLinearGroup.toGL : Subgroup SL(2, ℤ_[ℓ])) :
      Set SL(2, ℤ_[ℓ])) :=
  (Subgroup.isClosed_topologicalClosure ⁅H, H⁆).preimage SpecialLinearGroup.continuous_toGL

/-- **Serre's lifting lemma, the `GL₂` form.** For a prime `ℓ ≥ 5`, a closed subgroup `H` of
`GL₂(ℤ_ℓ)` whose reduction modulo `ℓ` contains `SL₂(𝔽_ℓ)` contains `SL₂(ℤ_ℓ)`, so it is the full
preimage of its image under the determinant. -/
theorem eq_comap_map_det_of_isClosed (hℓ5 : 5 ≤ ℓ) {H : Subgroup (GL (Fin 2) ℤ_[ℓ])}
    (hH : IsClosed (H : Set (GL (Fin 2) ℤ_[ℓ])))
    (hsl : (SpecialLinearGroup.toGL : SL(2, ZMod ℓ) →* GL (Fin 2) (ZMod ℓ)).range ≤
      H.map (GeneralLinearGroup.map (toZMod (p := ℓ)))) :
    H = (H.map GeneralLinearGroup.det).comap GeneralLinearGroup.det := by
  -- The determinant-one part `K` of the closure of `⁅H, H⁆` reduces onto the perfect group
  -- `SL₂(𝔽_ℓ)`, so it is all of `SL₂(ℤ_ℓ)` by the lifting lemma.
  have hKmap : (⁅H, H⁆.topologicalClosure.comap SpecialLinearGroup.toGL).map
      (SpecialLinearGroup.map toZMod) = ⊤ := by
    have h2 : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
    have h3 : (3 : ZMod ℓ) ≠ 0 := by
      exact_mod_cast ZMod.natCast_ne_zero_of_mem_Ico (k := 3)
        (Finset.mem_Ico.2 ⟨by norm_num, by omega⟩)
    have h4 : (2 : ZMod ℓ) ^ 2 ≠ 1 := fun h ↦ h3 (by linear_combination h)
    rw [eq_top_iff, ← SL2.commutator_eq_top h2 h4, commutator_def]
    intro s hs
    refine mem_map_comap_toGL_topologicalClosure_commutator toZMod H ?_
    have hs' : SpecialLinearGroup.toGL s ∈ (⁅⊤, ⊤⁆ : Subgroup SL(2, ZMod ℓ)).map
        SpecialLinearGroup.toGL := ⟨s, hs, rfl⟩
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map] at hs'
    exact Subgroup.commutator_mono hsl hsl hs'
  refine (Subgroup.comap_map_eq_self ?_).symm
  rw [← SpecialLinearGroup.range_toGL_eq_ker_det]
  exact range_toGL_le_of_comap_toGL_eq_top hH (eq_top_of_isClosed_of_map_toZMod_eq_top hℓ5
    (isClosed_comap_toGL_topologicalClosure H) hKmap)

/-- For a prime `ℓ ≥ 5`, a closed subgroup of `GL₂(ℤ_ℓ)` whose reduction modulo `ℓ` contains
`SL₂(𝔽_ℓ)` and whose determinant is surjective onto `ℤ_ℓˣ` is all of `GL₂(ℤ_ℓ)`. -/
theorem eq_top_of_isClosed_of_map_det_eq_top (hℓ5 : 5 ≤ ℓ) {H : Subgroup (GL (Fin 2) ℤ_[ℓ])}
    (hH : IsClosed (H : Set (GL (Fin 2) ℤ_[ℓ])))
    (hsl : (SpecialLinearGroup.toGL : SL(2, ZMod ℓ) →* GL (Fin 2) (ZMod ℓ)).range ≤
      H.map (GeneralLinearGroup.map (toZMod (p := ℓ))))
    (hdet : H.map GeneralLinearGroup.det = ⊤) : H = ⊤ := by
  rw [eq_comap_map_det_of_isClosed hℓ5 hH hsl, hdet, Subgroup.comap_top]

/-! ### The `GL₂` form modulo `ℓ²` -/

/-- If `H` surjects onto `GL₂(ℤ/ℓ²)`, every unit of `ℤ_ℓ` is congruent modulo `ℓ²` to the
determinant of an element of `H`. -/
private theorem exists_mem_inv_det_mul_mem_unitsPrincipal {H : Subgroup (GL (Fin 2) ℤ_[ℓ])}
    (hmap : H.map (GeneralLinearGroup.map (toZModPow (p := ℓ) 2)) = ⊤) (v : ℤ_[ℓ]ˣ) :
    ∃ h ∈ H, (GeneralLinearGroup.det h)⁻¹ * v ∈ unitsPrincipal ℓ 2 := by
  obtain ⟨g, rfl⟩ := GeneralLinearGroup.det_surjective (n := Fin 2) v
  obtain ⟨h, hh, e⟩ : GeneralLinearGroup.map (toZModPow 2) g ∈
      H.map (GeneralLinearGroup.map (toZModPow 2)) := hmap ▸ Subgroup.mem_top _
  refine ⟨h, hh, ?_⟩
  have hdet := congrArg (fun g ↦ (GeneralLinearGroup.det g : ZMod (ℓ ^ 2))) e
  simp only [GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_ofClass] at hdet
  rw [mem_unitsPrincipal_iff_toZModPow, Units.val_mul, map_mul, ← hdet, ← map_mul,
    Units.inv_mul, map_one]

/-- For an odd prime `ℓ`, a closed subgroup `H` of `GL₂(ℤ_ℓ)` that contains `SL₂(ℤ_ℓ)` and surjects
onto `GL₂(ℤ/ℓ²)` is all of `GL₂(ℤ_ℓ)`. -/
private theorem eq_top_of_range_toGL_le (hℓ2 : ℓ ≠ 2) {H : Subgroup (GL (Fin 2) ℤ_[ℓ])}
    (hH : IsClosed (H : Set (GL (Fin 2) ℤ_[ℓ])))
    (hmap : H.map (GeneralLinearGroup.map (toZModPow (p := ℓ) 2)) = ⊤)
    (hSL : (SpecialLinearGroup.toGL : SL(2, ℤ_[ℓ]) →* GL (Fin 2) ℤ_[ℓ]).range ≤ H) : H = ⊤ := by
  -- The units `u` with `diag(1, u) ∈ H` form a closed subgroup `D` of `ℤ_ℓˣ`.
  let δ : ℤ_[ℓ]ˣ →* GL (Fin 2) ℤ_[ℓ] := diagGL.comp (MonoidHom.mulSingle (fun _ ↦ ℤ_[ℓ]ˣ) 1)
  have hδ (u : ℤ_[ℓ]ˣ) : GeneralLinearGroup.det (δ u) = u := by simp [δ]
  have hD : IsClosed (H.comap δ : Set ℤ_[ℓ]ˣ) :=
    hH.preimage (continuous_diagGL.comp (continuous_mulSingle (A := fun _ : Fin 2 ↦ ℤ_[ℓ]ˣ) 1))
  -- `D` contains every determinant of `H`, since `H` contains `SL₂(ℤ_ℓ)`.
  have hSL' (g : GL (Fin 2) ℤ_[ℓ]) : (δ (GeneralLinearGroup.det g))⁻¹ * g ∈ H := hSL <| by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, map_mul, map_inv, hδ,
      inv_mul_cancel]
  have hdetD (h : GL (Fin 2) ℤ_[ℓ]) (hh : h ∈ H) : GeneralLinearGroup.det h ∈ H.comap δ :=
    Subgroup.mem_comap.2 (by simpa using H.mul_mem hh (H.inv_mem (hSL' h)))
  -- So `D` surjects onto `(ℤ/ℓ²)ˣ`, and hence it is all of `ℤ_ℓˣ`.
  have hDtop : H.comap δ = ⊤ := by
    refine eq_top_of_isClosed_of_map_unitsToZModPow_eq_top le_rfl (fun h ↦ absurd h hℓ2) hD
      (eq_top_iff.2 fun x _ ↦ ?_)
    obtain ⟨v, rfl⟩ := unitsToZModPow_surjective 2 x
    obtain ⟨h, hh, he⟩ := exists_mem_inv_det_mul_mem_unitsPrincipal hmap v
    refine ⟨_, hdetD h hh, ?_⟩
    rwa [← ker_unitsToZModPow, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at he
  refine eq_top_iff.2 fun g _ ↦ ?_
  have hg : GeneralLinearGroup.det g ∈ H.comap δ := hDtop ▸ Subgroup.mem_top _
  simpa using H.mul_mem hg (hSL' g)

/-- **The lifting lemma modulo `ℓ²`, the `GL₂` form.** For an odd prime `ℓ`, a closed subgroup of
`GL₂(ℤ_ℓ)` whose truncation modulo `ℓ²` is all of `GL₂(ℤ/ℓ²)` is all of `GL₂(ℤ_ℓ)`. Unlike the
residual criterion `TauCeti.eq_top_of_isClosed_of_map_det_eq_top`, no hypothesis on the determinant
is needed: a closed subgroup of `ℤ_ℓˣ` surjecting onto `(ℤ/ℓ²)ˣ` is all of `ℤ_ℓˣ`
(`TauCeti.eq_top_of_isClosed_of_map_unitsToZModPow_eq_top`). -/
theorem eq_top_of_isClosed_of_map_generalLinearGroupMap_toZModPow_two_eq_top (hℓ2 : ℓ ≠ 2)
    {H : Subgroup (GL (Fin 2) ℤ_[ℓ])} (hH : IsClosed (H : Set (GL (Fin 2) ℤ_[ℓ])))
    (hmap : H.map (GeneralLinearGroup.map (toZModPow (p := ℓ) 2)) = ⊤) : H = ⊤ := by
  -- Modulo `ℓ²` the commutator subgroup of `H` is that of `GL₂(ℤ/ℓ²)`, which is `SL₂(ℤ/ℓ²)`
  -- because `ℤ/ℓ²` is a local ring in which `2` and `2 - 1` are units.
  have hcop : Nat.Coprime 2 (ℓ ^ 2) := Nat.Coprime.pow_right 2
    ((Nat.coprime_primes Nat.prime_two hℓ.out).2 hℓ2.symm)
  have hKmap : (⁅H, H⁆.topologicalClosure.comap SpecialLinearGroup.toGL).map
      (SpecialLinearGroup.map (toZModPow 2)) = ⊤ := by
    refine eq_top_iff.2 fun s _ ↦ mem_map_comap_toGL_topologicalClosure_commutator _ H ?_
    rw [hmap, ← commutator_def, GeneralLinearGroup.commutator_eq_ker_det_fin_two_of_isLocalRing
      (ZMod.unitOfCoprime 2 hcop) (by norm_num), ← SpecialLinearGroup.range_toGL_eq_ker_det]
    exact ⟨s, rfl⟩
  exact eq_top_of_range_toGL_le hℓ2 hH hmap <| range_toGL_le_of_comap_toGL_eq_top hH <|
    eq_top_of_isClosed_of_map_toZModPow_two_eq_top hℓ2 (isClosed_comap_toGL_topologicalClosure H)
      hKmap

end TauCeti
