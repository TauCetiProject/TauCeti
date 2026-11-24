/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import TauCeti.Topology.Algebra.Group.Units

/-!
# Congruence subgroups of `GLₙ(ℤ_p)`

Entrywise reduction modulo `p ^ k` defines a family of group homomorphisms
`TauCeti.redPadicPow p k : GL n ℤ_[p] →* GL n (ZMod (p ^ k))`. Because `ℤ_[p]` carries the `p`-adic
metric topology and `GL n ℤ_[p]` has the unit-group topology of `Matrix n n ℤ_[p]`, the principal
congruence kernels `(TauCeti.redPadicPow p k).ker` form a neighborhood basis of `1`
(`OpenSubgroup.exists_ker_redPadicPow_le`). Every open subgroup `U ≤ GL n ℤ_[p]` therefore has a
well-defined local level `U.localLevel = p ^ U.localLevelExp`, the smallest prime power `p ^ k`
whose congruence kernel is contained in `U`.

## Main definitions

* `TauCeti.redPadicPow`: reduction modulo `p ^ k` on `GL n ℤ_[p]`.
* `OpenSubgroup.localLevelExp`: the least exponent `k` with `(TauCeti.redPadicPow p k).ker ≤ U`.
* `OpenSubgroup.localLevel`: the local level `p ^ U.localLevelExp`.

## Main results

* `TauCeti.ker_redPadicPow_le_of_le`: `(redPadicPow p k).ker ≤ (redPadicPow p m).ker` for `m ≤ k`.
* `OpenSubgroup.exists_ker_redPadicPow_le`: every open subgroup of `GL n ℤ_[p]` contains
  `(redPadicPow p k).ker` for some `k`.
* `OpenSubgroup.ker_redPadicPow_le_iff`, `OpenSubgroup.ker_redPadicPow_le_iff_dvd`: level tests
  for congruence kernels inside an open subgroup of `GL n ℤ_[p]`.
-/

public section

namespace TauCeti

open Matrix

/-- Reduction modulo `p ^ k` on `GL n ℤ_[p]`, given by entrywise `PadicInt.toZModPow k`. -/
noncomputable def redPadicPow {n : Type*} [Fintype n] [DecidableEq n] (p : ℕ) [Fact p.Prime]
    (k : ℕ) : GL n ℤ_[p] →* GL n (ZMod (p ^ k)) :=
  GeneralLinearGroup.map (PadicInt.toZModPow k)

@[simp]
theorem redPadicPow_apply {n : Type*} [Fintype n] [DecidableEq n] (p : ℕ) [Fact p.Prime]
    (k : ℕ) (A : GL n ℤ_[p]) (i j : n) :
    (redPadicPow p k A : Matrix n n (ZMod (p ^ k))) i j =
      PadicInt.toZModPow k ((A : Matrix n n ℤ_[p]) i j) := by
  simp [redPadicPow]

/-- `(redPadicPow p k).ker ≤ (redPadicPow p m).ker` whenever `m ≤ k`. -/
theorem ker_redPadicPow_le_of_le {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ}
    [Fact p.Prime] {m k : ℕ} (h : m ≤ k) :
    (redPadicPow (n := n) p k).ker ≤ (redPadicPow p m).ker := by
  intro A hA
  rw [MonoidHom.mem_ker] at hA ⊢
  have hcast : GeneralLinearGroup.map
      (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) (redPadicPow p k A) =
        redPadicPow p m A := by
    ext i j
    simp [PadicInt.cast_toZModPow m k h]
  rw [← hcast, hA, map_one]

end TauCeti

namespace OpenSubgroup

open Matrix

/-- Every open subgroup of `GL n ℤ_[p]` contains the principal congruence kernel
`(TauCeti.redPadicPow p k).ker` for some `k : ℕ`. -/
theorem exists_ker_redPadicPow_le {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ}
    [Fact p.Prime] (U : OpenSubgroup (GL n ℤ_[p])) :
    ∃ k : ℕ, (TauCeti.redPadicPow p k).ker ≤ U.toSubgroup := by
  let I₁ : n → n → ℤ_[p] := (1 : Matrix n n ℤ_[p])
  obtain ⟨t, ht, t', ht', hsub⟩ := Units.mem_nhds_iff.mp (U.isOpen.mem_nhds U.one_mem)
  have hpi : (t ∩ t' : Set (n → n → ℤ_[p])) ∈ nhds I₁ := Filter.inter_mem ht ht'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpi
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨k, fun A hA ↦ ?_⟩
  have hmem : ∀ B ∈ (TauCeti.redPadicPow (n := n) p k).ker,
      (B : Matrix n n ℤ_[p]) ∈ t ∩ t' := by
    intro B hB
    refine hball ((dist_pi_lt_iff hε).mpr fun i ↦ (dist_pi_lt_iff hε).mpr fun j ↦ ?_)
    have hBij := congrArg (fun M : GL n (ZMod (p ^ k)) ↦ (M : Matrix n n (ZMod (p ^ k))) i j) hB
    simp only [TauCeti.redPadicPow_apply, Units.val_one] at hBij
    have h1 : PadicInt.toZModPow k (I₁ i j) = (1 : Matrix n n (ZMod (p ^ k))) i j := by
      simp only [I₁, Matrix.one_apply]
      split_ifs <;> simp
    have hker : ((B : Matrix n n ℤ_[p]) i j - I₁ i j) ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
      rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker, map_sub, hBij, h1, sub_self]
    rw [dist_eq_norm]
    exact ((PadicInt.norm_le_pow_iff_mem_span_pow _ k).mpr hker).trans_lt hk
  exact hsub A (hmem A hA).1 (hmem A⁻¹ (inv_mem hA)).2

/-- The least exponent `k : ℕ` such that `(TauCeti.redPadicPow p k).ker ≤ U`. -/
noncomputable def localLevelExp {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]
    (U : OpenSubgroup (GL n ℤ_[p])) : ℕ := by
  classical
  exact Nat.find U.exists_ker_redPadicPow_le

/-- The **local level** of an open subgroup `U ≤ GL n ℤ_[p]`: `p` raised to the least exponent
whose reduction kernel lies in `U`. -/
noncomputable def localLevel {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]
    (U : OpenSubgroup (GL n ℤ_[p])) : ℕ :=
  p ^ U.localLevelExp

/-- The local level of an open subgroup of `GL n ℤ_[p]` is positive. -/
theorem localLevel_pos {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]
    (U : OpenSubgroup (GL n ℤ_[p])) : 0 < U.localLevel :=
  pow_pos (Fact.out : p.Prime).pos _

/-- Every open subgroup `U ≤ GL n ℤ_[p]` contains `(TauCeti.redPadicPow p U.localLevelExp).ker`. -/
theorem ker_redPadicPow_localLevelExp_le {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ}
    [Fact p.Prime] (U : OpenSubgroup (GL n ℤ_[p])) :
    (TauCeti.redPadicPow p U.localLevelExp).ker ≤ U.toSubgroup := by
  classical
  exact Nat.find_spec U.exists_ker_redPadicPow_le

/-- `(TauCeti.redPadicPow p k).ker ≤ U` if and only if `U.localLevelExp ≤ k`. -/
theorem ker_redPadicPow_le_iff {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]
    {U : OpenSubgroup (GL n ℤ_[p])} {k : ℕ} :
    (TauCeti.redPadicPow p k).ker ≤ U.toSubgroup ↔ U.localLevelExp ≤ k := by
  classical
  exact ⟨fun hk ↦ Nat.find_min' U.exists_ker_redPadicPow_le hk,
    fun hle ↦ (TauCeti.ker_redPadicPow_le_of_le hle).trans U.ker_redPadicPow_localLevelExp_le⟩

/-- `(TauCeti.redPadicPow p k).ker ≤ U` if and only if `U.localLevel ∣ p ^ k`. -/
theorem ker_redPadicPow_le_iff_dvd {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ}
    [Fact p.Prime] {U : OpenSubgroup (GL n ℤ_[p])} {k : ℕ} :
    (TauCeti.redPadicPow p k).ker ≤ U.toSubgroup ↔ U.localLevel ∣ p ^ k := by
  rw [ker_redPadicPow_le_iff, localLevel, Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt]

end OpenSubgroup
