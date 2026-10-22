/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import TauCeti.QuantumGroups.UqSl2.Commutator
public import TauCeti.QuantumGroups.UqSl2.Weights

import Mathlib.Tactic

/-!
# The signed ladder modules of `U_q(sl₂)`

For a nonzero complex parameter `q`, a natural number `m` and a sign `ε : ℤˣ`, this file
constructs the `(m + 1)`-dimensional `UqSl2 q`-module `L_m^ε` with basis `v₀, …, v_m` and action

* `K v_j = ε q^(m - 2j) v_j` and `K⁻¹ v_j = ε q^(2j - m) v_j`,
* `F v_j = [j + 1]_q v_(j + 1)`, and
* `E v_j = ε [m - j + 1]_q v_(j - 1)`,

where `[r]_q` is the symmetric quantum integer and the out-of-range vectors `v_(-1)` and
`v_(m + 1)` are zero. The basis vectors are indexed by all integers, with `v_j = 0` outside
`0 ≤ j ≤ m`; with this convention the action formulas hold for every integer `j`.

These are the signed simple modules of `U_q(sl₂)`. For a generic parameter (nonzero and not a
root of unity), `L_m^ε` is a simple module whose endomorphisms are the complex scalars (Schur's
lemma), and `L_m^ε` and `L_n^δ` are isomorphic only when `m = n` and `ε = δ`.

A vector `v` of weight `ε q^m` in any `UqSl2 q`-module, killed by `E` and by `F^(m+1)`,
determines a unique module map from `L_m^ε` that sends `v₀` to `v`, and more generally sends
`v_j` to the normalized lowering string `F^j v / ([1]_q ⋯ [j]_q)`.

## Main definitions

* `TauCeti.UqSl2.LadderModule q m ε`: the module `L_m^ε`.
* `TauCeti.UqSl2.LadderModule.basis`: its basis `v₀, …, v_m`.
* `TauCeti.UqSl2.LadderModule.vec`: the integer-indexed vectors `v_j`.
* `TauCeti.UqSl2.LadderModule.rep`: the action as an algebra map to complex endomorphisms.
* `TauCeti.UqSl2.LadderModule.lift`: the module map determined by a highest vector of weight
  `ε q^m` whose lowering string has length at most `m + 1`.

## Main results

* `TauCeti.UqSl2.LadderModule.e_smul_vec`, `f_smul_vec`, `k_smul_vec`, `kInv_smul_vec`:
  the action of the generators.
* `TauCeti.UqSl2.LadderModule.e_pow_smul_vec`, `f_pow_smul_vec`: the action of their powers.
* `TauCeti.UqSl2.LadderModule.isSimpleModule`: `L_m^ε` is simple at a generic parameter.
* `TauCeti.UqSl2.LadderModule.hom_ext`: at a generic parameter, module maps out of `L_m^ε` are
  determined by their value at `v₀`.
* `TauCeti.UqSl2.LadderModule.lift_vec_zero`: `lift` sends `v₀` to the given vector.
* `TauCeti.UqSl2.LadderModule.lift_injective`: the map induced by a nonzero vector is injective.
* `TauCeti.UqSl2.LadderModule.algebraMap_end_bijective`: Schur's lemma for `L_m^ε`.
* `TauCeti.UqSl2.LadderModule.nonempty_linearEquiv_iff`: `L_m^ε ≅ L_n^δ` iff `m = n` and
  `ε = δ`, at a generic parameter.

## References

* A. Virelizier, *Quantum groups*, Section 2.4, for these modules in the rank-one convention.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VI.3, where the same
  modules appear as `V_(ε,n)`.
-/

public noncomputable section

open Module

namespace TauCeti

namespace UqSl2

/-- The underlying complex vector space `ℂ^(m + 1)` of the signed ladder module `L_m^ε` of
`UqSl2 q`. Its `UqSl2 q`-module structure, defined for nonzero `q`, is
`LadderModule.instModule`. -/
def LadderModule (_q : ℂ) (m : ℕ) (_ε : ℤˣ) : Type := Fin (m + 1) → ℂ

namespace LadderModule

instance (q : ℂ) (m : ℕ) (ε : ℤˣ) : AddCommGroup (LadderModule q m ε) :=
  inferInstanceAs (AddCommGroup (Fin (m + 1) → ℂ))

instance (q : ℂ) (m : ℕ) (ε : ℤˣ) : Module ℂ (LadderModule q m ε) :=
  inferInstanceAs (Module ℂ (Fin (m + 1) → ℂ))

instance (q : ℂ) (m : ℕ) (ε : ℤˣ) : FiniteDimensional ℂ (LadderModule q m ε) :=
  inferInstanceAs (FiniteDimensional ℂ (Fin (m + 1) → ℂ))

/-- The ladder basis `v₀, …, v_m` of `L_m^ε`. -/
def basis (q : ℂ) (m : ℕ) (ε : ℤˣ) : Basis (Fin (m + 1)) ℂ (LadderModule q m ε) :=
  Pi.basisFun ℂ (Fin (m + 1))

/-- The ladder vector `v_j` of `L_m^ε` for an integer `j`: the basis vector for `0 ≤ j ≤ m`
and zero otherwise. -/
def vec (q : ℂ) (m : ℕ) (ε : ℤˣ) (j : ℤ) : LadderModule q m ε :=
  if h : 0 ≤ j ∧ j ≤ m then basis q m ε ⟨j.toNat, by omega⟩ else 0

variable {q : ℂ} {m : ℕ} {ε : ℤˣ}

/-- The ladder vector with index in range is the corresponding basis vector. -/
theorem vec_coe (i : Fin (m + 1)) : vec q m ε i = basis q m ε i := by
  rw [vec]
  split_ifs with h
  · congr
  · omega

/-- The ladder vectors vanish exactly outside the range `0 ≤ j ≤ m`. -/
@[simp]
theorem vec_eq_zero_iff {j : ℤ} : vec q m ε j = 0 ↔ j < 0 ∨ (m : ℤ) < j := by
  rw [vec]
  split_ifs with h
  · simp only [(basis q m ε).ne_zero, false_iff]
    omega
  · simp only [true_iff]
    omega

/-- The ladder vectors with negative index vanish. -/
@[simp]
theorem vec_eq_zero_of_neg {j : ℤ} (hj : j < 0) : vec q m ε j = 0 :=
  vec_eq_zero_iff.mpr (.inl hj)

/-- The ladder vectors with index above `m` vanish. -/
@[simp]
theorem vec_eq_zero_of_lt {j : ℤ} (hj : (m : ℤ) < j) : vec q m ε j = 0 :=
  vec_eq_zero_iff.mpr (.inr hj)

/-- The complex dimension of `L_m^ε` is `m + 1`. -/
@[simp]
theorem finrank_eq : finrank ℂ (LadderModule q m ε) = m + 1 := by
  simp [finrank_eq_card_basis (basis q m ε)]

/-! ### The generator operators -/

/-- The weighted shift sending `v_j` to `c j • v_(j + s)`. -/
private def shift (c : ℤ → ℂ) (s : ℤ) : Module.End ℂ (LadderModule q m ε) :=
  (basis q m ε).constr ℂ fun i => c i • vec q m ε (i + s)

private theorem shift_vec {c : ℤ → ℂ} {s j : ℤ}
    (h : j < 0 ∨ (m : ℤ) < j → c j • vec q m ε (j + s) = 0) :
    shift (ε := ε) c s (vec q m ε j) = c j • vec q m ε (j + s) := by
  by_cases hj : 0 ≤ j ∧ j ≤ m
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (m + 1), (i : ℤ) = j := ⟨⟨j.toNat, by omega⟩, by simp; omega⟩
    rw [vec_coe, shift, Basis.constr_basis]
  · rw [vec_eq_zero_iff.mpr (by omega), map_zero, h (by omega)]

/-- The operator of `K`. -/
private def kOp (q : ℂ) (m : ℕ) (ε : ℤˣ) : Module.End ℂ (LadderModule q m ε) :=
  shift (fun j => ε * q ^ ((m : ℤ) - 2 * j)) 0

/-- The operator of `K⁻¹`. -/
private def kInvOp (q : ℂ) (m : ℕ) (ε : ℤˣ) : Module.End ℂ (LadderModule q m ε) :=
  shift (fun j => ε * q ^ (2 * j - m)) 0

/-- The operator of `E`. -/
private def eOp (q : ℂ) (m : ℕ) (ε : ℤˣ) : Module.End ℂ (LadderModule q m ε) :=
  shift (fun j => ε * quantumInteger q (m - j + 1)) (-1)

/-- The operator of `F`. -/
private def fOp (q : ℂ) (m : ℕ) (ε : ℤˣ) : Module.End ℂ (LadderModule q m ε) :=
  shift (fun j => quantumInteger q (j + 1)) 1

private theorem kOp_vec (j : ℤ) :
    kOp q m ε (vec q m ε j) = (ε * q ^ ((m : ℤ) - 2 * j)) • vec q m ε j := by
  rw [kOp, shift_vec, add_zero]
  intro h
  rw [add_zero, vec_eq_zero_iff.mpr h, smul_zero]

private theorem kInvOp_vec (j : ℤ) :
    kInvOp q m ε (vec q m ε j) = (ε * q ^ (2 * j - m)) • vec q m ε j := by
  rw [kInvOp, shift_vec, add_zero]
  intro h
  rw [add_zero, vec_eq_zero_iff.mpr h, smul_zero]

private theorem eOp_vec (j : ℤ) :
    eOp q m ε (vec q m ε j) = (ε * quantumInteger q (m - j + 1)) • vec q m ε (j - 1) := by
  rw [eOp, shift_vec, ← sub_eq_add_neg]
  rintro (h | h)
  · rw [vec_eq_zero_of_neg (by omega), smul_zero]
  · rcases eq_or_lt_of_le (Int.add_one_le_iff.mpr h) with rfl | h'
    · simp
    · rw [vec_eq_zero_of_lt (by omega), smul_zero]

private theorem fOp_vec (j : ℤ) :
    fOp q m ε (vec q m ε j) = quantumInteger q (j + 1) • vec q m ε (j + 1) := by
  rw [fOp, shift_vec]
  rintro (h | h)
  · rcases eq_or_lt_of_le (Int.add_one_le_iff.mpr h) with h' | h'
    · rw [h', quantumInteger_zero, zero_smul]
    · rw [vec_eq_zero_of_neg (by omega), smul_zero]
  · rw [vec_eq_zero_of_lt (by omega), smul_zero]

/-- Equality of endomorphisms of `L_m^ε` can be checked on the ladder vectors. -/
private theorem end_ext {T U : Module.End ℂ (LadderModule q m ε)}
    (h : ∀ j : ℤ, T (vec q m ε j) = U (vec q m ε j)) : T = U :=
  (basis q m ε).ext fun i => by rw [← vec_coe, h]

/-- The generator operators satisfy the defining relations of `UqSl2 q`. -/
private def tuple (q : ℂ) [Fact (q ≠ 0)] (m : ℕ) (ε : ℤˣ) :
    GeneratorTuple q (Module.End ℂ (LadderModule q m ε)) where
  e := eOp q m ε
  f := fOp q m ε
  k := kOp q m ε
  kInv := kInvOp q m ε
  k_mul_kInv := end_ext fun j => by
    simp [kOp_vec, kInvOp_vec, smul_smul, mul_mul_mul_comm, ← Int.cast_mul,
      ← zpow_add₀ (Fact.out : q ≠ 0)]
  kInv_mul_k := end_ext fun j => by
    simp [kOp_vec, kInvOp_vec, smul_smul, mul_mul_mul_comm, ← Int.cast_mul,
      ← zpow_add₀ (Fact.out : q ≠ 0)]
  k_mul_e := end_ext fun j => by
    simp only [LinearMap.smul_apply, Module.End.mul_apply, kOp_vec, eOp_vec, map_smul, smul_smul]
    congr 1
    -- Split the exponent of `q` as `2 + (m - 2j)` so that `zpow_add₀` exposes the factor `q ^ 2`.
    rw [show (m : ℤ) - 2 * (j - 1) = 2 + (m - 2 * j) by ring, zpow_add₀ (Fact.out : q ≠ 0),
      zpow_two]
    ring
  k_mul_f := end_ext fun j => by
    simp only [LinearMap.smul_apply, Module.End.mul_apply, kOp_vec, fOp_vec, map_smul, smul_smul]
    congr 1
    -- Split the exponent of `q` as `-2 + (m - 2j)` so that `zpow_add₀` exposes `q⁻¹ ^ 2`.
    rw [show (m : ℤ) - 2 * (j + 1) = -2 + (m - 2 * j) by ring, zpow_add₀ (Fact.out : q ≠ 0),
      zpow_neg, zpow_two]
    ring
  e_mul_f_sub_f_mul_e := end_ext fun j => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, eOp_vec,
      fOp_vec, kOp_vec, kInvOp_vec, map_smul, smul_smul, add_sub_cancel_right, sub_add_cancel,
      ← sub_smul]
    congr 1
    -- The scalar identity is `ε [m - 2j]_q = ε ([m - j]_q [j + 1]_q - [m - j + 1]_q [j]_q)`.
    have h := quantumInteger_sub q ((m : ℤ) - j) j
    -- Put `h` in the shape of the goal: rewrite `[m - 2j]_q` through its defining quotient,
    -- with the exponents written as `m - 2j` and `2j - m` as in the actions of `K` and `K⁻¹`.
    rw [show (m : ℤ) - j - j = m - 2 * j by ring, quantumInteger_def,
      show -((m : ℤ) - 2 * j) = 2 * j - m by ring, div_eq_inv_mul] at h
    -- The coefficient of `E` on `v_(j + 1)` is `[m - (j + 1) + 1]_q`; match it with `[m - j]_q`.
    rw [show (m : ℤ) - (j + 1) + 1 = m - j by ring]
    linear_combination -(ε : ℂ) * h

/-! ### The module structure -/

variable [Fact (q ≠ 0)]

variable (q m ε) in
/-- The action of `UqSl2 q` on `L_m^ε`, as an algebra map to complex endomorphisms. -/
def rep : UqSl2 q →ₐ[ℂ] Module.End ℂ (LadderModule q m ε) :=
  lift (tuple q m ε)

/-- The `UqSl2 q`-module structure of `L_m^ε`, given by `LadderModule.rep`. -/
instance instModule : Module (UqSl2 q) (LadderModule q m ε) :=
  Module.compHom _ (rep q m ε).toRingHom

/-- An element of `UqSl2 q` acts on `L_m^ε` through `LadderModule.rep`. -/
theorem smul_def (a : UqSl2 q) (x : LadderModule q m ε) : a • x = rep q m ε a x := (rfl)

/-- The generator tuple of `LadderModule.rep` is the tuple of generator operators. -/
private theorem liftEquiv_rep : liftEquiv (rep q m ε) = tuple q m ε := by
  rw [rep, ← liftEquiv_symm_apply, Equiv.apply_symm_apply]

instance : IsScalarTower ℂ (UqSl2 q) (LadderModule q m ε) where
  smul_assoc c a x := by
    rw [smul_def, smul_def, map_smul, LinearMap.smul_apply]

/-- The action of `E` on the ladder vectors: `E v_j = ε [m - j + 1]_q v_(j - 1)`. -/
@[simp]
theorem e_smul_vec (j : ℤ) :
    e q • vec q m ε j = (ε * quantumInteger q (m - j + 1)) • vec q m ε (j - 1) := by
  rw [smul_def, ← liftEquiv_apply_e, liftEquiv_rep]
  exact eOp_vec j

/-- The action of `F` on the ladder vectors: `F v_j = [j + 1]_q v_(j + 1)`. -/
@[simp]
theorem f_smul_vec (j : ℤ) :
    f q • vec q m ε j = quantumInteger q (j + 1) • vec q m ε (j + 1) := by
  rw [smul_def, ← liftEquiv_apply_f, liftEquiv_rep]
  exact fOp_vec j

/-- The action of `K` on the ladder vectors: `K v_j = ε q^(m - 2j) v_j`. -/
@[simp]
theorem k_smul_vec (j : ℤ) :
    k q • vec q m ε j = (ε * q ^ ((m : ℤ) - 2 * j)) • vec q m ε j := by
  rw [smul_def, ← liftEquiv_apply_k, liftEquiv_rep]
  exact kOp_vec j

/-- The action of `K⁻¹` on the ladder vectors: `K⁻¹ v_j = ε q^(2j - m) v_j`. -/
@[simp]
theorem kInv_smul_vec (j : ℤ) :
    kInv q • vec q m ε j = (ε * q ^ (2 * j - m)) • vec q m ε j := by
  rw [smul_def, ← liftEquiv_apply_kInv, liftEquiv_rep]
  exact kInvOp_vec j

/-- The action of the powers of `E` on the ladder vectors. -/
theorem e_pow_smul_vec (n : ℕ) (j : ℤ) :
    e q ^ n • vec q m ε j =
      (∏ i ∈ Finset.range n, (ε * quantumInteger q (m - j + i + 1))) • vec q m ε (j - n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, smul_comm, e_smul_vec, smul_smul, Finset.prod_range_succ,
      Nat.cast_succ, sub_add_eq_sub_sub]
    -- The new factor `ε [m - (j - n) + 1]_q` is the factor of index `n` of the product.
    rw [show (m : ℤ) - (j - n) + 1 = m - j + n + 1 by ring]

/-- The action of the powers of `F` on the ladder vectors. -/
theorem f_pow_smul_vec (n : ℕ) (j : ℤ) :
    f q ^ n • vec q m ε j =
      (∏ i ∈ Finset.range n, quantumInteger q (j + i + 1)) • vec q m ε (j + n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, smul_comm, f_smul_vec, smul_smul, Finset.prod_range_succ,
      Nat.cast_succ, add_assoc]

/-! ### Simplicity -/

/-- A `UqSl2 q`-submodule of `L_m^ε` containing a nonzero complex multiple of `v_j` contains
`v_j`. -/
private theorem vec_mem_of_smul_mem {N : Submodule (UqSl2 q) (LadderModule q m ε)} {c : ℂ}
    (hc : c ≠ 0) {j : ℤ} (h : c • vec q m ε j ∈ N) : vec q m ε j ∈ N :=
  (Submodule.smul_mem_iff (N.restrictScalars ℂ) hc).mp h

/-- At a generic parameter, every nonzero vector of `L_m^ε` generates the whole module. -/
private theorem span_singleton_eq_top (hq : IsGenericQuantumParameter q)
    {x : LadderModule q m ε} (hx : x ≠ 0) : Submodule.span (UqSl2 q) {x} = ⊤ := by
  set N := Submodule.span (UqSl2 q) {x}
  -- Let `j₀` be the largest index of a nonzero coordinate of `x`.
  have hs : ((basis q m ε).repr x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff, Ne, LinearEquiv.map_eq_zero_iff]
    exact hx
  set j₀ := ((basis q m ε).repr x).support.max' hs
  -- Then `E ^ j₀ • x` is a nonzero multiple of `v₀`.
  have hv₀ : vec q m ε 0 ∈ N := by
    have hmem : e q ^ (j₀ : ℕ) • x ∈ N := N.smul_mem _ (Submodule.mem_span_singleton_self x)
    rw [← (basis q m ε).sum_repr x] at hmem
    rw [Finset.smul_sum, Finset.sum_eq_single j₀] at hmem
    · rw [smul_comm, ← vec_coe, e_pow_smul_vec, sub_self, smul_smul] at hmem
      refine vec_mem_of_smul_mem (mul_ne_zero ?_ ?_) hmem
      · exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs)
      · exact Finset.prod_ne_zero_iff.mpr fun i hi =>
          mul_ne_zero (Int.cast_ne_zero.mpr ε.ne_zero) (quantumInteger_ne_zero hq (by omega))
    · intro i _ hi
      by_cases his : i ∈ ((basis q m ε).repr x).support
      · have hlt : i < j₀ := lt_of_le_of_ne (Finset.le_max' _ i his) hi
        rw [smul_comm, ← vec_coe, e_pow_smul_vec, vec_eq_zero_of_neg (by omega), smul_zero,
          smul_zero]
      · rw [Finsupp.notMem_support_iff.mp his, zero_smul, smul_zero]
    · simp
  -- The powers of `F` recover every basis vector from `v₀`.
  have hbasis (i : Fin (m + 1)) : basis q m ε i ∈ N := by
    have hmem : f q ^ (i : ℕ) • vec q m ε 0 ∈ N := N.smul_mem _ hv₀
    rw [f_pow_smul_vec, zero_add] at hmem
    rw [← vec_coe]
    exact vec_mem_of_smul_mem (Finset.prod_ne_zero_iff.mpr fun l _ =>
      quantumInteger_ne_zero hq (by omega)) hmem
  rw [Submodule.eq_top_iff']
  intro z
  rw [← (basis q m ε).sum_repr z]
  exact N.sum_mem fun i _ => N.smul_of_tower_mem _ (hbasis i)

/-- At a generic parameter, the signed ladder module `L_m^ε` is a simple `UqSl2 q`-module. -/
theorem isSimpleModule (hq : IsGenericQuantumParameter q) :
    IsSimpleModule (UqSl2 q) (LadderModule q m ε) := by
  have : Nontrivial (LadderModule q m ε) := nontrivial_of_ne _ _ ((basis q m ε).ne_zero 0)
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨this, fun x hx z => ?_⟩
  have hz : z ∈ Submodule.span (UqSl2 q) {x} := by
    rw [span_singleton_eq_top hq hx]
    exact Submodule.mem_top
  exact Submodule.mem_span_singleton.mp hz

/-- At a generic parameter, a `UqSl2 q`-module map out of `L_m^ε` is determined by its value at
the highest vector `v₀`. -/
theorem hom_ext (hq : IsGenericQuantumParameter q) {V : Type*} [AddCommMonoid V]
    [Module (UqSl2 q) V] {φ ψ : LadderModule q m ε →ₗ[UqSl2 q] V}
    (h : φ (vec q m ε 0) = ψ (vec q m ε 0)) : φ = ψ := by
  refine LinearMap.ext_on (span_singleton_eq_top hq (x := vec q m ε 0) (by simp)) ?_
  simpa only [Set.eqOn_singleton] using h

/-! ### Universal property -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

variable (q) in
/-- The normalized lowering string `F^j v / ([1]_q ⋯ [j]_q)` through a vector `v`. -/
private def string (v : V) (j : ℕ) : V :=
  (∏ i ∈ Finset.range j, quantumInteger q (i + 1))⁻¹ • f q ^ j • v

section String

variable {v : V} (hq : IsGenericQuantumParameter q)
  (hv : v ∈ weightSpace q V (ε * q ^ m)) (he : e q • v = 0) (hf : f q ^ (m + 1) • v = 0)

omit [Fact (q ≠ 0)] [IsScalarTower ℂ (UqSl2 q) V] in
private theorem string_zero : string q v 0 = v := by
  simp [string]

omit [Fact (q ≠ 0)] in
include hq in
private theorem f_smul_string (j : ℕ) :
    f q • string q v j = quantumInteger q (j + 1) • string q v (j + 1) := by
  have hj : quantumInteger q ((j : ℤ) + 1) ≠ 0 := quantumInteger_ne_zero hq (by omega)
  rw [string, string, smul_smul, Finset.prod_range_succ, mul_inv, mul_left_comm,
    mul_inv_cancel₀ hj, mul_one, smul_comm, pow_succ', mul_smul]

omit [Fact (q ≠ 0)] in
include hq hv in
private theorem k_smul_string (j : ℕ) :
    k q • string q v j = (ε * q ^ ((m : ℤ) - 2 * j)) • string q v j := by
  have hw := mem_weightSpace_iff.mp (f_pow_smul_mem_weightSpace hv j)
  rw [string, smul_comm, hw, smul_comm]
  congr 1
  rw [zpow_sub₀ hq.ne_zero, zpow_natCast, zpow_mul, zpow_ofNat, zpow_natCast, inv_pow,
    div_eq_mul_inv, ← inv_pow, ← inv_pow]
  ring

omit [Fact (q ≠ 0)] [IsScalarTower ℂ (UqSl2 q) V] in
include hf in
private theorem string_eq_zero {j : ℕ} (hj : m < j) : string q v j = 0 := by
  rw [string, ← Nat.sub_add_cancel hj, pow_add, mul_smul, hf, smul_zero, smul_zero]

omit [Fact (q ≠ 0)] in
include hq hv he in
private theorem e_smul_string (j : ℕ) :
    e q • string q v (j + 1) = (ε * quantumInteger q (m - j)) • string q v j := by
  have hq0 := hq.ne_zero
  have hk : k q • v = (ε * q ^ m : ℂ) • v := mem_weightSpace_iff.mp hv
  have hkInv := kInv_smul_of_mem_weightSpace hv
  -- Apply the commutator formula to `v`; only its `K`, `K⁻¹` term survives.
  have h := congrArg (· • v) (e_mul_f_pow hq.sub_inv_ne_zero (j + 1))
  simp only [add_smul, mul_smul, he, smul_zero, zero_add, smul_assoc, sub_smul, hk, hkInv,
    Nat.add_sub_cancel, smul_sub, smul_comm (f q ^ j) (_ : ℂ)] at h
  have hj : quantumInteger q ((j : ℤ) + 1) ≠ 0 := quantumInteger_ne_zero hq (by omega)
  rw [string, string, smul_comm, h]
  generalize f q ^ j • v = w
  match_scalars
  have hP : ∏ i ∈ Finset.range j, quantumInteger q (i + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => quantumInteger_ne_zero hq (by omega)
  rw [Finset.prod_range_succ, quantumInteger_def q ((m : ℤ) - j), zpow_sub₀ hq0, zpow_neg,
    zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
  generalize ∏ i ∈ Finset.range j, quantumInteger q (i + 1) = P at hP ⊢
  generalize quantumInteger q (j + 1) = Q at hj ⊢
  have hq1 := hq.sub_inv_ne_zero
  rw [inv_pow]
  rcases Int.units_eq_one_or ε with rfl | rfl
  · push_cast
    field_simp
  · push_cast
    field_simp
    ring

omit [Fact (q ≠ 0)] [IsScalarTower ℂ (UqSl2 q) V] in
include hf in
/-- The images of the ladder vectors under the map induced by `v`. -/
private theorem constr_vec (j : ℕ) :
    (basis q m ε).constr ℂ (fun i => string q v i) (vec q m ε j) = string q v j := by
  by_cases hj : j ≤ m
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (m + 1), (i : ℕ) = j := ⟨⟨j, by omega⟩, rfl⟩
    rw [vec_coe, Basis.constr_basis]
  · rw [vec_eq_zero_of_lt (by omega), map_zero, string_eq_zero hf (by omega)]

end String

/-- Commutation of a complex-linear map out of `L_m^ε` with an element of `UqSl2 q` can be
checked on the ladder vectors. -/
private theorem map_smul_of_vec (φ : LadderModule q m ε →ₗ[ℂ] V) (a : UqSl2 q)
    (h : ∀ j : ℕ, j ≤ m → φ (a • vec q m ε j) = a • φ (vec q m ε j))
    (x : LadderModule q m ε) : φ (a • x) = a • φ x := by
  have hext : φ ∘ₗ Algebra.lsmul ℂ ℂ _ a = Algebra.lsmul ℂ ℂ V a ∘ₗ φ :=
    (basis q m ε).ext fun i => by simpa [← vec_coe] using h i (by omega)
  simpa using LinearMap.congr_fun hext x

/-- The `UqSl2 q`-module map `L_m^ε → V` determined by a vector `v` of weight `ε q^m` killed by
`E` and by `F^(m+1)`. It sends `v_j` to `F^j v / ([1]_q ⋯ [j]_q)`. -/
def lift (hq : IsGenericQuantumParameter q) {v : V} (hv : v ∈ weightSpace q V (ε * q ^ m))
    (he : e q • v = 0) (hf : f q ^ (m + 1) • v = 0) : LadderModule q m ε →ₗ[UqSl2 q] V :=
  let φ := (basis q m ε).constr ℂ fun i => string q v i
  { φ.toAddHom with
    map_smul' := by
      have hφ := constr_vec (ε := ε) hf
      have hφ0 : φ (vec q m ε 0) = v := by simpa only [Nat.cast_zero, string_zero] using hφ 0
      refine φ.map_smul_of_commute_uqSl2 (fun x => ?_) (fun x => ?_) (fun x => ?_)
      · refine map_smul_of_vec φ _ (fun j _ => ?_) x
        rcases j with _ | j
        · rw [e_smul_vec, map_smul, vec_eq_zero_of_neg (by omega), map_zero, smul_zero,
            Nat.cast_zero, hφ0, he]
        · rw [e_smul_vec, map_smul, hφ (j + 1), Nat.cast_succ, add_sub_cancel_right,
            sub_add_eq_sub_sub, sub_add_cancel, hφ, e_smul_string hq hv he]
      · refine map_smul_of_vec φ _ (fun j _ => ?_) x
        rw [f_smul_vec, map_smul, ← Nat.cast_succ, hφ, hφ, f_smul_string hq, Nat.cast_succ]
      · refine map_smul_of_vec φ _ (fun j _ => ?_) x
        rw [k_smul_vec, map_smul, hφ, k_smul_string hq hv] }

variable (hq : IsGenericQuantumParameter q) {v : V} (hv : v ∈ weightSpace q V (ε * q ^ m))
  (he : e q • v = 0) (hf : f q ^ (m + 1) • v = 0)

/-- The map induced by `v` sends `v_j` to `F^j v / ([1]_q ⋯ [j]_q)`. -/
theorem lift_vec (j : ℕ) :
    lift hq hv he hf (vec q m ε j) =
      (∏ i ∈ Finset.range j, quantumInteger q (i + 1))⁻¹ • f q ^ j • v :=
  constr_vec hf j

/-- The map induced by `v` sends the highest vector `v₀` to `v`. -/
@[simp]
theorem lift_vec_zero : lift hq hv he hf (vec q m ε 0) = v := by
  simpa using lift_vec hq hv he hf 0

include hq in
/-- The map induced by a nonzero vector is injective. -/
theorem lift_injective (hv0 : v ≠ 0) : Function.Injective (lift hq hv he hf) :=
  have := isSimpleModule (m := m) (ε := ε) hq
  LinearMap.injective_of_ne_zero fun h0 => hv0 <| by
    rw [← lift_vec_zero hq hv he hf, h0, LinearMap.zero_apply]

/-! ### Schur's lemma and pairwise non-isomorphism -/

/-- Schur's lemma for `L_m^ε`: at a generic parameter, every `UqSl2 q`-endomorphism of `L_m^ε`
is multiplication by a unique complex scalar. -/
theorem algebraMap_end_bijective (hq : IsGenericQuantumParameter q) :
    Function.Bijective (algebraMap ℂ (Module.End (UqSl2 q) (LadderModule q m ε))) :=
  have := isSimpleModule (m := m) (ε := ε) hq
  IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ

/-- The trace of `K⁻¹` on `L_m^ε` is `ε [m + 1]_q`. -/
theorem trace_rep_kInv (hq : q - q⁻¹ ≠ 0) :
    LinearMap.trace ℂ _ (rep q m ε (kInv q)) = ε * quantumInteger q ((m : ℤ) + 1) := by
  have hdiag (i : Fin (m + 1)) :
      (LinearMap.toMatrix (basis q m ε) (basis q m ε) (rep q m ε (kInv q))).diag i =
        ε * q ^ (2 * (i : ℕ) - (m : ℤ)) := by
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← smul_def, ← vec_coe, kInv_smul_vec,
      vec_coe, map_smul, Basis.repr_self]
    simp
  have hsum := quantumInteger_natCast_eq_sum hq (m + 1)
  push_cast at hsum
  rw [LinearMap.trace_eq_matrix_trace ℂ (basis q m ε), Matrix.trace, Finset.sum_congr rfl
    fun i _ => hdiag i, ← Finset.mul_sum, hsum,
    Fin.sum_univ_eq_sum_range (fun j => q ^ (2 * (j : ℤ) - m))]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring_nf

/-- At a generic parameter, `L_m^ε` and `L_n^δ` are isomorphic exactly when `m = n` and
`ε = δ`. -/
theorem nonempty_linearEquiv_iff (hq : IsGenericQuantumParameter q) {n : ℕ} {δ : ℤˣ} :
    Nonempty (LadderModule q m ε ≃ₗ[UqSl2 q] LadderModule q n δ) ↔ m = n ∧ ε = δ := by
  refine ⟨fun ⟨φ⟩ => ?_, fun ⟨hmn, hεδ⟩ => hmn ▸ hεδ ▸ ⟨LinearEquiv.refl _ _⟩⟩
  -- The dimension recovers `m`.
  obtain rfl : m = n := by simpa using (φ.restrictScalars ℂ).finrank_eq
  refine ⟨rfl, ?_⟩
  -- The trace of `K⁻¹`, an isomorphism invariant, recovers the sign.
  have hconj : (φ.restrictScalars ℂ).conj (rep q m ε (kInv q)) = rep q m δ (kInv q) := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.restrictScalars_apply, ← smul_def,
      ← smul_def, map_smul, LinearEquiv.restrictScalars_symm_apply, LinearEquiv.apply_symm_apply]
  have htr := LinearMap.trace_conj' (rep q m ε (kInv q)) (φ.restrictScalars ℂ)
  rw [hconj, trace_rep_kInv hq.sub_inv_ne_zero, trace_rep_kInv hq.sub_inv_ne_zero] at htr
  have hδε : ((δ : ℤ) : ℂ) = ε := mul_right_cancel₀ (quantumInteger_ne_zero hq (by omega)) htr
  exact Units.ext (Int.cast_injective hδε).symm

end LadderModule

end UqSl2

end TauCeti
