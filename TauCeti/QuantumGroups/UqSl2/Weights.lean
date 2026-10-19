/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Basic
public import TauCeti.QuantumGroups.QuantumInteger
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Weights and highest vectors for U_q(sl₂)

The weight spaces of a native `UqSl2 q`-module are the eigenspaces of the action of `K`.
The generators `E` and `F` shift weights by `q²` and `q⁻²`, respectively. At a generic
parameter, raising a weight vector in a finite-dimensional module eventually kills it:
otherwise the finite spectrum of `K` would contain an infinite geometric progression.
Consequently every nonzero finite-dimensional module has a highest-weight vector, without
any assumption that `K` is diagonalizable. This is the starting point for classifying
finite-dimensional simple modules.

The action conventions are those of A. Virelizier, *Quantum groups*, Sections 2.3--2.4.
-/

public section

namespace TauCeti.UqSl2

variable {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

/-- The `μ`-weight space of a module is the native eigenspace of the action of `K`. -/
def weightSpace (q : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V] (μ : ℂ) : Submodule ℂ V :=
  (Algebra.lsmul ℂ ℂ V (k q)).eigenspace μ

/-- The weight space agrees with the native eigenspace of the action of `K`. -/
theorem weightSpace_def (μ : ℂ) :
    weightSpace q V μ = (Algebra.lsmul ℂ ℂ V (k q)).eigenspace μ := (rfl)

/-- Membership in a weight space means that `K` acts by its weight. -/
@[simp]
theorem mem_weightSpace_iff {μ : ℂ} {v : V} :
    v ∈ weightSpace q V μ ↔ k q • v = μ • v := by
  simp only [weightSpace_def, Module.End.mem_eigenspace_iff, Algebra.lsmul_coe]

/-- The zero-weight space vanishes because `K` is invertible. -/
@[simp]
theorem weightSpace_zero : weightSpace q V 0 = ⊥ := by
  ext v
  simp only [mem_weightSpace_iff, zero_smul, Submodule.mem_bot]
  constructor
  · intro hv
    have := congrArg (kInv q • ·) hv
    simpa [smul_smul, kInv_mul_k] using this
  · rintro rfl
    simp

/-- Every nonzero weight vector has nonzero weight. -/
theorem weight_ne_zero {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ) (hv0 : v ≠ 0) :
    μ ≠ 0 := by
  rintro rfl
  exact hv0 (by rwa [weightSpace_zero, Submodule.mem_bot] at hv)

/-- On a vector of weight `μ`, the generator `K⁻¹` acts by `μ⁻¹`. -/
theorem kInv_smul_of_mem_weightSpace {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ) :
    kInv q • v = μ⁻¹ • v := by
  have hv' : v = μ • kInv q • v := by
    rw [← smul_comm, ← mem_weightSpace_iff.mp hv, smul_smul, kInv_mul_k, one_smul]
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [zero_smul] at hv'
    simp [hv']
  · calc
      kInv q • v = μ⁻¹ • μ • kInv q • v := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • v := by rw [← hv']

/-- Raising a weight vector multiplies its weight by `q²`. -/
theorem e_smul_mem_weightSpace {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ) :
    e q • v ∈ weightSpace q V (q ^ 2 * μ) := by
  rw [mem_weightSpace_iff] at hv ⊢
  calc
    k q • e q • v = (k q * e q) • v := (mul_smul _ _ _).symm
    _ = (q ^ 2 • (e q * k q)) • v := by rw [k_mul_e]
    _ = (q ^ 2 * μ) • e q • v := by
      simp [smul_assoc, mul_smul, hv, smul_comm (e q) μ v]

/-- Lowering a weight vector multiplies its weight by `q⁻²`. -/
theorem f_smul_mem_weightSpace {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ) :
    f q • v ∈ weightSpace q V (q⁻¹ ^ 2 * μ) := by
  rw [mem_weightSpace_iff] at hv ⊢
  calc
    k q • f q • v = (k q * f q) • v := (mul_smul _ _ _).symm
    _ = (q⁻¹ ^ 2 • (f q * k q)) • v := by rw [k_mul_f]
    _ = (q⁻¹ ^ 2 * μ) • f q • v := by
      simp [smul_assoc, mul_smul, hv, smul_comm (f q) μ v]

/-- The weight after `n` raising operations. -/
theorem e_pow_smul_mem_weightSpace {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ) (n : ℕ) :
    e q ^ n • v ∈ weightSpace q V ((q ^ 2) ^ n * μ) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    simpa [pow_succ', mul_smul, mul_assoc] using e_smul_mem_weightSpace ih

/-- The weight after `n` lowering operations. -/
theorem f_pow_smul_mem_weightSpace {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ) (n : ℕ) :
    f q ^ n • v ∈ weightSpace q V ((q⁻¹ ^ 2) ^ n * μ) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    simpa [pow_succ', mul_smul, mul_assoc] using f_smul_mem_weightSpace ih

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- At a generic parameter `p`, a sequence of vectors whose `n`-th term has weight
`(p²)ⁿ μ` eventually vanishes: otherwise the finite spectrum of `K` would contain an infinite
geometric progression. -/
theorem exists_eq_zero_of_forall_mem_weightSpace {p : ℂ} (hp : IsGenericQuantumParameter p)
    {μ : ℂ} {w : ℕ → V} (hw : ∀ n, w n ∈ weightSpace q V ((p ^ 2) ^ n * μ)) :
    ∃ n : ℕ, w n = 0 := by
  by_contra! h
  have hmu : μ ≠ 0 := by simpa using weight_ne_zero (hw 0) (h 0)
  let ev : ℕ → (Algebra.lsmul ℂ ℂ V (k q)).Eigenvalues := fun n =>
    ⟨(p ^ 2) ^ n * μ, Module.End.hasEigenvalue_of_hasEigenvector ⟨hw n, h n⟩⟩
  apply not_injective_infinite_finite ev
  intro n m hnm
  have hp' : p ^ (2 * n) = p ^ (2 * m) := by
    simpa only [ev, ← pow_mul, mul_left_inj' hmu] using congrArg Subtype.val hnm
  have := hp.pow_injective hp'
  omega

/-- At a generic parameter, the raising string through any weight vector terminates. -/
theorem exists_e_pow_smul_eq_zero (hq : IsGenericQuantumParameter q)
    {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ) : ∃ n : ℕ, e q ^ n • v = 0 :=
  exists_eq_zero_of_forall_mem_weightSpace hq (e_pow_smul_mem_weightSpace hv)

/-- At a generic parameter, the lowering string through any weight vector terminates. -/
theorem exists_f_pow_smul_eq_zero (hq : IsGenericQuantumParameter q)
    {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ) : ∃ n : ℕ, f q ^ n • v = 0 :=
  exists_eq_zero_of_forall_mem_weightSpace hq.inv (f_pow_smul_mem_weightSpace hv)

/-- Every nonzero finite-dimensional module at a generic parameter has a highest-weight
vector. No diagonalizability of `K` is assumed. -/
theorem exists_highest_weight_vector (hq : IsGenericQuantumParameter q) [Nontrivial V] :
    ∃ (μ : ℂ) (v : V), μ ≠ 0 ∧ v ≠ 0 ∧ k q • v = μ • v ∧ e q • v = 0 := by
  classical
  obtain ⟨μ, hμ⟩ := (Algebra.lsmul ℂ ℂ V (k q)).exists_eigenvalue
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have ht := exists_e_pow_smul_eq_zero hq hv
  let n := Nat.find ht
  have hn : 0 < n := by
    by_contra! hn
    have hz : e q ^ n • v = 0 := Nat.find_spec ht
    exact hv0 (by simpa [Nat.eq_zero_of_le_zero hn] using hz)
  refine ⟨(q ^ 2) ^ (n - 1) * μ, e q ^ (n - 1) • v, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq.ne_zero)) (weight_ne_zero hv hv0)
  · exact Nat.find_min ht (by omega)
  · exact mem_weightSpace_iff.mp (e_pow_smul_mem_weightSpace hv (n - 1))
  · simpa [← mul_smul, ← pow_succ', Nat.sub_add_cancel hn] using Nat.find_spec ht

end FiniteDimensional

end TauCeti.UqSl2
