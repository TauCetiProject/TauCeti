/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.Pow
public import TauCeti.LinearAlgebra.Eigenspace.Transport
public import TauCeti.QuantumGroups.UqSl2.Basic
public import TauCeti.QuantumGroups.QuantumInteger.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Module

/-!
# Weights and highest vectors for U_q(sl₂)

The weight spaces of a native `UqSl2 q`-module are the eigenspaces of the action of `K`, and
its generalized weight spaces are the maximal generalized eigenspaces of `K`. The generators
`E` and `F` shift both kinds of weight by `q²` and `q⁻²`, respectively. A finite-dimensional
module is the direct sum of its generalized weight spaces, whether or not `K` is
diagonalizable. At a generic parameter, raising or lowering any vector of a finite-dimensional
module therefore eventually kills it: otherwise the finite spectrum of `K` would contain an
infinite geometric progression. Consequently every nonzero finite-dimensional module has a
highest-weight vector. More precisely, every nonzero generalized weight vector is moved by some
element of `UqSl2 q` to a nonzero highest-weight vector, and by another to a nonzero
lowest-weight vector. This is the starting point for classifying finite-dimensional simple
modules, and the generalized weight decomposition is the setting of the finite-dimensional
complete-reducibility argument. Taking generalized weight spaces of finite-dimensional modules is
exact: a surjective module map carries generalized weight spaces onto those of its target.

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

/-- On a vector of weight `μ`, the integer power `K ^ b` acts by `μ ^ b`. -/
theorem kUnit_zpow_smul_of_mem_weightSpace {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ)
    (b : ℤ) : ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) • v = μ ^ b • v := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [weightSpace_zero, Submodule.mem_bot] at hv
    simp [hv]
  induction b using Int.induction_on with
  | zero => simp
  | succ n ih =>
    simpa [zpow_add_one, zpow_add_one₀ hμ, mul_smul, mem_weightSpace_iff.mp hv,
      smul_comm (k q ^ n) μ, smul_comm (μ ^ n) μ] using congrArg (μ • ·) ih
  | pred n ih =>
    simpa [zpow_sub_one, zpow_sub_one₀ hμ, mul_smul, kInv_smul_of_mem_weightSpace hv,
      smul_comm (kInv q ^ n) μ⁻¹, smul_comm (μ ^ n)⁻¹ μ⁻¹] using congrArg (μ⁻¹ • ·) ih

/-- A module map carries each weight space into the weight space of the same weight. -/
theorem map_weightSpace_le {W : Type*} [AddCommGroup W] [Module ℂ W] [Module (UqSl2 q) W]
    [IsScalarTower ℂ (UqSl2 q) W] (φ : V →ₗ[UqSl2 q] W) (μ : ℂ) :
    (weightSpace q V μ).map (φ.restrictScalars ℂ) ≤ weightSpace q W μ :=
  Module.End.map_genEigenspace_le _ (LinearMap.ext fun x => (φ.map_smul (k q) x).symm) μ 1

/-! ### Generalized weight spaces -/

/-- The generalized `μ`-weight space of a module is the native maximal generalized eigenspace of
the action of `K`: the vectors killed by some power of `K - μ`. -/
def genWeightSpace (q : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V] (μ : ℂ) : Submodule ℂ V :=
  (Algebra.lsmul ℂ ℂ V (k q)).maxGenEigenspace μ

/-- The generalized weight space agrees with the native maximal generalized eigenspace of the
action of `K`. -/
theorem genWeightSpace_def (μ : ℂ) :
    genWeightSpace q V μ = (Algebra.lsmul ℂ ℂ V (k q)).maxGenEigenspace μ := (rfl)

/-- Membership in a generalized weight space means that some power of `K - μ` kills the
vector. -/
@[simp]
theorem mem_genWeightSpace_iff {μ : ℂ} {v : V} :
    v ∈ genWeightSpace q V μ ↔ ∃ n : ℕ, (k q - algebraMap ℂ (UqSl2 q) μ) ^ n • v = 0 := by
  rw [genWeightSpace_def, Module.End.mem_maxGenEigenspace, ← Algebra.algebraMap_eq_smul_one,
    ← AlgHom.commutes (Algebra.lsmul ℂ ℂ V (A := UqSl2 q))]
  simp only [← map_sub, ← map_pow, Algebra.lsmul_coe]

/-- Every weight space lies in the generalized weight space of the same weight. -/
theorem weightSpace_le_genWeightSpace (μ : ℂ) : weightSpace q V μ ≤ genWeightSpace q V μ :=
  Module.End.eigenspace_le_maxGenEigenspace

/-- The generalized zero-weight space vanishes because `K` is invertible. -/
@[simp]
theorem genWeightSpace_zero : genWeightSpace q V 0 = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  obtain ⟨n, hn⟩ := mem_genWeightSpace_iff.mp hv
  rw [map_zero, sub_zero, ← kUnit_val, ← Units.val_pow_eq_pow_val] at hn
  exact ((kUnit q ^ n).isUnit.smul_eq_zero).mp hn

/-- An element `a` that `q`-commutes with `K` in the form `K a = c (a K)` maps the generalized
`μ`-weight space into the generalized `c μ`-weight space. -/
theorem smul_mem_genWeightSpace_of_k_mul {a : UqSl2 q} {c μ : ℂ} (ha : k q * a = c • (a * k q))
    {v : V} (hv : v ∈ genWeightSpace q V μ) : a • v ∈ genWeightSpace q V (c * μ) := by
  obtain ⟨n, hn⟩ := mem_genWeightSpace_iff.mp hv
  refine mem_genWeightSpace_iff.mpr ⟨n, ?_⟩
  -- `(K - c μ) a = a (c (K - μ))`, so the powers of the two factors intertwine `a`.
  have h : SemiconjBy a (c • (k q - algebraMap ℂ (UqSl2 q) μ))
      (k q - algebraMap ℂ (UqSl2 q) (c * μ)) := by
    rw [SemiconjBy, sub_mul, ha, map_mul, mul_assoc, Algebra.commutes μ a, ← Algebra.smul_def,
      ← smul_sub, mul_smul_comm, mul_sub]
  rw [← mul_smul, ← (h.pow_right n).eq, smul_pow, mul_smul, smul_assoc, hn, smul_zero, smul_zero]

/-- Raising a generalized weight vector multiplies its generalized weight by `q²`. -/
theorem e_smul_mem_genWeightSpace {μ : ℂ} {v : V} (hv : v ∈ genWeightSpace q V μ) :
    e q • v ∈ genWeightSpace q V (q ^ 2 * μ) :=
  smul_mem_genWeightSpace_of_k_mul k_mul_e hv

/-- Lowering a generalized weight vector multiplies its generalized weight by `q⁻²`. -/
theorem f_smul_mem_genWeightSpace {μ : ℂ} {v : V} (hv : v ∈ genWeightSpace q V μ) :
    f q • v ∈ genWeightSpace q V (q⁻¹ ^ 2 * μ) :=
  smul_mem_genWeightSpace_of_k_mul k_mul_f hv

/-- The generalized weight after `n` raising operations. -/
theorem e_pow_smul_mem_genWeightSpace {μ : ℂ} {v : V} (hv : v ∈ genWeightSpace q V μ) (n : ℕ) :
    e q ^ n • v ∈ genWeightSpace q V ((q ^ 2) ^ n * μ) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    simpa [pow_succ', mul_smul, mul_assoc] using e_smul_mem_genWeightSpace ih

/-- The generalized weight after `n` lowering operations. -/
theorem f_pow_smul_mem_genWeightSpace {μ : ℂ} {v : V} (hv : v ∈ genWeightSpace q V μ) (n : ℕ) :
    f q ^ n • v ∈ genWeightSpace q V ((q⁻¹ ^ 2) ^ n * μ) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    simpa [pow_succ', mul_smul, mul_assoc] using f_smul_mem_genWeightSpace ih

/-- Generalized weight spaces for distinct weights are independent. -/
theorem iSupIndep_genWeightSpace : iSupIndep (genWeightSpace q V) :=
  Module.End.independent_maxGenEigenspace _

/-- `K` preserves every generalized weight space. -/
theorem k_smul_mem_genWeightSpace {μ : ℂ} {v : V} (hv : v ∈ genWeightSpace q V μ) :
    k q • v ∈ genWeightSpace q V μ := by
  simpa using smul_mem_genWeightSpace_of_k_mul (a := k q) (c := 1) (by rw [one_smul]) hv

/-- `K⁻¹` preserves every generalized weight space. -/
theorem kInv_smul_mem_genWeightSpace {μ : ℂ} {v : V} (hv : v ∈ genWeightSpace q V μ) :
    kInv q • v ∈ genWeightSpace q V μ := by
  simpa using smul_mem_genWeightSpace_of_k_mul (a := kInv q) (c := 1)
    (by rw [one_smul, k_mul_kInv, kInv_mul_k]) hv

/-- A vector of weight `α` in the generalized weight space of a different weight vanishes. -/
theorem eq_zero_of_mem_weightSpace_of_mem_genWeightSpace {α ν : ℂ} (h : α ≠ ν) {v : V}
    (hα : v ∈ weightSpace q V α) (hν : v ∈ genWeightSpace q V ν) : v = 0 :=
  Submodule.disjoint_def.mp ((iSupIndep_genWeightSpace (q := q) (V := V)).pairwiseDisjoint h)
    v (weightSpace_le_genWeightSpace α hα) hν

/-- If `K² v = ρ² v` for a generalized weight vector `v` of weight `ν ≠ -ρ`, then `K v = ρ v`. -/
theorem k_smul_eq_of_k_sq_smul_eq {ν ρ : ℂ} (h : -ρ ≠ ν) {v : V}
    (hv : v ∈ genWeightSpace q V ν) (hk : k q ^ 2 • v = ρ ^ 2 • v) : k q • v = ρ • v := by
  -- The vector `K v - ρ v` has weight `-ρ`, so it vanishes.
  have hw : k q • v - ρ • v ∈ weightSpace q V (-ρ) := by
    rw [mem_weightSpace_iff, smul_sub, smul_comm (k q) ρ v, ← mul_smul, ← sq, hk]
    generalize k q • v = x
    module
  exact sub_eq_zero.mp (eq_zero_of_mem_weightSpace_of_mem_genWeightSpace h hw
    (sub_mem (k_smul_mem_genWeightSpace hv) (Submodule.smul_mem _ ρ hv)))

/-- Some power of `K - μ` sends a nonzero generalized weight vector of weight `μ` to a nonzero
weight vector of weight `μ`. -/
theorem exists_pow_smul_mem_weightSpace {μ : ℂ} {w : V} (hw : w ∈ genWeightSpace q V μ)
    (hw0 : w ≠ 0) :
    ∃ r : ℕ, (k q - algebraMap ℂ (UqSl2 q) μ) ^ r • w ≠ 0 ∧
      (k q - algebraMap ℂ (UqSl2 q) μ) ^ r • w ∈ weightSpace q V μ := by
  obtain ⟨r, hr0, hr⟩ := exists_pow_smul_ne_zero_and_smul_eq_zero hw0 (mem_genWeightSpace_iff.mp hw)
  rw [sub_smul, algebraMap_smul, sub_eq_zero] at hr
  exact ⟨r, hr0, mem_weightSpace_iff.mpr hr⟩

/-- If `x` satisfies `K x = c (x K)` and some power of `x` kills a nonzero generalized weight
vector `w`, then some element of `UqSl2 q` sends `w` to a nonzero weight vector killed by `x`. -/
private theorem exists_smul_mem_weightSpace_of_k_mul {x : UqSl2 q} {c : ℂ}
    (hx : k q * x = c • (x * k q)) (hc : c ≠ 0) {μ : ℂ} {w : V}
    (hw : w ∈ genWeightSpace q V μ) (hw0 : w ≠ 0) (hxw : ∃ n : ℕ, x ^ n • w = 0) :
    ∃ (a : UqSl2 q) (n : ℕ), a • w ≠ 0 ∧ a • w ∈ weightSpace q V (c ^ n * μ) ∧
      x • a • w = 0 := by
  -- First push `w` along `x` to the last nonzero vector `u` of its `x`-string.
  obtain ⟨n, hu0, hxu⟩ := exists_pow_smul_ne_zero_and_smul_eq_zero hw0 hxw
  have hxn : k q * x ^ n = c ^ n • (x ^ n * k q) := by
    have h : SemiconjBy (k q) x (c • x) := by rw [SemiconjBy, hx, smul_mul_assoc]
    rw [(h.pow_right n).eq, smul_pow, smul_mul_assoc]
  -- Then apply a power of `K - c^n μ` to reach a genuine weight vector.
  obtain ⟨r, hr0, hrw⟩ :=
    exists_pow_smul_mem_weightSpace (smul_mem_genWeightSpace_of_k_mul hxn hw) hu0
  -- Commuting `x` past `K - c^n μ` replaces `K` by `c⁻¹ K`, so `x` still kills the result.
  have hxD : SemiconjBy x (k q - algebraMap ℂ (UqSl2 q) (c ^ n * μ))
      (c⁻¹ • k q - algebraMap ℂ (UqSl2 q) (c ^ n * μ)) := by
    have hxk : x * k q = c⁻¹ • (k q * x) := by rw [hx, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [SemiconjBy, mul_sub, sub_mul, hxk, smul_mul_assoc, Algebra.commutes]
  refine ⟨(k q - algebraMap ℂ (UqSl2 q) (c ^ n * μ)) ^ r * x ^ n, n, by rwa [mul_smul],
    by rwa [mul_smul], ?_⟩
  rw [← mul_smul, ← mul_assoc, (hxD.pow_right r).eq, mul_assoc, mul_smul, mul_smul, hxu,
    smul_zero]

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- A finite-dimensional module is the sum of its generalized weight spaces. -/
theorem iSup_genWeightSpace_eq_top : ⨆ μ, genWeightSpace q V μ = ⊤ :=
  Module.End.iSup_maxGenEigenspace_eq_top _

/-- A surjective module map carries the generalized weight spaces of a finite-dimensional module
onto the generalized weight spaces of its target. In particular, taking generalized weight
spaces is exact on quotient modules. -/
theorem map_genWeightSpace_eq_of_surjective {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    [Module (UqSl2 q) V'] [IsScalarTower ℂ (UqSl2 q) V'] {φ : V →ₗ[UqSl2 q] V'}
    (hφ : Function.Surjective φ) (μ : ℂ) :
    (genWeightSpace q V μ).map (φ.restrictScalars ℂ) = genWeightSpace q V' μ := by
  rw [genWeightSpace_def, genWeightSpace_def]
  exact map_maxGenEigenspace_eq_of_intertwine hφ (fun x => φ.map_smul (k q) x)
    (by simpa only [genWeightSpace_def] using iSup_genWeightSpace_eq_top (q := q) (V := V)) μ

/-- At a generic parameter `p`, a sequence of vectors whose `n`-th term has generalized weight
`(p²)ⁿ μ` eventually vanishes: otherwise the finite spectrum of `K` would contain an infinite
geometric progression. -/
theorem exists_eq_zero_of_forall_mem_genWeightSpace {p : ℂ} (hp : IsGenericQuantumParameter p)
    {μ : ℂ} {w : ℕ → V} (hw : ∀ n, w n ∈ genWeightSpace q V ((p ^ 2) ^ n * μ)) :
    ∃ n : ℕ, w n = 0 := by
  by_contra! h
  have hmu : μ ≠ 0 := by
    rintro rfl
    exact h 0 (by simpa using hw 0)
  let ev : ℕ → (Algebra.lsmul ℂ ℂ V (k q)).Eigenvalues := fun n =>
    ⟨(p ^ 2) ^ n * μ,
      Module.End.HasUnifEigenvalue.lt zero_lt_one ((Submodule.ne_bot_iff _).mpr ⟨_, hw n, h n⟩)⟩
  apply not_injective_infinite_finite ev
  intro n m hnm
  have hp' : p ^ (2 * n) = p ^ (2 * m) := by
    simpa only [ev, ← pow_mul, mul_left_inj' hmu] using congrArg Subtype.val hnm
  have := hp.pow_injective hp'
  omega

/-- An element that eventually kills every generalized weight vector of a finite-dimensional
module eventually kills every vector. -/
private theorem exists_pow_smul_eq_zero_of_genWeightSpace {a : UqSl2 q}
    (h : ∀ μ, ∀ v ∈ genWeightSpace q V μ, ∃ n : ℕ, a ^ n • v = 0) (v : V) :
    ∃ n : ℕ, a ^ n • v = 0 := by
  -- The vectors killed by a power of `a` form the generalized `0`-eigenspace of its action.
  have hle : ⊤ ≤ (Algebra.lsmul ℂ ℂ V a).maxGenEigenspace 0 := by
    rw [← iSup_genWeightSpace_eq_top (q := q)]
    exact iSup_le fun μ v hv => by simpa [← map_pow] using h μ v hv
  simpa [← map_pow] using hle Submodule.mem_top

/-- At a generic parameter, the raising string through any vector of a finite-dimensional module
terminates: `E` acts locally nilpotently. -/
theorem exists_e_pow_smul_eq_zero (hq : IsGenericQuantumParameter q) (v : V) :
    ∃ n : ℕ, e q ^ n • v = 0 :=
  exists_pow_smul_eq_zero_of_genWeightSpace (fun _ _ hv =>
    exists_eq_zero_of_forall_mem_genWeightSpace hq (e_pow_smul_mem_genWeightSpace hv)) v

/-- At a generic parameter, the lowering string through any vector of a finite-dimensional
module terminates: `F` acts locally nilpotently. -/
theorem exists_f_pow_smul_eq_zero (hq : IsGenericQuantumParameter q) (v : V) :
    ∃ n : ℕ, f q ^ n • v = 0 :=
  exists_pow_smul_eq_zero_of_genWeightSpace (fun _ _ hv =>
    exists_eq_zero_of_forall_mem_genWeightSpace hq.inv (f_pow_smul_mem_genWeightSpace hv)) v

/-- At a generic parameter, the raising string through a nonzero vector of a finite-dimensional
module ends in a nonzero vector `Eⁿ v` killed by `E`. When `v` has weight `μ`, this is a
highest-weight vector of weight `(q²)ⁿ μ`. -/
theorem exists_e_pow_smul_ne_zero_and_e_smul_eq_zero (hq : IsGenericQuantumParameter q) {v : V}
    (hv0 : v ≠ 0) : ∃ n : ℕ, e q ^ n • v ≠ 0 ∧ e q • e q ^ n • v = 0 :=
  exists_pow_smul_ne_zero_and_smul_eq_zero hv0 (exists_e_pow_smul_eq_zero hq v)

/-- Every nonzero finite-dimensional module at a generic parameter has a highest-weight
vector. No diagonalizability of `K` is assumed. -/
theorem exists_highest_weight_vector (hq : IsGenericQuantumParameter q) [Nontrivial V] :
    ∃ (μ : ℂ) (v : V), μ ≠ 0 ∧ v ≠ 0 ∧ k q • v = μ • v ∧ e q • v = 0 := by
  obtain ⟨μ, hμ⟩ := (Algebra.lsmul ℂ ℂ V (k q)).exists_eigenvalue
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  obtain ⟨n, hn0, hn⟩ := exists_e_pow_smul_ne_zero_and_e_smul_eq_zero hq hv0
  refine ⟨(q ^ 2) ^ n * μ, e q ^ n • v, ?_, hn0, ?_, hn⟩
  · exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq.ne_zero)) (weight_ne_zero hv hv0)
  · exact mem_weightSpace_iff.mp (e_pow_smul_mem_weightSpace hv n)

/-- At a generic parameter, every nonzero generalized weight space of weight `ν` yields a nonzero
vector of weight `(q²)ⁿ ν`, for some `n`, killed by `E`. -/
theorem exists_highest_weight_vector_of_genWeightSpace_ne_bot
    (hq : IsGenericQuantumParameter q) {ν : ℂ} (hν : genWeightSpace q V ν ≠ ⊥) :
    ∃ (n : ℕ) (v : V), v ∈ weightSpace q V ((q ^ 2) ^ n * ν) ∧ v ≠ 0 ∧ e q • v = 0 := by
  rw [genWeightSpace_def] at hν
  have hev : (Algebra.lsmul ℂ ℂ V (k q)).HasEigenvalue ν :=
    Module.End.HasUnifEigenvalue.lt zero_lt_one hν
  obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
  replace hv : v ∈ weightSpace q V ν := by rwa [weightSpace_def]
  obtain ⟨n, hn0, hn⟩ := exists_e_pow_smul_ne_zero_and_e_smul_eq_zero hq hv0
  exact ⟨n, e q ^ n • v, e_pow_smul_mem_weightSpace hv n, hn0, hn⟩

/-- At a generic parameter, every nonzero generalized weight vector `w` of weight `μ` in a
finite-dimensional module can be moved by an element of `UqSl2 q` to a nonzero highest-weight
vector, of weight `q^(2n) μ` for some `n`. -/
theorem exists_smul_highest_weight_vector_of_mem_genWeightSpace
    (hq : IsGenericQuantumParameter q) {μ : ℂ} {w : V} (hw : w ∈ genWeightSpace q V μ)
    (hw0 : w ≠ 0) :
    ∃ (a : UqSl2 q) (n : ℕ), a • w ≠ 0 ∧ a • w ∈ weightSpace q V ((q ^ 2) ^ n * μ) ∧
      e q • a • w = 0 :=
  exists_smul_mem_weightSpace_of_k_mul k_mul_e (pow_ne_zero 2 hq.ne_zero) hw hw0
    (exists_e_pow_smul_eq_zero hq w)

/-- At a generic parameter, every nonzero generalized weight vector `w` of weight `μ` in a
finite-dimensional module can be moved by an element of `UqSl2 q` to a nonzero lowest-weight
vector, of weight `q^(-2n) μ` for some `n`. -/
theorem exists_smul_lowest_weight_vector_of_mem_genWeightSpace
    (hq : IsGenericQuantumParameter q) {μ : ℂ} {w : V} (hw : w ∈ genWeightSpace q V μ)
    (hw0 : w ≠ 0) :
    ∃ (a : UqSl2 q) (n : ℕ), a • w ≠ 0 ∧ a • w ∈ weightSpace q V ((q⁻¹ ^ 2) ^ n * μ) ∧
      f q • a • w = 0 :=
  exists_smul_mem_weightSpace_of_k_mul k_mul_f (pow_ne_zero 2 (inv_ne_zero hq.ne_zero)) hw hw0
    (exists_f_pow_smul_eq_zero hq w)

end FiniteDimensional

end TauCeti.UqSl2
