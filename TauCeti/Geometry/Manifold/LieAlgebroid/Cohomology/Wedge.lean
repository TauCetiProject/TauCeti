/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Cohomology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating.Wedge
import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating.Extension

/-!
# Wedge calculus on Lie algebroid cochains

The Lie derivative `A.lieDeriv` is an ungraded derivation of `ContMDiffSection.wedge`
(`TauCeti.LieAlgebroid.lieDeriv_wedge`), and the Chevalley–Eilenberg differential `A.extDeriv`
satisfies the scalar derivation rule (`TauCeti.LieAlgebroid.extDeriv_smul`) and the graded
Leibniz rule (`TauCeti.LieAlgebroid.extDeriv_wedge`).
-/

public section
noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti.LieAlgebroid
section Wedge
open ContMDiffSection (wedge wedge_zero_left wedge_zero_right wedge_comm wedge_apply_zero_right
  interior interior_wedge interior_cast ext_of_interior alternating_cast_apply trivialEquiv
  alternatingIsEmptyEquiv)
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] (A : LieAlgebroid I F V)

omit [FiniteDimensional ℝ E] [T2Space M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
private lemma cochainZeroEquiv_eq (ξ : A.Cochain 0) :
    trivialEquiv (alternatingIsEmptyEquiv ξ) = A.cochainZeroEquiv ξ := by ext x; simp

/-- The Lie derivative is an ungraded derivation of `ContMDiffSection.wedge`. -/
theorem lieDeriv_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.lieDeriv a (wedge φ ψ) = wedge (A.lieDeriv a φ) ψ + wedge φ (A.lieDeriv a ψ) := by
  obtain ⟨n, hn⟩ : ∃ n, k + l = n := ⟨k + l, rfl⟩
  induction n using Nat.strong_induction_on generalizing k l with
  | ind n ih =>
    rcases k with _ | k
    · simp only [wedge_zero_left, A.cochainZeroEquiv_eq, A.lieDeriv_cast,
        A.lieDeriv_smul, map_add, A.cochainZeroEquiv_lieDeriv]; exact add_comm _ _
    rcases l with _ | l
    · simp only [wedge_zero_right, A.cochainZeroEquiv_eq, A.lieDeriv_cast,
        A.lieDeriv_smul, map_add, A.cochainZeroEquiv_lieDeriv]
    refine ext_of_interior (k := k + 1 + l) fun b ↦ ?_
    have ih₁ := ih (k + (l + 1)) (by omega) (interior b φ) ψ rfl
    have ih₂ := ih ((k + 1) + l) (by omega) φ (interior b ψ) rfl
    simp only [A.interior_lieDeriv, interior_wedge, map_add, map_sub, map_smul,
      LinearMap.sub_apply, A.lieDeriv_cast, ih₁, ih₂]; module

/-- Scalar derivation rule for `A.extDeriv` in terms of `ContMDiffSection.wedge`. -/
theorem extDeriv_smul {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) :
    A.extDeriv k (f • η) = LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) (Nat.add_comm 1 k)
        (wedge (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η) + f • A.extDeriv k η := by
  induction k with
  | zero =>
    ext x v; have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    have hcast : ((![v 0] : Fin 1 → V x) ∘ Fin.cast (Nat.add_comm 1 0)) ∘
        Fin.cast (Nat.add_zero 1).symm = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    rw [hv, ContMDiffSection.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      alternating_cast_apply, ContMDiffSection.smul_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, A.extDeriv_zero_apply, A.extDeriv_zero_apply, map_smul, smul_eq_mul,
      ContMDiffMap.coe_mul, wedge_apply_zero_right, ← A.cochainZeroEquiv_apply η x, hcast,
      A.extDeriv_zero_apply, LinearEquiv.apply_symm_apply,
      mvfderiv_mul (f.contMDiff.mdifferentiableAt (by simp))
        ((A.cochainZeroEquiv η).contMDiff.mdifferentiableAt (by simp))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]; ring
  | succ k ih =>
    refine ext_of_interior fun a ↦ ?_
    simp only [A.interior_extDeriv_succ, A.lieDeriv_smul, map_add, interior_cast,
      interior_wedge (k := 0) a (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η,
      A.interior_extDeriv_zero, wedge_zero_left, A.cochainZeroEquiv_eq, A.cochainZeroEquiv_lieDeriv,
      LinearEquiv.apply_symm_apply, LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯),
      ih (interior a η)]
    simp only [smul_sub, LinearEquiv.cast_apply, cast_cast, cast_eq]; module

/-- Pointwise scalar derivation rule for `A.extDeriv` in terms of `ContMDiffSection.wedge`. -/
theorem extDeriv_smul_apply {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) (x : M)
    (v : Fin (k + 1) → V x) : (A.extDeriv k (f • η)) x v =
      wedge (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η x (v ∘ Fin.cast (Nat.add_comm 1 k)) +
        f x * (A.extDeriv k η) x v := by
  rw [A.extDeriv_smul, ContMDiffSection.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    alternating_cast_apply, ContMDiffSection.smul_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]

private lemma extDeriv_wedge_zero_left {l : ℕ} (φ : A.Cochain 0) (ψ : A.Cochain l) :
    A.extDeriv (0 + l) (wedge φ ψ) = LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (show 0 + 1 + l = 0 + l + 1 by omega) (wedge (A.extDeriv 0 φ) ψ) + (-1 : ℝ) ^ 0 •
        LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
          (show 0 + (l + 1) = 0 + l + 1 by omega) (wedge φ (A.extDeriv l ψ)) := by
  simp only [wedge_zero_left, A.cochainZeroEquiv_eq]
  rw [A.extDeriv_cast, A.extDeriv_smul, LinearEquiv.symm_apply_apply, map_add]
  simp only [pow_zero, one_smul, LinearEquiv.cast_apply, cast_cast]

private lemma extDeriv_wedge_zero_right {k : ℕ} (φ : A.Cochain (k + 1)) (ψ : A.Cochain 0) :
    A.extDeriv (k + 1 + 0) (wedge φ ψ) = LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (show k + 1 + 1 + 0 = k + 1 + 0 + 1 by omega) (wedge (A.extDeriv (k + 1) φ) ψ) +
      (-1 : ℝ) ^ (k + 1) • LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (show k + 1 + (0 + 1) = k + 1 + 0 + 1 by omega) (wedge φ (A.extDeriv 0 ψ)) := by
  have hsmul_sq (ξ : A.Cochain (k + 1 + 0 + 1)) :
      (-1 : ℝ) ^ (k + 1) • (-1 : ℝ) ^ ((k + 1) * (0 + 1)) • ξ = ξ := by
    rw [smul_smul, zero_add, mul_one, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_smul]
  simp only [wedge_zero_right, A.cochainZeroEquiv_eq]
  rw [A.extDeriv_cast, A.extDeriv_smul, LinearEquiv.symm_apply_apply, wedge_comm φ (A.extDeriv 0 ψ)]
  simp only [LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯), LinearEquiv.cast_apply,
    cast_cast, hsmul_sq]; exact add_comm _ _

/-- **Graded Leibniz rule** for `A.extDeriv` with respect to `ContMDiffSection.wedge`. -/
theorem extDeriv_wedge {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.extDeriv (k + l) (wedge φ ψ) = LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (show k + 1 + l = k + l + 1 by omega) (wedge (A.extDeriv k φ) ψ) + (-1 : ℝ) ^ k •
        LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
          (show k + (l + 1) = k + l + 1 by omega) (wedge φ (A.extDeriv l ψ)) := by
  obtain ⟨n, hn⟩ : ∃ n, k + l = n := ⟨k + l, rfl⟩
  induction n using Nat.strong_induction_on generalizing k l with
  | ind n ih =>
    rcases k with _ | k; · exact A.extDeriv_wedge_zero_left φ ψ
    rcases l with _ | l; · exact A.extDeriv_wedge_zero_right φ ψ
    refine ext_of_interior (k := k + 1 + l + 1) fun a ↦ ?_
    have ih₁ := ih (k + (l + 1)) (by omega) (interior a φ) ψ rfl
    have ih₂ := ih ((k + 1) + l) (by omega) φ (interior a ψ) rfl
    have hsmul_add {m : ℕ} (c : ℝ) (x y : A.Cochain m) : c • (x + y) = c • x + c • y := by
      ext p v; simp [smul_add]
    have hneg_smul {m : ℕ} (c : ℝ) (x : A.Cochain m) : (-c) • x = -(c • x) := by
      ext p v; simp [neg_smul]
    have hsmul_neg {m : ℕ} (c : ℝ) (x : A.Cochain m) : c • (-x) = -(c • x) := by
      ext p v; simp [smul_neg]
    have hsmul_sq {m : ℕ} (x : A.Cochain m) : (-1 : ℝ) ^ k • (-1 : ℝ) ^ k • x = x := by
      rw [smul_smul, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_smul]
    refine (A.interior_extDeriv_succ (k := k + 1 + l) a (wedge φ ψ)).trans ?_
    simp only [A.lieDeriv_wedge a φ ψ, interior_wedge a φ ψ, interior_cast,
      interior_wedge a (A.extDeriv (k + 1) φ) ψ, interior_wedge a φ (A.extDeriv (l + 1) ψ),
      A.interior_extDeriv_succ, A.extDeriv_cast, map_add, map_sub, map_smul, LinearMap.sub_apply,
      ih₁, ih₂, smul_add, smul_sub, LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯)]
    simp only [LinearEquiv.cast_apply, cast_cast, cast_eq, hsmul_add, pow_succ, mul_neg, mul_one,
      hneg_smul, hsmul_neg, neg_neg, hsmul_sq]; module

/-- Pointwise **graded Leibniz rule** for `A.extDeriv` with respect to `ContMDiffSection.wedge`. -/
theorem extDeriv_wedge_apply {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l) (x : M)
    (v : Fin (k + l + 1) → V x) : (A.extDeriv (k + l) (wedge φ ψ)) x v =
      wedge (A.extDeriv k φ) ψ x (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • wedge φ (A.extDeriv l ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  rw [A.extDeriv_wedge, ContMDiffSection.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    alternating_cast_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, alternating_cast_apply]
end Wedge
end TauCeti.LieAlgebroid
