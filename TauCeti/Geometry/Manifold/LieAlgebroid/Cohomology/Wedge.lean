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
private lemma linearEquiv_cast_cast {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)] {m p q : ι}
    (h₁ : m = p) (h₂ : p = q) (η : M m) :
    LinearEquiv.cast (R := R) (M := M) h₂ (LinearEquiv.cast (R := R) (M := M) h₁ η) =
      LinearEquiv.cast (R := R) (M := M) (h₁.trans h₂) η := by
  cases h₁; cases h₂; rfl

private lemma linearEquiv_cast_rfl {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)] {m : ι} (h : m = m) (η : M m) :
    LinearEquiv.cast (R := R) (M := M) h η = η := by
  cases h; rfl

section Wedge
open ContMDiffSection (wedge wedge_zero_left wedge_zero_right wedge_comm wedge_apply_zero_right
  interior interior_wedge interior_cast ext_of_interior alternating_add_apply
  alternating_const_smul_apply alternating_smul_apply alternating_cast_apply trivialEquiv
  alternatingIsEmptyEquiv)
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] (A : LieAlgebroid I F V)

/-- The Lie derivative is an ungraded derivation of `ContMDiffSection.wedge`. -/
theorem lieDeriv_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.lieDeriv a (wedge φ ψ) = wedge (A.lieDeriv a φ) ψ + wedge φ (A.lieDeriv a ψ) := by
  obtain ⟨n, hn⟩ : ∃ n, k + l = n := ⟨k + l, rfl⟩
  induction n using Nat.strong_induction_on generalizing k l with
  | ind n ih =>
    rcases k with _ | k
    · simp only [wedge_zero_left, A.trivialEquiv_alternatingIsEmptyEquiv, A.lieDeriv_cast,
        A.lieDeriv_smul, map_add, A.cochainZeroEquiv_lieDeriv]; exact add_comm _ _
    rcases l with _ | l
    · simp only [wedge_zero_right, A.trivialEquiv_alternatingIsEmptyEquiv, A.lieDeriv_cast,
        A.lieDeriv_smul, map_add, A.cochainZeroEquiv_lieDeriv]
    refine ext_of_interior (k := k + 1 + l) fun b ↦ ?_
    have ih₁ := ih (k + (l + 1)) (by omega) (interior b φ) ψ rfl
    have ih₂ := ih ((k + 1) + l) (by omega) φ (interior b ψ) rfl
    simp only [A.interior_lieDeriv, interior_wedge, map_add, map_sub, map_smul,
      LinearMap.sub_apply, A.lieDeriv_cast, ih₁, ih₂]; module
private theorem extDeriv_zero_mul (f g : C^∞⟮I, M; ℝ⟯) :
    A.extDeriv 0 (A.cochainZeroEquiv.symm (f * g)) =
      g • A.extDeriv 0 (A.cochainZeroEquiv.symm f) +
        f • A.extDeriv 0 (A.cochainZeroEquiv.symm g) := by
  ext x v
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  rw [hv]
  simp [A.extDeriv_zero_apply, mvfderiv_mul (f.contMDiff.mdifferentiableAt (by simp))
    (g.contMDiff.mdifferentiableAt (by simp))]
  ring

/-- Scalar derivation rule for `A.extDeriv` in terms of `ContMDiffSection.wedge`. -/
theorem extDeriv_smul {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) :
    A.extDeriv k (f • η) = LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) (Nat.add_comm 1 k)
        (wedge (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η) + f • A.extDeriv k η := by
  induction k with
  | zero =>
    have hη : f • η = A.cochainZeroEquiv.symm (f * A.cochainZeroEquiv η) :=
      A.cochainZeroEquiv.injective (by simp [smul_eq_mul])
    rw [hη, A.extDeriv_zero_mul, wedge_zero_right]
    simp [A.trivialEquiv_alternatingIsEmptyEquiv]
  | succ k ih =>
    refine ext_of_interior fun a ↦ ?_
    simp only [A.interior_extDeriv_succ, A.lieDeriv_smul, map_add, interior_cast,
      interior_wedge (k := 0) a (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η,
      A.interior_extDeriv_zero, wedge_zero_left, A.trivialEquiv_alternatingIsEmptyEquiv,
      A.cochainZeroEquiv_lieDeriv, LinearEquiv.apply_symm_apply,
      LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯), ih (interior a η)]
    simp only [smul_sub, LinearEquiv.cast_apply, cast_cast, cast_eq]; module
/-- Pointwise scalar derivation rule for `A.extDeriv` in terms of `ContMDiffSection.wedge`. -/
theorem extDeriv_smul_apply {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) (x : M)
    (v : Fin (k + 1) → V x) : (A.extDeriv k (f • η)) x v =
      wedge (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η x (v ∘ Fin.cast (Nat.add_comm 1 k)) +
        f x * (A.extDeriv k η) x v := by
  rw [A.extDeriv_smul, alternating_add_apply, alternating_cast_apply, alternating_smul_apply,
    smul_eq_mul]
private lemma extDeriv_wedge_zero_left {l : ℕ} (φ : A.Cochain 0) (ψ : A.Cochain l) :
    A.extDeriv (0 + l) (wedge φ ψ) = LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (Nat.add_right_comm 0 1 l) (wedge (A.extDeriv 0 φ) ψ) + (-1 : ℝ) ^ 0 •
        LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
          (Nat.add_assoc 0 l 1).symm (wedge φ (A.extDeriv l ψ)) := by
  simp only [wedge_zero_left, A.trivialEquiv_alternatingIsEmptyEquiv]
  rw [A.extDeriv_cast, A.extDeriv_smul, LinearEquiv.symm_apply_apply, map_add]
  simp only [pow_zero, one_smul, linearEquiv_cast_cast]
private lemma extDeriv_wedge_zero_right {k : ℕ} (φ : A.Cochain (k + 1)) (ψ : A.Cochain 0) :
    A.extDeriv (k + 1 + 0) (wedge φ ψ) = LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (Nat.add_right_comm (k + 1) 1 0) (wedge (A.extDeriv (k + 1) φ) ψ) +
      (-1 : ℝ) ^ (k + 1) • LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (Nat.add_assoc (k + 1) 0 1).symm (wedge φ (A.extDeriv 0 ψ)) := by
  simp only [wedge_zero_right, A.trivialEquiv_alternatingIsEmptyEquiv]
  rw [A.extDeriv_cast, A.extDeriv_smul, LinearEquiv.symm_apply_apply, wedge_comm φ (A.extDeriv 0 ψ)]
  simp only [LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯), linearEquiv_cast_cast,
    zero_add, mul_one, smul_smul, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_smul]
  exact add_comm _ _
/-- **Graded Leibniz rule** for `A.extDeriv` with respect to `ContMDiffSection.wedge`. -/
theorem extDeriv_wedge {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.extDeriv (k + l) (wedge φ ψ) = LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (Nat.add_right_comm k 1 l) (wedge (A.extDeriv k φ) ψ) + (-1 : ℝ) ^ k •
        LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
          (Nat.add_assoc k l 1).symm (wedge φ (A.extDeriv l ψ)) := by
  obtain ⟨n, hn⟩ : ∃ n, k + l = n := ⟨k + l, rfl⟩
  induction n using Nat.strong_induction_on generalizing k l with
  | ind n ih =>
    rcases k with _ | k; · exact A.extDeriv_wedge_zero_left φ ψ
    rcases l with _ | l; · exact A.extDeriv_wedge_zero_right φ ψ
    refine ext_of_interior (k := k + 1 + l + 1) fun a ↦ ?_
    have ih₁ := ih (k + (l + 1)) (by omega) (interior a φ) ψ rfl
    have ih₂ := ih ((k + 1) + l) (by omega) φ (interior a ψ) rfl
    refine (A.interior_extDeriv_succ (k := k + 1 + l) a (wedge φ ψ)).trans ?_
    simp only [A.lieDeriv_wedge a φ ψ, interior_wedge a φ ψ, interior_cast,
      interior_wedge a (A.extDeriv (k + 1) φ) ψ, interior_wedge a φ (A.extDeriv (l + 1) ψ),
      A.interior_extDeriv_succ, A.extDeriv_cast, map_add, map_sub, LinearMap.sub_apply,
      ih₁, ih₂, LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯),
      LinearMapClass.map_smul_of_tower (S := ℝ), linearEquiv_cast_cast, linearEquiv_cast_rfl]
    simp only [smul_add (M := ℝ) (A := A.Cochain (k + 1 + l + 1)),
      smul_sub (M := ℝ) (A := A.Cochain (k + 1 + l + 1)),
      smul_smul (M := ℝ) (α := A.Cochain (k + 1 + l + 1)),
      ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_smul]
    simp only [pow_succ, mul_neg, mul_one, neg_smul]
    module
/-- Pointwise **graded Leibniz rule** for `A.extDeriv` with respect to `ContMDiffSection.wedge`. -/
theorem extDeriv_wedge_apply {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l) (x : M)
    (v : Fin (k + l + 1) → V x) : (A.extDeriv (k + l) (wedge φ ψ)) x v =
      wedge (A.extDeriv k φ) ψ x (v ∘ Fin.cast (Nat.add_right_comm k 1 l)) +
        (-1 : ℝ) ^ k • wedge φ (A.extDeriv l ψ) x
          (v ∘ Fin.cast (Nat.add_assoc k l 1).symm) := by
  rw [A.extDeriv_wedge, alternating_add_apply, alternating_cast_apply, alternating_const_smul_apply,
    alternating_cast_apply]
end Wedge
end TauCeti.LieAlgebroid
