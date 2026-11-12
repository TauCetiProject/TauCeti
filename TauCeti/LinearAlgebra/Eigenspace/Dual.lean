/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Eigenspaces of the transpose of an involution

Let `T` be an involutive endomorphism of a module `M` over a commutative ring in which `2` is a
unit, and let `μ` be a square root of `1`. A functional `φ` is a `μ`-eigenvector of the transpose
`T.dualMap` exactly when it vanishes on the `-μ`-eigenspace of `T`. Thus transposition does not
change the labels of the eigenspaces of an involution: the `μ`-eigenspace of `T.dualMap` is the
annihilator of the opposite eigenspace of `T`. When the two eigenspaces are complementary, for
instance for `μ = ±1`, restriction then identifies it with the dual of the `μ`-eigenspace of `T`
(`Submodule.dualAnnihilatorEquivOfIsCompl`).

No finiteness is assumed of `M`.
-/

public section

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For an involution `T` over a ring in which `2` is a unit, and a square root `μ` of `1`,
the `μ`-eigenspace of the transpose of `T` is the annihilator of the `-μ`-eigenspace of `T`. -/
theorem eigenspace_dualMap_eq_dualAnnihilator (h2 : IsUnit (2 : R)) {T : End R M}
    (hT : Function.Involutive T) {μ : R} (hμ : μ * μ = 1) :
    eigenspace T.dualMap μ = (eigenspace T (-μ)).dualAnnihilator := by
  ext φ
  rw [mem_eigenspace_iff, Submodule.mem_dualAnnihilator]
  constructor
  · intro hφ x hx
    -- `φ (T x)` is both `μ φ x` and `-μ φ x`, so `2 μ φ x = 0`.
    have h₁ : φ (T x) = μ * φ x := by simpa using LinearMap.congr_fun hφ x
    rw [mem_eigenspace_iff.1 hx, map_smul, smul_eq_mul] at h₁
    have h₂ : (2 * μ) * φ x = 0 := by linear_combination -h₁
    exact (h2.mul (IsUnit.of_mul_eq_one μ hμ)).mul_right_eq_zero.1 h₂
  · intro hφ
    ext x
    -- `x - μ T x` lies in the `-μ`-eigenspace of `T`, so `φ x = μ φ (T x)`.
    have hy : x - μ • T x ∈ eigenspace T (-μ) := by
      rw [mem_eigenspace_iff]
      simp [hT x, smul_sub, smul_smul, hμ]
      abel
    have h₁ := hφ _ hy
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h₁
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination -μ * h₁ - φ (T x) * hμ

end Module.End
