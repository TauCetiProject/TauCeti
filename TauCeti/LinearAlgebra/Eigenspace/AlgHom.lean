/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Generalized eigenspaces of algebra endomorphisms

For an algebra endomorphism `f` of an `R`-algebra `A`, generalized eigenvalues multiply: the
product of a generalized `λ`-eigenvector and a generalized `μ`-eigenvector of `f` is a
generalized `λ * μ`-eigenvector, with the exponents adding. This is the multiplicative
counterpart of the additivity of generalized weights on tensor products of Lie modules.

It applies for instance to translation by a point on the coordinate algebra of an affine group,
where it shows that the eigenvalues of a point in all representations are controlled by its
eigenvalues on generators of the coordinate algebra.

## Main results

* `AlgHom.mul_mem_genEigenspace`: generalized eigenvectors multiply, with exponents adding.
* `AlgHom.mul_mem_maxGenEigenspace`: the same for maximal generalized eigenspaces.
* `AlgHom.one_mem_iSup_maxGenEigenspace`, `AlgHom.mul_mem_iSup_maxGenEigenspace`: the sum of the
  generalized eigenspaces for the eigenvalues in a submonoid contains `1` and is closed under
  multiplication.
-/

public section

namespace AlgHom

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **Generalized eigenvectors of an algebra endomorphism multiply.** If `x` is a generalized
`a`-eigenvector of exponent `m` and `y` a generalized `b`-eigenvector of exponent `n` of the
algebra endomorphism `f`, then `x * y` is a generalized `a * b`-eigenvector of exponent
`m + n`. -/
theorem mul_mem_genEigenspace (f : A →ₐ[R] A) {a b : R} {m n : ℕ} {x y : A}
    (hx : x ∈ Module.End.genEigenspace f.toLinearMap a m)
    (hy : y ∈ Module.End.genEigenspace f.toLinearMap b n) :
    x * y ∈ Module.End.genEigenspace f.toLinearMap (a * b) (m + n) := by
  set F : Module.End R A := f.toLinearMap
  set P := F - a • 1
  set Q := F - b • 1
  set D := F - (a * b) • 1
  -- `D` acts on products by a twisted Leibniz rule.
  have hD (x y : A) : D (x * y) = P x * F y + a • (x * Q y) := by
    simp only [D, P, Q, F, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self,
      AlgHom.toLinearMap_apply, map_mul, sub_mul, mul_sub, smul_sub, smul_mul_assoc,
      mul_smul_comm, smul_smul]
    abel
  have hQF (n : ℕ) (y : A) : (Q ^ n) (F y) = F ((Q ^ n) y) := by
    have : Commute F Q := (Commute.refl F).sub_right (Commute.one_right F |>.smul_right b)
    exact LinearMap.congr_fun (this.pow_right n).eq.symm y
  have key (m n : ℕ) (x y : A) (hx : (P ^ m) x = 0) (hy : (Q ^ n) y = 0) :
      (D ^ (m + n)) (x * y) = 0 := by
    induction m generalizing n x y with
    | zero => simp [show x = 0 by simpa using hx]
    | succ m ihm =>
      induction n generalizing x y with
      | zero => simp [show y = 0 by simpa using hy]
      | succ n ihn =>
        rw [pow_succ, mul_apply_eq_comp] at hx
        have hy' := hy
        rw [pow_succ, mul_apply_eq_comp] at hy'
        have h₁ : (D ^ (m + (n + 1))) (P x * F y) = 0 :=
          ihm (n + 1) _ _ hx (by rw [hQF, hy, map_zero])
        have h₂ : (D ^ (m + 1 + n)) (x * Q y) = 0 :=
          ihn _ _ (by rw [pow_succ, mul_apply_eq_comp, hx]) hy'
        rw [show m + 1 + (n + 1) = m + 1 + n + 1 by omega, pow_succ, mul_apply_eq_comp, hD,
          map_add, map_smul, h₂, smul_zero, add_zero, show m + 1 + n = m + (n + 1) by omega, h₁]
  rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hx hy
  rw [← Nat.cast_add, Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
  exact key m n x y hx hy

/-- **Maximal generalized eigenspaces of an algebra endomorphism multiply.** The product of a
generalized `a`-eigenvector and a generalized `b`-eigenvector of the algebra endomorphism `f` is
a generalized `a * b`-eigenvector. -/
theorem mul_mem_maxGenEigenspace (f : A →ₐ[R] A) {a b : R} {x y : A}
    (hx : x ∈ Module.End.maxGenEigenspace f.toLinearMap a)
    (hy : y ∈ Module.End.maxGenEigenspace f.toLinearMap b) :
    x * y ∈ Module.End.maxGenEigenspace f.toLinearMap (a * b) := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
  exact Module.End.genEigenspace_le_maximal _ _ (m + n) <| f.mul_mem_genEigenspace
    (Module.End.mem_genEigenspace_nat.mpr hm) (Module.End.mem_genEigenspace_nat.mpr hn)

/-- The unit is a generalized eigenvector with eigenvalue `1` of every algebra endomorphism, so
it lies in the sum of the generalized eigenspaces for the eigenvalues in any submonoid. -/
theorem one_mem_iSup_maxGenEigenspace (f : A →ₐ[R] A) (S : Submonoid R) :
    (1 : A) ∈ ⨆ a ∈ S, Module.End.maxGenEigenspace f.toLinearMap a := by
  refine Submodule.mem_iSup_of_mem 1 (Submodule.mem_iSup_of_mem S.one_mem ?_)
  refine Module.End.eigenspace_le_maxGenEigenspace ?_
  rw [Module.End.mem_eigenspace_iff, AlgHom.toLinearMap_apply, map_one, one_smul]

/-- The sum of the generalized eigenspaces of an algebra endomorphism for the eigenvalues in a
submonoid is closed under multiplication. -/
theorem mul_mem_iSup_maxGenEigenspace (f : A →ₐ[R] A) {S : Submonoid R} {x y : A}
    (hx : x ∈ ⨆ a ∈ S, Module.End.maxGenEigenspace f.toLinearMap a)
    (hy : y ∈ ⨆ a ∈ S, Module.End.maxGenEigenspace f.toLinearMap a) :
    x * y ∈ ⨆ a ∈ S, Module.End.maxGenEigenspace f.toLinearMap a := by
  set E := ⨆ a ∈ S, Module.End.maxGenEigenspace f.toLinearMap a
  suffices hE : E * E ≤ E from hE (Submodule.mul_mem_mul hx hy)
  simp only [E, Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup₂_le fun b hb ↦ iSup₂_le fun a ha ↦ Submodule.mul_le.mpr fun x hx y hy ↦ ?_
  exact Submodule.mem_iSup_of_mem (a * b) <|
    Submodule.mem_iSup_of_mem (S.mul_mem ha hb) (f.mul_mem_maxGenEigenspace hx hy)

end AlgHom
