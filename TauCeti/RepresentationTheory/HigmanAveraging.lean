/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RepresentationTheory.Invariants

import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Higman averaging and Kronecker characteristic polynomials

Let `Δ` be a finite group acting on a finite-dimensional `ZMod l`-vector space `V` (`l` prime)
admitting a Higman trace-one operator `τ : V →+ V` (`∑ g, σ g (τ (σ g⁻¹ a)) = a`), and on a
free `ℤ`-module `L` with basis `b`. The averaging operator `f ↦ ∑ g, σ g ∘ τ ∘ f ∘ ρ g⁻¹` projects
`L →ₗ[ℤ] V` onto the `Δ`-equivariant homomorphisms `(ρ.linHom σ).invariants`. Its cardinality is
therefore `l ^ m`, where `m` is the multiplicity of `1` as a root modulo `l` of the characteristic
polynomial of an integral lift built from Kronecker products of transposed matrices of `ρ g⁻¹`
with integral lifts of `σ g ∘ τ`. Moreover, if a `K`-basis `γ` of `L →ₗ[ℤ] K` (over a
characteristic-zero field `K`) is permuted by `Δ` like a finite `Δ`-set `Z`, then that integral
Kronecker sum has the same characteristic polynomial as for the permutation lattice `ℤ[Z]`.

## Main results

* `TauCeti.natCard_invariants_linHom_eq_pow_rootMultiplicity`: cardinality of
  `(ρ.linHom σ).invariants` as `Nat.card (ZMod l)` raised to the multiplicity of `1` in the
  reduced Kronecker characteristic polynomial.
* `TauCeti.charpoly_sum_kronecker_eq_of_perm`: invariance of the integral Kronecker characteristic
  polynomial under passing from `L` to the permutation representation `ℤ[Z]`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, file
  `src/Lib/ClassField/GaloisCohomology/TateIndexFormula.lean` (declarations
  `card_invariants_linHom`, `charpoly_sum_kronecker_eq_of_perm`); Apache 2.0,
  Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti

open Matrix LinearMap Representation

/-- Let `Δ` be a finite group acting on a `ZMod l`-vector space `V` (`l` prime) with basis `c` and
Higman trace-one operator `τ`, and on a free `ℤ`-module `L` with basis `b`. If `T g` is an integral
lift of the matrix of `σ g ∘ τ` in the basis `c`, then `#Hom_Δ(L, V)` equals
`#(ZMod l)` raised to the multiplicity of `1` as a root modulo `l` of the characteristic polynomial
of `∑ g, (M(ρ g⁻¹))ᵀ ⊗ T g`. -/
theorem natCard_invariants_linHom_eq_pow_rootMultiplicity {Δ V ι κ L : Type*} [Group Δ]
    [Fintype Δ] [AddCommGroup V] {l : ℕ} [Fact l.Prime] [Module (ZMod l) V]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [AddCommGroup L]
    {σ : Representation ℤ Δ V} {τ : V →+ V} (hτ : ∀ a : V, ∑ g : Δ, σ g (τ (σ g⁻¹ a)) = a)
    (c : Module.Basis κ (ZMod l) V) {T : Δ → Matrix κ κ ℤ}
    (hT : ∀ (g : Δ) (i j : κ), (T g i j : ZMod l) = c.repr (σ g (τ (c j))) i)
    (b : Module.Basis ι ℤ L) (ρ : Representation ℤ Δ L) :
    Nat.card (ρ.linHom σ).invariants =
      Nat.card (ZMod l) ^
        ((∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).charpoly.map
            (algebraMap ℤ (ZMod l))).rootMultiplicity 1 := by
  let π : (L →ₗ[ℤ] V) →ₗ[ZMod l] L →ₗ[ℤ] V :=
    ((∑ g, ρ.linHom σ g) ∘ₗ .compRight ℤ τ.toIntLinearMap).toAddMonoidHom.toZModLinearMap l
  let e : Module.Basis (ι × κ) (ZMod l) (L →ₗ[ℤ] V) :=
    ((Pi.basis fun _ ↦ c).reindex (.sigmaEquivProd ι κ)).map (b.constr (ZMod l))
  have matrix_eq : (∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ (ZMod l)) =
      toMatrix e e π := by
    ext ⟨i, k⟩ ⟨i', k'⟩
    simp [e, π, hT, Matrix.sum_apply, toMatrix_apply, Pi.single_apply, Finset.sum_apply, mul_comm]
  have h_finite_hom : Module.Finite (ZMod l) (L →ₗ[ℤ] V) := Module.Finite.of_basis e
  have h_π_fixed (x : L →ₗ[ℤ] V) (hx : x ∈ (ρ.linHom σ).invariants) : π x = x := by
    ext y
    have hx' : ∀ g : Δ, x (ρ g⁻¹ y) = σ g⁻¹ (x y) := fun g ↦ by
      have h := congrArg (σ g⁻¹) (LinearMap.congr_fun (hx g) y)
      simpa [Representation.linHom_apply, ← mul_apply_eq_comp, ← map_mul] using h
    simpa [π, LinearMap.sum_apply, hx'] using hτ (x y)
  have h_π_mem (x : L →ₗ[ℤ] V) : π x ∈ (ρ.linHom σ).invariants := fun g ↦
    Representation.self_norm_apply (ρ.linHom σ) g _
  have h_mem_of_pow (k : ℕ) (x : L →ₗ[ℤ] V)
      (hx : ((π - (1 : ZMod l) • 1 : Module.End (ZMod l) (L →ₗ[ℤ] V)) ^ k) x = 0) :
      x ∈ (ρ.linHom σ).invariants := by
    induction k generalizing x with
    | zero => simp_all
    | succ k ih =>
      simpa using sub_mem (h_π_mem x) (ih (π x - x) (by simpa [pow_succ] using hx))
  rw [← Matrix.charpoly_map, matrix_eq, π.charpoly_toMatrix,
    ← finrank_maxGenEigenspace_eq (φ := π) 1, ← Module.natCard_eq_pow_finrank]
  congr! 3 with x
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨fun hx ↦ ⟨1, by simp [h_π_fixed x hx]⟩, fun ⟨k, hk⟩ ↦ h_mem_of_pow k x hk⟩

/-- If `Δ` acts on a free `ℤ`-module `L` with basis `b` and a `K`-basis `γ` of `L →ₗ[ℤ] K`
(over a characteristic-zero field `K`) is permuted by `Δ` as a finite `Δ`-set `Z`, then for any
integral matrices `T g`, `∑ g, (M(ρ g⁻¹))ᵀ ⊗ T g` has the same characteristic polynomial as the
corresponding sum for the permutation representation `ℤ[Z]`. -/
theorem charpoly_sum_kronecker_eq_of_perm {Δ K ι κ L Z : Type*} [Group Δ] [Fintype Δ]
    [Field K] [CharZero K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype Z] [DecidableEq Z] [MulAction Δ Z] [AddCommGroup L]
    (b : Module.Basis ι ℤ L) (ρ : Representation ℤ Δ L) (γ : Module.Basis Z K (L →ₗ[ℤ] K))
    (hγ : ∀ (g : Δ) (z : Z), (ρ g⁻¹).lcomp K K (γ z) = γ (g • z)) (T : Δ → Matrix κ κ ℤ) :
    (∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).charpoly =
      (∑ g : Δ, (toMatrix (MonoidAlgebra.basis Z ℤ) (MonoidAlgebra.basis Z ℤ)
        (ofMulAction ℤ Δ Z g⁻¹))ᵀ.kronecker (T g)).charpoly := by
  let Φ : Module.End K (TensorProduct K (L →ₗ[ℤ] K) (κ → K)) :=
    ∑ g, TensorProduct.map (lcomp K K (ρ g⁻¹)) (toLin' ((T g).map (algebraMap ℤ K)))
  simp_rw [← (Polynomial.map_injective _ (algebraMap ℤ K).injective_int).eq_iff,
    ← Matrix.charpoly_map]
  let e_b := ((Pi.basisFun K ι).map (b.constr K)).tensorProduct (Pi.basisFun K κ)
  let e_γ := γ.tensorProduct (Pi.basisFun K κ)
  have h_mat_b : (∑ g, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ K) =
      toMatrix e_b e_b Φ := by
    ext ⟨i, k⟩ ⟨i', k'⟩
    simp [e_b, Φ, Pi.single_apply, mul_comm, Matrix.sum_apply, toMatrix_apply]
  have h_mat_γ : (∑ g, (toMatrix (MonoidAlgebra.basis Z ℤ) (MonoidAlgebra.basis Z ℤ)
      (ofMulAction ℤ Δ Z g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ K) = toMatrix e_γ e_γ Φ := by
    ext ⟨z, k⟩ ⟨z', k'⟩
    simp [e_γ, Φ, mul_comm, hγ, MonoidAlgebra.basis, Finsupp.single_apply, eq_inv_smul_iff,
      eq_comm, Matrix.sum_apply, toMatrix_apply]
  have : Module.Finite K (L →ₗ[ℤ] K) := Module.Finite.of_basis γ
  rw [h_mat_b, h_mat_γ, Φ.charpoly_toMatrix, Φ.charpoly_toMatrix]

end TauCeti
