/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Degree-one exactness of the Amitsur complex

For an `R`-algebra `S` and an `R`-module `M`, let `C₀ = S ⊗[R] M` and
`Cᵢ₊₁ = S ⊗[R] Cᵢ`. This file defines the first two differentials
`TauCeti.Amitsur.d₀ : C₀ →ₗ[R] C₁` and `TauCeti.Amitsur.d₁ : C₁ →ₗ[R] C₂`.
The sign of `d₀` agrees with `Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one`:
the insertion on the right has positive sign. The three insertions in `d₁` have signs
`+ - +`, starting on the left.

For a faithfully flat algebra, `TauCeti.Amitsur.exact_d₀_d₁` says that every additive
descent cocycle is a coboundary. This is the module-theoretic input for trivializing
vector-group torsors over affine schemes. The ambiguity of a primitive is exactly an
element `1 ⊗ m`, by `TauCeti.Amitsur.d₀_eq_d₀_iff` and degree-zero exactness.

The contracting homotopy after tensoring with `S` multiplies the first two factors,
as in the degree-zero proof originally in `TauCeti.RingTheory.Flat.EffectiveDescent`.

## References

* The Stacks Project, Lemma 35.3.6, Tag 023M (exactness of the extended Amitsur complex).
-/

public section

open TensorProduct

namespace TauCeti.Amitsur

variable {R : Type*} [CommSemiring R] (S M : Type*) [Ring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The degree-zero Amitsur differential, with the right insertion positive. -/
noncomputable def d₀ : S ⊗[R] M →ₗ[R] S ⊗[R] (S ⊗[R] M) :=
  (TensorProduct.assoc R S S M).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeLeftSubRight R S).rTensor M

/-- The degree-one Amitsur differential: unit insertions with signs `+ - +`
from the left. -/
noncomputable def d₁ : S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] (S ⊗[R] (S ⊗[R] M)) :=
  TensorProduct.mk R S (S ⊗[R] (S ⊗[R] M)) 1 + (d₀ S M).lTensor S

theorem d₀_def : d₀ (R := R) S M =
    (TensorProduct.mk R S M 1).lTensor S - TensorProduct.mk R S (S ⊗[R] M) 1 := by
  ext s m
  simp [d₀, sub_tmul]

@[simp]
theorem d₀_tmul (s : S) (m : M) :
    d₀ S M (s ⊗ₜ[R] m) = s ⊗ₜ[R] (1 ⊗ₜ[R] m) - 1 ⊗ₜ[R] (s ⊗ₜ[R] m) := by
  simp [d₀_def]

@[simp]
theorem d₁_tmul (s t : S) (m : M) :
    d₁ S M (s ⊗ₜ[R] (t ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] (s ⊗ₜ[R] (t ⊗ₜ[R] m)) - s ⊗ₜ[R] (1 ⊗ₜ[R] (t ⊗ₜ[R] m)) +
        s ⊗ₜ[R] (t ⊗ₜ[R] (1 ⊗ₜ[R] m)) := by
  simp [d₁, tmul_sub]
  abel

/-- The augmentation followed by the degree-zero Amitsur differential is zero. -/
@[simp]
theorem d₀_comp_mk_one : d₀ (R := R) S M ∘ₗ TensorProduct.mk R S M 1 = 0 := by
  ext m
  simp

/-- The first two Amitsur differentials compose to zero over any algebra. -/
@[simp]
theorem d₁_comp_d₀ : d₁ (R := R) S M ∘ₗ d₀ S M = 0 := by
  ext s m
  simp

/-- Applying successive Amitsur differentials to any cochain gives zero. -/
@[simp]
theorem d₁_d₀ (x : S ⊗[R] M) : d₁ S M (d₀ S M x) = 0 :=
  DFunLike.congr_fun (d₁_comp_d₀ S M) x

end TauCeti.Amitsur

section

variable {R : Type*} [CommRing R] (S M : Type*) [Ring S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- **Amitsur exactness.** If `S` is a faithfully flat `R`-algebra, then for every `R`-module
`M` the sequence `M → S ⊗[R] M → S ⊗[R] (S ⊗[R] M)`, with maps `m ↦ 1 ⊗ m` and
`s ⊗ m ↦ s ⊗ (1 ⊗ m) - 1 ⊗ (s ⊗ m)`, is exact. -/
theorem Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one [Module.FaithfullyFlat R S] :
    Function.Exact (TensorProduct.mk R S M 1) (TauCeti.Amitsur.d₀ S M) := by
  -- Multiplication of the first two factors contracts the complex after base change.
  let h := TauCeti.tensorProductMulLeft (R := R) S M
  let h' := TauCeti.tensorProductMulLeft (R := R) S (S ⊗[R] M)
  have key : h' ∘ₗ (TauCeti.Amitsur.d₀ S M).lTensor S =
      (TensorProduct.mk R S M 1).lTensor S ∘ₗ h - LinearMap.id := by
    ext s t m
    simp [TauCeti.Amitsur.d₀_def, h, h']
  apply Module.FaithfullyFlat.lTensor_reflects_exact R S
  refine LinearMap.exact_of_comp_of_mem_range ?_ fun y hy ↦ ?_
  · rw [← LinearMap.lTensor_comp, TauCeti.Amitsur.d₀_comp_mk_one, LinearMap.lTensor_zero]
  · refine ⟨h y, ?_⟩
    have hk := congr($key y)
    simp only [LinearMap.comp_apply, hy, map_zero, LinearMap.sub_apply,
      LinearMap.id_apply] at hk
    exact sub_eq_zero.mp hk.symm

namespace TauCeti.Amitsur

/-- Over a faithfully flat algebra, every degree-one Amitsur cocycle is a coboundary. -/
theorem exact_d₀_d₁ [Module.FaithfullyFlat R S] :
    Function.Exact (d₀ (R := R) S M) (d₁ S M) := by
  -- Multiplication of the first two factors contracts the complex after base change.
  let h' := tensorProductMulLeft (R := R) S (S ⊗[R] M)
  let h'' := tensorProductMulLeft (R := R) S (S ⊗[R] (S ⊗[R] M))
  have key : h'' ∘ₗ (d₁ S M).lTensor S =
      LinearMap.id + (d₀ S M).lTensor S ∘ₗ h' := by
    ext s t u m
    simp [h', h'', d₁, d₀_def]
  apply Module.FaithfullyFlat.lTensor_reflects_exact R S
  refine LinearMap.exact_of_comp_of_mem_range ?_ fun y hy ↦ ?_
  · rw [← LinearMap.lTensor_comp, d₁_comp_d₀, LinearMap.lTensor_zero]
  · refine ⟨-h' y, ?_⟩
    have hk := congr($key y)
    simp only [LinearMap.comp_apply, hy, map_zero, LinearMap.add_apply,
      LinearMap.id_apply] at hk
    simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hk.symm).symm

/-- Two primitives have the same coboundary precisely when their difference comes from `M`. -/
theorem d₀_eq_d₀_iff [Module.FaithfullyFlat R S] (x y : S ⊗[R] M) :
    d₀ S M x = d₀ S M y ↔ ∃ m : M, x - y = 1 ⊗ₜ[R] m := by
  rw [← sub_eq_zero, ← map_sub]
  exact (Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one S M (x - y)).trans
    (exists_congr fun _ ↦ eq_comm)

end TauCeti.Amitsur

end
