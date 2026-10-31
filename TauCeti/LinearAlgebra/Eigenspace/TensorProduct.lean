/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic

/-!
# Eigenspaces and tensoring with a flat module

Let `f` be an endomorphism of a module `S` over a commutative ring `k`, and `X` a flat
`k`-module. The eigenspace inclusion of `f` at `μ` is exact against `f - μ`, and tensoring with
`X` preserves this: the kernel of `(f - μ) ⊗ id` on `S ⊗[k] X` is the image of
`Eig(f, μ) ⊗[k] X`. Flatness cannot be dropped: for `S = k` and a non-zero-divisor `r ∈ k`,
the `0`-eigenspace of `r` is zero, while the kernel of `r ⊗ id` on `X` is its `r`-torsion.

When `f` is the action of an element `a` of a `k`-algebra `A` acting on `S`, the endomorphism
`(f - μ) ⊗ id` is the action of `a - μ` on `S ⊗[k] X` through the left factor.

A linear map `l` from `S` to a vector space over a field `K` extending `k` with `l ∘ f = μ • l`
has a `K`-linear extension `l.liftBaseChange K` to `K ⊗[k] S` vanishing on every eigenspace of the
base change of `f` for an eigenvalue other than `μ`.

## Main results

* `Module.End.exact_rTensor_eigenspace`: `Eig(f, μ) ⊗ X → S ⊗ X → S ⊗ X` is exact for flat `X`.
* `TauCeti.rTensor_lsmul_sub_smul_apply`: `(a - μ) ⊗ id` acts as `a - μ` on the left factor.
* `LinearMap.liftBaseChange_eq_zero_of_mem_eigenspace_baseChange`: the extension of an
  eigenvector of precomposition by `f` kills the other eigenspaces of the base change of `f`.
-/

public section

open TensorProduct

variable {k S : Type*} [CommRing k] [AddCommGroup S] [Module k S]

/-- For a flat module `X`, the eigenspace inclusion of `f` at `μ`, tensored with `X`, is exact
against `(f - μ) ⊗ id`. -/
theorem Module.End.exact_rTensor_eigenspace (f : Module.End k S) (μ : k) (X : Type*)
    [AddCommGroup X] [Module k X] [Module.Flat k X] :
    Function.Exact ((f.eigenspace μ).subtype.rTensor X) ((f - μ • 1).rTensor X) := by
  refine Module.Flat.rTensor_exact X ?_
  rw [LinearMap.exact_iff, Submodule.range_subtype]
  ext s
  simp [sub_eq_zero]

/-- If `l (f v) = μ • l v` for all `v`, the `K`-linear extension of `l` vanishes on the eigenspace
of the base change of `f` for every eigenvalue `ν ≠ μ`. -/
theorem LinearMap.liftBaseChange_eq_zero_of_mem_eigenspace_baseChange {K N : Type*} [Field K]
    [Algebra k K] [AddCommGroup N] [Module k N] [Module K N] [IsScalarTower k K N]
    (l : S →ₗ[k] N) (f : Module.End k S) {μ ν : K} (hl : ∀ v, l (f v) = μ • l v) (hνμ : ν ≠ μ)
    {X : K ⊗[k] S} (hX : X ∈ Module.End.eigenspace (f.baseChange K) ν) :
    l.liftBaseChange K X = 0 := by
  have hcomm : l.liftBaseChange K ∘ₗ f.baseChange K = μ • l.liftBaseChange K := by
    ext v
    simp [hl]
  have h : ν • l.liftBaseChange K X = μ • l.liftBaseChange K X := by
    simpa [Module.End.mem_eigenspace_iff.1 hX] using LinearMap.congr_fun hcomm X
  exact (smul_eq_zero.1 (by rw [sub_smul, h, sub_self])).resolve_left (sub_ne_zero.2 hνμ)

namespace TauCeti

variable {A : Type*} [Ring A] [Algebra k A] [Module A S] [IsScalarTower k A S]

/-- `(a - μ) ⊗ id` acts on `S ⊗[k] X` as `a - μ` for the action of `A` on the left factor. -/
theorem rTensor_lsmul_sub_smul_apply (X : Type*) [AddCommGroup X] [Module k X] (a : A)
    (μ : k) (t : S ⊗[k] X) :
    (Algebra.lsmul k k S a - μ • 1).rTensor X t = a • t - μ • t := by
  induction t using TensorProduct.inductionOn with
  | tmul s x => simp [smul_tmul']
  | add t u ht hu => rw [map_add, ht, hu, smul_add, smul_add]; abel

end TauCeti
