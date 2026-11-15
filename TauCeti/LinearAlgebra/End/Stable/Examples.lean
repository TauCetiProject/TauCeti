/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.LinearAlgebra.End.Stable.Constructions
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Counterexamples for infinite products and direct sums of stable endomorphisms

For a commutative ring `A` and `j : ℕ`, multiplication by `X` on the truncated polynomial module
`TruncPolyMod A j := A[X] ⧸ Ideal.span {X ^ (j + 1)}` is nilpotent of index `j + 1`, hence stable at
exponent `j + 1`. When `A` is nontrivial, no smaller power kills the `j`-th factor. Consequently:

* On the infinite product `∀ j : ℕ, TruncPolyMod A j`, the coordinatewise operator
  `LinearMap.piMap (mulXTruncPolyMod A)` has trivial stable range (`⨅ n, range (P ^ n) = ⊥`), yet
  when `A` is nontrivial no power of `P` vanishes (`∀ n, P ^ n ≠ 0`). Thus `P` is stable if and
  only if `Subsingleton A`, showing that `Module.End.IsStableAt.piMap` requires a uniform positive
  exponent across factors.
* On the infinite direct sum `⨁ j : ℕ, TruncPolyMod A j`, the summandwise operator
  `DirectSum.lmap (mulXTruncPolyMod A)` satisfies `⨆ n, ker (S ^ n) = ⊤` and
  `⨅ n, range (S ^ n) = ⊥` (so the eventual kernel and stable range are complementary), yet `S` is
  stable if and only if `Subsingleton A`, showing both that `Module.End.IsStableAt.lmap` requires a
  uniform positive exponent and that local nilpotence on `⨆ n, ker (S ^ n)` cannot replace genuine
  nilpotence in `Module.End.isStable_iff_isCompl_and_isNilpotent_and_bijective`.

## References

* D. Helm, *The Bernstein center of the category of smooth `W(k)[GL_n(F)]`-modules*,
  arXiv:1201.1874v3, Definition 11.9 and Lemma 11.10.
* J.-F. Dat, D. Helm, R. Kurinczuk, and G. Moss, *Finiteness for Hecke algebras of `p`-adic groups*,
  arXiv:2203.04929v2, Section 4.
-/

public section

open DirectSum Polynomial

namespace TauCeti

/-- The truncated polynomial `A`-module `A[X] ⧸ (X ^ (j + 1))` of nilpotency index `j + 1`. -/
abbrev TruncPolyMod (A : Type*) [CommRing A] (j : ℕ) : Type _ :=
  A[X] ⧸ Ideal.span ({X ^ (j + 1)} : Set A[X])

/-- Left multiplication by `X` as an `A`-linear endomorphism of `TruncPolyMod A j`. -/
noncomputable def mulXTruncPolyMod (A : Type*) [CommRing A] (j : ℕ) :
    Module.End A (TruncPolyMod A j) :=
  Algebra.lmul A (TruncPolyMod A j) (Ideal.Quotient.mk (Ideal.span ({X ^ (j + 1)} : Set A[X])) X)

section Factor

variable (A : Type*) [CommRing A]

theorem mulXTruncPolyMod_pow (j k : ℕ) :
    mulXTruncPolyMod A j ^ k =
      Algebra.lmul A (TruncPolyMod A j)
        (Ideal.Quotient.mk (Ideal.span ({X ^ (j + 1)} : Set A[X])) (X ^ k)) := by
  rw [mulXTruncPolyMod, ← map_pow, ← map_pow]

theorem mulXTruncPolyMod_pow_eq_zero_iff (j k : ℕ) :
    mulXTruncPolyMod A j ^ k = 0 ↔ X ^ k ∈ Ideal.span ({X ^ (j + 1)} : Set A[X]) := by
  rw [mulXTruncPolyMod_pow, map_eq_zero_iff _ Algebra.lmul_injective,
    Ideal.Quotient.eq_zero_iff_mem]

@[simp]
theorem mulXTruncPolyMod_pow_succ_eq_zero (j : ℕ) :
    mulXTruncPolyMod A j ^ (j + 1) = 0 :=
  (mulXTruncPolyMod_pow_eq_zero_iff A j (j + 1)).mpr (Ideal.mem_span_singleton_self _)

theorem mulXTruncPolyMod_pow_eq_zero_of_lt {j k : ℕ} (hjk : j < k) :
    mulXTruncPolyMod A j ^ k = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hjk)
  have hexp := pow_add (mulXTruncPolyMod A j) (j + 1) d
  rw [hexp, mulXTruncPolyMod_pow_succ_eq_zero, zero_mul]

/-- Multiplication by `X` on `TruncPolyMod A j` is stable at exponent `j + 1`. -/
theorem isStableAt_mulXTruncPolyMod (j : ℕ) :
    (mulXTruncPolyMod A j).IsStableAt (j + 1) :=
  Module.End.IsStableAt.of_pow_eq_zero (Nat.succ_le_succ (Nat.zero_le j))
    (mulXTruncPolyMod_pow_succ_eq_zero A j)

/-- Multiplication by `X` on `TruncPolyMod A j` is stable for every `j`. -/
theorem isStable_mulXTruncPolyMod (j : ℕ) :
    (mulXTruncPolyMod A j).IsStable :=
  (isStableAt_mulXTruncPolyMod A j).isStable

/-- Over a nontrivial commutative ring `A`, the `j`-th power of multiplication by `X` on
`TruncPolyMod A j` is nonzero. -/
theorem mulXTruncPolyMod_pow_self_ne_zero [Nontrivial A] (j : ℕ) :
    mulXTruncPolyMod A j ^ j ≠ 0 := by
  intro h0
  rw [mulXTruncPolyMod_pow_eq_zero_iff, Ideal.mem_span_singleton] at h0
  obtain ⟨q, hq⟩ := h0
  have hcoeff := congrArg (fun p : A[X] ↦ p.coeff j) hq
  simp [Polynomial.coeff_X_pow_mul', Nat.not_succ_le_self j] at hcoeff

end Factor

section ProductAndDirectSum

variable (A : Type*) [CommRing A]

/-- On `∀ j : ℕ, TruncPolyMod A j`, the intersection of ranges of powers of
`LinearMap.piMap (mulXTruncPolyMod A)` is trivial. -/
theorem iInf_range_pow_piMap_mulXTruncPolyMod :
    (⨅ n, LinearMap.range
      ((LinearMap.piMap (mulXTruncPolyMod A) : Module.End A (∀ j, TruncPolyMod A j)) ^ n)) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ funext fun j ↦ ?_
  obtain ⟨y, hy⟩ := (Submodule.mem_iInf _).mp hx (j + 1)
  have hyj := congrFun hy j
  rw [Module.End.piMap_pow, LinearMap.coe_piMap, Pi.map_apply,
    mulXTruncPolyMod_pow_succ_eq_zero, LinearMap.zero_apply] at hyj
  exact hyj.symm

/-- Over a nontrivial commutative ring `A`, no power of the product operator
`LinearMap.piMap (mulXTruncPolyMod A)` vanishes. -/
theorem piMap_mulXTruncPolyMod_pow_ne_zero [Nontrivial A] (n : ℕ) :
    (LinearMap.piMap (mulXTruncPolyMod A) : Module.End A (∀ j, TruncPolyMod A j)) ^ n ≠ 0 := by
  classical
  rw [Module.End.piMap_pow]
  intro h0
  refine mulXTruncPolyMod_pow_self_ne_zero A n (LinearMap.ext fun v ↦ ?_)
  have hv := congrFun (LinearMap.congr_fun h0 (Pi.single n v)) n
  rw [LinearMap.coe_piMap, Pi.map_apply, Pi.single_eq_same,
    LinearMap.zero_apply, Pi.zero_apply] at hv
  exact hv

/-- The coordinatewise operator `LinearMap.piMap (mulXTruncPolyMod A)` on
`∀ j : ℕ, TruncPolyMod A j` is stable if and only if `Subsingleton A`. -/
@[simp]
theorem isStable_piMap_mulXTruncPolyMod_iff :
    Module.End.IsStable (LinearMap.piMap (mulXTruncPolyMod A)) ↔ Subsingleton A := by
  refine ⟨fun h ↦ ?_, fun hA ↦ ?_⟩
  · rw [Module.End.isStable_def] at h
    obtain ⟨c, hc⟩ := h
    have hfactor : (mulXTruncPolyMod A c).IsStableAt c :=
      (Module.End.isStableAt_piMap_iff.mp hc).2 c
    have hker : LinearMap.ker (mulXTruncPolyMod A c ^ c) = ⊤ := by
      rw [← hfactor.ker_pow_succ_eq, mulXTruncPolyMod_pow_succ_eq_zero, LinearMap.ker_zero]
    by_contra hnot
    have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hnot
    exact mulXTruncPolyMod_pow_self_ne_zero A c (LinearMap.ker_eq_top.mp hker)
  · have h0 : (LinearMap.piMap (mulXTruncPolyMod A) :
        Module.End A (∀ j, TruncPolyMod A j)) = 0 := Subsingleton.elim _ _
    exact h0 ▸ Module.End.IsStable.zero

/-- On `⨁ j : ℕ, TruncPolyMod A j`, the increasing union of kernels of powers of
`DirectSum.lmap (mulXTruncPolyMod A)` is the entire direct sum. -/
theorem iSup_ker_pow_lmap_mulXTruncPolyMod :
    (⨆ n, LinearMap.ker
      ((DirectSum.lmap (mulXTruncPolyMod A) : Module.End A (⨁ j, TruncPolyMod A j)) ^ n)) = ⊤ := by
  classical
  refine eq_top_iff.mpr fun x _ ↦ ?_
  refine Submodule.mem_iSup_of_mem (x.support.sup fun j ↦ j + 1) ?_
  rw [LinearMap.mem_ker, Module.End.lmap_pow]
  refine DFinsupp.ext fun j ↦ ?_
  by_cases hj : j ∈ x.support
  · have hlt : j < x.support.sup fun k ↦ k + 1 :=
      Nat.lt_of_succ_le (Finset.le_sup (f := fun k ↦ k + 1) hj)
    rw [DirectSum.lmap_apply, mulXTruncPolyMod_pow_eq_zero_of_lt A hlt, LinearMap.zero_apply]
    rfl
  · have hxj : x j = 0 := DFinsupp.notMem_support_iff.mp hj
    rw [DirectSum.lmap_apply, hxj, map_zero]
    rfl

/-- On `⨁ j : ℕ, TruncPolyMod A j`, the intersection of ranges of powers of
`DirectSum.lmap (mulXTruncPolyMod A)` is trivial. -/
theorem iInf_range_pow_lmap_mulXTruncPolyMod :
    (⨅ n, LinearMap.range
      ((DirectSum.lmap (mulXTruncPolyMod A) : Module.End A (⨁ j, TruncPolyMod A j)) ^ n)) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ DFinsupp.ext fun j ↦ ?_
  obtain ⟨y, hy⟩ := (Submodule.mem_iInf _).mp hx (j + 1)
  have hyj := DFunLike.congr_fun hy j
  rw [Module.End.lmap_pow, DirectSum.lmap_apply,
    mulXTruncPolyMod_pow_succ_eq_zero, LinearMap.zero_apply] at hyj
  exact hyj.symm

/-- On `⨁ j : ℕ, TruncPolyMod A j`, the eventual kernel and stable range of
`DirectSum.lmap (mulXTruncPolyMod A)` are complementary submodules regardless of `A`. -/
theorem isCompl_iSup_ker_pow_iInf_range_pow_lmap_mulXTruncPolyMod :
    IsCompl
      (⨆ n, LinearMap.ker
        ((DirectSum.lmap (mulXTruncPolyMod A) : Module.End A (⨁ j, TruncPolyMod A j)) ^ n))
      (⨅ n, LinearMap.range
        ((DirectSum.lmap (mulXTruncPolyMod A) : Module.End A (⨁ j, TruncPolyMod A j)) ^ n)) := by
  rw [iSup_ker_pow_lmap_mulXTruncPolyMod, iInf_range_pow_lmap_mulXTruncPolyMod]
  exact isCompl_top_bot

/-- Despite having complementary eventual kernel and stable range, the direct-sum operator
`DirectSum.lmap (mulXTruncPolyMod A)` is stable if and only if `Subsingleton A`. -/
@[simp]
theorem isStable_lmap_mulXTruncPolyMod_iff :
    Module.End.IsStable (DirectSum.lmap (mulXTruncPolyMod A)) ↔ Subsingleton A := by
  refine ⟨fun h ↦ ?_, fun hA ↦ ?_⟩
  · rw [Module.End.isStable_def] at h
    obtain ⟨c, hc⟩ := h
    have hfactor : (mulXTruncPolyMod A c).IsStableAt c :=
      (Module.End.isStableAt_lmap_iff.mp hc).2 c
    have hker : LinearMap.ker (mulXTruncPolyMod A c ^ c) = ⊤ := by
      rw [← hfactor.ker_pow_succ_eq, mulXTruncPolyMod_pow_succ_eq_zero, LinearMap.ker_zero]
    by_contra hnot
    have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hnot
    exact mulXTruncPolyMod_pow_self_ne_zero A c (LinearMap.ker_eq_top.mp hker)
  · have : ∀ j, Subsingleton (TruncPolyMod A j) := fun _ ↦ inferInstance
    have h0 : (DirectSum.lmap (mulXTruncPolyMod A) :
        Module.End A (⨁ j, TruncPolyMod A j)) = 0 := Subsingleton.elim _ _
    exact h0 ▸ Module.End.IsStable.zero

end ProductAndDirectSum

end TauCeti

end
