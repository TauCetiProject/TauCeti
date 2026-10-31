/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.LinearAlgebra.TensorProduct.Kernel
import TauCeti.LinearAlgebra.Submodule.Primitive
import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# Kernels that commute with every base change over a principal ideal domain

Let `R` be a principal ideal domain and `f : M →ₗ[R] N` a linear map into a torsion-free
`R`-module. Extending scalars to an `R`-algebra `A` always gives the containment
`(ker f).baseChange A ≤ ker (f.baseChange A)`. This file shows that the containment is an equality
for **every** `A` as soon as it is one for the residue fields `A = R ⧸ p` of the maximal ideals
`p` of `R`; that is, formation of `ker f` commutes with arbitrary base change once it commutes with
reduction modulo every maximal ideal.

Both conditions are equivalent to the torsion-freeness of the cokernel `N ⧸ range f`
(`LinearMap.isTorsionFree_quotient_range_iff_forall_isMaximal`); over a principal ideal domain a
torsion-free module is flat, so the equality for every `A` is then
`LinearMap.ker_baseChange_of_flat_quotient_range`.

A typical application is to the invariant ring of a finite group `G` acting on a flat algebra `B`
over `R`: it is the kernel of `b ↦ (g • b - b)_g`, so formation of `B^G` commutes with every base
change exactly when, for every maximal ideal `p`, every invariant of `B ⧸ p B` lifts to an
invariant of `B`.

## Main results

* `LinearMap.isTorsionFree_quotient_range_iff_forall_isMaximal`: the cokernel of `f` is
  torsion-free if and only if, for every maximal ideal `p`, every element of the kernel of
  `f.baseChange (R ⧸ p)` comes from `ker f`.
* `LinearMap.ker_baseChange_of_forall_isMaximal`: under that condition at every maximal ideal,
  `ker (f.baseChange A) = (ker f).baseChange A` for every `R`-algebra `A`.

## Implementation notes

Reduction modulo a prime element `π` detects `π`-torsion in the cokernel: if `π • n = f m`, then
`1 ⊗ m` lies in the kernel of `f.baseChange (R ⧸ (π))`, and writing it as the image of an element
of `(R ⧸ (π)) ⊗ ker f` shows `m ∈ ker f + π • M`, whence `n ∈ range f` because `N` is
torsion-free. Factoring an arbitrary nonzero scalar into primes handles the remaining torsion.
-/

public section

open TensorProduct

namespace LinearMap

variable {R M N : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)

omit [IsPrincipalIdealRing R] in
/-- Reduction modulo a prime element `π` detects `π`-torsion in the cokernel of `f`: if every
element of the kernel of `f.baseChange (R ⧸ (π))` comes from `ker f` and `N` is torsion-free, then
`π • n ∈ range f` implies `n ∈ range f`. -/
private theorem mem_range_of_prime_smul_mem_range [Module.IsTorsionFree R N] {π : R}
    (hπ : Prime π)
    (h : ker (f.baseChange (R ⧸ Ideal.span {π})) ≤ (ker f).baseChange (R ⧸ Ideal.span {π}))
    {n : N} (hn : π • n ∈ range f) : n ∈ range f := by
  set p := Ideal.span {π}
  obtain ⟨m, hm⟩ := hn
  -- `1 ⊗ m` lies in the kernel of `f` reduced modulo `π`.
  have h₁ : (1 : R ⧸ p) ⊗ₜ[R] m ∈ ker (f.baseChange (R ⧸ p)) := by
    have hπp : Ideal.Quotient.mk p π = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π)
    rw [mem_ker, baseChange_tmul, hm, ← smul_tmul, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, hπp, zero_mul, zero_tmul]
  -- Hence `1 ⊗ m = 1 ⊗ k` for some `k ∈ ker f`, that is, `k - m = π • m'` for some `m'`.
  obtain ⟨x, hx⟩ := h h₁
  obtain ⟨k, rfl⟩ := exists_one_tmul_eq p x
  rw [baseChange_tmul, ← sub_eq_zero, ← tmul_sub, one_tmul_eq_zero_iff_exists_smul_eq] at hx
  obtain ⟨m', hm'⟩ := hx
  -- So `π • n = f m = π • f (-m')`, and `n = f (-m')` as `N` is torsion-free.
  refine ⟨-m', smul_right_injective N hπ.ne_zero ?_⟩
  simp only [map_neg, smul_neg, ← map_smul, hm', map_sub, Submodule.subtype_apply, mem_ker.1 k.2,
    zero_sub, neg_neg, hm]

/-- Over a principal ideal domain, for a linear map `f : M →ₗ[R] N` into a torsion-free module,
**the cokernel `N ⧸ range f` is torsion-free if and only if, for every maximal ideal `p`, every
element of the kernel of `f.baseChange (R ⧸ p)` comes from `ker f`**. The reverse containment
always holds, so the condition says that formation of `ker f` commutes with reduction modulo
every maximal ideal. -/
theorem isTorsionFree_quotient_range_iff_forall_isMaximal [Module.IsTorsionFree R N] :
    Module.IsTorsionFree R (N ⧸ range f) ↔
      ∀ p : Ideal R, p.IsMaximal → ker (f.baseChange (R ⧸ p)) ≤ (ker f).baseChange (R ⧸ p) := by
  refine ⟨fun _ p _ ↦ (ker_baseChange_of_flat_quotient_range _ f).le, fun h ↦ ?_⟩
  -- Factor a nonzero scalar into primes and apply the prime case to each factor.
  refine (range f).isTorsionFree_quotient_of_smul_mem fun d n hd hn ↦ ?_
  induction d using UniqueFactorizationMonoid.induction_on_prime generalizing n with
  | h₁ => exact absurd rfl hd
  | h₂ u hu =>
    obtain ⟨u, rfl⟩ := hu
    simpa [smul_smul] using Submodule.smul_mem _ (↑u⁻¹ : R) hn
  | h₃ a π ha hπ ih =>
    rw [mul_smul] at hn
    exact ih _ ha (mem_range_of_prime_smul_mem_range f hπ
      (h _ (PrincipalIdealRing.isMaximal_of_irreducible hπ.irreducible)) hn)

/-- Over a principal ideal domain, for a linear map `f : M →ₗ[R] N` into a torsion-free module,
**if formation of `ker f` commutes with reduction modulo every maximal ideal, then it commutes with
every base change**: `ker (f.baseChange A) = (ker f).baseChange A` for every `R`-algebra `A`. -/
theorem ker_baseChange_of_forall_isMaximal [Module.IsTorsionFree R N]
    (h : ∀ p : Ideal R, p.IsMaximal → ker (f.baseChange (R ⧸ p)) ≤ (ker f).baseChange (R ⧸ p))
    (A : Type*) [Ring A] [Algebra R A] :
    ker (f.baseChange A) = (ker f).baseChange A :=
  have := (isTorsionFree_quotient_range_iff_forall_isMaximal f).2 h
  ker_baseChange_of_flat_quotient_range A f

end LinearMap
