/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Algebra.Module.GradedModule.Quotient
import TauCeti.Algebra.Module.GradedModule.Finite

/-!
# Integer-graded modules over a polynomial ring

Let `A` be a commutative semiring and `M` a module over the polynomial ring `A[X_σ]`, with an
integer grading `ℳ : ℤ → Submodule A M` by `A`-submodules on which a homogeneous polynomial of
degree `i` raises degrees by `i`. This is a graded module over the standard graded polynomial
ring; when finitely generated, its generators may sit in negative degrees.

This file provides polynomial-ring specializations used in the proof of the Hilbert–Serre theorem:
* every sufficiently high graded piece generates the subsequent tail over `A[X_σ]`
  (`TauCeti.MvPolynomial.exists_degree_ge_le_span_piece`), using the general graded-module
  finiteness results in `TauCeti.Algebra.Module.GradedModule.Finite`;
* multiplication by a variable is homogeneous of degree one
  (`TauCeti.MvPolynomial.isHomogeneous_lsmul_X`), and the gradings on the kernel and quotient of a
  homogeneous map remain compatible with `A[X_σ]`.

## Main results

* `TauCeti.MvPolynomial.exists_degree_ge_le_span_piece`: for a finitely generated `ℤ`-graded
  `MvPolynomial σ A`-module, every sufficiently high graded piece generates the subsequent tail.
* `TauCeti.MvPolynomial.isHomogeneous_lsmul_X`: multiplication by a variable has degree one.
* `TauCeti.MvPolynomial.smul_mem_ker_piece`, `TauCeti.MvPolynomial.smul_mem_quotient_piece`: the
  gradings of the kernel of a homogeneous map and of the quotient by a homogeneous submodule are
  again compatible with the grading of the polynomial ring.

## References

* The Stacks Project, Commutative Algebra, Section 10.58, Lemmas 10.58.5 and 10.58.6.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 11, proof of
  Theorem 11.1.
-/

public section

open DirectSum MvPolynomial

namespace TauCeti.MvPolynomial

section Pieces

variable {σ A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
  [Module (MvPolynomial σ A) M] {ℳ : ℤ → Submodule A M} [Decomposition ℳ]

/-- For a finitely generated `ℤ`-graded `MvPolynomial σ A`-module, there is `N₀` such that for
every `N₁ ≥ N₀`, each piece `ℳ d` with `d ≥ N₁` lies in the `MvPolynomial σ A`-span of `ℳ N₁`. -/
theorem exists_degree_ge_le_span_piece [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (hℳ : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) :
    ∃ N₀ : ℤ, ∀ N₁ ≥ N₀, ∀ d ≥ N₁,
      ℳ d ≤ (Submodule.span (MvPolynomial σ A) (ℳ N₁ : Set M)).restrictScalars A := by
  classical
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := A)
  obtain ⟨G, hGmem, hGspan⟩ := GradedModule.exists_finset_homogeneous_span (B := MvPolynomial σ A) ℳ
  let N₀ : ℤ := if h : G.Nonempty then (G.image Prod.fst).max' (h.image _) else 0
  refine ⟨N₀, fun N₁ hN₁ d hd m hm ↦ ?_⟩
  obtain ⟨c, rfl⟩ := GradedModule.exists_eq_sum_filter_decompose_smul
    (homogeneousSubmodule σ A) ℳ hℳ hGmem hm (hGspan ▸ Submodule.mem_top)
  refine Submodule.sum_mem _ fun p _ ↦ ?_
  have hp_le : p.val.1 ≤ N₁ := le_trans (by
    have hne : G.Nonempty := ⟨p.val, p.property⟩
    simp only [N₀, hne, ↓reduceDIte]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩)) hN₁
  set q := decompose (homogeneousSubmodule σ A) (c p) (d - p.val.1).toNat
  have hdeg : (d - p.val.1).toNat = (d - N₁).toNat + (N₁ - p.val.1).toNat := by omega
  have hq : (q : MvPolynomial σ A) ∈
      homogeneousSubmodule σ A (d - N₁).toNat *
        homogeneousSubmodule σ A (N₁ - p.val.1).toNat := by
    have hpow1 : homogeneousSubmodule σ A (d - N₁).toNat =
        homogeneousSubmodule σ A 1 ^ (d - N₁).toNat :=
      (homogeneousSubmodule_one_pow A _).symm
    have hpow2 : homogeneousSubmodule σ A (N₁ - p.val.1).toNat =
        homogeneousSubmodule σ A 1 ^ (N₁ - p.val.1).toNat :=
      (homogeneousSubmodule_one_pow A _).symm
    rw [hpow1, hpow2, ← pow_add, homogeneousSubmodule_one_pow, ← hdeg]
    exact q.property
  refine Submodule.mul_induction_on hq (fun r₁ _ r₂ hr₂ ↦ ?_) (fun u v hu hv ↦ by
    rw [add_smul]; exact add_mem hu hv)
  rw [mul_smul]
  have hr₂m : r₂ • p.val.2 ∈ ℳ N₁ := by
    have h1 := hℳ (N₁ - p.val.1).toNat p.val.1 r₂ hr₂ p.val.2 (hGmem p.val p.property)
    rwa [Int.toNat_of_nonneg (sub_nonneg.mpr hp_le), add_sub_cancel] at h1
  exact Submodule.smul_mem _ r₁ (Submodule.subset_span hr₂m)

end Pieces

section Ker

variable {σ A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
  [Module (MvPolynomial σ A) M] (G : InternalGrading A M ℤ)

/-- Multiplication by a variable is homogeneous of degree one. -/
theorem isHomogeneous_lsmul_X
    (hG : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ homogeneousSubmodule σ A i → ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i)) (i : σ) :
    LinearMap.IsHomogeneous (LinearMap.lsmul (MvPolynomial σ A) M (X i)) G.piece G.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
    simpa using hG 1 p (X i) ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X A i)) x hx

variable [IsScalarTower A (MvPolynomial σ A) M]

/-- The kernel of a homogeneous map is again graded compatibly with the polynomial ring. -/
theorem smul_mem_ker_piece
    (hG : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ homogeneousSubmodule σ A i → ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i))
    {N : Type*} [AddCommMonoid N] [Module A N] [Module (MvPolynomial σ A) N]
    {H : InternalGrading A N ℤ} {f : M →ₗ[MvPolynomial σ A] N} {r : ℤ}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece r)
    (i : ℕ) (j : ℤ) {p : MvPolynomial σ A} (hp : p ∈ homogeneousSubmodule σ A i)
    (z : LinearMap.ker f) (hz : z ∈ (G.ker hf).piece j) : p • z ∈ (G.ker hf).piece (j + i) :=
  (G.mem_ker_piece hf).2 (hG i j p hp _ ((G.mem_ker_piece hf).1 hz))

end Ker

section Quotient

variable {σ A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M] (G : InternalGrading A M ℤ)

/-- The quotient by a homogeneous submodule is again graded compatibly with the polynomial ring. -/
theorem smul_mem_quotient_piece
    (hG : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ homogeneousSubmodule σ A i → ∀ m ∈ G.piece j, p • m ∈ G.piece (j + i))
    (U : Submodule (MvPolynomial σ A) M) (hU : SetLike.IsHomogeneous G.piece U)
    (i : ℕ) (j : ℤ) {p : MvPolynomial σ A} (hp : p ∈ homogeneousSubmodule σ A i)
    (y : M ⧸ U) (hy : y ∈ (G.quotient U hU).piece j) : p • y ∈ (G.quotient U hU).piece (j + i) := by
  obtain ⟨x, hx, rfl⟩ := (G.mem_quotient_piece_iff _ _).mp hy
  rw [← Submodule.Quotient.mk_smul]
  exact G.mk_mem_quotient_piece _ _ (hG i j p hp x hx)

end Quotient

end TauCeti.MvPolynomial
