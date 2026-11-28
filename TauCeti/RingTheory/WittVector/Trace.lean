/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.RingTheory.WittVector.Truncated.Basic

import Mathlib.FieldTheory.Galois.Infinite
import TauCeti.RingTheory.WittVector.Ideal
import TauCeti.RingTheory.WittVector.Units

/-!
# Galois traces of Witt vectors

For a finite Galois extension `L/K`, the sum of the conjugates of a Witt vector over `L`
descends uniquely to a Witt vector over `K`. This trace is surjective in characteristic `p`,
including when `K` is imperfect and when `p` divides the extension degree. It commutes with
every finite truncation. All sums use Witt addition, rather than coordinatewise addition.

Trace surjectivity is one of the exactness assertions in additive Hilbert 90 for Witt vectors.
It follows by lifting an element of field trace one: its Witt trace has zeroth coordinate one,
so is a unit, and multiplication by its inverse normalizes the lift.

## References

* M. Kosters and D. Wan, *On the arithmetic of ℤ_p-extensions*, Proposition 3.1.
-/

public section

noncomputable section

namespace WittVector

variable {p : ℕ} [Fact p.Prime]
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] in
/-- A Witt vector over a Galois extension comes from the base field exactly when
every Galois automorphism fixes it. -/
theorem mem_range_map_algebraMap_iff (x : WittVector p L) :
    x ∈ Set.range (map (algebraMap K L) : WittVector p K → WittVector p L) ↔
      ∀ σ : L ≃ₐ[K] L, map (σ : L →+* L) x = x := by
  simp only [mem_range_map_iff, InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K),
    WittVector.ext_iff, map_coeff]
  exact forall_comm

omit [IsGalois K L] in
private theorem map_sum_conjugates (σ : L ≃ₐ[K] L) (x : WittVector p L) :
    map (σ : L →+* L) (∑ τ : L ≃ₐ[K] L, map (τ : L →+* L) x) =
      ∑ τ : L ≃ₐ[K] L, map (τ : L →+* L) x := by
  rw [map_sum]
  apply Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ)
  intro τ
  ext i
  simp [AlgEquiv.mul_apply]

private def galoisTraceFun (x : WittVector p L) : WittVector p K :=
  Classical.choose ((mem_range_map_algebraMap_iff K L _).mpr
    (fun σ ↦ map_sum_conjugates K L σ x))

private theorem map_galoisTraceFun (x : WittVector p L) :
    map (algebraMap K L) (galoisTraceFun K L x) = ∑ σ : L ≃ₐ[K] L, map (σ : L →+* L) x :=
  Classical.choose_spec ((mem_range_map_algebraMap_iff K L _).mpr
    (fun σ ↦ map_sum_conjugates K L σ x))

/-- The Witt trace of a finite Galois extension, the sum of all conjugates descended to
the base field. -/
def galoisTrace : WittVector p L →+ WittVector p K where
  toFun := galoisTraceFun K L
  map_zero' := by
    apply map_injective (algebraMap K L) (algebraMap K L).injective
    simp only [map_galoisTraceFun, map_zero, Finset.sum_const_zero]
  map_add' x y := by
    apply map_injective (algebraMap K L) (algebraMap K L).injective
    simp only [map_add, map_galoisTraceFun, Finset.sum_add_distrib]

/-- After inclusion into the extension, the Witt trace is the sum of the conjugates. -/
theorem map_galoisTrace (x : WittVector p L) :
    map (algebraMap K L) (galoisTrace K L x) = ∑ σ : L ≃ₐ[K] L, map (σ : L →+* L) x :=
  map_galoisTraceFun K L x

/-- The zeroth coordinate of the Witt trace is the ordinary field trace. -/
@[simp]
theorem coeff_zero_galoisTrace (x : WittVector p L) :
    (galoisTrace K L x).coeff 0 = Algebra.trace K L (x.coeff 0) := by
  apply (algebraMap K L).injective
  have h := congrArg (constantCoeff (p := p)) (map_galoisTrace K L x)
  simpa [constantCoeff_apply, trace_eq_sum_automorphisms] using h

/-- The projection formula for the Witt trace. -/
theorem galoisTrace_map_mul (a : WittVector p K) (x : WittVector p L) :
    galoisTrace K L (map (algebraMap K L) a * x) = a * galoisTrace K L x := by
  apply map_injective (algebraMap K L) (algebraMap K L).injective
  rw [map_galoisTrace, map_mul, map_galoisTrace]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_mul]
  congr 1
  ext i
  simp

/-- Galois automorphisms preserve the Witt trace. -/
@[simp]
theorem galoisTrace_map (σ : L ≃ₐ[K] L) (x : WittVector p L) :
    galoisTrace K L (map (σ : L →+* L) x) = galoisTrace K L x := by
  apply map_injective (algebraMap K L) (algebraMap K L).injective
  rw [map_galoisTrace, map_galoisTrace]
  apply Fintype.sum_bijective (· * σ) (Group.mulRight_bijective σ)
  intro τ
  ext i
  simp [AlgEquiv.mul_apply]

/-- The Witt trace is onto for a finite Galois extension in characteristic `p`.
No perfectness or prime-to-`p` degree hypothesis is needed. -/
theorem galoisTrace_surjective [CharP L p] :
    Function.Surjective (galoisTrace (p := p) K L) := by
  have : CharP K p := (algebraMap K L).charP (algebraMap K L).injective p
  obtain ⟨a, ha⟩ := Algebra.trace_surjective K L 1
  let t := galoisTrace (p := p) K L (teichmuller p a)
  have ht : t.coeff 0 = 1 := by
    rw [coeff_zero_galoisTrace, teichmuller_coeff_zero]
    exact ha
  obtain ⟨u, hu⟩ := isUnit_of_coeff_zero_ne_zero t (ht ▸ one_ne_zero)
  intro y
  refine ⟨map (algebraMap K L) (y * (↑u⁻¹ : WittVector p K)) * teichmuller p a, ?_⟩
  rw [galoisTrace_map_mul]
  dsimp only [t] at hu
  rw [← hu]
  simp [mul_assoc]

end WittVector

namespace TruncatedWittVector

variable {p : ℕ} [Fact p.Prime]
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] in
/-- A truncated Witt vector over a Galois extension descends to the base field exactly when
every Galois automorphism fixes it. This includes length zero. -/
theorem mem_range_map_algebraMap_iff (n : ℕ) (x : TruncatedWittVector p n L) :
    x ∈ Set.range (map n (algebraMap K L) : TruncatedWittVector p n K → _) ↔
      ∀ σ : L ≃ₐ[K] L, map n (σ : L →+* L) x = x := by
  constructor
  · rintro ⟨y, rfl⟩ σ
    ext i
    simp
  · intro hx
    have hcoeff (i : Fin n) : x.coeff i ∈ Set.range (algebraMap K L) := by
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      simpa using congrArg (fun y ↦ y.coeff i) (hx σ)
    choose y hy using hcoeff
    exact ⟨mk p y, ext fun i ↦ by simpa only [map_coeff, coeff_mk] using hy i⟩

private theorem map_truncate_galoisTrace_out (n : ℕ) (x : TruncatedWittVector p n L) :
    map n (algebraMap K L) (WittVector.truncate n (WittVector.galoisTrace K L x.out)) =
      ∑ σ : L ≃ₐ[K] L, map n (σ : L →+* L) x := by
  rw [map_wittVector_truncate, WittVector.map_galoisTrace, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← map_wittVector_truncate]
  congr 1
  ext i
  rw [WittVector.coeff_truncate, coeff_out]

/-- The Galois trace on length-`n` Witt vectors. -/
def galoisTrace (n : ℕ) : TruncatedWittVector p n L →+ TruncatedWittVector p n K where
  toFun x := WittVector.truncate n (WittVector.galoisTrace K L x.out)
  map_zero' := by
    apply map_injective n (algebraMap K L) (algebraMap K L).injective
    rw [map_truncate_galoisTrace_out]
    simp
  map_add' x y := by
    apply map_injective n (algebraMap K L) (algebraMap K L).injective
    simp only [map_add, map_truncate_galoisTrace_out, Finset.sum_add_distrib]

/-- The truncated Witt trace is the sum of conjugates, viewed in the extension. -/
theorem map_galoisTrace (n : ℕ) (x : TruncatedWittVector p n L) :
    map n (algebraMap K L) (galoisTrace K L n x) =
      ∑ σ : L ≃ₐ[K] L, map n (σ : L →+* L) x :=
  map_truncate_galoisTrace_out K L n x

/-- The trace commutes with truncation from the full Witt ring. -/
@[simp]
theorem galoisTrace_wittVector_truncate (n : ℕ) (x : WittVector p L) :
    galoisTrace K L n (WittVector.truncate n x) =
      WittVector.truncate n (WittVector.galoisTrace K L x) := by
  apply map_injective n (algebraMap K L) (algebraMap K L).injective
  rw [map_galoisTrace, map_wittVector_truncate, WittVector.map_galoisTrace, map_sum]
  simp only [map_wittVector_truncate]

/-- The trace commutes with every projection between finite Witt lengths. -/
@[simp]
theorem galoisTrace_truncate {m n : ℕ} (hmn : m ≤ n) (x : TruncatedWittVector p n L) :
    galoisTrace K L m (truncate hmn x) = truncate hmn (galoisTrace K L n x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n L x
  simp only [truncate_wittVector_truncate, galoisTrace_wittVector_truncate]

/-- The zeroth coordinate of the truncated Witt trace is the field trace. -/
@[simp]
theorem constantCoeff_galoisTrace (n : ℕ) [NeZero n] (x : TruncatedWittVector p n L) :
    constantCoeff (galoisTrace K L n x) = Algebra.trace K L (constantCoeff x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n L x
  simp only [galoisTrace_wittVector_truncate, constantCoeff_wittVector_truncate,
    WittVector.coeff_zero_galoisTrace]

/-- The projection formula for the truncated Witt trace. -/
theorem galoisTrace_map_mul (n : ℕ) (a : TruncatedWittVector p n K)
    (x : TruncatedWittVector p n L) :
    galoisTrace K L n (map n (algebraMap K L) a * x) = a * galoisTrace K L n x := by
  obtain ⟨a, rfl⟩ := WittVector.truncate_surjective p n K a
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n L x
  simp only [map_wittVector_truncate, ← map_mul, galoisTrace_wittVector_truncate,
    WittVector.galoisTrace_map_mul]

/-- Galois automorphisms preserve the truncated Witt trace. -/
@[simp]
theorem galoisTrace_map (n : ℕ) (σ : L ≃ₐ[K] L) (x : TruncatedWittVector p n L) :
    galoisTrace K L n (map n (σ : L →+* L) x) = galoisTrace K L n x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n L x
  simp only [map_wittVector_truncate, galoisTrace_wittVector_truncate, WittVector.galoisTrace_map]

/-- The truncated Witt trace is onto in characteristic `p`, at every length. -/
theorem galoisTrace_surjective [CharP L p] (n : ℕ) :
    Function.Surjective (galoisTrace (p := p) K L n) := by
  intro y
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n K y
  obtain ⟨x, hx⟩ := WittVector.galoisTrace_surjective K L y
  exact ⟨WittVector.truncate n x, by
    rw [galoisTrace_wittVector_truncate, hx]⟩

end TruncatedWittVector
