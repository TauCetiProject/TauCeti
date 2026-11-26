/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.RingTheory.Norm.Units
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.LinearAlgebra.Trace.Pi
import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# Norms and traces of finite products

This file records the determinant, norm, and trace calculations for finite dependent products.
`TauCeti.Algebra.normUnits_eq_finprod_of_algEquiv` transports the unit norm to a finite product;
`TauCeti.Algebra.mem_range_normUnits_iff_of_algEquiv` characterizes its range;
`AlgEquiv.trace_symm_single_mul` computes the trace pairing of an element supported in a single
component under an algebra isomorphism to a finite product; and `AlgEquiv.sum_trace_mul_smul_eq`
transports finite trace-dual expansions through a base-change isomorphism to a finite product.
The scalar-extension identities used by the number-field local-global development live in
`TauCeti.RingTheory.NormTrace.BaseChange`.
-/

public section

namespace TauCeti

open scoped BigOperators

universe u v

variable {K : Type u} [CommRing K]

variable {ι : Type v} [Fintype ι]

open Module

section Norm

variable {L : ι → Type*} [∀ i, Ring (L i)] [∀ i, Algebra K (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]

/-- The norm of an element of a finite dependent product is the product of its component norms. -/
@[simp]
theorem Algebra.norm_pi (x : ∀ i, L i) :
    Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  rw [Algebra.norm_apply]
  have h : Algebra.lmul K (∀ i, L i) x = LinearMap.piMap fun i ↦ Algebra.lmul K (L i) (x i) := by
    ext y i
    simp [Algebra.lmul]
  simp_rw [h, LinearMap.det_piMap, Algebra.norm_apply]

end Norm

section NormUnits

variable {ι : Type*} [Finite ι] {S : Type*} [Ring S] [Algebra K S]
  {T : ι → Type*} [∀ i, Ring (T i)] [∀ i, Algebra K (T i)]
  [∀ i, Module.Free K (T i)] [∀ i, Module.Finite K (T i)]

/-- Transporting a norm on units to a finite product gives the product of the component norms. -/
theorem Algebra.normUnits_eq_finprod_of_algEquiv (e : S ≃ₐ[K] ∀ i, T i) (u : Sˣ) :
    Algebra.normUnits K u =
      ∏ᶠ i, Algebra.normUnits K (MulEquiv.piUnits (Units.map e.toMonoidHom u) i) := by
  let := Fintype.ofFinite ι
  apply Units.ext
  rw [Algebra.coe_normUnits, ← Algebra.norm_eq_of_algEquiv e,
    Algebra.norm_pi, finprod_eq_prod_of_fintype]
  simp

/-- A unit lies in the norm range of an algebra equivalent to a finite product exactly when it
is a product of norms of units of the factors. -/
theorem Algebra.mem_range_normUnits_iff_of_algEquiv (e : S ≃ₐ[K] ∀ i, T i) (a : Kˣ) :
    a ∈ (Algebra.normUnits K (S := S)).range ↔
      ∃ u : ∀ i, (T i)ˣ, (∏ᶠ i, Algebra.normUnits K (u i)) = a := by
  let eu := (Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨eu u, (Algebra.normUnits_eq_finprod_of_algEquiv e u).symm⟩
  · rintro ⟨u, hu⟩
    refine ⟨eu.symm u, ?_⟩
    rw [Algebra.normUnits_eq_finprod_of_algEquiv e]
    exact (congrArg (fun z ↦ ∏ᶠ i, Algebra.normUnits K (z i))
      (eu.apply_symm_apply u)).trans hu

end NormUnits

section Trace

variable {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]

/-- The trace of an element of a finite dependent product is the sum of its component traces. -/
@[simp]
theorem Algebra.trace_pi (x : ∀ i, L i) :
    Algebra.trace K (∀ i, L i) x = ∑ i, Algebra.trace K (L i) (x i) := by
  rw [Algebra.trace_apply]
  have h : Algebra.lmul K (∀ i, L i) x = LinearMap.piMap fun i ↦ Algebra.lmul K (L i) (x i) := by
    ext y i
    simp [Algebra.lmul]
  simp_rw [h, LinearMap.trace_piMap, Algebra.trace_apply]

end Trace

end TauCeti

namespace AlgEquiv

section TraceSingle

variable {K : Type*} [CommRing K]
  {ι : Type*} [Finite ι] [DecidableEq ι] {S : Type*} [CommRing S] [Algebra K S]
  {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]

/-- Under an algebra isomorphism `e : S ≃ₐ[K] ∀ j, L j` to a finite product, the trace pairing of
an element supported in a single component `i` with any `s : S` reduces to the trace pairing in
`L i`. -/
theorem trace_symm_single_mul (e : S ≃ₐ[K] ∀ j, L j) (i : ι) (z : L i)
    (s : S) :
    Algebra.trace K S (e.symm (Pi.single i z) * s) = Algebra.trace K (L i) (z * e s i) := by
  let := Fintype.ofFinite ι
  rw [← Algebra.trace_eq_of_algEquiv e, map_mul, AlgEquiv.apply_symm_apply,
    TauCeti.Algebra.trace_pi, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

end TraceSingle

section TraceDualExpansion

open scoped TensorProduct

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Module.Free K B]
  {ι : Type*} [Finite ι] {L : ι → Type*}
  [∀ i, CommRing (L i)] [∀ i, Algebra A (L i)]
  [∀ i, Module.Free A (L i)] [∀ i, Module.Finite A (L i)]

/-- **Trace-dual expansions pass through a finite-product decomposition after base change.** If
`e : A ⊗[K] B ≃ₐ[A] ∀ i, L i` is an `A`-algebra isomorphism to a finite product, then any finite
`K`-linear trace-dual expansion on `B` holds in every factor `L i`. -/
theorem sum_trace_mul_smul_eq
    (e : A ⊗[K] B ≃ₐ[A] ∀ i, L i) {J : Type*} [Fintype J] (b y : J → B)
    (h : ∀ x : B, ∑ j, Algebra.trace K B (x * b j) • y j = x)
    (i : ι) (z : L i) :
    ∑ j, Algebra.trace A (L i) (z * e (1 ⊗ₜ[K] b j) i) • e (1 ⊗ₜ[K] y j) i = z := by
  classical
  -- Extend the `K`-linear expansion to `A ⊗[K] B`, evaluate at `e.symm (Pi.single i z)`,
  -- and read off the `i`-th component.
  have h' := congrArg (fun ξ ↦ e ξ i)
    (TauCeti.Algebra.sum_trace_mul_smul_tmul_eq (A := A) b y h (e.symm (Pi.single i z)))
  simp only [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, e.trace_symm_single_mul] at h'
  exact h'

end TraceDualExpansion

end AlgEquiv
