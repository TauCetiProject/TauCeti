/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Localization.NormTrace
import TauCeti.LinearAlgebra.FreeModule.LengthQuotient

/-!
# The discriminant and the length of the complementary module

Let `A` be a principal ideal domain with fraction field `K`, let `B` be an `A`-algebra with a
finite basis `b`, and let `L` be the localization of `B` at the nonzero elements of `A`, a
finite separable extension of `K`. The trace Gram matrix `Tᵢⱼ = Tr_{B/A}(bᵢ bⱼ)` has
determinant the discriminant `Algebra.discr A b`. The complementary module
`C = Submodule.traceDual A K 1` has the trace-dual basis `b^∨` over `A`, and
`bⱼ = ∑ᵢ Tᵢⱼ • b^∨ᵢ`. Thus the inclusion of `B` into `C` has determinant `Algebra.discr A b`,
and the length of `C/B` over `A` is the order of vanishing of the discriminant:

  `length_A (C/B) = ord_A (discr A b)`.

Here `B` need not be integrally closed. When `A` is a discrete valuation ring and `B` is its
integral closure in `L` and a discrete valuation ring, the complementary-module length formula
`TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank` turns this into
`ord_A (discr A b) = d * f`, where `d` is the different exponent and `f` the full residue degree,
including its inseparable factor. Thus the discriminant, the residue degree and the different
exponent are related on the rings themselves, with no separability of residue fields and no
monogenic generator.

## Main results

* `TauCeti.length_traceDual_quotient_eq_ord_discr`: `length_A (C/B) = ord_A (discr A b)`.
* `TauCeti.ord_discr_eq_multiplicity_mul_finrank`: `ord_A (discr A b) = d * f` for an extension
  of discrete valuation rings.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §§2–3 (the discriminant, the complementary module
  and the different).
-/

public section

open Module Submodule

open scoped nonZeroDivisors

namespace TauCeti

section Order

variable {A B K L : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [CommRing B] [Field K] [Field L]
  [Algebra A B] [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K]
  [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L] [Algebra.IsSeparable K L]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsDomain A] [IsPrincipalIdealRing A] [Algebra.IsSeparable K L] in
/-- If `B` is finite free over `A` and `L` is its localization at the nonzero elements of `A`, then
`B` lies in its complementary module: traces from `L` to `K` of elements of `B` lie in `A`.
Unlike `Submodule.one_le_traceDual_one`, neither `A` nor `B` need be integrally closed. -/
theorem one_le_traceDual_one_of_free [Module.Free A B] [Module.Finite A B] :
    (1 : Submodule B L) ≤ Submodule.traceDual A K (1 : Submodule B L) := by
  intro y hy
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hy
  rw [Submodule.mem_traceDual]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hx
  rw [Algebra.traceForm_apply, ← map_mul, Algebra.trace_localization A A⁰]
  exact RingHom.mem_range_self _ _

/-- **The discriminant computes the length of the complementary module.** For an `A`-basis `b`
of `B` over a principal ideal domain `A`, the length over `A` of the complementary module modulo
`B` is the order of vanishing of the discriminant of `b`, the determinant of the trace Gram
matrix. -/
theorem length_traceDual_quotient_eq_ord_discr (b : Basis ι A B) :
    Module.length A ((Submodule.traceDual A K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype) =
      Ring.ord A (Algebra.discr A b) := by
  -- We write the inclusion `B → C` as an endomorphism `f` of `C` in the trace-dual basis, whose
  -- matrix is the trace Gram matrix, and apply `LinearMap.length_quotient_range_eq_ord_det`.
  have : Module.Free A B := .of_basis b
  have : Module.Finite A B := .of_basis b
  let bL : Basis ι K L := b.localizationLocalization K A⁰ L
  have : FiniteDimensional K L := .of_basis bL
  set C := Submodule.traceDual A K (1 : Submodule B L)
  -- `B` is the `A`-lattice spanned by `bL`, so `C` is spanned by the trace-dual basis.
  have hB : (1 : Submodule B L).restrictScalars A = span A (Set.range bL) := by
    rw [b.localizationLocalization_span K A⁰ L]
    ext x
    simp [Submodule.mem_one]
  have hC : C.restrictScalars A = span A (Set.range bL.traceDual) :=
    traceDual_span_of_basis A (1 : Submodule B L) bL hB
  let E : span A (Set.range bL.traceDual) ≃ₗ[A] C :=
    (LinearEquiv.ofEq _ _ hC.symm).trans ((C.restrictScalarsEquiv A).restrictScalars A)
  let bC : Basis ι A C := (bL.traceDual.restrictScalars A).map E
  -- Both `LinearEquiv.ofEq` and `Submodule.restrictScalarsEquiv` are the identity on elements.
  have hE (y : span A (Set.range bL.traceDual)) : (E y : L) = y := rfl
  have hbC (x : C) (i : ι) : algebraMap A K (bC.repr x i) = bL.traceDual.repr x i := by
    obtain ⟨y, rfl⟩ := E.surjective x
    simp [bC, hE]
  have hmem (y : B) : algebraMap B L y ∈ C :=
    one_le_traceDual_one_of_free (Submodule.mem_one.mpr ⟨y, rfl⟩)
  -- The inclusion of `B` into `C`, written in the basis `bC`.
  let f : C →ₗ[A] C := bC.constr A fun i ↦ ⟨algebraMap B L (b i), hmem (b i)⟩
  let N := (1 : Submodule B L).comap C.subtype
  have hrange : LinearMap.range f = N.restrictScalars A := by
    apply Submodule.map_injective_of_injective (f := C.subtype.restrictScalars A)
      Subtype.val_injective
    rw [Basis.constr_range, Submodule.map_span, ← Set.range_comp]
    have hv : (C.subtype.restrictScalars A ∘ fun i ↦ (⟨algebraMap B L (b i), hmem (b i)⟩ : C)) =
        bL := funext fun i ↦ by simp [bL]
    rw [hv, ← hB]
    ext x
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, Submodule.mem_comap,
      Submodule.subtype_apply, LinearMap.coe_restrictScalars, N]
    refine ⟨fun hx ↦ ?_, fun ⟨y, hy, hyx⟩ ↦ hyx ▸ hy⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hx
    exact ⟨⟨_, hmem z⟩, hx, rfl⟩
  -- In the basis `bC`, the matrix of `f` is the transposed trace Gram matrix.
  have hdet : f.det = Algebra.discr A b := by
    apply IsFractionRing.injective A K
    rw [← LinearMap.det_toMatrix bC, RingHom.map_det,
      ← Algebra.discr_localizationLocalization A A⁰ L b, Algebra.discr_def,
      ← Matrix.det_transpose (Algebra.traceMatrix K _)]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, f, hbC, bL, Basis.traceDual_repr_apply,
      Algebra.traceMatrix_apply]
  have hdisc : Algebra.discr A b ≠ 0 := fun h ↦ Algebra.discr_not_zero_of_basis K bL <| by
    rw [Algebra.discr_localizationLocalization A A⁰ L b, h, map_zero]
  have : Module.Free A C := .of_basis bC
  have : Module.Finite A C := .of_basis bC
  rw [← (Submodule.Quotient.restrictScalarsEquiv A N).length_eq, ← hrange,
    LinearMap.length_quotient_range_eq_ord_det (hdet ▸ hdisc), hdet]

end Order

section DiscreteValuationRing

variable {A B K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K] [Field L]
  [Algebra A B] [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
  [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [Module.IsTorsionFree A B]
  [IsLocalHom (algebraMap A B)] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (K L) in
include K L in
/-- **The discriminant is the different exponent times the full residue degree.** For an
`A`-basis `b` of an extension `B` of discrete valuation rings, with `B` the integral closure of `A`
in a finite separable extension `L` of the fraction field `K`, the valuation of the discriminant
of `b` is `d * f`, where `d` is the multiplicity of the maximal ideal of `B` in the different and
`f` is the residue degree, including its inseparable factor. -/
theorem ord_discr_eq_multiplicity_mul_finrank (b : Basis ι A B) :
    Ring.ord A (Algebra.discr A b) =
      (multiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) : ℕ∞) *
        Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  have : Module.Free A B := .of_basis b
  have : Module.Finite A B := .of_basis b
  have := IsIntegralClosure.isLocalization A K L B
  have : FiniteDimensional K L := .of_basis (b.localizationLocalization K A⁰ L)
  rw [← length_traceDual_quotient_eq_ord_discr (K := K) (L := L) b,
    length_traceDual_quotient_eq_multiplicity_mul_finrank]

end DiscreteValuationRing

end TauCeti
