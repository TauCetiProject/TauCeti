/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.FiniteNormal
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Regular.Free
import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# Flatness of finite normal local algebras in dimension two

A finite injective local algebra over a two-dimensional regular local ring is free, and hence
flat, if it is a normal local domain. This is the finite local case of miracle flatness.

The proof reduces modulo a regular parameter of the base. The quotient base is a discrete
valuation ring, and normality supplies a second parameter regular on the quotient module.
Consequently that quotient is torsion free and finite over a principal ideal domain, hence
free. Freeness lifts through the first regular parameter using
`Module.free_quotSMulTop_iff_free`.

## References

* The Stacks Project, Lemma 10.128.1 (00R4), miracle flatness. This file proves its finite
  normal local dimension-two case, rather than the general Cohen–Macaulay statement.
-/

public section

open IsLocalRing Ideal RingTheory.Sequence

namespace TauCeti.Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsRegularLocalRing A] [IsLocalRing B] [IsDomain B] [IsIntegrallyClosed B]
  [Module.Finite A B]

/-- A finite injective algebra over a two-dimensional regular local ring is flat if it is a
normal local domain. Locality of the algebra map follows from finiteness and injectivity. -/
theorem flat_of_normal_dim_two (hinj : Function.Injective (algebraMap A B))
    (hdim : ringKrullDim A = 2) : Module.Flat A B := by
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have : IsLocalHom (algebraMap A B) := inferInstance
  -- Cutting by a base parameter gives a one-dimensional regular local ring.
  obtain ⟨x, hxm, hx2, _⟩ :=
    TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes
      (R := A) (by rw [hdim]; decide)
  have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
  let Q := A ⧸ span {x}
  have : IsRegularLocalRing Q :=
    TauCeti.IsRegularLocalRing.quotient_span_singleton hxm hx2
  have : IsDiscreteValuationRing Q :=
    TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
      (TauCeti.ringKrullDim_quotient_span_singleton_eq_one hdim hxm
        (mem_nonZeroDivisors_of_ne_zero hx0))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective π
  have hxy : span {x, y} = maximalIdeal A := by
    apply span_insert_eq_of_quotient _ hxm {y}
    rw [Set.image_singleton, hy, ← hπ.maximalIdeal_eq,
      map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  -- Normality makes the lifted parameter pair regular on the algebra.
  have hreg := TauCeti.IsRegularLocalRing.isRegular_pair_of_finite_normal hinj hdim hxy
  have hxreg : IsSMulRegular B x := ((isRegular_cons_iff B x [y]).mp hreg).1
  have hyreg : IsSMulRegular (QuotSMulTop x B) y := by
    exact (isWeaklyRegular_singleton_iff _ _).mp
      ((isRegular_cons_iff B x [y]).mp hreg).2.toIsWeaklyRegular
  have hπreg : IsSMulRegular (QuotSMulTop x B) π := by
    rw [← hy, ← Ideal.Quotient.algebraMap_eq, isSMulRegular_algebraMap_iff]
    exact hyreg
  -- Every nonzero quotient scalar is a unit times a power of its regular uniformizer.
  have : Module.IsTorsionFree Q (QuotSMulTop x B) := by
    constructor
    intro q hq
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq.ne_zero hπ
    exact (u.isSMulRegular _).mul (hπreg.pow n)
  have : Module.Finite Q (QuotSMulTop x B) := Module.Finite.of_restrictScalars_finite A Q _
  have : Module.Free Q (QuotSMulTop x B) := inferInstance
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  have : Module.Free A B := (Module.free_quotSMulTop_iff_free A B
    (by rwa [jacobson_eq_maximalIdeal ⊥ bot_ne_top]) hxreg).mp inferInstance
  infer_instance

end TauCeti.Algebra
