/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra

import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Equiv
import TauCeti.LinearAlgebra.SymmetricAlgebra.Primitive

/-!
# Primitive elements of universal enveloping algebras

For an arbitrary Lie algebra over a commutative rational algebra, the primitive elements of its
universal enveloping algebra are precisely the images of the Lie generators. The linear
equivalence `primitiveEquiv` identifies the Lie algebra with the submodule of primitive elements,
without a freeness or flatness hypothesis.

The classification transports `SymmetricAlgebra.isPrimitiveElem_iff_mem_range_ι` through
`pbwSymmetrizationCoalgEquiv`, the symmetrization form of PBW.

## References

* F. Petracci, *Universal representations of Lie algebras by coderivations*
  (arXiv:math/0303020), §8, for the symmetrization coalgebra equivalence.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R

/-- Over a commutative rational algebra, an enveloping-algebra element is primitive exactly
when it is the image of a Lie generator. -/
theorem isPrimitiveElem_iff_mem_range_ι (p : U) :
    Bialgebra.IsPrimitiveElem R p ↔ p ∈ Set.range (ι : L → U) := by
  let e := pbwSymmetrizationCoalgEquiv R L
  have he : e (1 : SymmetricAlgebra R L) = 1 := by
    simp [e]
  constructor
  · intro hp
    have hq : Bialgebra.IsPrimitiveElem R (e.symm p) := by
      apply (Coalgebra.isSkewPrimitiveElem_map_equiv e).mp
      simpa only [he, CoalgEquiv.apply_symm_apply] using hp
    obtain ⟨x, hx⟩ := (SymmetricAlgebra.isPrimitiveElem_iff_mem_range_ι (e.symm p)).mp hq
    refine ⟨x, ?_⟩
    have h := congrArg e hx
    simpa only [e, CoalgEquiv.apply_symm_apply, pbwSymmetrizationCoalgEquiv_apply,
      pbwSymmetrizationMap_ι] using h
  · rintro ⟨x, rfl⟩
    apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr
    simpa only [add_comm] using comul_ι R L x

/-- The Lie algebra is linearly equivalent to the primitive submodule of its enveloping
algebra, through the canonical Lie inclusion. -/
noncomputable def primitiveEquiv : L ≃ₗ[R] Coalgebra.skewPrimitive R (1 : U) 1 :=
  LinearEquiv.ofBijective
    ((ι : L →ₗ⁅R⁆ U).toLinearMap.codRestrict _ fun x =>
      (isPrimitiveElem_iff_mem_range_ι R L (ι x)).mpr ⟨x, rfl⟩)
    ⟨(LinearMap.injective_codRestrict_iff _).mpr fun x y h =>
      SymmetricAlgebra.ι_injective R L <| pbwSymmetrizationMap_injective R L (by
        simpa only [pbwSymmetrizationMap_ι, LieHom.coe_toLinearMap] using h),
      fun p => by
        obtain ⟨x, hx⟩ := (isPrimitiveElem_iff_mem_range_ι R L p).mp p.property
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The primitive equivalence sends an element to its canonical image in the enveloping
algebra. -/
@[simp]
theorem primitiveEquiv_apply (x : L) : (primitiveEquiv R L x : U) = ι x := (rfl)

/-- Recovering a Lie element from its primitive image returns that element. -/
-- The inverse equations run before `ι` normalizes to its `mkAlgHom` presentation.
@[simp↓]
theorem primitiveEquiv_symm_ι (x : L) (h : Bialgebra.IsPrimitiveElem R (ι x)) :
    (primitiveEquiv R L).symm ⟨ι x, h⟩ = x := by
  apply (primitiveEquiv R L).injective
  apply Subtype.ext
  simp

/-- The Lie element recovered from a primitive element maps back to that element. -/
@[simp↓]
theorem ι_primitiveEquiv_symm (p : Coalgebra.skewPrimitive R (1 : U) 1) :
    ι ((primitiveEquiv R L).symm p) = (p : U) := by
  simpa only [primitiveEquiv_apply] using
    congrArg Subtype.val ((primitiveEquiv R L).apply_symm_apply p)

end TauCeti.UniversalEnvelopingAlgebra
