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

Over a commutative rational algebra, the canonical Lie map into a universal enveloping algebra
identifies the Lie algebra with its primitive elements: those with counit zero and coproduct
`1 ⊗ x + x ⊗ 1`. Every primitive element lies in this canonical Lie image, without a freeness or
flatness hypothesis. The primitive submodule is `Coalgebra.skewPrimitive R 1 1`.

`UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι` recovers a Lie element from a
primitive element. `TauCeti.UniversalEnvelopingAlgebra.primitiveEquiv` gives the resulting linear
equivalence, with forward and inverse equations and compatibility of the Lie bracket with the
commutator. These classification results assume `R : Type` and `[Algebra ℚ R]`; the Lie algebra
may lie in any universe. Primitivity of canonical generators itself needs only a commutative ring
and is available in `TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra`.

## References

Formal dependencies: `SymmetricAlgebra.isPrimitiveElem_iff_mem_range_ι` and
`TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationCoalgEquiv`.

* F. Petracci, *Universal representations of Lie algebras by coderivations*
  (arXiv:math/0303020), §8, for the symmetrization coalgebra equivalence.
-/

public section

namespace UniversalEnvelopingAlgebra

universe v

variable {R : Type} {L : Type v} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R

/-- Over a commutative rational algebra, an enveloping-algebra element is primitive exactly
when it is the image of a Lie element. -/
theorem isPrimitiveElem_iff_mem_range_ι (p : U) :
    Bialgebra.IsPrimitiveElem R p ↔ p ∈ Set.range (ι : L → U) := by
  let e := TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationCoalgEquiv R L
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
    simpa only [e, CoalgEquiv.apply_symm_apply,
      TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationCoalgEquiv_apply,
      TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationMap_ι] using h
  · rintro ⟨x, rfl⟩
    exact TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_ι R L x

end UniversalEnvelopingAlgebra

namespace TauCeti.UniversalEnvelopingAlgebra

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R

/-- Over a commutative rational algebra `R : Type`, the canonical Lie inclusion identifies
the Lie algebra with the primitive submodule of its enveloping algebra. No freeness or flatness
hypothesis is needed. -/
noncomputable def primitiveEquiv : L ≃ₗ[R] Coalgebra.skewPrimitive R (1 : U) 1 :=
  LinearEquiv.ofBijective
    ((ι : L →ₗ⁅R⁆ U).toLinearMap.codRestrict _ fun x =>
      isPrimitiveElem_ι R L x)
    ⟨(LinearMap.injective_codRestrict_iff _).mpr fun x y h =>
      SymmetricAlgebra.ι_injective R L <| pbwSymmetrizationMap_injective R L (by
        simpa only [pbwSymmetrizationMap_ι, LieHom.coe_toLinearMap] using h),
      fun p => by
        obtain ⟨x, hx⟩ :=
          (_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι (p : U)).mp p.property
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The primitive equivalence sends an element to its canonical image in the enveloping
algebra. -/
@[simp]
theorem coe_primitiveEquiv_apply (x : L) : (primitiveEquiv R L x : U) = ι x := (rfl)

/-- Recovering a Lie element from its primitive image returns that element. -/
theorem primitiveEquiv_symm_ι (x : L) (h : Bialgebra.IsPrimitiveElem R (ι x)) :
    (primitiveEquiv R L).symm ⟨ι x, h⟩ = x := by
  apply (primitiveEquiv R L).injective
  apply Subtype.ext
  simp

/-- The Lie element recovered from a primitive element maps back to that element. -/
theorem ι_primitiveEquiv_symm (p : Coalgebra.skewPrimitive R (1 : U) 1) :
    ι ((primitiveEquiv R L).symm p) = (p : U) := by
  simpa only [coe_primitiveEquiv_apply] using
    congrArg Subtype.val ((primitiveEquiv R L).apply_symm_apply p)

/-- The inverse equation for a canonical generator in its simplifier normal form. -/
@[simp]
theorem primitiveEquiv_symm_ι' (x : L) :
    (primitiveEquiv R L).symm
      ⟨_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x),
        isPrimitiveElem_ι R L x⟩ = x :=
  primitiveEquiv_symm_ι R L x (isPrimitiveElem_ι R L x)

/-- The recovered Lie element maps back to the primitive element, in simplifier normal form. -/
@[simp]
theorem ι_primitiveEquiv_symm' (p : Coalgebra.skewPrimitive R (1 : U) 1) :
    _root_.UniversalEnvelopingAlgebra.mkAlgHom R L
      (TensorAlgebra.ι R ((primitiveEquiv R L).symm p)) = (p : U) :=
  ι_primitiveEquiv_symm R L p

/-- The primitive equivalence sends Lie brackets to commutators. -/
theorem coe_primitiveEquiv_lie (x y : L) :
    (primitiveEquiv R L ⁅x, y⁆ : U) =
      (primitiveEquiv R L x : U) * (primitiveEquiv R L y : U) -
        (primitiveEquiv R L y : U) * (primitiveEquiv R L x : U) := by
  simpa only [coe_primitiveEquiv_apply, LieRing.of_associative_ring_bracket] using
    (ι : L →ₗ⁅R⁆ U).map_lie x y

/-- Recovering the Lie elements from a commutator recovers their Lie bracket. -/
theorem primitiveEquiv_symm_commutator (p q : Coalgebra.skewPrimitive R (1 : U) 1) :
    (primitiveEquiv R L).symm
        ⟨(p : U) * (q : U) - (q : U) * (p : U),
          Bialgebra.IsPrimitiveElem.commutator p.property q.property⟩ =
      ⁅(primitiveEquiv R L).symm p, (primitiveEquiv R L).symm q⁆ := by
  apply (primitiveEquiv R L).injective
  apply Subtype.ext
  rw [coe_primitiveEquiv_lie]
  simp only [LinearEquiv.apply_symm_apply]

end TauCeti.UniversalEnvelopingAlgebra
