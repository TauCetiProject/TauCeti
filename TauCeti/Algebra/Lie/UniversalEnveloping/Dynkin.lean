/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.HopfAlgebra.Dynkin
public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.HopfAlgebra

/-!
# Dynkin operators in universal enveloping algebras

The Dynkin operator associated with any lifted Lie derivation has values in the canonical
Lie image. Consequently, a primitive eigenvector of the lifted derivation belongs to the
Lie image whenever its eigenvalue is a unit. Applied to Euler derivations, this recovers
homogeneous primitive elements of invertible weight as Lie elements. No basis, grading,
or injectivity assumption on the canonical Lie map is needed.

Adapted from `Mei/Algebra/Lie/UniversalEnveloping/Dynkin/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `97304cc1bd51a202db1a705709fb4763f61e190a` (Apache 2.0).
-/

public section

open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieDerivation
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
local notation "U" => UniversalEnvelopingAlgebra R L
local notation "ι" => UniversalEnvelopingAlgebra.ι R

/-- The Dynkin operator of a lifted Lie derivation takes its values in the canonical Lie image. -/
theorem dynkinOperator_mem_range_ι (D : LieDerivation R L L) (a : U) :
    TauCeti.HopfAlgebra.dynkinOperator
      (TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L D) a ∈
        (ι : L →ₗ⁅R⁆ U).toLinearMap.range := by
  let Y := TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L D
  let T := TauCeti.HopfAlgebra.dynkinOperator Y
  let P := (ι : L →ₗ⁅R⁆ U).toLinearMap.range
  have hprim (x : L) : Bialgebra.IsPrimitiveElem R (ι x) :=
    ⟨TauCeti.UniversalEnvelopingAlgebra.counit_ι R L x, by
      rw [TauCeti.UniversalEnvelopingAlgebra.comul_ι]
      exact add_comm _ _⟩
  -- The strengthened statement handles arbitrary products in the algebra-generation induction.
  have hright (b : U) : ∀ a : U, T a ∈ P → T (a * b) ∈ P := by
    induction b using TauCeti.UniversalEnvelopingAlgebra.induction_ι R L with
    | «ι» x =>
      intro a ha
      obtain ⟨z, hz⟩ := ha
      rw [TauCeti.HopfAlgebra.dynkinOperator_mul_primitive Y a (hprim x),
        TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι, ← hz]
      refine ⟨⁅z, x⁆ + Coalgebra.counit (R := R) a • D x, ?_⟩
      simp only [LieHom.coe_toLinearMap, map_add, map_smul, LieHom.map_lie,
        LieRing.of_associative_ring_bracket]
    | algebraMap r =>
      intro a ha
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_smul]
      exact P.smul_mem r ha
    | add b c hb hc =>
      intro a ha
      rw [mul_add, map_add]
      exact P.add_mem (hb a ha) (hc a ha)
    | mul b c hb hc =>
      intro a ha
      rw [← mul_assoc]
      exact hc _ (hb _ ha)
  simpa only [one_mul] using hright a 1 (by
    rw [TauCeti.HopfAlgebra.dynkinOperator_one]
    exact P.zero_mem)

/-- A primitive eigenvector of a lifted Lie derivation lies in the canonical Lie image
when its eigenvalue is a unit. -/
theorem mem_range_ι_of_isPrimitiveElem_of_envelopingDerivation_eq_smul
    (D : LieDerivation R L L) {a : U} (ha : Bialgebra.IsPrimitiveElem R a)
    {r : R} (hr : IsUnit r)
    (h : (TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L D : Module.End R U) a =
      r • a) :
    a ∈ (ι : L →ₗ⁅R⁆ U).toLinearMap.range := by
  apply (Submodule.smul_mem_iff_of_isUnit _ hr).mp
  rw [← h, ← TauCeti.HopfAlgebra.dynkinOperator_of_isPrimitiveElem _ ha]
  exact D.dynkinOperator_mem_range_ι a

end LieDerivation
