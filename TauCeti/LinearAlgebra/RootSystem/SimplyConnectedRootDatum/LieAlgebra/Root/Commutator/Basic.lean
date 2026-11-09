/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant

/-!
# Single-term Chevalley root-subgroup relations

For every valid Dynkin type, a root sum whose vector commutes with both input vectors gives a
single-term product relation on every Kostant-stable lattice, over every commutative value ring.
The structure constant is the integer supplied by the pinned Chevalley system.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable {t : DynkinType} {ht : t.Valid} {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ z ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ z v ∈ M)
variable (hnil : ∀ r, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator r))))

-- Match the tensor-product module to the algebra structure stored by the value ring.
attribute [local instance high] Algebra.toModule

/-- The single-term Chevalley product relation, when the sum-root vector commutes with both
input vectors. No restriction on Dynkin type or root lengths is required. -/
theorem chevalleyRootSubgroup_mul_of_add
    {i j k : Fin t.numRoots}
    (hij : (t.simplyConnectedRootDatum ht).root k =
      (t.simplyConnectedRootDatum ht).root i + (t.simplyConnectedRootDatum ht).root j)
    (hik : ⁅t.chevalleySystem ht i, t.chevalleySystem ht k⁆ = 0)
    (hjk : ⁅t.chevalleySystem ht j, t.chevalleySystem ht k⁆ = 0)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil j A (Multiplicative.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil k A
          (Multiplicative.ofAdd ((t.structureConstant ht i j : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd u) := by
  exact chevalleyRootSubgroup_mul_of_lie_eq ρ M hM hnil
    (lie_chevalleySystem_eq_structureConstant_zsmul hij) hik hjk A u v

end

end TauCeti.DynkinType
