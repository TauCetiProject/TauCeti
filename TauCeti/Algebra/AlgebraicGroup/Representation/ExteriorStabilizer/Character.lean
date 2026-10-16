/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.DefiningSubcomodule
public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.SubgroupWeights
import TauCeti.Algebra.Coalgebra.Subcomodule.ExteriorPower

/-!
# The subgroup character of a Chevalley line

Every closed subgroup with finitely generated defining ideal is the stabilizer of a line in
an exterior power of a finite regular subcomodule. The line is a subrepresentation after
restriction to the subgroup, so the subgroup acts on it by a unique character. Here characters
are group-like elements of the quotient coordinate Hopf algebra; no reducedness, smoothness,
or algebraic closure is needed.

The character places the Chevalley line inside the sum of the subgroup's weight spaces. For a
normal subgroup this sum is an ambient subrepresentation under the hypotheses of
`HopfIdeal.IsNormal.iSupWeightSpaceSubcomodule`. Its block-diagonal endomorphisms are the next
representation used to realize the normal subgroup as a kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
* J. E. Humphreys, *Linear Algebraic Groups*, §11.5.

The exterior-line construction uses `Subcomodule.exists_line_corestrict_exteriorPower` and
`HopfIdeal.definingSubcomodule`; its stabilizer is detected by
`HopfIdeal.mem_quotientPointsSubgroup_iff_map_baseChange_range_exteriorPowerMap_eq`.
-/

public section

open scoped TensorProduct
open CategoryTheory

universe u v w

namespace TauCeti.HopfIdeal

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}

attribute [local instance] Comodule.exteriorPower

/-- The top exterior line of the defining subspace of a closed subgroup transforms by a
unique character of that subgroup. Only the defining subspace must be finite-dimensional. -/
theorem existsUnique_topExteriorLine_le_weightSpace (I : HopfIdeal k H)
    (V : Subcomodule k H H) (hW : Module.Finite k (I.definingSubspace V)) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    ∃! χ : GroupLike k (H ⧸ I.toIdeal),
      LinearMap.range (_root_.exteriorPower.map (Module.finrank k (I.definingSubspace V))
        (I.definingSubspace V).subtype) ≤
          I.weightSpace (⋀[k]^(Module.finrank k (I.definingSubspace V)) V) χ := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k (I.definingSubspace V) := hW
  let f := (CommHopfAlgCat.mkQuotient H I).hom
  let : Comodule k (CommHopfAlgCat.quotient H I) V := Comodule.Corestrict f.toCoalgHom
  have hline :=
    Subcomodule.exists_line_corestrict_exteriorPower f (I.definingSubcomodule V) (by
      rw [I.definingSubcomodule_toSubmodule V]
      infer_instance)
  let : Comodule k (CommHopfAlgCat.quotient H I)
      (⋀[k]^(Module.finrank k (I.definingSubcomodule V).toSubmodule) V) :=
    Comodule.Corestrict f.toCoalgHom
  obtain ⟨L, hcarrier, hdim⟩ := hline
  have hchar : ∃! χ : GroupLike k (H ⧸ I.toIdeal),
      L.toSubmodule ≤
        I.weightSpace (⋀[k]^(Module.finrank k (I.definingSubcomodule V).toSubmodule) V) χ := by
    obtain ⟨χ, hχ, huniq⟩ := L.existsUnique_le_groupLikeWeightSpace_of_finrank_eq_one hdim
    refine ⟨χ, ?_, ?_⟩
    · intro x hx
      rw [mem_weightSpace]
      exact GroupLike.mem_weightSpace.mp (hχ hx)
    · intro ψ hψ
      apply huniq
      intro x hx
      rw [GroupLike.mem_weightSpace]
      exact mem_weightSpace.mp (hψ hx)
  have hW' : (I.definingSubcomodule V).toSubmodule = I.definingSubspace V := by
    exact I.definingSubcomodule_toSubmodule V
  rw [hcarrier] at hchar
  -- The exterior degree depends on the subspace. Package the entire character statement
  -- before replacing it, so the degree and its module instances are transported together.
  let P (W : Submodule k V) : Prop :=
    ∃! χ : GroupLike k (H ⧸ I.toIdeal),
      LinearMap.range (_root_.exteriorPower.map (Module.finrank k W) W.subtype) ≤
        I.weightSpace (⋀[k]^(Module.finrank k W) V) χ
  have hP : P (I.definingSubcomodule V).toSubmodule := hchar
  rw [hW'] at hP
  exact hP

/-- **Chevalley's theorem with the subgroup character.** A closed subgroup with finitely
generated defining ideal is the stabilizer, over every commutative value algebra, of a line in
a finite-dimensional exterior-power representation. The line lies in the weight space of a
unique character of the subgroup, including when the subgroup is nonreduced. -/
theorem exists_finite_subcomodule_exteriorPower_line_stabilizer (I : HopfIdeal k H)
    (hI : I.toIdeal.FG) :
    ∃ (V : Subcomodule k H H) (n : ℕ), Module.Finite k V.toSubmodule ∧
      let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
      ∃ L : Submodule k (⋀[k]^n V), Module.finrank k L = 1 ∧
        (∃! χ : GroupLike k (H ⧸ I.toIdeal), L ≤ I.weightSpace (⋀[k]^n V) χ) ∧
        ∀ (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A),
          g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
            (L.baseChange A).map (Comodule.endOfPoint (⋀[k]^n V) g.ofConv) = L.baseChange A := by
  obtain ⟨V, hV, hgen⟩ := I.exists_finite_subcomodule_generating hI
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let W := I.definingSubspace V
  refine ⟨V, Module.finrank k W, hV, LinearMap.range (_root_.exteriorPower.map _ W.subtype),
    ?_, I.existsUnique_topExteriorLine_le_weightSpace V (by infer_instance), ?_⟩
  · rw [exteriorPower.finrank_range_map W.injective_subtype, Nat.choose_self]
  · exact fun A g ↦
      I.mem_quotientPointsSubgroup_iff_map_baseChange_range_exteriorPowerMap_eq V hgen A g

end TauCeti.HopfIdeal
