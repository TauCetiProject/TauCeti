/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.SubgroupWeights
public import TauCeti.LinearAlgebra.End.FamilyInvariant

/-!
# Detecting a subgroup by endomorphisms preserving each character space

Suppose a representation is spanned by the character spaces of a closed subgroup, and the
subgroup is the stabilizer of a line inside one character space. A point belongs to the subgroup
if and only if it commutes with the scalar extensions of all endomorphisms preserving each
character space.

The forward implication uses the subgroup's scalar action on each character space. For the
reverse implication, independence of the character spaces supplies a projection onto the line
preserving each character space. Commuting with its scalar extension forces the point to stabilize
the line.
All coefficient algebras are allowed, so the criterion detects scheme-theoretic subgroups,
including nonreduced ones.

For the normal-subgroup kernel argument, the representation is the sum of the subgroup weight
spaces containing a Chevalley line. This file proves the centralizer criterion from the spanning
and line-stabilizer properties; it does not construct that representation or its line.

The character-space API is `HopfIdeal.weightSpace`; the linear-algebra argument is
`Submodule.map_baseChange_eq_of_forall_commute_familyInvariant`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §11.5.
* A. Borel, *Linear Algebraic Groups*, §5.5.
-/

public section

open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v w x

section Ring

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R}
variable (I : HopfIdeal R H) (V : Type w) [AddCommMonoid V] [Module R V] [Comodule R H V]

/-- If subgroup character spaces span a representation, every subgroup point commutes with the
scalar extensions of the endomorphisms preserving each character space. This assertion needs
neither normality, finite type, reducedness, nor algebraic closure. -/
theorem commute_baseChange_of_mem_quotientPointsSubgroup
    (hV : ⨆ χ, I.weightSpace V χ = ⊤) (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := H) A)
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A)
    {p : Module.End R V} (hp : p ∈ Submodule.familyInvariant (I.weightSpace V)) :
    Commute (Comodule.endOfPoint V g.ofConv) (p.baseChange A) := by
  have hzero := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H I A g).mp hg
  let q := CommHopfAlgCat.liftQuotientPoint H I A g hzero
  have hq : q.ofConv.comp (Ideal.Quotient.mkₐ R I.toIdeal) = g.ofConv := by
    ext a
    exact CommHopfAlgCat.liftQuotientPoint_mk H I A g hzero a
  rw [← hq]
  apply Submodule.commute_baseChange_of_forall_tmul_eq_smul (I.weightSpace V) hV
    _ (fun χ ↦ q.ofConv χ.val) _ hp
  intro χ v hv
  simpa only [one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    I.endOfPoint_comp_mkₐ_tmul_of_mem_weightSpace q.ofConv 1 hv

end Ring

section Field

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}
variable (I : HopfIdeal k H) (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V]

/-- A subgroup that stabilizes a subspace inside one character space of a representation spanned
by its character spaces is detected by centralizing the endomorphisms preserving each character
space, over the whole coefficient algebra. The implication from stabilizing the subspace to
subgroup membership is an explicit input. -/
theorem mem_quotientPointsSubgroup_iff_forall_commute_familyInvariant_of_subspace_stabilizer
    (hV : ⨆ χ, I.weightSpace V χ = ⊤)
    (χ : GroupLike k (H ⧸ I.toIdeal)) (L : Submodule k V) (hL : L ≤ I.weightSpace V χ)
    (A : CommAlgCat.{x} k)
    (g : HopfAlgebra.points (R := k) (H := H) A)
    (hstab : (L.baseChange A).map (Comodule.endOfPoint V g.ofConv) = L.baseChange A →
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
      ∀ p ∈ Submodule.familyInvariant (I.weightSpace V),
        Commute (Comodule.endOfPoint V g.ofConv) (p.baseChange A) := by
  refine ⟨fun hg p hp ↦ I.commute_baseChange_of_mem_quotientPointsSubgroup V hV A g hg hp,
    fun hg ↦ hstab ?_⟩
  have h := Submodule.map_baseChange_eq_of_forall_commute_familyInvariant
    (I.weightSpace V) χ (I.iSupIndep_weightSpace V χ) L hL (Comodule.pointsAction V g) (by
      simpa only [Comodule.pointsAction_toLinearMap] using hg)
  simpa only [Comodule.pointsAction_toLinearMap] using h

end Field

end TauCeti.HopfIdeal
