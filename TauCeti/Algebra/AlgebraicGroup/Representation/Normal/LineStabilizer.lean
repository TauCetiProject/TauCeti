/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Character
public import TauCeti.Algebra.Coalgebra.Comodule.Cat
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.FiniteType

/-!
# A Chevalley line in the sum of subgroup weight spaces

A normal closed subgroup of a reduced affine group of finite type over an algebraically closed
field is the stabilizer of a line in a finite-dimensional representation spanned by the
subgroup's character spaces. The stabilizer equality holds over every commutative value algebra,
including nonreduced ones. The subgroup itself need not be reduced.

Chevalley's exterior-line representation has a line transforming by one subgroup character.
Restrict that representation to the sum of its subgroup weight spaces, which is an ambient
subcomodule by normality. The inclusion detects both character spaces and scalar-extended line
stabilizers. This gives the representation on whose block-diagonal endomorphisms the ambient
group acts with the prescribed normal subgroup as kernel.

The construction follows the normal-subgroup argument of J. E. Humphreys,
*Linear Algebraic Groups*, §11.5, and A. Borel, *Linear Algebraic Groups*, §5.5. Its formal inputs
are `HopfIdeal.exists_finite_subcomodule_exteriorPower_line_stabilizer` and
`HopfIdeal.IsNormal.iSupWeightSpaceSubcomodule`.
-/

public section

open CategoryTheory

universe u v w u'

namespace TauCeti.HopfIdeal

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{v} k}
variable [Algebra.FiniteType k H] [IsReduced H]

attribute [local instance] Comodule.exteriorPower

/-- A line-stabilizer representation of a normal subgroup can be replaced by the sum of its
subgroup weight spaces without changing the stabilizer over any value algebra. -/
theorem IsNormal.exists_finite_weightSpace_line_stabilizer_of_line_stabilizer
    {I : HopfIdeal k H} (hI : I.IsNormal) (V : Type w) [AddCommGroup V] [Module k V]
    [Comodule k H V] [Module.Finite k V] (L : Submodule k V)
    (hdim : Module.finrank k L = 1)
    (hχ : ∃! χ : GroupLike k (H ⧸ I.toIdeal), L ≤ I.weightSpace V χ)
    (hstab : ∀ (A : CommAlgCat.{u'} k) (g : HopfAlgebra.points (R := k) (H := H) A),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
        (L.baseChange A).map (Comodule.endOfPoint V g.ofConv) = L.baseChange A) :
    ∃ W : ComoduleCat.{u, v, w} k H, Module.Finite k W ∧
      (⨆ χ, I.weightSpace W χ) = ⊤ ∧
      ∃ L : Submodule k W, Module.finrank k L = 1 ∧
        (∃! χ : GroupLike k (H ⧸ I.toIdeal), L ≤ I.weightSpace W χ) ∧
        ∀ (A : CommAlgCat.{u'} k) (g : HopfAlgebra.points (R := k) (H := H) A),
          g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
            (L.baseChange A).map (Comodule.endOfPoint W g.ofConv) = L.baseChange A := by
  let W := hI.iSupWeightSpaceSubcomodule V
  let f := Subcomodule.subtype W
  let L' := L.comap f.toLinearMap
  obtain ⟨χ, hχ, huniq⟩ := hχ
  have hLW : L ≤ W.toSubmodule := by
    rw [hI.iSupWeightSpaceSubcomodule_toSubmodule V]
    exact hχ.trans (le_iSup (I.weightSpace V) χ)
  have hmap : L'.map f.toLinearMap = L := by
    rw [Submodule.map_comap_eq, Subcomodule.subtype_toLinearMap, Subcomodule.range_subtype]
    exact inf_eq_right.mpr hLW
  have hdim' : Module.finrank k L' = 1 := by
    have h := (L'.equivMapOfInjective f.toLinearMap W.subtype_injective).finrank_eq
    rw [hmap] at h
    exact h.trans hdim
  have hchar' : ∃! ψ : GroupLike k (H ⧸ I.toIdeal), L' ≤ I.weightSpace W ψ := by
    refine ⟨χ, ?_, ?_⟩
    · exact (Submodule.comap_mono hχ).trans_eq
        (comap_weightSpace (I := I) f W.subtype_injective χ)
    · intro ψ hψ
      apply huniq ψ
      rw [← hmap]
      exact Submodule.map_le_iff_le_comap.mpr
        (hψ.trans_eq (comap_weightSpace (I := I) f W.subtype_injective ψ).symm)
  have hstab' (A : CommAlgCat.{u'} k) (g : HopfAlgebra.points (R := k) (H := H) A) :
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
        (L'.baseChange A).map (Comodule.endOfPoint W g.ofConv) = L'.baseChange A := by
    rw [hstab A g, ← hmap]
    exact (f.map_endOfPoint_baseChange_eq_iff W.subtype_injective L' g.ofConv).symm
  exact ⟨ComoduleCat.of k H W,
    Module.Finite.of_injective f.toLinearMap W.subtype_injective,
    hI.iSup_weightSpace_iSupWeightSpaceSubcomodule_eq_top V, L', hdim', hchar', hstab'⟩

/-- A normal closed subgroup is the line stabilizer in a finite-dimensional representation
spanned by its subgroup character spaces. The line belongs to a unique character space, and
its stabilizer identifies the subgroup over every commutative value algebra. -/
theorem IsNormal.exists_finite_weightSpace_line_stabilizer {I : HopfIdeal k H}
    (hI : I.IsNormal) :
    ∃ V : ComoduleCat.{u, v, max u v} k H, Module.Finite k V ∧
      (⨆ χ, I.weightSpace V χ) = ⊤ ∧
      ∃ L : Submodule k V, Module.finrank k L = 1 ∧
        (∃! χ : GroupLike k (H ⧸ I.toIdeal), L ≤ I.weightSpace V χ) ∧
        ∀ (A : CommAlgCat.{u'} k) (g : HopfAlgebra.points (R := k) (H := H) A),
          g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
            (L.baseChange A).map (Comodule.endOfPoint V g.ofConv) = L.baseChange A := by
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨V, n, hV, L, hdim, hχ, hstab⟩ :=
    I.exists_finite_subcomodule_exteriorPower_line_stabilizer
      (IsNoetherian.noetherian I.toIdeal)
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  exact hI.exists_finite_weightSpace_line_stabilizer_of_line_stabilizer (⋀[k]^n V)
    L hdim hχ hstab

end TauCeti.HopfIdeal
