/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Character
import Mathlib.RingTheory.FiniteType

/-!
# A Chevalley line in the weight-sum representation

Let `N` be a normal closed subgroup of a reduced affine group of finite type over an
algebraically closed field. Chevalley's theorem realizes `N` as the stabilizer of a line
in a finite-dimensional representation. That line lies in one character space of `N`,
hence in the subrepresentation spanned by all its character spaces. Restricting to this
subrepresentation preserves the line and its stabilizer over every commutative value
algebra, including nonreduced ones.

The resulting representation is spanned by its `N`-weight spaces and contains a line
whose stabilizer is exactly `N`. These are the inputs to the construction of a
representation with kernel `N`, by conjugation on block-diagonal endomorphisms.

The construction uses `HopfIdeal.exists_finite_subcomodule_exteriorPower_line_stabilizer`
and `HopfIdeal.IsNormal.iSupWeightSpaceSubcomodule`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §11.5.
* A. Borel, *Linear Algebraic Groups*, §5.5.
-/

public section

namespace TauCeti.HopfIdeal

universe u v w x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k H] [IsReduced H]

attribute [local instance] Comodule.exteriorPower

private theorem restrict_line_stabilizer {I : HopfIdeal k H} (hI : I.IsNormal)
    (V : FGComoduleCat.{u, v, x} k H) (χ : GroupLike k (H ⧸ I.toIdeal))
    (L : Submodule k V) (hdim : Module.finrank k L = 1) (hχ : L ≤ I.weightSpace V χ)
    (hstab : ∀ (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
        (L.baseChange A).map (Comodule.endOfPoint V g.ofConv) = L.baseChange A) :
    ∃ W : FGComoduleCat.{u, v, x} k H,
      (⨆ ψ, I.weightSpace W ψ) = ⊤ ∧
      ∃ L' : Submodule k W, Module.finrank k L' = 1 ∧ L' ≤ I.weightSpace W χ ∧
        ∀ (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A),
          g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
            (L'.baseChange A).map (Comodule.endOfPoint W g.ofConv) = L'.baseChange A := by
  let W := hI.iSupWeightSpaceSubcomodule V
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k W := W.finite
  have hL : L ≤ W.toSubmodule := by
    rw [IsNormal.iSupWeightSpaceSubcomodule_toSubmodule]
    exact hχ.trans (le_iSup (I.weightSpace V) χ)
  let L' := L.comap (SMulMemClass.subtype W)
  have hrange : LinearMap.range (SMulMemClass.subtype W) = W.toSubmodule :=
    Submodule.range_subtype W.toSubmodule
  have himage : L'.map W.subtype.toLinearMap = L := by
    rw [Subcomodule.subtype_toLinearMap]
    exact Submodule.map_comap_eq_of_le (by rw [hrange]; exact hL)
  have hdim' : Module.finrank k L' = 1 :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hL)).trans hdim
  refine ⟨FGComoduleCat.of W,
    hI.iSup_weightSpace_iSupWeightSpaceSubcomodule_eq_top V, L', hdim', ?_, ?_⟩
  · -- The bundled finite comodule carries the same induced coaction on `W`.
    intro x hx
    have hx' : x ∈ (I.weightSpace V χ).comap (SMulMemClass.subtype W) := hχ hx
    exact (I.weightSpace_subcomodule W χ).symm ▸ hx'
  · intro A g
    rw [hstab A g, ← himage]
    exact Comodule.Hom.map_endOfPoint_baseChange_eq_iff
      W.subtype (by
        intro x y hxy
        apply Subtype.val_injective
        simpa only [Subcomodule.subtype_apply] using hxy) L' g.ofConv

/-- A normal closed subgroup is the stabilizer of a line in a finite-dimensional
representation spanned by its subgroup weight spaces. The line lies in a single weight
space, and the stabilizer equality holds over every commutative value algebra. -/
theorem IsNormal.exists_finite_weightSum_line_stabilizer {I : HopfIdeal k H}
    (hI : I.IsNormal) :
    ∃ V : FGComoduleCat.{u, v, max u v} k H,
      (⨆ χ, I.weightSpace V χ) = ⊤ ∧
      ∃ (χ : GroupLike k (H ⧸ I.toIdeal)) (L : Submodule k V),
        Module.finrank k L = 1 ∧ L ≤ I.weightSpace V χ ∧
        ∀ (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A),
          g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
            (L.baseChange A).map (Comodule.endOfPoint V g.ofConv) = L.baseChange A := by
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨U, n, hU, h⟩ := I.exists_finite_subcomodule_exteriorPower_line_stabilizer
    (IsNoetherian.noetherian _)
  let : Module.Finite k U := hU
  let : AddCommGroup U := Module.addCommMonoidToAddCommGroup k
  obtain ⟨L, hdim, ⟨χ, hχ, _⟩, hstab⟩ := h
  obtain ⟨W, hW, L', hdim', hχ', hstab'⟩ :=
    restrict_line_stabilizer hI (FGComoduleCat.of (⋀[k]^n U)) χ L hdim hχ hstab
  exact ⟨W, hW, χ, L', hdim', hχ', hstab'⟩

end TauCeti.HopfIdeal
