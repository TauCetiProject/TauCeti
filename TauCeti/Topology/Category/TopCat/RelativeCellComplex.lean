/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding

/-!
# The weak topology of relative cell complexes

A relative cell complex in `TopCat` carries the final topology for its base map and its
characteristic maps. Consequently, a subset is closed exactly when its preimage in the base
and in every cell is closed (`HomotopicalAlgebra.RelativeCellComplex.isClosed_iff`), and a map
out of the complex is continuous exactly when its composites with those maps are continuous
(`HomotopicalAlgebra.RelativeCellComplex.continuous_iff`). No separation or embedding
assumptions are required.

In particular, these criteria apply directly to `TopCat.RelativeCWComplex`: the characteristic
maps have closed disks as their domains. This establishes the weak-topology part of the
comparison with classical relative CW complexes; closure finiteness is a separate property.
The same criteria for a single attachment are also provided here.

## References

* A. Hatcher, *Algebraic Topology*, Appendix, Proposition A.2, for the weak topology of CW
  complexes.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, for the categorical construction of cell complexes.
-/

public section

open CategoryTheory Limits

universe w w' t u v

namespace HomotopicalAlgebra.AttachCells

variable {α : Type t} {A B : α → TopCat.{u}} {g : (a : α) → A a ⟶ B a}
  {X Y : TopCat.{u}} {f : X ⟶ Y} (c : AttachCells.{w} g f)

/-- A subset of a space obtained by attaching cells is closed exactly when its preimages in
the old space and in each attached cell are closed. -/
theorem isClosed_iff (S : Set Y) :
    IsClosed S ↔ IsClosed (f ⁻¹' S) ∧ ∀ i, IsClosed (c.cell i ⁻¹' S) := by
  rw [TauCeti.TopCat.isClosed_iff_of_isPushout c.isPushout,
    TopCat.isClosed_iff_of_isColimit _ c.isColimit₂]
  constructor
  · rintro ⟨h₀, h⟩
    exact ⟨h₀, fun i ↦ h ⟨i⟩⟩
  · rintro ⟨h₀, h⟩
    exact ⟨h₀, fun ⟨i⟩ ↦ h i⟩

/-- Continuity out of an attachment can be checked on the old space and every attached cell. -/
theorem continuous_iff {Z : Type v} [TopologicalSpace Z] (p : Y → Z) :
    Continuous p ↔ Continuous (p ∘ f) ∧ ∀ i, Continuous (p ∘ c.cell i) := by
  constructor
  · intro hp
    exact ⟨hp.comp f.hom.continuous, fun i ↦ hp.comp (c.cell i).hom.continuous⟩
  · rintro ⟨h₀, h⟩
    exact continuous_iff_isClosed.2 fun S hS ↦ (c.isClosed_iff _).2
      ⟨hS.preimage h₀, fun i ↦ hS.preimage (h i)⟩

end HomotopicalAlgebra.AttachCells

namespace HomotopicalAlgebra.RelativeCellComplex

variable {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → TopCat.{u}}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} {X Y : TopCat.{u}} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} basicCell f)

/-- A relative cell complex has the weak topology for its base and characteristic maps:
a subset is closed exactly when its preimages in the base and in every cell are closed. -/
theorem isClosed_iff (S : Set Y) :
    IsClosed S ↔ IsClosed (f ⁻¹' S) ∧ ∀ γ : c.Cells, IsClosed (γ.ι ⁻¹' S) := by
  refine ⟨fun hS ↦ ⟨hS.preimage f.hom.continuous,
    fun γ ↦ hS.preimage γ.ι.hom.continuous⟩, ?_⟩
  rintro ⟨h₀, h⟩
  apply (TopCat.isClosed_iff_of_isColimit _ c.isColimit S).2
  intro j
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    have hbot : c.incl.app ⊥ = c.isoBot.hom ≫ f := by
      simpa only [Iso.hom_inv_id_assoc] using
        congrArg (fun q ↦ c.isoBot.hom ≫ q) c.fac
    rw [hbot, ConcreteCategory.coe_comp, Set.preimage_comp]
    exact h₀.preimage c.isoBot.hom.hom.continuous
  | succ j hj ih =>
    apply ((c.attachCells j hj).isClosed_iff _).2
    refine ⟨?_, fun i ↦ h ⟨j, hj, i⟩⟩
    have hw : c.F.map (homOfLE (Order.le_succ j)) ≫ c.incl.app (Order.succ j) =
        c.incl.app j := by simp
    rw [← Set.preimage_comp, ← ConcreteCategory.coe_comp, hw]
    exact ih
  | isSuccLimit j hj ih =>
    apply (TopCat.isClosed_iff_of_isColimit _
      (c.F.isColimitOfIsWellOrderContinuous j hj) _).2
    intro ⟨k, hk⟩
    have hw : c.F.map (homOfLE hk.le) ≫ c.incl.app j = c.incl.app k := by
      simp
    simp only [PrincipalSeg.cocone_ι_app]
    rw [← Set.preimage_comp, ← ConcreteCategory.coe_comp, hw]
    exact ih k hk

/-- A map out of a relative cell complex is continuous exactly when its composite with the
base map and with every characteristic map is continuous. The target is arbitrary. -/
theorem continuous_iff {Z : Type v} [TopologicalSpace Z] (p : Y → Z) :
    Continuous p ↔ Continuous (p ∘ f) ∧ ∀ γ : c.Cells, Continuous (p ∘ γ.ι) := by
  constructor
  · intro hp
    exact ⟨hp.comp f.hom.continuous, fun γ ↦ hp.comp γ.ι.hom.continuous⟩
  · rintro ⟨h₀, h⟩
    exact continuous_iff_isClosed.2 fun S hS ↦ (c.isClosed_iff _).2
      ⟨hS.preimage h₀, fun γ ↦ hS.preimage (h γ)⟩

end HomotopicalAlgebra.RelativeCellComplex
