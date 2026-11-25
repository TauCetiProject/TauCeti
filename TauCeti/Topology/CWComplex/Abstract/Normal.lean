/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Limits.Basic
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.Separation.Sigma

/-!
# Relative CW complexes on normal spaces are normal

For a morphism `f : X ⟶ Y` of `TopCat`, `c : TopCat.RelativeCWComplex f` presents `Y` as the
sequential colimit of stages starting at `X`, each obtained by attaching disks along boundary
spheres. This file proves that `Y` is normal when `X` is (`TopCat.RelativeCWComplex.normalSpace`),
and hence every categorical CW complex is normal (`TopCat.CWComplex.normalSpace`). At each step,
the coproduct of attached disks is normal via `TopCat.sigmaCofanIsColimit` and `Sigma.normalSpace`,
so `TauCeti.TopCat.normalSpace_of_isPushout` (`HomotopicalAlgebra.AttachCells.normalSpace`) and
`TauCeti.TopCat.normalSpace_of_isColimit` (`HomotopicalAlgebra.RelativeCellComplex.normalSpace`)
propagate normality along the closed stage inclusions.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Proposition A.3.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press, 1990.
-/

public section

open CategoryTheory Limits MorphismProperty Topology

universe t u

namespace HomotopicalAlgebra

variable {α : Type t} {A B : α → TopCat.{u}} {g : ∀ a, A a ⟶ B a} {X₁ X₂ : TopCat.{u}}
  {f : X₁ ⟶ X₂}

/-- Attaching cells to a normal space gives a normal space, provided the cells are closed
embeddings into normal spaces. -/
theorem AttachCells.normalSpace (a : AttachCells.{u} g f) [NormalSpace X₁] [∀ k, NormalSpace (B k)]
    (hg : ∀ i, IsClosedEmbedding (g (a.π i))) : NormalSpace X₂ := by
  let e := TopCat.homeoOfIso
    (a.isColimit₂.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit fun i ↦ B (a.π i)))
  -- The carrier of `TopCat.sigmaCofan` is the sigma type, which instance search does not see.
  have : NormalSpace (TopCat.sigmaCofan fun i ↦ B (a.π i)).pt :=
    inferInstanceAs (NormalSpace (Σ i, B (a.π i)))
  have : NormalSpace a.cofan₂.pt := e.symm.normalSpace
  have hm : IsClosedEmbedding a.m := (TauCeti.TopCat.isClosedEmbedding_iff _).1 <|
    IsStableUnderColimitsOfShape.condition _ _ _ _ a.isColimit₁ a.isColimit₂
      (Discrete.natTrans fun i ↦ g (a.π i.as))
      (fun i ↦ (TauCeti.TopCat.isClosedEmbedding_iff _).2 (hg i.as)) a.m (fun i ↦ a.hm i.as)
  exact TauCeti.TopCat.normalSpace_of_isPushout a.isPushout hm

namespace RelativeCellComplex

variable {α : ℕ → Type t} {A B : (n : ℕ) → α n → TopCat.{u}}
  {basicCell : (n : ℕ) → (i : α n) → A n i ⟶ B n i} {X Y : TopCat.{u}} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u} basicCell f)

/-- A sequential relative cell complex `f : X ⟶ Y` in `TopCat` on a normal space `X` has a normal
target `Y`, provided its basic cells are closed embeddings into normal spaces. -/
theorem normalSpace [NormalSpace X] [∀ n i, NormalSpace (B n i)]
    (hc : ∀ s : c.Cells, IsClosedEmbedding (basicCell s.j s.i)) : NormalSpace Y := by
  have _ (n : ℕ) : NormalSpace (c.F.obj n) := by
    induction n with
    | zero => exact (TopCat.homeoOfIso c.isoBot).symm.normalSpace
    | succ n _ => exact (c.attachCells n (not_isMax n)).normalSpace fun i ↦ hc ⟨n, not_isMax n, i⟩
  exact TauCeti.TopCat.normalSpace_of_isColimit
    (fun n ↦ c.isClosedEmbedding_map hc n.le_succ) c.isColimit

end RelativeCellComplex

end HomotopicalAlgebra

namespace TopCat

/-- **A relative CW complex on a normal space is normal.** -/
theorem RelativeCWComplex.normalSpace {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f)
    [NormalSpace X] : NormalSpace Y :=
  HomotopicalAlgebra.RelativeCellComplex.normalSpace c
    fun s ↦ TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion s.j

/-- **A CW complex is normal.** -/
theorem CWComplex.normalSpace {X : TopCat.{u}} (c : CWComplex X) : NormalSpace X :=
  RelativeCWComplex.normalSpace c

end TopCat
