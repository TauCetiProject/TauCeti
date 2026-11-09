/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.CategoryTheory.Limits.Over
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Closed

/-!
# Kan lifting for based pullback–hom maps

For a based monomorphism `i : A ⟶ X` and a based map `p : E ⟶ B` whose underlying
map is a Kan fibration, the corner map
`Map_*(X,E) ⟶ Map_*(A,E) ×[Map_*(A,B)] Map_*(X,B)` is a Kan fibration.
In particular restriction along `i` is a fibration when the target is Kan.

The corner is Mathlib's native `Functor.PullbackObjObj` for the pointed internal
hom, not a new mapping-space carrier. The proof transfers unpointed corner lifts:
the prescribed restriction to `A` forces the lift to preserve the basepoint.
This is the relative mapping-space lifting statement used in simplicial model
structures.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter I.
* The unpointed lifting theorem is `SSet.fibration_pullbackObjObjπ`.
-/

public section

open CategoryTheory CategoryTheory.ConcreteCategory MonoidalCategory MonoidalClosed Limits
  HomotopicalAlgebra

open scoped Simplicial

universe u

namespace TauCeti.PointedSSet

open SSet.modelCategoryQuillen

variable {A X E B : PointedSSet.{u}} (i : A ⟶ X) (p : E ⟶ B)

/-- An unpointed lift of the corner square, whose two components are the prescribed based
families, corestricts to a based lift: restriction to `A` fixes the basepoint. -/
private lemma hasLift_of_unpointedLift
    (P : MonoidalClosed.internalHom.PullbackObjObj i p) {K L : SSet.{u}} (j : K ⟶ L)
    {a : K ⟶ (basedMaps X E).toSSet} {b : L ⟶ P.pt.right}
    (sq : CommSq a j P.π.right b) (u : L ⟶ (CategoryTheory.ihom X.right).obj E.right)
    (hu : j ≫ u = a ≫ (basedMaps X E).ι)
    (hlA : u ≫ (MonoidalClosed.pre i.right).app E.right =
      b ≫ P.fst.right ≫ (basedMaps A E).ι)
    (hlB : u ≫ (CategoryTheory.ihom X.right).map p.right =
      b ≫ P.snd.right ≫ (basedMaps X B).ι) : sq.HasLift := by
  dsimp only [MonoidalClosed.internalHom] at P
  have hfst := congrArg Under.Hom.right P.π_fst
  have hsnd := congrArg Under.Hom.right P.π_snd
  simp only [Under.comp_right] at hfst hsnd
  let hP := P.isPullback.map (Under.forget (Δ[0] : SSet.{u}))
  -- Restriction to A fixes the basepoint, so the unpointed lift lands in based maps.
  have hl : SSet.Subcomplex.range u ≤ basedMaps X E := by
    rw [range_le_basedMaps_iff, ← Under.w i, MonoidalClosed.pre_map, NatTrans.comp_app]
    rw [← Category.assoc, hlA]
    erw [Category.assoc, Category.assoc, basedMaps_ι_comp_pre, comp_pointRestriction]
    exact comp_pointRestriction E b
  -- Corestrict the lift and check its two equations through the subcomplex inclusions.
  let l := SSet.Subcomplex.lift u hl
  refine ⟨⟨l, ?_, ?_⟩⟩
  · apply (cancel_mono (basedMaps X E).ι).1
    dsimp only [l]
    erw [Category.assoc, SSet.Subcomplex.lift_ι]
    exact hu
  · apply hP.hom_ext
    · apply (cancel_mono (basedMaps A E).ι).1
      dsimp only [Under.forget_map, l]
      erw [Category.assoc, Category.assoc, reassoc_of% hfst, pre_right_comp_ι,
        ← Category.assoc, SSet.Subcomplex.lift_ι]
      erw [Category.assoc]
      exact hlA
    · apply (cancel_mono (basedMaps X B).ι).1
      dsimp only [Under.forget_map, l]
      erw [Category.assoc, Category.assoc, reassoc_of% hsnd, ihom_map_right_comp_ι,
        ← Category.assoc, SSet.Subcomplex.lift_ι]
      erw [Category.assoc]
      exact hlB

/-- Lifting for an unpointed corner transfers to the corresponding based corner.
The prescribed restriction along a based map already fixes the basepoint. -/
lemma hasLiftingProperty_pullbackObjObjπ
    (Q : MonoidalClosed.internalHom.PullbackObjObj i.right p.right)
    (P : MonoidalClosed.internalHom.PullbackObjObj i p)
    {K L : SSet.{u}} (j : K ⟶ L) [HasLiftingProperty j Q.π] :
    HasLiftingProperty j P.π.right := by
  have hjQ : HasLiftingProperty j Q.π := inferInstance
  -- Normalize the internal-hom bifunctors to the chosen pointed and unpointed right adjoints.
  dsimp only [MonoidalClosed.internalHom] at Q P
  -- Fix the source carrier explicitly so rewriting need not unfold a closed-structure instance.
  change HasLiftingProperty j (P.π.right : (basedMaps X E).toSSet ⟶ P.pt.right)
  have hfst := congrArg Under.Hom.right P.π_fst
  have hsnd := congrArg Under.Hom.right P.π_snd
  simp only [Under.comp_right] at hfst hsnd
  let hP := P.isPullback.map (Under.forget (Δ[0] : SSet.{u}))
  constructor
  intro a b sq
  -- Include both prescribed based families into the unpointed corner.
  -- Extended rewriting is needed because its native closed-structure objects and the
  -- based-mapping subcomplex carriers are not definitionally equal at implicit transparency.
  let b' : L ⟶ Q.pt := Q.isPullback.lift
    (b ≫ P.fst.right ≫ (basedMaps A E).ι)
    (b ≫ P.snd.right ≫ (basedMaps X B).ι) (by
      have h := congrArg (fun f ↦ b ≫ f.right ≫ (basedMaps A B).ι) P.isPullback.w
      simp only [Under.comp_right] at h
      erw [Category.assoc, Category.assoc, ihom_map_right_comp_ι,
        pre_right_comp_ι] at h
      erw [Category.assoc, Category.assoc]
      exact h)
  have sq' : CommSq (a ≫ (basedMaps X E).ι) j Q.π b' := by
    constructor
    apply Q.hom_ext
    · simp only [Category.assoc, Q.π_fst, b', IsPullback.lift_fst]
      have h := congrArg (fun f ↦ f ≫ P.fst.right ≫ (basedMaps A E).ι) sq.w
      erw [Category.assoc, Category.assoc, reassoc_of% hfst, pre_right_comp_ι] at h
      erw [Category.assoc]
      exact h
    · simp only [Category.assoc, Q.π_snd, b', IsPullback.lift_snd]
      have h := congrArg (fun f ↦ f ≫ P.snd.right ≫ (basedMaps X B).ι) sq.w
      erw [Category.assoc, Category.assoc, reassoc_of% hsnd, ihom_map_right_comp_ι] at h
      erw [Category.assoc]
      exact h
  have : sq'.HasLift := hjQ.sq_hasLift sq'
  have hlA : sq'.lift ≫ (MonoidalClosed.pre i.right).app E.right =
      b ≫ P.fst.right ≫ (basedMaps A E).ι := by
    erw [← Q.π_fst, ← Category.assoc, sq'.fac_right]
    exact Q.isPullback.lift_fst _ _ _
  have hlB : sq'.lift ≫ (CategoryTheory.ihom X.right).map p.right =
      b ≫ P.snd.right ≫ (basedMaps X B).ι := by
    erw [← Q.π_snd, ← Category.assoc, sq'.fac_right]
    exact Q.isPullback.lift_snd _ _ _
  exact hasLift_of_unpointedLift i p P j sq sq'.lift sq'.fac_left hlA hlB

/-- The based pullback–hom corner of a monomorphism and a Kan fibration is a Kan
fibration on underlying simplicial sets. -/
theorem fibration_pullbackObjObjπ [Mono i.right] [Fibration p.right]
    (P : MonoidalClosed.internalHom.PullbackObjObj i p) : Fibration P.π.right := by
  let Q := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i.right p.right
  have : Fibration Q.π := SSet.fibration_pullbackObjObjπ Q
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro K L j hj
  have : HasLiftingProperty j Q.π :=
    (SSet.modelCategoryQuillen.fibration_iff Q.π).1 inferInstance j hj
  exact hasLiftingProperty_pullbackObjObjπ i p Q P j

/-- Restriction of based mapping spaces along a monomorphism is a Kan fibration
when the target is Kan. -/
instance fibration_pre (i : A ⟶ X) [Mono i.right] (E : PointedSSet.{u})
    [SSet.KanComplex E.right] : Fibration ((MonoidalClosed.pre i).app E).right := by
  have hT := terminalIsTerminal.isTerminalObj (Under.forget (Δ[0] : SSet.{u}))
    (⊤_ PointedSSet.{u})
  have : Fibration (terminal.from E).right :=
    (isFibrant_iff_of_isTerminal _ hT).1 inferInstance
  exact fibration_pullbackObjObjπ i (terminal.from E)
    (Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom i (terminal.from E)
      terminalIsTerminal)

end TauCeti.PointedSSet
