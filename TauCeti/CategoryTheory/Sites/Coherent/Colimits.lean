/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Pointwise colimits on a coherent site

On a finitary extensive, preregular site, the coherent sheaf condition consists of
finite product preservation and the kernel-pair equalizer condition. Thus colimits
whose colimit functor preserves finite limits can be computed on presheaves.
This extends the pointwise colimit argument of Mathlib's
`Mathlib.CategoryTheory.Sites.Coherent.ExtensiveColimits` to the coherent topology.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C A J : Type*} [Category* C] [Category* A] [Category* J]
  [Preregular C] [FinitaryExtensive C]
  [hpb : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] [HasColimitsOfShape J A]

/-- A colimit of coherent sheaves is computed pointwise when the colimit functor
in the coefficient category preserves finite limits. If only kernel pairs of effective
epimorphisms are available, supply them explicitly as `hpb`. -/
noncomputable instance createsColimitsOfShapeCoherent
    [PreservesFiniteLimits (colim (J := J) (C := A))] :
    CreatesColimitsOfShape J (sheafToPresheaf (coherentTopology C) A) where
  CreatesColimit {F} := by
    apply createsColimitOfIsSheaf
    intro c hc
    let G := F ⋙ sheafToPresheaf (coherentTopology C) A
    let e : c.pt ≅ G.flip ⋙ colim := hc.coconePointUniqueUpToIso (pointwiseIsColimit G)
    rw [Presheaf.isSheaf_of_iso_iff e]
    refine Presheaf.isSheaf_coherent_of_hasPullbacks_comp G.flip colim (h := hpb) ?_
    rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition (h := hpb)]
    constructor
    · exact ⟨fun _ ↦ preservesLimitsOfShape_of_evaluation G.flip _ fun j ↦
        inferInstanceAs (PreservesLimitsOfShape _ (F.obj j).obj)⟩
    · intro X B π _ p hp
      refine ⟨evaluationJointlyReflectsLimits _ fun j ↦ ?_⟩
      have h := (Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition (h := hpb)
        (F.obj j).obj).mp (F.obj j).property
      exact (isLimitMapConeForkEquiv _ _).symm (h.2 π p hp).some

end CategoryTheory.Sheaf
