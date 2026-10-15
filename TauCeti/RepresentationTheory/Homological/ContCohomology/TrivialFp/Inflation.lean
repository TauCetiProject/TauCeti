/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit

/-!
# Inflation with trivial `𝔽_p` coefficients

This file compares the canonical map on continuous cohomology along a quotient with explicit
inflation in degree two. The comparison identifies trivial `𝔽_p` coefficients on the quotient
with the fixed points of the subgroup action.

## Main results

* `TauCeti.cohomFpAddEquivH2_cohomFpMap_quotientMk_eq_explicitInfl2`: the canonical degree-two
  map along a quotient is explicit inflation under the cocycle comparison.
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

-- Several imported descriptions derive the additive group of `ZMod p`; the ring structure is the
-- one used by the trivial-coefficient representation and its linear cohomology.
attribute [local instance 2000] Ring.toAddCommGroup

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- Under the explicit degree-two comparison, the canonical cohomology map along a quotient is
explicit inflation after identifying the trivial coefficients with the subgroup-fixed points. -/
theorem cohomFpAddEquivH2_cohomFpMap_quotientMk_eq_explicitInfl2
    (N : Subgroup G) [N.Normal] [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
    [DistribMulAction (G ⧸ N) (ZMod p)] [ContinuousSMul (G ⧸ N) (ZMod p)]
    (htrivG : ∀ (g : G) (m : ZMod p), g • m = m)
    (htrivQ : ∀ (q : G ⧸ N) (m : ZMod p), q • m = m)
    (e : ZMod p ≃+ FixedPoints.addSubgroup N (ZMod p))
    (he : ∀ m, (e m).1 = m)
    (hequiv : ∀ (q : G ⧸ N) (m : ZMod p),
      e ((ContinuousMulEquiv.refl (G ⧸ N)) q • m) = q • e m)
    (x : cohomFp p (G ⧸ N) 2) :
    cohomFpAddEquivH2 p G htrivG
        (cohomFpMap p (ContinuousMonoidHom.quotientMk N) 2 x) =
      explicitInfl2 G (ZMod p) N
        (explicitMap2Equiv (G ⧸ N) (ZMod p) (G ⧸ N)
          (FixedPoints.addSubgroup N (ZMod p)) (ContinuousMulEquiv.refl (G ⧸ N)) e
          continuous_of_discreteTopology continuous_of_discreteTopology hequiv
          (cohomFpAddEquivH2 p (G ⧸ N) htrivQ x)) := by
  rw [cohomFpAddEquivH2_cohomFpMap p (G ⧸ N) htrivQ htrivG]
  generalize cohomFpAddEquivH2 p (G ⧸ N) htrivQ x = y
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    -- `explicitMap2_mk` is applied as a term to `explicitMap2Equiv`, whose continuity proof does
    -- not reduce to its coercion during rewriting.
    rw [explicitMap2_mk, explicitMap2Equiv_apply]
    refine Eq.trans ?_ (congrArg (explicitInfl2 G (ZMod p) N)
      (explicitMap2_mk (G ⧸ N) (ZMod p) (G ⧸ N) _ _ _ _ _ c)).symm
    rw [explicitInfl2_mk]
    -- Both cocycles read `c` at the images of the two arguments in the quotient.
    refine congrArg _ (Subtype.ext (funext fun ⟨g, h⟩ ↦ ?_))
    rw [cocyclesMap2_apply, cocyclesMap2_apply]
    exact (he _).symm.trans
      (congrArg Subtype.val (cocyclesMap2_apply (G ⧸ N) (ZMod p) (G ⧸ N) _
        (ContinuousMulEquiv.refl (G ⧸ N)) e.toAddMonoidHom _ hequiv c _ _)).symm

end TauCeti
