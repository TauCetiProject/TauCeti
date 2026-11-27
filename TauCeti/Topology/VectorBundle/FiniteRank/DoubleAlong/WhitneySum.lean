/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.FiniteRank.DoubleAlong

/-!
# Doubling a Whitney sum

For complex cores `C` and `D` real along `A ⊆ X`, the Whitney sum `C ⊕ D` is real along `A`
(`FiniteRankBundleCore.IsRealAlong.whitneySum`): its transitions are block diagonal with the
transitions of `C` and `D` as blocks. In terms of bundle pairs, the real subbundle of
`(C ⊕ D, F ⊕ F')` is the sum of the real subbundles. The projections and inclusions of the Whitney
sum commute with coordinatewise conjugation at every point, since they are the coordinate blocks.

Doubling commutes with Whitney sums (`doubleAlongWhitneySumIso`): the double of `C ⊕ D` is the
Whitney sum of the doubles, by the identity in coordinates. This reduces the additivity of the
Maslov index under direct sums of bundle pairs to the Whitney sum formula for the first Chern class
of the doubles.
-/

public section

noncomputable section

open Bundle CategoryTheory

namespace TauCeti.FiniteRankBundleCore

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X} {C D : FiniteRankBundleCore ℂ X}

/-- The Whitney sum of cores real along `A` is real along `A`: its transitions are block diagonal
with the transitions of the summands as blocks. -/
theorem IsRealAlong.whitneySum (hC : C.IsRealAlong A) (hD : D.IsRealAlong A) :
    (whitneySum C D).IsRealAlong A :=
  -- The vectors of the Whitney sum are concatenated coordinate vectors (`rank_whitneySum`).
  isRealAlong_iff_coordChange_star.2 fun i j x hx hi hj (v : Fin (C.rank + D.rank) → ℂ) ↦
    (splitCoords (𝕜 := ℂ) C.rank D.rank).injective <| by
      refine (splitCoords_coordChange_whitneySum C D i j x (star v)).trans (Eq.trans ?_
        ((congrArg star (splitCoords_coordChange_whitneySum C D i j x v)).symm.trans
          (splitCoords_star _).symm))
      rw [splitCoords_star, Prod.fst_star, Prod.snd_star, hC.coordChange_star hx hi.1 hj.1,
        hD.coordChange_star hx hi.2 hj.2, Prod.star_def]

variable (C D)

/-- The first projection of a Whitney sum commutes with coordinatewise conjugation. -/
theorem fiberMap_whitneyFst_star (x : X) (v : Fin (whitneySum C D).rank → ℂ) :
    (whitneyFst C D).fiberMap x (star v) = star ((whitneyFst C D).fiberMap x v) := by
  rw [fiberMap_whitneyFst]
  exact congrArg Prod.fst (splitCoords_star v)

/-- The second projection of a Whitney sum commutes with coordinatewise conjugation. -/
theorem fiberMap_whitneySnd_star (x : X) (v : Fin (whitneySum C D).rank → ℂ) :
    (whitneySnd C D).fiberMap x (star v) = star ((whitneySnd C D).fiberMap x v) := by
  rw [fiberMap_whitneySnd]
  exact congrArg Prod.snd (splitCoords_star v)

variable {C D} (hC : C.IsRealAlong A) (hD : D.IsRealAlong A)

/-- The comparison map from the double of a Whitney sum to the Whitney sum of the doubles: the
pairing of the doubled projections. -/
def doubleAlongWhitneySumHom :
    (whitneySum C D).doubleAlong (hC.whitneySum hD) ⟶
      whitneySum (C.doubleAlong hC) (D.doubleAlong hD) :=
  whitneyLift (doubleAlongMap (hC.whitneySum hD) hC (whitneyFst C D)
      fun a _ ↦ fiberMap_whitneyFst_star C D a)
    (doubleAlongMap (hC.whitneySum hD) hD (whitneySnd C D) fun a _ ↦ fiberMap_whitneySnd_star C D a)

/-- In coordinates, the comparison map from the double of a Whitney sum to the Whitney sum of the
doubles is the identity. -/
theorem fiberMap_doubleAlongWhitneySumHom (y : DoubleAlong A) :
    (doubleAlongWhitneySumHom hC hD).fiberMap y =
      ContinuousLinearMap.id ℂ (Fin (C.rank + D.rank) → ℂ) := by
  refine ContinuousLinearMap.ext fun v ↦ (splitCoords (𝕜 := ℂ) (C.doubleAlong hC).rank
    (D.doubleAlong hD).rank).injective ?_
  rw [doubleAlongWhitneySumHom]
  refine (splitCoords_fiberMap_whitneyLift (doubleAlongMap (hC.whitneySum hD) hC (whitneyFst C D)
      fun a _ ↦ fiberMap_whitneyFst_star C D a)
    (doubleAlongMap (hC.whitneySum hD) hD (whitneySnd C D) fun a _ ↦ fiberMap_whitneySnd_star C D a)
    y v).trans ?_
  rw [fiberMap_doubleAlongMap_of_forall_star _ _ _ _ (fiberMap_whitneyFst_star C D),
    fiberMap_doubleAlongMap_of_forall_star _ _ _ _ (fiberMap_whitneySnd_star C D),
    fiberMap_whitneyFst, fiberMap_whitneySnd]
  -- Both sides are the two blocks of `v`.
  rfl

/-- **Doubling commutes with Whitney sums.** The double of `C ⊕ D` is the Whitney sum of the
doubles of `C` and `D`, by the identity in coordinates. -/
def doubleAlongWhitneySumIso :
    (whitneySum C D).doubleAlong (hC.whitneySum hD) ≅
      whitneySum (C.doubleAlong hC) (D.doubleAlong hD) :=
  isoOfContinuousEquiv (fun _ ↦ ContinuousLinearEquiv.refl ℂ (Fin (C.rank + D.rank) → ℂ))
    ((doubleAlongWhitneySumHom hC hD).continuous_totalSpaceMap.congr fun ⟨y, v⟩ ↦ by
      rw [VectorBundleCore.CoordinateHom.totalSpaceMap_mk, fiberMap_doubleAlongWhitneySumHom]
      -- Both sides are `⟨y, v⟩`.
      rfl)

@[simp]
theorem fiberMap_doubleAlongWhitneySumIso_hom (y : DoubleAlong A) :
    (doubleAlongWhitneySumIso hC hD).hom.fiberMap y =
      ContinuousLinearMap.id ℂ (Fin (C.rank + D.rank) → ℂ) :=
  fiberMap_isoOfContinuousEquiv_hom _ _ y

@[simp]
theorem fiberMap_doubleAlongWhitneySumIso_inv (y : DoubleAlong A) :
    (doubleAlongWhitneySumIso hC hD).inv.fiberMap y =
      ContinuousLinearMap.id ℂ (Fin (C.rank + D.rank) → ℂ) :=
  fiberMap_isoOfContinuousEquiv_inv _ _ y

end TauCeti.FiniteRankBundleCore
