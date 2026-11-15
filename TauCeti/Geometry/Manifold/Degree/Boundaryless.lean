/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Homological
public import TauCeti.Geometry.Manifold.ModelTransport.LinearEquiv
public import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Smooth and homological degree across boundaryless manifold models

`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul` identifies the
pushforward of the homological fundamental class `f_*[M]` with `degreeAtRegularValue o o' f y • [N]`
when `M` and `N` are both charted directly on the same real inner product space `F`. In geometric
constructions — such as the great-circle rotation family `Sᵐ × S¹ → Sᵐ⁺¹`, whose domain carries the
product model `(𝓡 m).prod (𝓡 1)` on `ModelProd` — the source manifold `(M, I)` is boundaryless but
charted on a general model `(E, H, I)` rather than `𝓘(ℝ, F)`.

Given a boundaryless `C¹` manifold `(M, I)` and a continuous linear equivalence `L : E ≃L[ℝ] F`,
pulling an orientation `o` of `M` back along the inverse of
`TauCeti.BoundarylessModel.diffeomorphTransContinuousLinearEquiv I L 1` equips the `F`-charted copy
`BoundarylessModel (I.transContinuousLinearEquiv L) M` with an orientation
`o.toBoundarylessModel L` having the same regular values and signed preimage counts
(`Diffeomorph.isRegularValue_comp_right`,
`Diffeomorph.degreeAtRegularValue_comp_of_isOrientationPreservingAt`,
`Diffeomorph.degree_comp_of_isOrientationPreservingAt`), and pushing the fundamental class forward
by `degreeAtRegularValue o o' f y • [N]`.

## Main definitions

* `TauCeti.Manifold.Orientation.toBoundarylessModel`: transport a smooth orientation of a
  boundaryless manifold `(M, I)` along `L : E ≃L[ℝ] F` to
  `BoundarylessModel (I.transContinuousLinearEquiv L) M`.

## Main results

* `TauCeti.Manifold.Orientation.isRegularValue_toBoundarylessModel`,
  `TauCeti.Manifold.Orientation.degreeAtRegularValue_toBoundarylessModel`,
  `TauCeti.Manifold.Orientation.degree_toBoundarylessModel`: recharting the source to
  `BoundarylessModel` preserves regular values, `degreeAtRegularValue`, and `degree`.
* `TauCeti.Manifold.Orientation.degree_toBoundarylessModel_toHomologicalOrientation`,
  `Manifold.Orientation.mapFundamentalClass_toBoundarylessModel_eq_degreeAtRegularValue_smul`:
  the signed preimage count at a regular value on `(M, I)` computes the homological degree and the
  pushforward of the fundamental class of its `F`-modelled copy.
-/

public section

noncomputable section

open Function Module Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold.Orientation

section Smooth

variable {E F H M G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {ι : Type*} [Fintype ι]

/-- Transport an orientation `o` of a boundaryless `C¹` manifold `(M, I)` along a continuous linear
equivalence `L : E ≃L[ℝ] F` to the vector-space-modelled copy
`BoundarylessModel (I.transContinuousLinearEquiv L) M`, by pulling `o` back along the inverse
identity diffeomorphism. -/
def toBoundarylessModel (o : Manifold.Orientation I M ι) (L : E ≃L[ℝ] F) :
    Manifold.Orientation 𝓘(ℝ, F) (BoundarylessModel (I.transContinuousLinearEquiv L) M) ι :=
  o.pullback
    (BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) L 1).symm.contMDiff
    (fun _ ↦ (BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) L 1
      ).symm.isInvertible_mfderiv one_ne_zero)
    (o.card_eq.trans L.toLinearEquiv.finrank_eq)

@[simp]
theorem toBoundarylessModel_neg (o : Manifold.Orientation I M ι) (L : E ≃L[ℝ] F) :
    (-o).toBoundarylessModel L = -o.toBoundarylessModel L :=
  pullback_neg o _ _ _

/-- The inverse identity diffeomorphism from `BoundarylessModel (I.transContinuousLinearEquiv L) M`
to `M` preserves orientation from `o.toBoundarylessModel L` to `o` at every point. -/
theorem isOrientationPreservingAt_symm_toBoundarylessModel (o : Manifold.Orientation I M ι)
    (L : E ≃L[ℝ] F) (x : BoundarylessModel (I.transContinuousLinearEquiv L) M) :
    IsOrientationPreservingAt (o.toBoundarylessModel L) o
      (BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) L 1).symm x :=
  isOrientationPreservingAt_pullback o _ _ _ x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I 1 M] [IsManifold J 1 N] in
/-- Recharting a boundaryless manifold `(M, I)` to
`BoundarylessModel (I.transContinuousLinearEquiv L) M` preserves regular values. -/
@[simp]
theorem isRegularValue_toBoundarylessModel (L : E ≃L[ℝ] F) (f : M → N) (y : N) :
    IsRegularValue 𝓘(ℝ, F) J
        (f ∘ (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm) y ↔
      IsRegularValue I J f y := by
  simpa only [BoundarylessModel.coe_diffeomorphTransContinuousLinearEquiv_symm] using
    (BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) L 1
      ).symm.isRegularValue_comp_right one_ne_zero (f := f) (y := y)

/-- Recharting the source `(M, I)` to `BoundarylessModel (I.transContinuousLinearEquiv L) M`
leaves `degreeAtRegularValue` unchanged. -/
@[simp]
theorem degreeAtRegularValue_toBoundarylessModel (o : Manifold.Orientation I M ι)
    (oN : Manifold.Orientation J N ι) (L : E ≃L[ℝ] F) (f : M → N) (y : N) :
    degreeAtRegularValue (o.toBoundarylessModel L) oN
        (f ∘ (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm) y =
      degreeAtRegularValue o oN f y := by
  simpa only [BoundarylessModel.coe_diffeomorphTransContinuousLinearEquiv_symm] using
    (BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) L 1
      ).symm.degreeAtRegularValue_comp_of_isOrientationPreservingAt one_ne_zero oN
      (o.isOrientationPreservingAt_symm_toBoundarylessModel L) f y

/-- Recharting the source `(M, I)` to `BoundarylessModel (I.transContinuousLinearEquiv L) M`
leaves `degree` unchanged. -/
@[simp]
theorem degree_toBoundarylessModel (o : Manifold.Orientation I M ι)
    (oN : Manifold.Orientation J N ι) (L : E ≃L[ℝ] F) (f : M → N) :
    degree (o.toBoundarylessModel L) oN
        (f ∘ (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm) =
      degree o oN f := by
  simpa only [BoundarylessModel.coe_diffeomorphTransContinuousLinearEquiv_symm] using
    (BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) L 1
      ).symm.degree_comp_of_isOrientationPreservingAt one_ne_zero oN
      (o.isOrientationPreservingAt_symm_toBoundarylessModel L) f

end Smooth

section Homological

variable {E H M F N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [T2Space N] [IsManifold 𝓘(ℝ, F) 1 N]
  {n : ℕ} (hF : finrank ℝ F = n + 1)

/-- **Homological degree across boundaryless models.** For a proper map `f : M → N` from a
boundaryless `C¹` manifold `(M, I)` to a preconnected `C¹` manifold `N` modelled on an inner product
space `F` of dimension `n + 1`, the homological degree of `f` on the recharted copy
`BoundarylessModel (I.transContinuousLinearEquiv L) M` equals `degreeAtRegularValue o o' f y` at
any regular value `y` of `f`. -/
theorem degree_toBoundarylessModel_toHomologicalOrientation [PreconnectedSpace N]
    (o : Manifold.Orientation I M (Fin (n + 1)))
    (o' : Manifold.Orientation 𝓘(ℝ, F) N (Fin (n + 1))) (L : E ≃L[ℝ] F)
    {f : C(M, N)} (hf : IsProperMap f) {y : N} (hy : IsRegularValue I 𝓘(ℝ, F) f y) :
    ((o.toBoundarylessModel L).toHomologicalOrientation hF).degree
        (o'.toHomologicalOrientation hF) hF
        (f.comp ⟨(BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm,
          (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm.continuous⟩) =
      degreeAtRegularValue o o' f y := by
  let ψ : C(BoundarylessModel (I.transContinuousLinearEquiv L) M, M) :=
    ⟨(BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm,
      (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm.continuous⟩
  have hproper : IsProperMap (f.comp ψ) :=
    hf.comp (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm.isProperMap
  have hy' : IsRegularValue 𝓘(ℝ, F) 𝓘(ℝ, F) (f.comp ψ) y :=
    (isRegularValue_toBoundarylessModel (J := 𝓘(ℝ, F)) L f y).2 hy
  rw [degree_toHomologicalOrientation hF (o.toBoundarylessModel L) o' hproper hy']
  exact degreeAtRegularValue_toBoundarylessModel o o' L f y

/-- **Fundamental-class pushforward across boundaryless models.** For a continuous map `f : M → N`
from a compact oriented boundaryless `C¹` manifold `(M, I, o)` to a compact preconnected oriented
`C¹` manifold `(N, 𝓘(ℝ, F), o')`, recharting `M` via `L : E ≃L[ℝ] F` pushes the fundamental class
forward to `degreeAtRegularValue o o' f y • [N]` at any regular value `y` of `f`. -/
theorem mapFundamentalClass_toBoundarylessModel_eq_degreeAtRegularValue_smul
    [CompactSpace M] [CompactSpace N] [PreconnectedSpace N]
    (o : Manifold.Orientation I M (Fin (n + 1)))
    (o' : Manifold.Orientation 𝓘(ℝ, F) N (Fin (n + 1))) (L : E ≃L[ℝ] F)
    {f : C(M, N)} {y : N} (hy : IsRegularValue I 𝓘(ℝ, F) f y) :
    ((o.toBoundarylessModel L).toHomologicalOrientation hF).mapFundamentalClass hF
        (f.comp ⟨(BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm,
          (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm.continuous⟩) =
      degreeAtRegularValue o o' f y • (o'.toHomologicalOrientation hF).fundamentalClass hF := by
  have hy' : IsRegularValue 𝓘(ℝ, F) 𝓘(ℝ, F)
      (f ∘ (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) M).symm) y :=
    (isRegularValue_toBoundarylessModel (J := 𝓘(ℝ, F)) L f y).2 hy
  rw [mapFundamentalClass_eq_degreeAtRegularValue_smul hF (o.toBoundarylessModel L) o' hy']
  congr 1
  exact degreeAtRegularValue_toBoundarylessModel o o' L f y

end Homological

end TauCeti.Manifold.Orientation
