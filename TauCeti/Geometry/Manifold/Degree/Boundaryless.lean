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

This file bridges that model gap in two steps:

1. Precomposing any map `f : M → N` with a `C^n` diffeomorphism `Φ : M' ≃ₘ^n⟮I', I⟯ M` (`n ≠ 0`)
   preserves regular points and regular values (`Diffeomorph.isRegularPoint_comp_right`,
   `Diffeomorph.isRegularValue_comp_right`), multiplies orientation signs
   (`Diffeomorph.orientationSign_comp_right`), and leaves `degreeAtRegularValue` and `degree`
   unchanged when `Φ` preserves orientation (and negates them when `Φ` reverses orientation).
2. Given a boundaryless `C¹` manifold `(M, I)` and a continuous linear equivalence `L : E ≃L[ℝ] F`,
   pulling an orientation `o` of `M` back along the inverse of
   `BoundarylessModel.diffeomorphTransContinuousLinearEquiv I L 1` equips the `F`-charted copy
   `BoundarylessModel (I.transContinuousLinearEquiv L) M` with an orientation
   `o.toBoundarylessModel L` having the same signed preimage counts and pushing the fundamental
   class forward by `degreeAtRegularValue o o' f y • [N]`.

## Main definitions

* `TauCeti.Manifold.Orientation.toBoundarylessModel`: transport a smooth orientation of a
  boundaryless manifold `(M, I)` along `L : E ≃L[ℝ] F` to
  `BoundarylessModel (I.transContinuousLinearEquiv L) M`.

## Main results

* `Diffeomorph.isRegularPoint_comp_right`, `Diffeomorph.isRegularValue_comp_right`: invariance of
  regular points and regular values under precomposition by a diffeomorphism.
* `Diffeomorph.degreeAtRegularValue_comp_of_isOrientationPreservingAt`,
  `Diffeomorph.degree_comp_of_isOrientationPreservingAt`: invariance of `degreeAtRegularValue` and
  `degree` under an orientation-preserving diffeomorphism of the source.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_toBoundarylessModel`: recharting the source to
  `BoundarylessModel` preserves `degreeAtRegularValue`.
* `Manifold.Orientation.mapFundamentalClass_toBoundarylessModel_eq_degreeAtRegularValue_smul`:
  the signed preimage count at a regular value on `(M, I)` computes the pushforward of the
  fundamental class of its `F`-modelled copy.
-/

public section

noncomputable section

open Function Module Set
open scoped ContDiff Manifold

/-! ### Invariance of regularity and degree under source diffeomorphisms -/

namespace Diffeomorph

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

/-- Precomposing a map with a `C^n` diffeomorphism (`n ≠ 0`) preserves regular points. No manifold
smoothness or finite-dimensionality assumption is needed. -/
theorem isRegularPoint_comp_right (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0) {f : M → N} {x : M'} :
    TauCeti.IsRegularPoint I' J (f ∘ Φ) x ↔ TauCeti.IsRegularPoint I J f (Φ x) := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ h.comp (TauCeti.isRegularPoint_iff.2 (Φ.isInvertible_mfderiv hn).surjective)⟩
  have hcomp : ((f ∘ Φ) ∘ Φ.symm) = f := funext fun z ↦ congrArg f (Φ.apply_symm_apply z)
  rw [← hcomp]
  have hx : TauCeti.IsRegularPoint I' J (f ∘ Φ) (Φ.symm (Φ x)) := by
    simpa only [Φ.symm_apply_apply] using h
  exact hx.comp (TauCeti.isRegularPoint_iff.2 (Φ.symm.isInvertible_mfderiv hn).surjective)

/-- Precomposing a map with a `C^n` diffeomorphism (`n ≠ 0`) preserves regular values. -/
theorem isRegularValue_comp_right (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0) {f : M → N} {y : N} :
    TauCeti.IsRegularValue I' J (f ∘ Φ) y ↔ TauCeti.IsRegularValue I J f y := by
  rw [TauCeti.isRegularValue_iff, TauCeti.isRegularValue_iff]
  refine ⟨fun h z hz ↦ ?_, fun h x hx ↦ (Φ.isRegularPoint_comp_right hn).2 (h (Φ x) hx)⟩
  have hz' : (f ∘ Φ) (Φ.symm z) = y := by simpa only [comp_apply, Φ.apply_symm_apply] using hz
  simpa only [Φ.apply_symm_apply] using (Φ.isRegularPoint_comp_right hn).1 (h (Φ.symm z) hz')

end Regularity

section Degree

open TauCeti TauCeti.Manifold.Orientation

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {ι : Type*} [Fintype ι] {n : ℕ∞ω}

/-- Precomposing an arbitrary map `f : M → N` with a `C^n` diffeomorphism `Φ` (`n ≠ 0`) multiplies
the orientation sign by that of `Φ`. Where `f` is not differentiable at `Φ x`, neither `f` nor
`f ∘ Φ` has invertible derivative, so both sides vanish. -/
theorem orientationSign_comp_right (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    (o' : Manifold.Orientation I' M' ι) (o : Manifold.Orientation I M ι)
    (oN : Manifold.Orientation J N ι) (f : M → N) (x : M') :
    orientationSign o' oN (f ∘ Φ) x =
      orientationSign o oN f (Φ x) * orientationSign o' o Φ x := by
  by_cases hf : MDifferentiableAt I J f (Φ x)
  · exact orientationSign_comp hf (Φ.mdifferentiable hn x)
  · have hnf : ¬(mfderiv I J f (Φ x)).IsInvertible :=
      fun hinv ↦ hf (mdifferentiableAt_of_isInvertible_mfderiv hinv)
    have hncomp : ¬(mfderiv I' J (f ∘ Φ) x).IsInvertible := by
      intro hinv
      have hd : MDifferentiableAt I J ((f ∘ Φ) ∘ Φ.symm) (Φ x) := by
        have hx : MDifferentiableAt I' J (f ∘ Φ) (Φ.symm (Φ x)) := by
          simpa only [Φ.symm_apply_apply] using mdifferentiableAt_of_isInvertible_mfderiv hinv
        exact hx.comp (Φ x) (Φ.symm.mdifferentiable hn (Φ x))
      have heq : (f ∘ Φ) ∘ Φ.symm = f := funext fun z ↦ congrArg f (Φ.apply_symm_apply z)
      rw [heq] at hd
      exact hf hd
    rw [orientationSign_of_not_isInvertible hncomp, orientationSign_of_not_isInvertible hnf,
      zero_mul]

/-- Precomposing with an orientation-preserving `C^n` diffeomorphism (`n ≠ 0`) leaves
`degreeAtRegularValue` unchanged at every point of `N`. -/
theorem degreeAtRegularValue_comp_of_isOrientationPreservingAt (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    {o' : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (oN : Manifold.Orientation J N ι) (ho : ∀ x, IsOrientationPreservingAt o' o Φ x)
    (f : M → N) (y : N) :
    degreeAtRegularValue o' oN (f ∘ Φ) y = degreeAtRegularValue o oN f y := by
  rw [degreeAtRegularValue_def, degreeAtRegularValue_def]
  have hbij : BijOn Φ ((f ∘ Φ) ⁻¹' {y}) (f ⁻¹' {y}) :=
    ⟨fun _ hx ↦ hx, Φ.injective.injOn,
      fun z hz ↦ ⟨Φ.symm z, by simpa only [mem_preimage, comp_apply, Φ.apply_symm_apply] using hz,
        Φ.apply_symm_apply z⟩⟩
  refine finsum_mem_eq_of_bijOn Φ hbij fun x _ ↦ ?_
  rw [Φ.orientationSign_comp_right hn o' o oN f x,
    orientationSign_of_isOrientationPreservingAt (ho x), mul_one]

/-- Precomposing with an orientation-reversing `C^n` diffeomorphism (`n ≠ 0`) negates
`degreeAtRegularValue` at every point of `N`. -/
theorem degreeAtRegularValue_comp_of_isOrientationReversingAt (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    {o' : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (oN : Manifold.Orientation J N ι) (ho : ∀ x, IsOrientationReversingAt o' o Φ x)
    (f : M → N) (y : N) :
    degreeAtRegularValue o' oN (f ∘ Φ) y = -degreeAtRegularValue o oN f y := by
  have h := Φ.degreeAtRegularValue_comp_of_isOrientationPreservingAt hn (o' := -o') (o := o) oN
    (fun x ↦ (isOrientationPreservingAt_neg_left o' o Φ x).2 (ho x)) f y
  rwa [degreeAtRegularValue_neg_left, neg_eq_iff_eq_neg] at h

/-- Precomposing with an orientation-preserving `C^n` diffeomorphism (`n ≠ 0`) preserves
`degree`. -/
theorem degree_comp_of_isOrientationPreservingAt (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    {o' : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (oN : Manifold.Orientation J N ι) (ho : ∀ x, IsOrientationPreservingAt o' o Φ x)
    (f : M → N) :
    degree o' oN (f ∘ Φ) = degree o oN f := by
  classical
  rw [degree_def, degree_def]
  simp_rw [Φ.degreeAtRegularValue_comp_of_isOrientationPreservingAt hn oN ho]
  have hp : (fun y ↦ IsRegularValue I' J (f ∘ Φ) y) = fun y ↦ IsRegularValue I J f y :=
    funext fun _ ↦ propext (Φ.isRegularValue_comp_right hn)
  exact congrArg
    (fun P : N → Prop ↦ if h : ∃ y, P y then degreeAtRegularValue o oN f h.choose else 0) hp

/-- Precomposing with an orientation-reversing `C^n` diffeomorphism (`n ≠ 0`) negates `degree`. -/
theorem degree_comp_of_isOrientationReversingAt (Φ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0)
    {o' : Manifold.Orientation I' M' ι} {o : Manifold.Orientation I M ι}
    (oN : Manifold.Orientation J N ι) (ho : ∀ x, IsOrientationReversingAt o' o Φ x)
    (f : M → N) :
    degree o' oN (f ∘ Φ) = -degree o oN f := by
  have h := Φ.degree_comp_of_isOrientationPreservingAt hn (o' := -o') (o := o) oN
    (fun x ↦ (isOrientationPreservingAt_neg_left o' o Φ x).2 (ho x)) f
  rwa [degree_neg_left, neg_eq_iff_eq_neg] at h

end Degree

end Diffeomorph

/-! ### Transporting orientations and degree to `BoundarylessModel` -/

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
