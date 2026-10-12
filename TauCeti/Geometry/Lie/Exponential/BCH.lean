/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Germ
public import TauCeti.Geometry.Lie.Exponential.LocalInverse
public import TauCeti.Geometry.Lie.Exponential.Smoothness
public import TauCeti.Geometry.Lie.Functor

/-!
# The local Baker--Campbell--Hausdorff germ of a Lie group

For a finite-dimensional real Lie group `G` with Lie algebra `𝔤` of left-invariant derivations,
the exponential map is a local diffeomorphism at `0`, with local inverse `lieLog`. So near the
origin of `𝔤 × 𝔤` the product `lieExp X * lieExp Y` has a logarithm, and the germ at `(0, 0)` of

`(X, Y) ↦ lieLog (lieExp X * lieExp Y)`

is the **local Baker--Campbell--Hausdorff germ** `TauCeti.lieLocalBCH I G`: the local group law
of `G` read in the exponential chart at the identity. Using a germ records that only its values
near the origin carry meaning; those depend on no choice, since the germ is the unique one tending
to zero whose exponential is the product of the two exponentials.

The germ is smooth at the origin, takes the value zero there, restricts to the identity on each
coordinate axis, has derivative `(X, Y) ↦ X + Y` at the origin, and is natural under smooth
homomorphisms: a smooth homomorphism `φ : G → G'` carries the local BCH germ of `G` to that of
`G'` through its Lie map `lieMap φ`. For the units
of a finite-dimensional real normed algebra it is the germ of the Banach-algebra series
(`TauCeti.lieLocalBCH_eq_unitsLocalBCH` in `TauCeti/Geometry/Lie/Exponential/Units/BCH.lean`).

## Main declarations

* `TauCeti.lieLocalBCH`: the local Baker--Campbell--Hausdorff germ of a Lie group.
* `TauCeti.lieLocalBCH_map_lieExp`: its exponential is the product of the two exponentials.
* `TauCeti.eq_lieLocalBCH_of_tendsto_of_map_lieExp_eq`: uniqueness among germs tending to zero
  with that exponential image.
* `TauCeti.lieLocalBCH_sliceLeft`, `TauCeti.lieLocalBCH_sliceRight`: the endpoint laws.
* `TauCeti.contDiffAt_lieLocalBCH_representative`: its representative is smooth at the origin.
* `TauCeti.hasFDerivAt_lieLocalBCH_representative`: the first-order law
  `bch X Y = X + Y + o(‖(X, Y)‖)`.
* `TauCeti.map_lieLocalBCH`: naturality under smooth homomorphisms.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Chapter 3.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Chapter 5.
-/

public section

noncomputable section

open Filter Manifold
open scoped ContDiff Manifold Topology

attribute [local instance] LieGroup.minSmoothnessThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

namespace TauCeti

section Group

/-- The product of the exponentials of two left-invariant derivations tends to the identity at the
origin. -/
private theorem tendsto_lieExp_mul_lieExp :
    Tendsto (fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieExp p.1 * lieExp p.2) (𝓝 (0, 0)) (𝓝 1) := by
  have hexp := (contMDiff_lieExp (I := I) (G := G)).continuous
  have hmul : Continuous (fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
      lieExp p.1 * lieExp p.2) :=
    let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    (hexp.comp continuous_fst).mul (hexp.comp continuous_snd)
  simpa using hmul.tendsto (0, 0)

variable (I G) in
/-- **The local Baker--Campbell--Hausdorff germ** of a Lie group: the germ at the origin of
`(X, Y) ↦ lieLog (lieExp X * lieExp Y)` on pairs of left-invariant derivations. Only its values
near the origin carry meaning, and those are characterized by
`TauCeti.eq_lieLocalBCH_of_tendsto_of_map_lieExp_eq`. -/
def lieLocalBCH :
    Germ (𝓝 ((0, 0) : LeftInvariantDerivation I G × LeftInvariantDerivation I G))
      (LeftInvariantDerivation I G) :=
  ↑(fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
    lieLog (I := I) (lieExp p.1 * lieExp p.2))

/-- `lieLocalBCH` is the germ of `(X, Y) ↦ lieLog (lieExp X * lieExp Y)`. -/
theorem lieLocalBCH_def :
    lieLocalBCH I G =
      ↑(fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2)) :=
  (rfl)

/-- The local Baker--Campbell--Hausdorff germ takes the value zero at the origin. -/
@[simp]
theorem lieLocalBCH_value : (lieLocalBCH I G).value = 0 := by
  rw [lieLocalBCH_def, Germ.value_ofFun]
  simp

/-- The local Baker--Campbell--Hausdorff germ tends to zero at the origin. -/
theorem lieLocalBCH_tendsto : (lieLocalBCH I G).Tendsto (𝓝 0) := by
  rw [lieLocalBCH_def, Germ.coe_tendsto]
  have hlog := (contMDiffAt_lieLog_one (I := I) (G := G)).continuousAt
  simpa [Function.comp_def] using hlog.tendsto.comp tendsto_lieExp_mul_lieExp

/-- **The local exponential law.** Applying the Lie-group exponential to the local
Baker--Campbell--Hausdorff germ gives the germ of the product of the two exponentials. -/
@[simp]
theorem lieLocalBCH_map_lieExp :
    (lieLocalBCH I G).map lieExp =
      ↑(fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieExp p.1 * lieExp p.2) := by
  rw [lieLocalBCH_def, Germ.map_coe, Germ.coe_eq]
  exact tendsto_lieExp_mul_lieExp.eventually (eventually_lieExp_lieLog (I := I) (G := G))

/-- **Uniqueness of the local Baker--Campbell--Hausdorff germ.** A germ tending to zero whose
exponential is that of `lieLocalBCH` is `lieLocalBCH`. -/
theorem eq_lieLocalBCH_of_tendsto_of_map_lieExp_eq
    (f : Germ (𝓝 ((0, 0) : LeftInvariantDerivation I G × LeftInvariantDerivation I G))
      (LeftInvariantDerivation I G))
    (hf : f.Tendsto (𝓝 0)) (hmap : f.map lieExp = (lieLocalBCH I G).map lieExp) :
    f = lieLocalBCH I G := by
  induction f using Germ.inductionOn with
  | _ g =>
    have hBCH := lieLocalBCH_tendsto (I := I) (G := G)
    rw [lieLocalBCH_def, Germ.coe_tendsto] at hBCH
    rw [Germ.coe_tendsto] at hf
    rw [lieLocalBCH_def, Germ.map_coe, Germ.map_coe, Germ.coe_eq] at hmap
    rw [lieLocalBCH_def, Germ.coe_eq]
    exact eventuallyEq_of_tendsto_of_lieExp_eventuallyEq hf hBCH hmap

/-- Restricting the local Baker--Campbell--Hausdorff germ to the first coordinate axis gives the
identity germ. -/
@[simp]
theorem lieLocalBCH_sliceLeft :
    (lieLocalBCH I G).sliceLeft =
      ↑(fun X : LeftInvariantDerivation I G ↦ X) := by
  rw [lieLocalBCH_def, Germ.sliceLeft_coe, Germ.coe_eq]
  filter_upwards [eventually_lieLog_lieExp (I := I) (G := G)] with X hX
  simpa using hX

/-- Restricting the local Baker--Campbell--Hausdorff germ to the second coordinate axis gives the
identity germ. -/
@[simp]
theorem lieLocalBCH_sliceRight :
    (lieLocalBCH I G).sliceRight =
      ↑(fun Y : LeftInvariantDerivation I G ↦ Y) := by
  rw [lieLocalBCH_def, Germ.sliceRight_coe, Germ.coe_eq]
  filter_upwards [eventually_lieLog_lieExp (I := I) (G := G)] with Y hY
  simpa using hY

/-- The representative defining `lieLocalBCH` is smooth at the origin. -/
theorem contDiffAt_lieLocalBCH_representative :
    ContDiffAt ℝ ∞
      (fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2))
      (0, 0) := by
  let 𝔤 := LeftInvariantDerivation I G
  have hexp := contMDiff_lieExp (I := I) (G := G)
  have hprod : ContMDiff 𝓘(ℝ, 𝔤 × 𝔤) I ∞ (fun p : 𝔤 × 𝔤 ↦ lieExp p.1 * lieExp p.2) :=
    (hexp.comp contDiff_fst.contMDiff).mul (hexp.comp contDiff_snd.contMDiff)
  have hlog : ContMDiffAt I 𝓘(ℝ, 𝔤) ∞ (lieLog (I := I) (G := G))
      (lieExp ((0, 0) : 𝔤 × 𝔤).1 * lieExp ((0, 0) : 𝔤 × 𝔤).2) := by
    simpa using contMDiffAt_lieLog_one (I := I) (G := G)
  exact (hlog.comp (0, 0) hprod.contMDiffAt).contDiffAt

/-- **The first-order law.** The derivative at the origin of the representative defining
`lieLocalBCH` is addition, so `bch X Y = X + Y + o(‖(X, Y)‖)`: to first order the local group law
of `G` is the addition of `𝔤`. -/
theorem hasFDerivAt_lieLocalBCH_representative :
    HasFDerivAt
      (fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦
        lieLog (I := I) (lieExp p.1 * lieExp p.2))
      (ContinuousLinearMap.fst ℝ (LeftInvariantDerivation I G) (LeftInvariantDerivation I G) +
        ContinuousLinearMap.snd ℝ (LeftInvariantDerivation I G) (LeftInvariantDerivation I G))
      (0, 0) := by
  let 𝔤 := LeftInvariantDerivation I G
  let f : 𝔤 × 𝔤 → 𝔤 := fun p ↦ lieLog (I := I) (lieExp p.1 * lieExp p.2)
  have hf : HasFDerivAt f (fderiv ℝ f (0, 0)) (0, 0) :=
    (contDiffAt_lieLocalBCH_representative.differentiableAt (by simp)).hasFDerivAt
  have hleft : (fderiv ℝ f (0, 0)).comp (ContinuousLinearMap.inl ℝ 𝔤 𝔤) =
      ContinuousLinearMap.id ℝ 𝔤 := by
    have hslice := lieLocalBCH_sliceLeft (I := I) (G := G)
    rw [lieLocalBCH_def, Germ.sliceLeft_coe, Germ.coe_eq] at hslice
    exact (HasFDerivAt.comp (f := fun X : 𝔤 ↦ (X, (0 : 𝔤))) (0 : 𝔤) hf
      (hasFDerivAt_prodMk_left (0 : 𝔤) (0 : 𝔤))).unique
      ((hasFDerivAt_id (0 : 𝔤)).congr_of_eventuallyEq hslice)
  have hright : (fderiv ℝ f (0, 0)).comp (ContinuousLinearMap.inr ℝ 𝔤 𝔤) =
      ContinuousLinearMap.id ℝ 𝔤 := by
    have hslice := lieLocalBCH_sliceRight (I := I) (G := G)
    rw [lieLocalBCH_def, Germ.sliceRight_coe, Germ.coe_eq] at hslice
    exact (HasFDerivAt.comp (f := fun Y : 𝔤 ↦ ((0 : 𝔤), Y)) (0 : 𝔤) hf
      (hasFDerivAt_prodMk_right (0 : 𝔤) (0 : 𝔤))).unique
      ((hasFDerivAt_id (0 : 𝔤)).congr_of_eventuallyEq hslice)
  convert hf using 1
  refine ContinuousLinearMap.prod_ext ?_ ?_
  · rw [hleft]; ext1 X; simp [𝔤]
  · rw [hright]; ext1 Y; simp [𝔤]

end Group

section Hom

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E'] [LieGroup I' ∞ G'] [T2Space G'] [BoundarylessManifold I' G']

/-- **Naturality of the local Baker--Campbell--Hausdorff germ.** A smooth homomorphism carries
the local BCH germ of its source to that of its target through its Lie map:
`lieMap φ (bch X Y) = bch (lieMap φ X) (lieMap φ Y)` near the origin. -/
@[simp high]
theorem map_lieLocalBCH (φ : ContMDiffMonoidMorphism I I' ∞ G G') :
    (lieLocalBCH I G).map (lieMap φ) =
      (lieLocalBCH I' G').compTendsto (Prod.map (lieMap φ) (lieMap φ))
        (((continuous_lieMap φ).prodMap (continuous_lieMap φ)).tendsto' (0, 0) (0, 0)
          (by simp)) := by
  have hφ : Tendsto (Prod.map (lieMap φ) (lieMap φ))
      (𝓝 ((0, 0) : LeftInvariantDerivation I G × LeftInvariantDerivation I G)) (𝓝 (0, 0)) :=
    ((continuous_lieMap φ).prodMap (continuous_lieMap φ)).tendsto' (0, 0) (0, 0) (by simp)
  have hBCH := lieLocalBCH_tendsto (I := I) (G := G)
  have hBCH' := lieLocalBCH_tendsto (I := I') (G := G')
  have hexp := lieLocalBCH_map_lieExp (I := I) (G := G)
  have hexp' := lieLocalBCH_map_lieExp (I := I') (G := G')
  rw [lieLocalBCH_def, Germ.coe_tendsto] at hBCH hBCH'
  rw [lieLocalBCH_def, Germ.map_coe, Germ.coe_eq] at hexp hexp'
  rw [lieLocalBCH_def, lieLocalBCH_def, Germ.map_coe, Germ.coe_compTendsto, Germ.coe_eq]
  refine eventuallyEq_of_tendsto_of_lieExp_eventuallyEq ?_
    (hBCH'.comp hφ) ?_
  · simpa using ((continuous_lieMap φ).tendsto 0).comp hBCH
  · filter_upwards [hexp, hφ.eventually hexp'] with p hp hp'
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd] at hp hp' ⊢
    rw [← map_lieExp φ, hp, map_mul, map_lieExp, map_lieExp, hp']

end Hom

end TauCeti
