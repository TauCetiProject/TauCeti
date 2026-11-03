/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.EtaleTwoDescent.NormKernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The cohomological and explicit `2`-Selmer groups

For an elliptic curve in characteristic-`≠ 2` normal form, the cohomological descent map

```text
H¹(G_K, E[2]) ⟶ (K[X] / (f))ˣ / squares
```

is injective and carries the cohomological Kummer map to the explicit `x - T` map. Consequently a
cohomology class lies in the image of the Kummer map exactly when its explicit image lies in the
image of `x - T` (`TauCeti.TwoDescent.cohomologicalMap_mem_range_μ_iff`). This identifies the
cohomological and explicit local conditions used to define the two versions of the `2`-Selmer
group.

This file proves two descriptions of the cohomological `2`-Selmer group. The first applies this
identification after restriction to every chosen extension field, describing the Selmer group
entirely in terms of the local explicit descent images. The second uses that the cohomological
descent map commutes with change of field (`TauCeti.TwoDescent.cohomologicalMap_torsionRes`) to
move the restriction past the descent map: a class lies in the Selmer group exactly when its
global descent image satisfies the explicit local condition `WeierstrassCurve.Affine.localCondition`
at every chosen extension field.

Together with the norm condition `TauCeti.TwoDescent.normM_cohomologicalMap`, the second
description shows that a class is Selmer at the completions of `K` at the finite places of a
Dedekind domain `R` with fraction field `K`, and at an auxiliary family `Loc` of fields, exactly
when its descent image lies in the explicit `2`-Selmer group
`WeierstrassCurve.Affine.selmerGroup₂ R Loc`. Since every square class with square norm is a
descent image (`TauCeti.TwoDescent.range_cohomologicalMap_eq_ker_normM`) and the descent map is
injective, the cohomological descent map is an isomorphism from the cohomological `2`-Selmer
group onto the explicit one.

## Main definitions

* `WeierstrassCurve.selmerGroupTwoMulEquivSelmerGroup₂`: the isomorphism from the cohomological
  `2`-Selmer group onto the explicit one, given by the cohomological descent map.

## Main results

* `WeierstrassCurve.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_range_μ`: membership in
  the cohomological `2`-Selmer group is equivalent to membership of every local explicit image in
  the corresponding local `x - T` image.
* `WeierstrassCurve.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_localCondition`: since the
  cohomological descent map commutes with change of field
  (`TauCeti.TwoDescent.cohomologicalMap_torsionRes`), the same membership is the explicit local
  condition `WeierstrassCurve.Affine.localCondition` on the global descent image.
* `WeierstrassCurve.cohomologicalMap_mem_selmerGroup₂_iff`: with the norm condition
  (`TauCeti.TwoDescent.normM_cohomologicalMap`), a class is Selmer at the finite places of a
  Dedekind domain and at an auxiliary family of fields exactly when the cohomological descent map
  sends it into the explicit `2`-Selmer group `WeierstrassCurve.Affine.selmerGroup₂`.
* `WeierstrassCurve.map_selmerGroup_two_eq_selmerGroup₂`: the explicit `2`-Selmer group is the
  image of the cohomological one.
* `WeierstrassCurve.coe_selmerGroupTwoMulEquivSelmerGroup₂_apply` and
  `WeierstrassCurve.cohomologicalMap_selmerGroupTwoMulEquivSelmerGroup₂_symm_apply`: the
  isomorphism and its inverse are read through the cohomological descent map.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1 and X.4.
-/

public section

noncomputable section

open TauCeti.ContCohomology

namespace WeierstrassCurve

open TauCeti

variable {K : Type*} [Field K] (W : WeierstrassCurve K)
  [W.IsElliptic] [W.toAffine.IsCharNeTwoNF]
  {I : Type*} (L : I → Type*) [(i : I) → Field (L i)] [(i : I) → Algebra K (L i)]
  (tau : (i : I) → SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-- **The cohomological `2`-Selmer condition in explicit local coordinates.** A class is in the
cohomological `2`-Selmer group exactly when, at every chosen extension field, its restricted
class maps into the image of the local `x - T` descent map. -/
theorem mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_range_μ
    [∀ i, DecidableEq (L i)] (h2 : IsUnit ((2 : ℕ) : K))
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)} :
    c ∈ W.selmerGroup tau 2 ↔ ∀ i,
      letI := W.toAffine.isCharNeTwoNF_map (algebraMap K (L i))
      TauCeti.TwoDescent.cohomologicalMap (W.baseChange (L i))
          (by rw [← map_natCast (algebraMap K (L i))]; exact h2.map (algebraMap K (L i)))
          (.ofAdd (W.torsionRes (tau i) 2 c)) ∈
        (Affine.μ (W := (W.baseChange (L i)).toAffine)).range := by
  rw [W.mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap tau h2]
  apply forall_congr'
  intro i
  exact (TauCeti.TwoDescent.cohomologicalMap_mem_range_μ_iff (W.baseChange (L i)) _).symm


/-- **The cohomological `2`-Selmer group is cut out by the explicit local conditions.** A class is
in the cohomological `2`-Selmer group exactly when its image under the cohomological descent map
satisfies the explicit local `2`-descent condition at every chosen extension field. -/
theorem mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_localCondition
    (h2 : IsUnit ((2 : ℕ) : K)) {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)} :
    c ∈ W.selmerGroup tau 2 ↔
      ∀ i, TauCeti.TwoDescent.cohomologicalMap W h2 (.ofAdd c) ∈
        W.toAffine.localCondition (L i) := by
  classical
  rw [W.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_range_μ L tau h2]
  refine forall_congr' fun i ↦ ?_
  rw [TauCeti.TwoDescent.cohomologicalMap_torsionRes, Affine.mem_localCondition_iff]

section SelmerGroup₂

open IsDedekindDomain

variable (h2 : IsUnit ((2 : ℕ) : K))
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {ι : Type*} (Loc : ι → Type*) [(i : ι) → Field (Loc i)] [(i : ι) → Algebra K (Loc i)]
  (tauV : (v : HeightOneSpectrum R) →
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (tauL : (i : ι) → SeparableClosure K →ₐ[K] SeparableClosure (Loc i))

/-- **The cohomological and explicit `2`-Selmer conditions agree.** Let `R` be a Dedekind domain
with fraction field `K` and `Loc` a family of field extensions of `K`. A class of
`H¹(G_K, E[2])` lies in the cohomological `2`-Selmer groups for the completions of `K` at the
finite places of `R` and for the family `Loc` exactly when the cohomological descent map sends it
into the explicit `2`-Selmer group `WeierstrassCurve.Affine.selmerGroup₂ R Loc`. The norm
condition holds on every image (`TauCeti.TwoDescent.normM_cohomologicalMap`). -/
theorem cohomologicalMap_mem_selmerGroup₂_iff
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)} :
    TauCeti.TwoDescent.cohomologicalMap W h2 (.ofAdd c) ∈ W.toAffine.selmerGroup₂ R Loc ↔
      c ∈ W.selmerGroup tauV 2 ∧ c ∈ W.selmerGroup tauL 2 := by
  rw [Affine.mem_selmerGroup₂_iff,
    W.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_localCondition _ tauV h2,
    W.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_localCondition Loc tauL h2]
  exact and_iff_right (TauCeti.TwoDescent.normM_cohomologicalMap W h2 _)

/-- **The explicit `2`-Selmer group is the image of the cohomological one** (Silverman X.1.4,
X.4): the cohomological descent map carries the classes that are Selmer at the finite places of
`R` and at the family `Loc` onto the explicit `2`-Selmer group
`WeierstrassCurve.Affine.selmerGroup₂ R Loc`. -/
theorem map_selmerGroup_two_eq_selmerGroup₂ :
    (W.selmerGroup tauV 2 ⊓ W.selmerGroup tauL 2).toSubgroup.map
        (TauCeti.TwoDescent.cohomologicalMap W h2) =
      W.toAffine.selmerGroup₂ R Loc := by
  refine le_antisymm ?_ fun m hm ↦ ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact (W.cohomologicalMap_mem_selmerGroup₂_iff h2 R Loc tauV tauL).2 hc
  -- an explicit Selmer element has square norm, so it is a cohomological descent image
  obtain ⟨c, rfl⟩ : m ∈ (TauCeti.TwoDescent.cohomologicalMap W h2).range := by
    rw [TauCeti.TwoDescent.range_cohomologicalMap_eq_ker_normM]
    exact ((Affine.mem_selmerGroup₂_iff _ _ _).1 hm).1
  exact ⟨c, (W.cohomologicalMap_mem_selmerGroup₂_iff h2 R Loc tauV tauL).1 hm, rfl⟩

/-- **The cohomological and explicit `2`-Selmer groups are isomorphic** through the cohomological
descent map. The cohomological side is the intersection of the `2`-Selmer groups for the
completions of `K` at the finite places of `R` and for the family `Loc`; the explicit side is
`WeierstrassCurve.Affine.selmerGroup₂ R Loc`. -/
noncomputable def selmerGroupTwoMulEquivSelmerGroup₂ :
    (W.selmerGroup tauV 2 ⊓ W.selmerGroup tauL 2).toSubgroup ≃* W.toAffine.selmerGroup₂ R Loc :=
  ((W.selmerGroup tauV 2 ⊓ W.selmerGroup tauL 2).toSubgroup.equivMapOfInjective _
    (TauCeti.TwoDescent.cohomologicalMap_injective W h2)).trans
      (MulEquiv.subgroupCongr (W.map_selmerGroup_two_eq_selmerGroup₂ h2 R Loc tauV tauL))

/-- `WeierstrassCurve.selmerGroupTwoMulEquivSelmerGroup₂` is the cohomological descent map. -/
@[simp]
theorem coe_selmerGroupTwoMulEquivSelmerGroup₂_apply
    (c : (W.selmerGroup tauV 2 ⊓ W.selmerGroup tauL 2).toSubgroup) :
    (W.selmerGroupTwoMulEquivSelmerGroup₂ h2 R Loc tauV tauL c : W.toAffine.M) =
      TauCeti.TwoDescent.cohomologicalMap W h2 c :=
  (rfl)

/-- The inverse of `WeierstrassCurve.selmerGroupTwoMulEquivSelmerGroup₂` sends an explicit
`2`-Selmer element to the cohomology class with that descent image. -/
@[simp]
theorem cohomologicalMap_selmerGroupTwoMulEquivSelmerGroup₂_symm_apply
    (m : W.toAffine.selmerGroup₂ R Loc) :
    TauCeti.TwoDescent.cohomologicalMap W h2
        ((W.selmerGroupTwoMulEquivSelmerGroup₂ h2 R Loc tauV tauL).symm m) = m := by
  rw [← coe_selmerGroupTwoMulEquivSelmerGroup₂_apply, MulEquiv.apply_symm_apply]

end SelmerGroup₂

end WeierstrassCurve
