/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.EtaleTwoDescent
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Local conditions in cohomological and explicit two-descent

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
description sends the classes that are Selmer at the completions of `K` at the finite places of a
Dedekind domain `R` with fraction field `K`, and at an auxiliary family `Loc` of fields, into the
explicit `2`-Selmer group `WeierstrassCurve.Affine.selmerGroup₂ R Loc`, injectively since the
cohomological descent map is injective.

## Main results

* `WeierstrassCurve.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_range_μ`: membership in
  the cohomological `2`-Selmer group is equivalent to membership of every local explicit image in
  the corresponding local `x - T` image.
* `WeierstrassCurve.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_localCondition`: since the
  cohomological descent map commutes with change of field
  (`TauCeti.TwoDescent.cohomologicalMap_torsionRes`), the same membership is the explicit local
  condition `WeierstrassCurve.Affine.localCondition` on the global descent image.
* `WeierstrassCurve.cohomologicalMap_mem_selmerGroup₂`: with the norm condition
  (`TauCeti.TwoDescent.normM_cohomologicalMap`), the cohomological descent map sends the classes
  that are Selmer at the finite places of a Dedekind domain and at an auxiliary family of fields
  into the explicit `2`-Selmer group `WeierstrassCurve.Affine.selmerGroup₂`.

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

open IsDedekindDomain in
/-- **The cohomological `2`-Selmer group maps into the explicit one.** Let `R` be a Dedekind domain
with fraction field `K` and `Loc` a family of field extensions of `K`. A class that lies in the
cohomological `2`-Selmer group for the completions of `K` at the finite places of `R` and in the
cohomological `2`-Selmer group for the family `Loc` is sent by the cohomological descent map into
the explicit `2`-Selmer group `WeierstrassCurve.Affine.selmerGroup₂ R Loc`: its image has square
norm (`TauCeti.TwoDescent.normM_cohomologicalMap`) and satisfies the explicit local conditions. -/
theorem cohomologicalMap_mem_selmerGroup₂ (h2 : IsUnit ((2 : ℕ) : K))
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
    {ι : Type*} (Loc : ι → Type*) [(i : ι) → Field (Loc i)] [(i : ι) → Algebra K (Loc i)]
    (tauV : (v : HeightOneSpectrum R) →
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (tauL : (i : ι) → SeparableClosure K →ₐ[K] SeparableClosure (Loc i))
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)} (hV : c ∈ W.selmerGroup tauV 2)
    (hL : c ∈ W.selmerGroup tauL 2) :
    TauCeti.TwoDescent.cohomologicalMap W h2 (.ofAdd c) ∈ W.toAffine.selmerGroup₂ R Loc :=
  (Affine.mem_selmerGroup₂_iff _ _ _).2
    ⟨TauCeti.TwoDescent.normM_cohomologicalMap W h2 _,
      (W.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_localCondition _ tauV h2).1 hV,
      (W.mem_selmerGroup_two_iff_forall_cohomologicalMap_mem_localCondition Loc tauL h2).1 hL⟩

end WeierstrassCurve
