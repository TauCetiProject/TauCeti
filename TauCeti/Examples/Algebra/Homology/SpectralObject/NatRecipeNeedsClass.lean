/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.SingleHomology
import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The class `HasSpectralSequence` is needed on natural positions

Let `K = (ℤ →(id) ℤ)` in degrees `0, 1`, with the increasing filtration `G_t = 0` for `t ≤ 0`,
`G_1 = K^1` (the degree-`1` term) and `G_t = K` for `t ≥ 2`. Its spectral object
(`CochainComplex.spectralObject`) has `H^0(1 ≤ 2) = H^0(K/K^1) = ℤ ≠ 0`. So the spectral object
satisfies neither `HasSpectralSequence coreE₂CohomologicalNat` (at the position `(1, 0)` on the
page `2`, the entering differential would come from the missing `(-1, 1)`, and the class asks
`H^0(1 ≤ 2)` to vanish) nor `IsFirstQuadrant` (which asks `H^0(1 ≤ 2) = 0` since `0 < 1`).

This is the contrast in the title: over `ℤ × ℤ` the class
`HasSpectralSequence coreE₂Cohomological` holds for every spectral object indexed by `EInt` (a
Mathlib instance), but over `ℕ × ℕ` the class `HasSpectralSequence coreE₂CohomologicalNat` is a
real condition, which Mathlib supplies only from `IsFirstQuadrant`. This example shows that the
condition can fail.

We take `K` to be the mapping cone of the identity of `ℤ[-1]`, the complex `ℤ` concentrated in
degree `1`: its terms are `ℤ` in degrees `0` and `1`, with the identity as differential, and
`mappingCone.inr` includes `ℤ[-1]` as the degree-`1` term `K^1`. Instead of computing the
quotient, we use the long exact sequence of `0 → K^1 → K → K/K^1 → 0`: if `H^0(K/K^1)` vanished,
then `H^1(K^1) = ℤ` would inject into `H^1(K)`, which vanishes because `K` is contractible.

## Main declarations

* `TauCeti.Examples.NatRecipeNeedsClass.filtrationFunctor`: the functor `EInt ⥤ CochainComplex`
  of the filtration `0 ⊆ K^1 ⊆ K`.
* `TauCeti.Examples.NatRecipeNeedsClass.not_isZero_H_one_two`: `H^0(1 ≤ 2) ≠ 0`.
* `TauCeti.Examples.NatRecipeNeedsClass.not_hasSpectralSequence`,
  `TauCeti.Examples.NatRecipeNeedsClass.not_isFirstQuadrant`: the two classes fail.
-/

public section

noncomputable section

namespace TauCeti.Examples.NatRecipeNeedsClass

open CategoryTheory Limits ComposableArrows CategoryTheory.Abelian CochainComplex
  HomologicalComplex

/-- The complex `ℤ[-1]`: the abelian group `ℤ` concentrated in degree `1`. -/
abbrev degreeOne : CochainComplex (ModuleCat ℤ) ℤ :=
  (single (ModuleCat ℤ) (ComplexShape.up ℤ) 1).obj (ModuleCat.of ℤ ℤ)

/-- The complex `K = (ℤ →(id) ℤ)` in degrees `0, 1`, as the mapping cone of the identity of
`ℤ[-1]`. -/
abbrev idComplex : CochainComplex (ModuleCat ℤ) ℤ :=
  mappingCone (𝟙 degreeOne)

/-- The filtration `G_t = 0` for `t ≤ 0`, `G_1 = K^1` and `G_t = K` for `t ≥ 2`. -/
def filtration (t : ℤ) : Subobject idComplex :=
  if t ≤ 0 then ⊥ else if t = 1 then Subobject.mk (mappingCone.inr (𝟙 degreeOne)) else ⊤

/-- The filtration `0 ⊆ K^1 ⊆ K` is increasing. -/
theorem monotone_filtration : Monotone filtration := by
  intro s t hst
  unfold filtration
  split_ifs <;> first | exact bot_le | exact le_top | exact le_rfl | lia

/-- The functor `EInt ⥤ CochainComplex` of the filtration `0 ⊆ K^1 ⊆ K`. -/
abbrev filtrationFunctor : EInt ⥤ CochainComplex (ModuleCat ℤ) ℤ :=
  CochainComplex.filtrationFunctor filtration monotone_filtration

/-- The spectral object of the filtration `0 ⊆ K^1 ⊆ K`. -/
abbrev spectralObject : SpectralObject (ModuleCat ℤ) EInt :=
  CochainComplex.spectralObject filtrationFunctor

/-- The inequality `1 ≤ 2` between the integers `1` and `2` viewed in `EInt`. -/
theorem coe_one_le_coe_two : ((1 : ℤ) : EInt) ≤ ((2 : ℤ) : EInt) :=
  WithBotTop.coe_le_coe.2 (by norm_num)

/-- `H^1(ℤ[-1]) = ℤ ≠ 0`. -/
theorem not_isZero_homology_degreeOne : ¬ IsZero (degreeOne.homology 1) := fun h => by
  have := (ModuleCat.isZero_iff_subsingleton.1
    (h.of_iso (singleObjHomologySelfIso (ComplexShape.up ℤ) 1 (ModuleCat.of ℤ ℤ)).symm))
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

/-- **`H^0(1 ≤ 2) ≠ 0`** for the spectral object of the filtration `0 ⊆ K^1 ⊆ K`: it is
`H^0(K/K^1) = ℤ`. -/
theorem not_isZero_H_one_two :
    ¬ IsZero ((spectralObject.H 0).obj (mk₁ (homOfLE coe_one_le_coe_two))) := fun h => by
  set f : ((1 : ℤ) : EInt) ⟶ ((2 : ℤ) : EInt) := homOfLE coe_one_le_coe_two
  have hS := TauCeti.cokernelSequence_shortExact (filtrationFunctor.map f)
  -- `H^0` of the quotient vanishes, so `H^1` of the subcomplex injects into `H^1` of `K`.
  have hQ : IsZero ((cokernel (filtrationFunctor.map f)).homology 0) :=
    h.of_iso (spectralObjectHIsoCokernel filtrationFunctor f 0).symm
  have : Mono (homologyMap (filtrationFunctor.map f) 1) :=
    (hS.homology_exact₁ 0 1 (by simp)).mono_g (hQ.eq_of_src _ _)
  have h1 : filtration 1 = Subobject.mk (mappingCone.inr (𝟙 degreeOne)) := by
    simp [filtration]
  have h2 : filtration 2 = Subobject.mk (𝟙 idComplex) := by
    simp [filtration, Subobject.top_eq_id]
  -- `K` is contractible, so `H^1(K) = 0`.
  have hK : IsZero ((filtrationFunctor.obj ((2 : ℤ) : EInt)).homology 1) :=
    ((exactAt_iff_isZero_homology _ _).1
      ((mappingCone.homotopyToZeroOfId degreeOne).acyclic 1)).of_iso
        (homologyMapIso (filtrationFunctorObjIsoOfEqMk _ _ _ h2) 1)
  exact not_isZero_homology_degreeOne ((IsZero.of_mono (homologyMap
    (filtrationFunctor.map f) 1) hK).of_iso
      (homologyMapIso (filtrationFunctorObjIsoOfEqMk _ _ _ h1) 1).symm)

/-- **The class `HasSpectralSequence coreE₂CohomologicalNat` fails** for the spectral object of
`0 ⊆ K^1 ⊆ K`: at `(1, 0)` on the page `2` nothing enters from `ℕ × ℕ`, and the class would make
`H^0(1 ≤ 2)` vanish. -/
theorem not_hasSpectralSequence :
    ¬ spectralObject.HasSpectralSequence SpectralObject.coreE₂CohomologicalNat := fun _ =>
  not_isZero_H_one_two (spectralObject.isZero_H_obj_mk₁_i₃_le'
    SpectralObject.coreE₂CohomologicalNat 2 3 rfl le_rfl ((1 : ℕ), (0 : ℕ)) (fun pq h => by
      rw [ComplexShape.spectralSequenceNat_rel_iff] at h
      lia) 0 (by simp) _ _ (by simp) (by simp))

/-- **The spectral object of `0 ⊆ K^1 ⊆ K` is not first-quadrant**: `H^0(1 ≤ 2) ≠ 0` with
`0 < 1`. -/
theorem not_isFirstQuadrant : ¬ spectralObject.IsFirstQuadrant := fun _ =>
  not_isZero_H_one_two (spectralObject.isZero₂_of_isFirstQuadrant _ _ _ 0
    (WithBotTop.coe_lt_coe.2 (by norm_num)))

end TauCeti.Examples.NatRecipeNeedsClass
