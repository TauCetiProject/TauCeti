/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Cocycle

/-!
# The Evens norm in every degree

For a compact open subgroup `U` of finite index `l` in a topological group `G`, the Evens norm is
the function
```
N_U^G : Hⁿ(U, 𝔽₂) → H^{l n}(G, 𝔽₂)
```
sending the class of a homogeneous cocycle `z` to the class of its diagonal tensor `z ⊗ ⋯ ⊗ z`
in the tensor-induced resolution, `OpenSubgroup.tensorNormCocycleClass`. That class depends only
on the class of `z` and not on the transversal, so the norm is a function on cohomology. It is
not additive, and its signature uses `→` between the underlying types.

## Main definitions

* `OpenSubgroup.evensNorm`: the Evens norm `N_U^G : Hⁿ(U, 𝔽₂) → H^{l n}(G, 𝔽₂)`.

## Main results

* `OpenSubgroup.evensNorm_cochainClass`: the norm of the class of a homogeneous cocycle is its
  tensor norm, computed with any transversal.
* `OpenSubgroup.evensNorm_gradedCohomologyClass`: the norm of the class of a cocycle of the total
  coinduced resolution is the class of its diagonal tensor, computed with any transversal.
* `OpenSubgroup.evensNorm_zero`: the norm of zero is zero, in every degree.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–5.
-/

public section

namespace OpenSubgroup

open TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  [Fintype (G ⧸ U.toSubgroup)]

/-- **The Evens norm** `N_U^G : Hⁿ(U, 𝔽₂) → H^{l n}(G, 𝔽₂)`, for `l` the index of `U`: the
tensor norm of a homogeneous cocycle representing the class, computed with the default
transversal. By `evensNorm_cochainClass` neither the representative nor the transversal matters.
It is a function and not an additive map. -/
noncomputable def evensNorm {n : ℕ} (x : continuousCohomology n (trivialF2 U.toSubgroup)) :
    continuousCohomology (Fintype.card (G ⧸ U.toSubgroup) * n) (trivialF2 G) :=
  tensorNormCocycleClass U default (TopRep.exists_cochainClass_eq x).choose
    (TopRep.exists_cochainClass_eq x).choose_spec.choose

/-- **The defining equation of the Evens norm:** the norm of the class of a homogeneous cocycle
is the class of its diagonal tensor, computed with any transversal `t`. -/
theorem evensNorm_cochainClass (t : U.toSubgroup.LeftTransversal) {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z = 0) :
    U.evensNorm ((trivialF2 U.toSubgroup).cochainClass n z hz) =
      tensorNormCocycleClass U t z hz := by
  rw [evensNorm, tensorNormCocycleClass_changeTransversal U default t]
  exact tensorNormCocycleClass_eq_of_cochainClass_eq U t _ _ _ _
    (TopRep.exists_cochainClass_eq _).choose_spec.choose_spec

/-- **The Evens norm of a cocycle of the total resolution.** For a homogeneous cocycle `w` of degree
`n` of the total coinduced resolution of `𝔽₂`, fixed by `U`, the norm of its class is the class of
its diagonal tensor `w ⊗ ⋯ ⊗ w`, computed with any transversal `t`. -/
theorem evensNorm_gradedCohomologyClass (t : U.toSubgroup.LeftTransversal) {n : ℕ}
    {w : (trivialF2 U.toSubgroup).gradedResolutionModule}
    (hw : w ∈ (trivialF2 U.toSubgroup).gradedResolutionPiece n)
    (hinv : ∀ u, (trivialF2 U.toSubgroup).gradedResolutionTopRep.ρ u w = w)
    (hdw : (trivialF2 U.toSubgroup).gradedResolutionDifferential w = 0) :
    U.evensNorm ((TopRep.gradedResolutionContraction
        (isSmoothDiscrete_trivialF2 U.toSubgroup)).gradedCohomologyClass w hw hinv
        ((TopRep.gradedResolutionTopRepDifferential_apply _ w).trans hdw)) =
      ContinuousCohomology.coeffMap
        (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' t).hom.hom
        (Fintype.card (G ⧸ U.toSubgroup) * n)
        (smoothTensorInducedDiagonalClass.{0, u, u} U.toSubgroup U.isOpen' t
          ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
          (trivialF2_add_self U.toSubgroup) w hw hinv hdw) := by
  classical
  -- A homogeneous invariant cocycle of the total resolution is an included homogeneous cocycle.
  obtain ⟨z, rfl⟩ : ∃ z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n,
      (trivialF2 U.toSubgroup).cochainToGradedResolution n z = w := by
    obtain ⟨F, rfl⟩ := (SetLike.ext_iff.1
      ((trivialF2 U.toSubgroup).gradedResolutionPiece_natCast n) w).1 hw
    exact ⟨⟨F, fun g ↦ DirectSum.of_injective (β := fun n ↦
      (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).V) n
        ((TopRep.gradedResolutionTopRep_ρ_lof _ n g F).symm.trans (hinv g))⟩,
      TopRep.cochainToGradedResolution_apply _ n _⟩
  have hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z = 0 :=
    Subtype.ext <| DirectSum.of_injective (β := fun n ↦
      (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).V) (n + 1) <|
        (TopRep.cochainToGradedResolution_apply _ (n + 1) _).symm.trans <|
          ((TopRep.gradedResolutionDifferential_cochainToGradedResolution _ n z).symm.trans
            hdw).trans (map_zero _).symm
  refine (congrArg U.evensNorm (TopRep.gradedCohomologyClass_eq_degreeCast_cochainClass _ rfl z hz
    _ rfl _ _ _)).trans ?_
  rw [ContinuousCohomology.degreeCast_rfl, CategoryTheory.Iso.refl_hom,
    CategoryTheory.ConcreteCategory.id_apply, evensNorm_cochainClass U t,
    tensorNormCocycleClass_def]

/-- The Evens norm of zero is zero, in every degree. -/
@[simp]
theorem evensNorm_zero (n : ℕ) :
    U.evensNorm (0 : continuousCohomology n (trivialF2 U.toSubgroup)) = 0 := by
  rw [← TopRep.cochainClass_zero (X := trivialF2 U.toSubgroup) (n := n),
    evensNorm_cochainClass U default, tensorNormCocycleClass_zero]

end OpenSubgroup
