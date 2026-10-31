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

/-- The Evens norm of zero is zero, in every degree. -/
@[simp]
theorem evensNorm_zero (n : ℕ) :
    U.evensNorm (0 : continuousCohomology n (trivialF2 U.toSubgroup)) = 0 := by
  rw [← TopRep.cochainClass_zero (X := trivialF2 U.toSubgroup) (n := n),
    evensNorm_cochainClass U default, tensorNormCocycleClass_zero]

end OpenSubgroup
