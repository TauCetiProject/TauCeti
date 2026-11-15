/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier

/-!
# Presented points of the type-F4 short-root carrier

`TauCeti.F4ShortRoot.groupScheme` is the explicit short-root type-`F₄` carrier over `ℤ`, built
from the `26`-dimensional short-root representation, and `TauCeti.F4ShortRoot.points A` realizes its
`A`-valued points as a subgroup of `GL₂₆(A)`. `TauCeti.F4ShortRoot.pointsPresentation` presents
these points by the carrier's defining integral Hopf ideal. The shared
`GeneralLinear.IntegralPointsPresentation` API supplies the maps of points induced by
homomorphisms of value rings, their functoriality, and the representing equivalence with points
of the quotient coordinate Hopf algebra. This file proves that those maps preserve the two pinned
families:

```text
f (x_k(u)) = x_k(f(u)),        f (t(s)) = t(Units.map f ∘ s).
```

The coordinates of a weight-torus point are unit-valued, so the map induced on them is the map
`Units.map f` of unit groups rather than `f` itself.

Nothing here asserts reductivity, maximality of the weight torus, or an identification of the
carrier's root datum.

## Main declarations

* `TauCeti.F4ShortRoot.pointsPresentation`: the carrier's points, presented by its defining ideal.
* `TauCeti.F4ShortRoot.map_rootSubgroupPoints` and `TauCeti.F4ShortRoot.map_weightTorusPoints`:
  the induced maps on the numbered root subgroups and on the weight torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/

-- Adapted from `TauCeti.Algebra.Lie.E6.Minuscule.PointsFunctor`.

public section

namespace TauCeti.F4ShortRoot

universe v v'

noncomputable section

/-- The short-root carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation 26 definingIdeal A where
  val := points A
  property := points_def A

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp↓]
theorem map_rootSubgroupPoints (f : A →+* B) (k : Fin 4 ⊕ Fin 4)
    (u : Multiplicative A) :
    (pointsPresentation A).map (pointsPresentation B) f (rootSubgroupPoints k A u) =
      rootSubgroupPoints k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralRootSubgroupPoints
      (e := TauCeti.serreRootGenerator (CartanMatrix.F₄.transpose))
      (h := TauCeti.serreH ℚ (CartanMatrix.F₄.transpose)) (ρ := rep)
      (M := lattice.toAddSubgroup) (hM := rep_kostantForm_mem_lattice)
      (hnil := isNilpotent_rep_serreRootGenerator) (b := latticeBasis)
      (wt := TauCeti.DynkinType.f4ShortRootWeight) f k u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  simpa only [coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints] using h

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp↓]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin 4 → Aˣ) :
    (pointsPresentation A).map (pointsPresentation B) f (weightTorusPoints A s) =
      weightTorusPoints B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralWeightTorusPoints
      (e := TauCeti.serreRootGenerator (CartanMatrix.F₄.transpose))
      (h := TauCeti.serreH ℚ (CartanMatrix.F₄.transpose)) (ρ := rep)
      (M := lattice.toAddSubgroup) (hM := rep_kostantForm_mem_lattice)
      (hnil := isNilpotent_rep_serreRootGenerator) (b := latticeBasis)
      (wt := TauCeti.DynkinType.f4ShortRootWeight) f s)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  simpa only [coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints] using h

end

end TauCeti.F4ShortRoot
