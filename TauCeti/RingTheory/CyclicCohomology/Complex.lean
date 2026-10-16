/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cochain
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The cyclic cochain complex

The cyclic cochains of an associative unital algebra, with the Hochschild coboundary, form a
cochain complex.  Its cycles, boundaries, and homology are the cyclic cocycles, cyclic
coboundaries, and cyclic cohomology.  Algebra homomorphisms act contravariantly by precomposition,
both on the complex and on cyclic cohomology, using the pullback of cyclic cochains
`TauCeti.cyclicCochainPullback`.  Maps need not preserve the unit.

The construction is made in `ModuleCat`, so its homology uses Mathlib's kernel-and-cokernel
homology API.  In particular, cyclic boundaries are the kernel of the projection from cocycles
to cohomology, equivalently the image of the preceding Hochschild coboundary.  For a nonunital
algebra, cyclic cohomology is instead defined by the relative complex of its forced unitization;
that separate construction is not represented by the naive cochains assembled here.

## Main definitions

* `TauCeti.cyclicCochainComplex`: the nonnegatively graded cyclic cochain complex.
* `TauCeti.NonUnitalAlgHom.cyclicCochainComplexMap`: the contravariant cochain map induced by an
  algebra map.
* `TauCeti.cyclicCocycles`, `TauCeti.cyclicCoboundaries`, and `TauCeti.cyclicCohomology`:
  the cycles, boundaries, and homology objects of the complex.
* `TauCeti.NonUnitalAlgHom.cyclicCohomologyMap`: the induced map on cyclic cohomology.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, Section 1.
* J.-L. Loday, *Cyclic Homology*, Section 2.1.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace TauCeti

universe uR u

section Complex

variable (R : Type uR) (A M : Type u) [Ring R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M]

/-- The cochain complex of cyclic cochains with the Hochschild coboundary. -/
abbrev cyclicCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (cyclicCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (cyclicHochschildCoboundary R A M n))
    fun _n ↦ ModuleCat.hom_ext <| LinearMap.ext fun φ ↦
      cyclicHochschildCoboundary_cyclicHochschildCoboundary R A M φ

/-- The degree-`n` term of the cyclic cochain complex is the module of cyclic `n`-cochains. -/
@[simp]
theorem cyclicCochainComplex_X (n : ℕ) :
    (cyclicCochainComplex R A M).X n = ModuleCat.of R (cyclicCochains R A M n) :=
  rfl

/-- The differential in the cyclic cochain complex is the restricted Hochschild coboundary. -/
theorem cyclicCochainComplex_d (n : ℕ) :
    (cyclicCochainComplex R A M).d n (n + 1) =
      ModuleCat.ofHom (cyclicHochschildCoboundary R A M n) := by
  apply CochainComplex.of_d

/-- The cyclic cocycles in degree `n`, as the cycles object of the cyclic cochain complex. -/
abbrev cyclicCocycles (n : ℕ) : ModuleCat R := (cyclicCochainComplex R A M).cycles n

/-- The cyclic coboundaries in degree `n`, as the kernel in the cyclic cocycles of the projection
to cyclic cohomology. -/
abbrev cyclicCoboundaries (n : ℕ) : ModuleCat R :=
  kernel ((cyclicCochainComplex R A M).homologyπ n)

/-- The degree-`n` cyclic cohomology of `A` with values in `M`. -/
abbrev cyclicCohomology (n : ℕ) : ModuleCat R := (cyclicCochainComplex R A M).homology n

end Complex

section ComplexMap

variable {R : Type uR} {A B C M : Type u} [Ring R]
  [Ring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [Ring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [Ring C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M]

/-- The contravariant map of cyclic cochain complexes induced by a nonunital algebra map. -/
def NonUnitalAlgHom.cyclicCochainComplexMap (f : A →ₙₐ[R] B) :
    cyclicCochainComplex R B M ⟶ cyclicCochainComplex R A M :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (cyclicCochainPullback (f : A →ₗ[R] B) n))
    fun n ↦ by
      simp only [CochainComplex.of_d]
      exact ModuleCat.hom_ext
        (NonUnitalAlgHom.cyclicCochainPullback_cyclicHochschildCoboundary (M := M) f n).symm

/-- The degree-`n` component of the induced cochain map is pullback of cyclic cochains. -/
@[simp]
theorem NonUnitalAlgHom.cyclicCochainComplexMap_f (f : A →ₙₐ[R] B) (n : ℕ) :
    (cyclicCochainComplexMap (M := M) f).f n =
      ModuleCat.ofHom (cyclicCochainPullback (f : A →ₗ[R] B) n) := (rfl)

/-- The identity algebra map induces the identity on the cyclic cochain complex. -/
@[simp]
theorem NonUnitalAlgHom.cyclicCochainComplexMap_id :
    cyclicCochainComplexMap (M := M) (NonUnitalAlgHom.id R A) = 𝟙 _ := by
  ext n φ
  simp

/-- A composite algebra map induces the composite cochain map in contravariant order. -/
theorem NonUnitalAlgHom.cyclicCochainComplexMap_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    cyclicCochainComplexMap (M := M) (g.comp f) =
      cyclicCochainComplexMap (M := M) g ≫ cyclicCochainComplexMap (M := M) f := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [cyclicCochainComplexMap_f, HomologicalComplex.comp_f]
  exact ModuleCat.hom_ext
    (cyclicCochainPullback_comp (f : A →ₗ[R] B) (g : B →ₗ[R] C) n)

/-- The map on degree-`n` cyclic cohomology induced contravariantly by an algebra map. -/
abbrev NonUnitalAlgHom.cyclicCohomologyMap (f : A →ₙₐ[R] B) (n : ℕ) :
    cyclicCohomology R B M n ⟶ cyclicCohomology R A M n :=
  HomologicalComplex.homologyMap (cyclicCochainComplexMap (M := M) f) n

/-- The identity algebra map induces the identity on cyclic cohomology. -/
@[simp]
theorem NonUnitalAlgHom.cyclicCohomologyMap_id (n : ℕ) :
    cyclicCohomologyMap (M := M) (NonUnitalAlgHom.id R A) n = 𝟙 _ := by
  rw [cyclicCohomologyMap, cyclicCochainComplexMap_id,
    HomologicalComplex.homologyMap_id]

/-- Pullback on cyclic cohomology sends a composite to the contravariantly ordered composite. -/
theorem NonUnitalAlgHom.cyclicCohomologyMap_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) (n : ℕ) :
    cyclicCohomologyMap (M := M) (g.comp f) n =
      cyclicCohomologyMap (M := M) g n ≫ cyclicCohomologyMap (M := M) f n := by
  rw [cyclicCohomologyMap, cyclicCochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp]

end ComplexMap

end TauCeti
