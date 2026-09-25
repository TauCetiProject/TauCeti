/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import TauCeti.Algebra.Homology.Linear

/-!
# Linearity of Tate cohomology in the coefficient morphism

Mathlib shows that the Tate complex of a representation of a finite group is an additive functor
of the representation. This file records that it is moreover `k`-linear, and deduces that Tate
cohomology in each integer degree is an additive, `k`-linear functor: the map induced on
`tateCohomology · n` by `c • f` is `c` times the map induced by `f`.

## Main statements

* `TauCeti.TateCohomology.tateComplex_map_smul`: the chain map of Tate complexes induced by
  `c • f` is `c • tateComplex.map f`.
* The `Functor.Linear` instances on `tateComplexFunctor k G` and on `tateCohomologyFunctor n`,
  and the `Functor.Additive` instance on `tateCohomologyFunctor n`.
-/

public section

universe u

open CategoryTheory

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- The chain map of Tate complexes induced by a scalar multiple of a morphism of representations
is the scalar multiple of the induced chain map. -/
theorem tateComplex_map_smul {M N : Rep k G} (c : k) (f : M ⟶ N) :
    tateComplex.map (c • f) = c • tateComplex.map f := by
  have hchains : groupHomology.chainsMap (MonoidHom.id G) (c • f) =
      c • groupHomology.chainsMap (MonoidHom.id G) f := by
    ext i : 2
    ext a
    simp [Rep.smul_hom]
  ext (i | i) : 1
  -- In nonnegative degrees the component is that of `cochainsMap`, which is built from `f` by
  -- precomposition and so is linear in `f` by definition, as in Mathlib's `tateComplex.map_add`.
  · rfl
  -- In negative degrees the component is that of `chainsMap`; the remaining goal compares the
  -- scalar action on `tateComplex` morphisms with the one on `inhomogeneousChains` morphisms.
  · simp only [CochainComplex.ConnectData.map_f, hchains, HomologicalComplex.smul_f_apply]
    rfl

/-- The Tate complex is a `k`-linear functor of the representation. -/
instance : (tateComplexFunctor k G).Linear k where
  map_smul f c := tateComplex_map_smul c f

-- Typeclass search does not unfold the named `tateCohomologyFunctor` definition to find the
-- generic composition instances, so these expose them under the functor's public name.
/-- Tate cohomology in each degree is an additive functor of the representation. -/
instance (n : ℤ) : (tateCohomologyFunctor (R := k) (G := G) n).Additive :=
  inferInstanceAs (tateComplexFunctor k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) n).Additive

/-- Tate cohomology in each degree is a `k`-linear functor of the representation. -/
instance (n : ℤ) : (tateCohomologyFunctor (R := k) (G := G) n).Linear k :=
  inferInstanceAs <| Functor.Linear k (tateComplexFunctor k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) n)

end TauCeti.TateCohomology
