/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalization

/-!
# The normalized cubical chain complex functor

The normalized cubical chains of a topological space, with their boundary, form a chain complex
of modules over the coefficient ring, and continuous maps induce chain maps.  This packages the
concrete normalized cubical chains of `TauCeti.AlgebraicTopology.Singular.Cubical.Normalized` as a
functor `TopCat ⥤ ChainComplex (ModuleCat R) ℕ`, the form in which they are compared with the
simplicial singular chain complex.

## Main definitions

* `TauCeti.normalizedCubicalChainComplex R`: the functor sending a space to its normalized cubical
  chain complex with coefficients in `R`.
* `TauCeti.normalizedCubicalChainComplexXEquiv R X n`: its term in degree `n`, identified with the
  normalized cubical `n`-chains.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

variable (R : Type u) [Ring R]

/-- The **normalized cubical chain complex** of a topological space, with coefficients in `R`. -/
def normalizedCubicalChainComplexObj (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (NormalizedCubicalChain X R n))
    (fun n ↦ ModuleCat.ofHom (NormalizedCubicalChain.boundary X R n))
    fun n ↦ by
      rw [← ModuleCat.ofHom_comp, NormalizedCubicalChain.boundary_boundary]
      rfl

/-- The **normalized cubical chain complex functor**, with coefficients in `R`. -/
def normalizedCubicalChainComplex : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj X := normalizedCubicalChainComplexObj R X
  map f := ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (NormalizedCubicalChain.map R f.hom n)) fun n ↦ by
      simp only [normalizedCubicalChainComplexObj, ChainComplex.of_d,
        ← ModuleCat.ofHom_comp, NormalizedCubicalChain.map_boundary]
  map_id X := by
    ext n x
    simp [normalizedCubicalChainComplexObj]
  map_comp f g := by
    ext n x
    simp [normalizedCubicalChainComplexObj, NormalizedCubicalChain.map_comp]

variable {R}

@[simp]
theorem normalizedCubicalChainComplex_obj_X (X : TopCat.{u}) (n : ℕ) :
    ((normalizedCubicalChainComplex R).obj X).X n = ModuleCat.of R (NormalizedCubicalChain X R n) :=
  (rfl)

@[simp]
theorem normalizedCubicalChainComplex_obj_d_apply (X : TopCat.{u}) (n : ℕ)
    (x : NormalizedCubicalChain X R (n + 1)) :
    ((normalizedCubicalChainComplex R).obj X).d (n + 1) n x =
      NormalizedCubicalChain.boundary X R n x := by
  simp only [normalizedCubicalChainComplex, normalizedCubicalChainComplexObj, ChainComplex.of_d]
  rfl

@[simp]
theorem normalizedCubicalChainComplex_map_f_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : NormalizedCubicalChain X R n) :
    ((normalizedCubicalChainComplex R).map f).f n x = NormalizedCubicalChain.map R f.hom n x :=
  (rfl)

variable (R) in
/-- The term in degree `n` of the normalized cubical chain complex of `X` is the module of
normalized cubical `n`-chains. -/
def normalizedCubicalChainComplexXEquiv (X : TopCat.{u}) (n : ℕ) :
    ((normalizedCubicalChainComplex R).obj X).X n ≃ₗ[R] NormalizedCubicalChain X R n :=
  LinearEquiv.refl R _

/-- Under `normalizedCubicalChainComplexXEquiv`, the differential of the complex is the boundary of
normalized chains. -/
theorem normalizedCubicalChainComplexXEquiv_d (X : TopCat.{u}) (n : ℕ)
    (x : ((normalizedCubicalChainComplex R).obj X).X (n + 1)) :
    normalizedCubicalChainComplexXEquiv R X n
        (((normalizedCubicalChainComplex R).obj X).d (n + 1) n x) =
      NormalizedCubicalChain.boundary X R n
        (normalizedCubicalChainComplexXEquiv R X (n + 1) x) := by
  -- `normalizedCubicalChainComplexXEquiv` is the identity of the underlying modules.
  unfold normalizedCubicalChainComplexXEquiv
  exact normalizedCubicalChainComplex_obj_d_apply X n x

/-- Under `normalizedCubicalChainComplexXEquiv`, the chain map of a continuous map is its
push-forward of normalized chains. -/
theorem normalizedCubicalChainComplexXEquiv_map_f {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : ((normalizedCubicalChainComplex R).obj X).X n) :
    normalizedCubicalChainComplexXEquiv R Y n (((normalizedCubicalChainComplex R).map f).f n x) =
      NormalizedCubicalChain.map R f.hom n (normalizedCubicalChainComplexXEquiv R X n x) := by
  -- `normalizedCubicalChainComplexXEquiv` is the identity of the underlying modules.
  unfold normalizedCubicalChainComplexXEquiv
  exact normalizedCubicalChainComplex_map_f_apply f n x

/-- The terms of the normalized cubical chain complex are projective modules. -/
instance (X : TopCat.{u}) (n : ℕ) :
    Module.Projective R (((normalizedCubicalChainComplex R).obj X).X n) :=
  inferInstanceAs (Module.Projective R (NormalizedCubicalChain X R n))

end TauCeti
