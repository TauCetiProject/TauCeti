/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup

/-!
# Affine toric schemes of cones

The affine toric scheme associated to a cone is the spectrum of the complex monoid algebra of
its dual semigroup.  A compatible map of lattices carrying one cone into another induces a map
of dual semigroups in the opposite direction, hence a homomorphism of coordinate rings and,
after applying `Spec`, a morphism of affine toric schemes in the original direction.

This file fixes those carriers and proves their identity and composition laws.  No finite
generation hypothesis is needed to form the monoid algebra or its spectrum.  Finite generation
of the dual semigroup is the separate input that will later show that this affine scheme is of
finite type.

## Main declarations

* `TauCeti.Toric.affineCoordinateRing`: the complex monoid algebra of a dual semigroup.
* `TauCeti.Toric.affineToricScheme`: its affine spectrum.
* `TauCeti.Toric.affineCoordinateRingMap`: the contravariant coordinate-ring map induced by a
  compatible map of lattice cones.
* `TauCeti.Toric.affineToricSchemeMap`: the resulting covariant morphism of affine schemes.

## References

The construction follows §1.2 of W. Fulton, *Introduction to Toric Varieties*, and §§1.1–1.3 of
D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric

universe u

variable {V V' V'' : Type*} [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'} {υ : PointedCone ℝ V''}

/-! ### Coordinate rings -/

section CoordinateRing

variable {N N' N'' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

/-- The coordinate ring of the affine toric chart of a cone: the complex monoid algebra of its
dual semigroup. -/
abbrev affineCoordinateRing (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :=
  MonoidAlgebra ℂ (Multiplicative (dualSemigroup hi σ))

/-- A compatible map of lattices carrying `σ` into `τ` induces the homomorphism from the
coordinate ring of `τ` to the coordinate ring of `σ`. -/
noncomputable def affineCoordinateRingMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) :
    affineCoordinateRing hi' τ →ₐ[ℂ] affineCoordinateRing hi σ :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ
    (AddMonoidHom.toMultiplicative (dualSemigroupMap hi hi' f g hfg hστ))

/-- The coordinate-ring map sends the monomial of a character to the monomial of its pullback. -/
@[simp]
theorem affineCoordinateRingMap_single (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ)
    (m : dualSemigroup hi' τ) (z : ℂ) :
    affineCoordinateRingMap hi hi' f g hfg hστ
        (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd (dualSemigroupMap hi hi' f g hfg hστ m)) z := by
  simp [affineCoordinateRingMap]

/-- The identity map of a lattice cone induces the identity of its coordinate ring. -/
@[simp]
theorem affineCoordinateRingMap_id (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    affineCoordinateRingMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        (fun _ hx ↦ hx) = AlgHom.id ℂ (affineCoordinateRing hi σ) := by
  simp only [affineCoordinateRingMap, dualSemigroupMap_id, AddMonoidHom.toMultiplicative_id,
    MonoidAlgebra.mapDomainAlgHom_id]

/-- Coordinate-ring maps reverse composition, as required by their contravariance in cones. -/
@[simp]
theorem affineCoordinateRingMap_comp (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (hi'' : IsIntegralLattice i'')
    (f : N →+ N') (f' : N' →+ N'') (g : V →ₗ[ℝ] V') (g' : V' →ₗ[ℝ] V'')
    (hfg : ∀ n, g (i n) = i' (f n)) (hf'g' : ∀ n, g' (i' n) = i'' (f' n))
    (hστ : Set.MapsTo g σ τ) (hτυ : Set.MapsTo g' τ υ) :
    (affineCoordinateRingMap hi hi' f g hfg hστ).comp
        (affineCoordinateRingMap hi' hi'' f' g' hf'g' hτυ) =
      affineCoordinateRingMap hi hi'' (f'.comp f) (g'.comp g)
        (fun n ↦ by simp [hfg, hf'g']) (hτυ.comp hστ) := by
  refine MonoidAlgebra.algHom_ext (fun m ↦ ?_) (by ext)
  obtain ⟨m, rfl⟩ := ofAdd.surjective m
  simp [dualSemigroupMap_comp hi hi' hi'' f f' g g' hfg hf'g' hστ hτυ]

end CoordinateRing

/-! ### Affine spectra -/

section Scheme

/- Morphisms of schemes require a common universe, and the coordinate ring of a lattice `N`
lives in the universe of `N`; the ambient real vector spaces remain universe-polymorphic. -/
variable {N N' N'' : Type u} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

/-- The affine toric scheme associated to a cone is the spectrum of its complex monoid algebra. -/
noncomputable abbrev affineToricScheme (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    Scheme :=
  Spec (.of (affineCoordinateRing hi σ))

/-- A compatible map of lattice cones induces a morphism of their affine toric schemes. -/
noncomputable def affineToricSchemeMap (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) :
    affineToricScheme hi σ ⟶ affineToricScheme hi' τ :=
  Spec.map (CommRingCat.ofHom (affineCoordinateRingMap hi hi' f g hfg hστ).toRingHom)

/-- The affine toric morphism is `Spec` of the induced coordinate-ring map. -/
theorem affineToricSchemeMap_def (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) :
    affineToricSchemeMap hi hi' f g hfg hστ =
      Spec.map (CommRingCat.ofHom (affineCoordinateRingMap hi hi' f g hfg hστ).toRingHom) :=
  (rfl)

/-- The identity map of a lattice cone induces the identity of its affine toric scheme. -/
@[simp]
theorem affineToricSchemeMap_id (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    affineToricSchemeMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        (fun _ hx ↦ hx) = 𝟙 (affineToricScheme hi σ) := by
  simp only [affineToricSchemeMap, affineCoordinateRingMap_id]
  exact Spec.map_id _

/-- Applying `Spec` restores covariance: the morphism of a composite cone map is the composite
of the corresponding affine toric morphisms. -/
@[simp]
theorem affineToricSchemeMap_comp (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (hi'' : IsIntegralLattice i'')
    (f : N →+ N') (f' : N' →+ N'') (g : V →ₗ[ℝ] V') (g' : V' →ₗ[ℝ] V'')
    (hfg : ∀ n, g (i n) = i' (f n)) (hf'g' : ∀ n, g' (i' n) = i'' (f' n))
    (hστ : Set.MapsTo g σ τ) (hτυ : Set.MapsTo g' τ υ) :
    affineToricSchemeMap hi hi' f g hfg hστ ≫
        affineToricSchemeMap hi' hi'' f' g' hf'g' hτυ =
      affineToricSchemeMap hi hi'' (f'.comp f) (g'.comp g)
        (fun n ↦ by simp [hfg, hf'g']) (hτυ.comp hστ) := by
  rw [affineToricSchemeMap, affineToricSchemeMap, affineToricSchemeMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg CommRingCat.ofHom <| congrArg AlgHom.toRingHom
    (affineCoordinateRingMap_comp hi hi' hi'' f f' g g' hfg hf'g' hστ hτυ)

end Scheme

end TauCeti.Toric
