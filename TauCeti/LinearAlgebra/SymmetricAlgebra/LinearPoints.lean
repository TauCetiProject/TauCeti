/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Scalar

/-!
# Scalar-equivariant natural transformations of linear point functors

The functor `S ↦ (M →ₗ[R] S)` on commutative `R`-algebras is the functor of points of
`Spec (Sym_R M)`. A natural transformation from the points of `M` to the points of `N`
that commutes with multiplication by elements of every test algebra comes from a unique
linear map `N →ₗ[R] M`. Thus scalar equivariance already forces additivity. There is no
reducedness or characteristic assumption on the base ring, and no freeness or finiteness
assumption on the modules.

Naturality expresses every value in terms of the universal point `M → Sym_R M`. Testing
scalar equivariance in `(Sym_R M)[X]`, at the indeterminate `X`, gives equivariance for
`SymmetricAlgebra.scalarCoaction`. Its recognition theorem
`SymmetricAlgebra.map_scalarCoaction_eq_iff_existsUnique` recovers the linear map.
Testing only scalars in `R` would not suffice over finite rings.

## References

* The Stacks Project, Tag 01M1 (vector bundles).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

open CategoryTheory Polynomial

namespace TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommMonoid M] [Module R M]

/-- The functor of points of the affine linear spectrum of `M`: its points over a commutative
`R`-algebra `S` are the `R`-linear maps `M → S`. -/
-- An abbreviation so that scalar actions on components use the usual linear-map instances.
abbrev linearPoints : CommAlgCat.{max u v} R ⥤ Type (max u v) where
  obj S := M →ₗ[R] S
  map h := TypeCat.ofHom fun g ↦ h.hom.toLinearMap.comp g
  map_id S := by ext g m; rfl
  map_comp h k := by ext g m; rfl

/-- The points of a linear spectrum over `S` are linear functionals with values in `S`. -/
@[simp]
theorem linearPoints_obj (S : CommAlgCat.{max u v} R) :
    (linearPoints R M).obj S = (M →ₗ[R] S) := (rfl)

/-- A test-algebra morphism postcomposes the corresponding linear functionals. -/
@[simp]
theorem linearPoints_map_apply {S T : CommAlgCat.{max u v} R} (h : S ⟶ T)
    (g : M →ₗ[R] S) :
    (linearPoints R M).map h g = h.hom.toLinearMap.comp g := (rfl)

variable {M} {N : Type v} [AddCommMonoid N] [Module R N]

/-- A linear map induces a transformation of linear point functors by precomposition. -/
def linearPointsMap (f : N →ₗ[R] M) : linearPoints R M ⟶ linearPoints R N where
  app S := TypeCat.ofHom fun g ↦ g.comp f
  naturality S T h := by ext g n; rfl

/-- The transformation induced by `f` precomposes every test-algebra-valued functional with `f`. -/
@[simp]
theorem linearPointsMap_app_apply (f : N →ₗ[R] M)
    (S : CommAlgCat.{max u v} R) (g : M →ₗ[R] S) :
    (linearPointsMap R f).app S g = g.comp f := (rfl)

/-- Precomposition with the identity is the identity transformation. -/
@[simp]
theorem linearPointsMap_id : linearPointsMap R (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  ext S g m
  rfl

/-- Precomposition reverses composition of linear maps. -/
@[simp]
theorem linearPointsMap_comp {P : Type v} [AddCommMonoid P] [Module R P]
    (f : N →ₗ[R] M) (g : P →ₗ[R] N) :
    linearPointsMap R (f.comp g) = linearPointsMap R f ≫ linearPointsMap R g := by
  ext S h m
  rfl

/-- Precomposition commutes with scalars in every test algebra. -/
@[simp]
theorem linearPointsMap_app_smul (f : N →ₗ[R] M)
    (S : CommAlgCat.{max u v} R) (c : S) (g : M →ₗ[R] S) :
    (linearPointsMap R f).app S (c • g) = c • (linearPointsMap R f).app S g := by
  ext n
  rfl

/-- A linear map is determined by its transformation on linear point functors. -/
theorem linearPointsMap_injective :
    Function.Injective (linearPointsMap R : (N →ₗ[R] M) → _) := by
  intro f g h
  ext n
  apply ι_injective R M
  exact congrArg (fun τ ↦ (τ.app (.of R (_root_.SymmetricAlgebra R M))
    (_root_.SymmetricAlgebra.ι R M)) n) h

/-- The value of a transformation at the universal point `M → Sym_R M`. -/
def linearPointsUniversalValue (τ : linearPoints R M ⟶ linearPoints R N) :
    N →ₗ[R] _root_.SymmetricAlgebra R M :=
  τ.app (.of R (_root_.SymmetricAlgebra R M)) (_root_.SymmetricAlgebra.ι R M)

/-- The universal value is evaluation at the canonical map into the symmetric algebra. -/
@[simp]
theorem linearPointsUniversalValue_eq (τ : linearPoints R M ⟶ linearPoints R N) :
    linearPointsUniversalValue R τ =
      τ.app (.of R (_root_.SymmetricAlgebra R M)) (_root_.SymmetricAlgebra.ι R M) := (rfl)

/-- Every component is obtained by postcomposing the universal value with the lift of its
argument. -/
theorem linearPoints_app_eq_lift_comp_universalValue
    (τ : linearPoints R M ⟶ linearPoints R N)
    (S : CommAlgCat.{max u v} R) (g : M →ₗ[R] S) :
    τ.app S g = (_root_.SymmetricAlgebra.lift g).toLinearMap.comp
      (linearPointsUniversalValue R τ) := by
  let h : CommAlgCat.of R (_root_.SymmetricAlgebra R M) ⟶ S :=
    ConcreteCategory.ofHom (_root_.SymmetricAlgebra.lift g)
  have hn : τ.app S ((_root_.SymmetricAlgebra.lift g).toLinearMap.comp
      (_root_.SymmetricAlgebra.ι R M)) =
      (_root_.SymmetricAlgebra.lift g).toLinearMap.comp
        (linearPointsUniversalValue R τ) :=
    ConcreteCategory.congr_hom (τ.naturality h) (_root_.SymmetricAlgebra.ι R M)
  simpa only [AlgHom.toLinearMap_eq_coe, _root_.SymmetricAlgebra.lift_comp_ι] using hn

private theorem map_scalarCoaction_of_linearPoints_smul
    (τ : linearPoints R M ⟶ linearPoints R N)
    (hτ : ∀ (S : CommAlgCat.{max u v} R) (c : S) (g : M →ₗ[R] S),
      τ.app S (c • g) = c • (τ.app S g : N →ₗ[R] S)) :
    ∀ a, Polynomial.map (_root_.SymmetricAlgebra.lift
        (linearPointsUniversalValue R τ)).toRingHom
        (_root_.SymmetricAlgebra.scalarCoaction R N a) =
      _root_.SymmetricAlgebra.scalarCoaction R M (_root_.SymmetricAlgebra.lift
        (linearPointsUniversalValue R τ) a) := by
  let A := _root_.SymmetricAlgebra R M
  let p := linearPointsUniversalValue R τ
  let φ : _root_.SymmetricAlgebra R N →ₐ[R] A := _root_.SymmetricAlgebra.lift p
  intro a
  let C : A →ₐ[R] A[X] := Polynomial.CAlgHom
  let j : M →ₗ[R] A[X] := C.toLinearMap.comp (_root_.SymmetricAlgebra.ι R M)
  have hC : τ.app (.of R A[X]) j = C.toLinearMap.comp p := by
    exact ConcreteCategory.congr_hom (τ.naturality (CommAlgCat.ofHom C))
      (_root_.SymmetricAlgebra.ι R M)
  have hi : (_root_.SymmetricAlgebra.scalarCoaction R M).toLinearMap.comp
      (_root_.SymmetricAlgebra.ι R M) = (Polynomial.X : A[X]) • j := by
    apply LinearMap.ext
    intro m
    simp only [j, C, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      _root_.SymmetricAlgebra.scalarCoaction_ι, LinearMap.smul_apply,
      Polynomial.CAlgHom_apply, smul_eq_mul]
    rw [mul_comm, Polynomial.C_mul_X_eq_monomial]
  have hs : (_root_.SymmetricAlgebra.scalarCoaction R M).toLinearMap.comp p =
      (Polynomial.X : A[X]) • C.toLinearMap.comp p := by
    have hn : τ.app (.of R A[X])
        ((_root_.SymmetricAlgebra.scalarCoaction R M).toLinearMap.comp
          (_root_.SymmetricAlgebra.ι R M)) =
        (_root_.SymmetricAlgebra.scalarCoaction R M).toLinearMap.comp p :=
      ConcreteCategory.congr_hom (τ.naturality
        (CommAlgCat.ofHom (_root_.SymmetricAlgebra.scalarCoaction R M)))
        (_root_.SymmetricAlgebra.ι R M)
    rw [← hn, hi, hτ, hC]
  have he : (Polynomial.mapAlgHom φ).comp (_root_.SymmetricAlgebra.scalarCoaction R N) =
      (_root_.SymmetricAlgebra.scalarCoaction R M).comp φ := by
    apply _root_.SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro n
    have h := congrArg (fun g : N →ₗ[R] A[X] ↦ g n) hs
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
      C, Polynomial.CAlgHom_apply, smul_eq_mul] at h
    simp only [LinearMap.comp_apply, ← AlgHom.toLinearMap_eq_coe,
      AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      _root_.SymmetricAlgebra.scalarCoaction_ι, Polynomial.coe_mapAlgHom,
      Polynomial.map_monomial, φ, _root_.SymmetricAlgebra.lift_ι_apply]
    calc
      _ = Polynomial.monomial 1 (p n) :=
        congrArg (Polynomial.monomial 1) (_root_.SymmetricAlgebra.lift_ι_apply p n)
      _ = _ := by
        simpa only [← Polynomial.C_mul_X_eq_monomial, mul_comm] using h.symm
  exact _root_.AlgHom.congr_fun he a

/-- A scalar-equivariant natural transformation of affine linear-spectrum point functors is
precomposition with a unique linear map. Scalars range over every test algebra, so this holds
also in positive characteristic and over nonreduced base rings. -/
theorem existsUnique_linearMap_of_linearPoints_smul
    (τ : linearPoints R M ⟶ linearPoints R N)
    (hτ : ∀ (S : CommAlgCat.{max u v} R) (c : S) (g : M →ₗ[R] S),
      τ.app S (c • g) = c • (τ.app S g : N →ₗ[R] S)) :
    ∃! f : N →ₗ[R] M, τ = linearPointsMap R f := by
  let p := linearPointsUniversalValue R τ
  let φ := _root_.SymmetricAlgebra.lift p
  obtain ⟨f, hf, _⟩ :=
    (_root_.SymmetricAlgebra.map_scalarCoaction_eq_iff_existsUnique R φ).mp
      (map_scalarCoaction_of_linearPoints_smul R τ hτ)
  have hp (n : N) : p n = _root_.SymmetricAlgebra.ι R M (f n) := by
    have h := _root_.AlgHom.congr_fun hf (_root_.SymmetricAlgebra.ι R N n)
    simpa only [φ, _root_.SymmetricAlgebra.map_apply_ι,
      _root_.SymmetricAlgebra.lift_ι_apply] using h.symm
  have hτf : τ = linearPointsMap R f := by
    apply NatTrans.ext
    funext S
    apply ConcreteCategory.hom_ext
    intro g
    rw [linearPoints_app_eq_lift_comp_universalValue, linearPointsMap_app_apply]
    ext n
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [hp, _root_.SymmetricAlgebra.lift_ι_apply]
  refine ⟨f, hτf, ?_⟩
  intro f' hf'
  apply linearPointsMap_injective R
  rw [← hf', ← hτf]

/-- A transformation of linear point functors commutes with every test-algebra scalar exactly
when it is induced by a linear map. -/
theorem linearPoints_smul_iff_exists_linearMap
    (τ : linearPoints R M ⟶ linearPoints R N) :
    (∀ (S : CommAlgCat.{max u v} R) (c : S) (g : M →ₗ[R] S),
      τ.app S (c • g) = c • (τ.app S g : N →ₗ[R] S)) ↔
      ∃ f : N →ₗ[R] M, τ = linearPointsMap R f := by
  constructor
  · intro hτ
    exact (existsUnique_linearMap_of_linearPoints_smul R τ hτ).exists
  · rintro ⟨f, rfl⟩ S c g
    exact linearPointsMap_app_smul R f S c g

/-- Scalar equivariance of a natural transformation of linear point functors forces
additivity on every test algebra. -/
theorem linearPoints_add_of_smul (τ : linearPoints R M ⟶ linearPoints R N)
    (hτ : ∀ (S : CommAlgCat.{max u v} R) (c : S) (g : M →ₗ[R] S),
      τ.app S (c • g) = c • (τ.app S g : N →ₗ[R] S))
    (S : CommAlgCat.{max u v} R) (p q : M →ₗ[R] S) :
    τ.app S (p + q) = τ.app S p + τ.app S q := by
  obtain ⟨f, rfl⟩ := (linearPoints_smul_iff_exists_linearMap R τ).mp hτ
  simp only [linearPointsMap_app_apply R f, LinearMap.add_comp]

end TauCeti.SymmetricAlgebra
