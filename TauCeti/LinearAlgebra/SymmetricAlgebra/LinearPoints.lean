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

/-- Naturality determines a transformation of linear point functors by its value at the
universal point `ι : M → Sym_R M`. -/
theorem linearPoints_naturality_ι (τ : linearPoints R M ⟶ linearPoints R N)
    (S : CommAlgCat.{max u v} R) (g : M →ₗ[R] S) :
    τ.app S g = (_root_.SymmetricAlgebra.lift g).toLinearMap.comp
      (τ.app (.of R (_root_.SymmetricAlgebra R M)) (_root_.SymmetricAlgebra.ι R M)) := by
  let h : CommAlgCat.of R (_root_.SymmetricAlgebra R M) ⟶ S :=
    ConcreteCategory.ofHom (_root_.SymmetricAlgebra.lift g)
  have hn : τ.app S ((_root_.SymmetricAlgebra.lift g).toLinearMap.comp
      (_root_.SymmetricAlgebra.ι R M)) =
      (_root_.SymmetricAlgebra.lift g).toLinearMap.comp
        (τ.app (.of R (_root_.SymmetricAlgebra R M)) (_root_.SymmetricAlgebra.ι R M)) :=
    ConcreteCategory.congr_hom (τ.naturality h) (_root_.SymmetricAlgebra.ι R M)
  have hg : (_root_.SymmetricAlgebra.lift g).toLinearMap.comp
      (_root_.SymmetricAlgebra.ι R M) = g :=
    LinearMap.ext (_root_.SymmetricAlgebra.lift_ι_apply g)
  exact (congrArg (τ.app S) hg).symm.trans hn

private theorem map_scalarCoaction_of_linearPoints_smul
    (τ : linearPoints R M ⟶ linearPoints R N)
    (hτ : ∀ (S : CommAlgCat.{max u v} R) (c : S) (g : M →ₗ[R] S),
      τ.app S (c • g) = c • (τ.app S g : N →ₗ[R] S)) :
    ∀ a, Polynomial.map (_root_.SymmetricAlgebra.lift
        (τ.app (.of R (_root_.SymmetricAlgebra R M))
          (_root_.SymmetricAlgebra.ι R M))).toRingHom
        (_root_.SymmetricAlgebra.scalarCoaction R N a) =
      _root_.SymmetricAlgebra.scalarCoaction R M (_root_.SymmetricAlgebra.lift
        (τ.app (.of R (_root_.SymmetricAlgebra R M)) (_root_.SymmetricAlgebra.ι R M)) a) := by
  let A := _root_.SymmetricAlgebra R M
  let p : N →ₗ[R] A := τ.app (.of R A) (_root_.SymmetricAlgebra.ι R M)
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
    have hn := ConcreteCategory.congr_hom (τ.naturality
      (CommAlgCat.ofHom (_root_.SymmetricAlgebra.scalarCoaction R M)))
      (_root_.SymmetricAlgebra.ι R M)
    exact hn.symm.trans ((congrArg (τ.app (.of R A[X])) hi).trans
      ((hτ (.of R A[X]) Polynomial.X j).trans (congrArg (Polynomial.X • ·) hC)))
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
    exact (congrArg (Polynomial.monomial 1)
      (_root_.SymmetricAlgebra.lift_ι_apply p n)).trans
      ((Polynomial.C_mul_X_eq_monomial (a := p n)).symm.trans
        ((mul_comm _ _).trans h.symm))
  exact _root_.AlgHom.congr_fun he a

/-- A scalar-equivariant natural transformation of affine linear-spectrum point functors is
precomposition with a unique linear map. Scalars range over every test algebra, so this holds
also in positive characteristic and over nonreduced base rings. -/
theorem existsUnique_linearMap_of_linearPoints_smul
    (τ : linearPoints R M ⟶ linearPoints R N)
    (hτ : ∀ (S : CommAlgCat.{max u v} R) (c : S) (g : M →ₗ[R] S),
      τ.app S (c • g) = c • (τ.app S g : N →ₗ[R] S)) :
    ∃! f : N →ₗ[R] M, ∀ (S : CommAlgCat.{max u v} R) (g : M →ₗ[R] S),
      τ.app S g = g.comp f := by
  let A := _root_.SymmetricAlgebra R M
  let p : N →ₗ[R] A := τ.app (.of R A) (_root_.SymmetricAlgebra.ι R M)
  let φ : _root_.SymmetricAlgebra R N →ₐ[R] A := _root_.SymmetricAlgebra.lift p
  have hφ := map_scalarCoaction_of_linearPoints_smul R τ hτ
  obtain ⟨f, hf, huniq⟩ :=
    (_root_.SymmetricAlgebra.map_scalarCoaction_eq_iff_existsUnique R φ).mp hφ
  refine ⟨f, ?_, ?_⟩
  · intro S g
    rw [linearPoints_naturality_ι]
    apply LinearMap.ext
    intro n
    have hp : p n = _root_.SymmetricAlgebra.ι R M (f n) := by
      have h := _root_.AlgHom.congr_fun hf (_root_.SymmetricAlgebra.ι R N n)
      simpa only [φ, _root_.SymmetricAlgebra.map_apply_ι,
        _root_.SymmetricAlgebra.lift_ι_apply] using h.symm
    exact (congrArg (_root_.SymmetricAlgebra.lift g) hp).trans
      (_root_.SymmetricAlgebra.lift_ι_apply g (f n))
  · intro f' hf'
    apply huniq
    apply _root_.SymmetricAlgebra.algHom_ext
    ext n
    have h := congrArg (fun g : N →ₗ[R] A ↦ g n)
      (hf' (.of R A) (_root_.SymmetricAlgebra.ι R M))
    exact ((_root_.SymmetricAlgebra.map_apply_ι R f' n).trans h.symm).trans
      (_root_.SymmetricAlgebra.lift_ι_apply p n).symm

end TauCeti.SymmetricAlgebra
