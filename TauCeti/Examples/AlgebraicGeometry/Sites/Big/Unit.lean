/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Defs
public import TauCeti.AlgebraicGeometry.Sites.Big.Unit

/-!
# Examples: values of the big-site module of the structure sheaf

Let `S` be a scheme. The big-site module `(𝒪_S)^a : (T, h) ↦ Γ(T, h^* 𝒪_S)` of the structure
sheaf is the unit module over the big structure sheaf (`AlgebraicGeometry.Scheme.bigSheafUnitIso`),
so its value on an affine test scheme `Spec R ⟶ S` is `R`, as a module over the value
`Γ(Spec R, 𝒪) ≅ R` of the big structure sheaf:

* for every `S`-scheme `T`, `(𝒪_S)^a(T) = Γ(T, 𝒪_T)` as `Γ(T, 𝒪_T)`-modules, and for every
  affine `S`-scheme `Spec R`, `(𝒪_S)^a(Spec R) = R`, are the library equivalences
  `AlgebraicGeometry.Scheme.bigSheafUnitObjLinearEquiv` and
  `AlgebraicGeometry.Scheme.bigSheafUnitObjSpecEquiv`; this file specialises them:
* for `S = Spec k` and a ring `L` over `k`, `(𝒪_S)^a(Spec L) = L`: the value at `Spec k` over
  itself is `k`, and the value at `Spec k[t]` is `k[t]`;
* over `Spec ℚ`, `(𝒪_S)^a(Spec ℚ(i)) = ℚ(i)`, here `ℚ(i) = ℚ ⊕ ℚi` with `i² = -1`, a
  two-dimensional `ℚ`-vector space. The topological inverse image of `𝒪_{Spec ℚ}` along
  `Spec ℚ(i) ⟶ Spec ℚ` has global sections `ℚ`, while the big-site value is not even additively
  isomorphic to `ℚ`, so the big-site module is not computed by the topological inverse image.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Polynomial

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace TauCeti.AlgebraicGeometry.BigSheafUnitExamples

universe u

/-- **`F^a(Spec L) = L` for `F = 𝒪_S`, `S = Spec k`.** For a commutative `k`-algebra `L`, the
big-site module of the structure sheaf of `Spec k` has value `L` on `Spec L ⟶ Spec k`. -/
noncomputable def bigSheafUnitObjSpecAlgebraEquiv (k L : Type u) [CommRing k] [CommRing L]
    [Algebra k L] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ≃ₛₗ[RingHomClass.toRingHom
        (Scheme.bigRingCatSheafObjSpecRingEquiv _ (.of L)
          (Spec.map (CommRingCat.ofHom (algebraMap k L))))]
      L :=
  Scheme.bigSheafUnitObjSpecEquiv _ (.of L) _

/-- **Evaluation at `Spec k` over itself is `k`.** -/
noncomputable def bigSheafUnitObjSpecSelfEquiv (k : Type u) [CommRing k] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (𝟙 (Spec (.of k))))) ≃ₛₗ[RingHomClass.toRingHom
        (Scheme.bigRingCatSheafObjSpecRingEquiv _ (.of k) (𝟙 (Spec (.of k))))] k :=
  Scheme.bigSheafUnitObjSpecEquiv _ (.of k) _

/-- **Over `Spec k`, evaluation at `Spec k[t]` is `k[t]`.** -/
noncomputable def bigSheafUnitObjSpecPolynomialEquiv (k : Type u) [CommRing k] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))))) ≃ₛₗ[RingHomClass.toRingHom
        (Scheme.bigRingCatSheafObjSpecRingEquiv _ (.of k[X])
          (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))))]
      k[X] :=
  bigSheafUnitObjSpecAlgebraEquiv k k[X]

/-- The Gaussian rationals `ℚ(i) = ℚ ⊕ ℚi`, `i² = -1`, as Mathlib's quadratic algebra. -/
abbrev GaussianRat : Type := QuadraticAlgebra ℚ (-1) 0

/-- **`(𝒪_{Spec ℚ})^a(Spec ℚ(i)) = ℚ(i)`.** -/
noncomputable def bigSheafUnitObjSpecGaussianRatEquiv :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of ℚ)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ GaussianRat))))) ≃ₛₗ[
        RingHomClass.toRingHom (Scheme.bigRingCatSheafObjSpecRingEquiv _ (.of GaussianRat)
          (Spec.map (CommRingCat.ofHom (algebraMap ℚ GaussianRat))))] GaussianRat :=
  bigSheafUnitObjSpecAlgebraEquiv ℚ GaussianRat

/-- **`(𝒪_{Spec ℚ})^a(Spec ℚ(i))` is not the topological inverse image's `ℚ`.** The topological
inverse image of `𝒪_{Spec ℚ}` along `Spec ℚ(i) ⟶ Spec ℚ` has global sections `ℚ` (the underlying
space of `Spec ℚ(i)` is a point), whereas the big-site value is not even additively isomorphic
to `ℚ`, since it is the two-dimensional `ℚ`-vector space `ℚ(i)`. -/
theorem isEmpty_bigSheafUnitObjSpecGaussianRat_addEquiv_rat :
    IsEmpty ((Scheme.Modules.bigSheaf
      (MonoidalCategoryStruct.tensorUnit (Spec (.of ℚ)).Modules)).val.obj
        (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ GaussianRat))))) ≃+ ℚ) := by
  refine ⟨fun e ↦ ?_⟩
  let f : GaussianRat ≃+ ℚ := bigSheafUnitObjSpecGaussianRatEquiv.toAddEquiv.symm.trans e
  have := (LinearEquiv.ofBijective f.toAddMonoidHom.toRatLinearMap f.bijective).finrank_eq
  rw [QuadraticAlgebra.finrank_eq_two, Module.finrank_self] at this
  exact absurd this (by norm_num)

end TauCeti.AlgebraicGeometry.BigSheafUnitExamples
