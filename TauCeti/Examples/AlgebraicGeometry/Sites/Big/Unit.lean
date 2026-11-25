/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.AlgebraicGeometry.Sites.Big.Unit

/-!
# Examples: values of the big-site module of the structure sheaf

Let `S` be a scheme. The big-site module `(𝒪_S)^a : (T, h) ↦ Γ(T, h^* 𝒪_S)` of the structure
sheaf is the unit module over the big structure sheaf (`AlgebraicGeometry.Scheme.bigSheafUnitIso`),
so its value on an affine test scheme `Spec R ⟶ S` is `R`, linearly over `R`:

* for every `S`-scheme `T`, `(𝒪_S)^a(T) = Γ(T, 𝒪_T)`;
* for `S = Spec k` and a ring `L` over `k`, `(𝒪_S)^a(Spec L) = L`: the value at `Spec k` over
  itself is `k`, and the value at `Spec k[t]` is `k[t]`;
* over `Spec ℚ`, `(𝒪_S)^a(Spec ℚ(i)) = ℚ(i)`, here `ℚ(i) = ℚ[X]/(X² + 1)`, a two-dimensional
  `ℚ`-vector space. The topological inverse image of `𝒪_{Spec ℚ}` along `Spec ℚ(i) ⟶ Spec ℚ` has
  global sections `ℚ`, so the big-site module is not computed by the topological inverse image.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Polynomial

namespace TauCeti.AlgebraicGeometry.BigSheafUnitExamples

universe u

variable {S : Scheme.{u}}

/-- **`(𝒪_S)^a(T) = Γ(T, 𝒪_T)`.** The value of the big-site module of the structure sheaf on an
`S`-scheme `T`, through `bigSheafUnitIso`. -/
noncomputable def bigSheafUnitObjAddEquiv (T : Over S) :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit S.Modules)).val.obj (op T) ≃+
      Γ(T.left, ⊤) :=
  ((SheafOfModules.evaluation _ (op T)).mapIso (Scheme.bigSheafUnitIso S)).toLinearEquiv.toAddEquiv

/-- On sections, `bigSheafUnitObjAddEquiv` is the identification `h^* 𝒪_S ≅ 𝒪_T` on global
sections. -/
lemma bigSheafUnitObjAddEquiv_apply (T : Over S)
    (x : Γ((Scheme.Modules.pullback T.hom).obj (MonoidalCategoryStruct.tensorUnit S.Modules), ⊤)) :
    bigSheafUnitObjAddEquiv T x =
      (Scheme.Modules.pullbackObjUnitIso T.hom).hom.app ⊤ x :=
  Scheme.bigSheafUnitIso_hom_val_app_apply S T x

/-- **`(𝒪_S)^a(Spec R) = R`.** On an affine test scheme `h : Spec R ⟶ S`, the big-site module of
the structure sheaf has value `R`. -/
noncomputable def bigSheafUnitObjSpecEquiv (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit S.Modules)).val.obj
      (op (Over.mk h)) ≃+ R :=
  (bigSheafUnitObjAddEquiv (Over.mk h)).trans
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toAddEquiv

/-- **`F^a(Spec L) = L` for `F = 𝒪_S`, `S = Spec k`.** For a commutative `k`-algebra `L`, the
big-site module of the structure sheaf of `Spec k` has value `L` on `Spec L ⟶ Spec k`. -/
noncomputable def bigSheafUnitObjSpecAlgebraEquiv (k L : Type u) [CommRing k] [CommRing L]
    [Algebra k L] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ≃+ L :=
  bigSheafUnitObjSpecEquiv (.of L) _

/-- **Evaluation at `Spec k` over itself is `k`.** -/
noncomputable def bigSheafUnitObjSpecSelfEquiv (k : Type u) [CommRing k] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (𝟙 (Spec (.of k))))) ≃+ k :=
  bigSheafUnitObjSpecEquiv (.of k) _

/-- **Over `Spec k`, evaluation at `Spec k[t]` is `k[t]`.** -/
noncomputable def bigSheafUnitObjSpecPolynomialEquiv (k : Type u) [CommRing k] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))))) ≃+ k[X] :=
  bigSheafUnitObjSpecAlgebraEquiv k k[X]

/-- The Gaussian rationals `ℚ(i) = ℚ[X]/(X² + 1)`. -/
abbrev GaussianRat : Type := AdjoinRoot (X ^ 2 + 1 : ℚ[X])

/-- **`(𝒪_{Spec ℚ})^a(Spec ℚ(i)) = ℚ(i)`.** -/
noncomputable def bigSheafUnitObjSpecGaussianRatEquiv :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of ℚ)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ GaussianRat))))) ≃+ GaussianRat :=
  bigSheafUnitObjSpecAlgebraEquiv ℚ GaussianRat

/-- `ℚ(i)` is two-dimensional over `ℚ`, so `(𝒪_{Spec ℚ})^a(Spec ℚ(i))` is not the module `ℚ` of
global sections of the topological inverse image of `𝒪_{Spec ℚ}` (the underlying space of
`Spec ℚ(i)` is a point). -/
theorem finrank_gaussianRat : Module.finrank ℚ GaussianRat = 2 := by
  have hm : (X ^ 2 + 1 : ℚ[X]).Monic := by monicity!
  rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim]
  compute_degree!

end TauCeti.AlgebraicGeometry.BigSheafUnitExamples
