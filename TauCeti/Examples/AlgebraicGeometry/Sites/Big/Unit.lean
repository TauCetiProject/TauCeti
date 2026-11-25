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
so its value on an affine test scheme `Spec R ⟶ S` is `R`, as a module over the value
`Γ(Spec R, 𝒪) ≅ R` of the big structure sheaf:

* for every `S`-scheme `T`, `(𝒪_S)^a(T) = Γ(T, 𝒪_T)` as `Γ(T, 𝒪_T)`-modules;
* for `S = Spec k` and a ring `L` over `k`, `(𝒪_S)^a(Spec L) = L`: the value at `Spec k` over
  itself is `k`, and the value at `Spec k[t]` is `k[t]`;
* over `Spec ℚ`, `(𝒪_S)^a(Spec ℚ(i)) = ℚ(i)`, here `ℚ(i) = ℚ[X]/(X² + 1)`, a two-dimensional
  `ℚ`-vector space. The topological inverse image of `𝒪_{Spec ℚ}` along `Spec ℚ(i) ⟶ Spec ℚ` has
  global sections `ℚ`, while the big-site value is not even additively isomorphic to `ℚ`, so the
  big-site module is not computed by the topological inverse image.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Polynomial

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace TauCeti.AlgebraicGeometry.BigSheafUnitExamples

universe u

variable {S : Scheme.{u}}

/-- **`(𝒪_S)^a(T) = Γ(T, 𝒪_T)`.** The value of the big-site module of the structure sheaf on an
`S`-scheme `T`, as a module over the value `Γ(T, 𝒪_T)` of the big structure sheaf, through
`bigSheafUnitIso`. -/
noncomputable def bigSheafUnitObjLinearEquiv (T : Over S) :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit S.Modules)).val.obj (op T) ≃ₗ[
      S.bigRingCatSheaf.obj.obj (op T)] S.bigRingCatSheaf.obj.obj (op T) :=
  ((SheafOfModules.evaluation _ (op T)).mapIso (Scheme.bigSheafUnitIso S)).toLinearEquiv

/-- On sections, `bigSheafUnitObjLinearEquiv` is the identification `h^* 𝒪_S ≅ 𝒪_T` on global
sections. -/
lemma bigSheafUnitObjLinearEquiv_apply (T : Over S)
    (x : Γ((Scheme.Modules.pullback T.hom).obj (MonoidalCategoryStruct.tensorUnit S.Modules), ⊤)) :
    bigSheafUnitObjLinearEquiv T x = (Scheme.Modules.pullbackObjUnitIso T.hom).hom.app ⊤ x :=
  Scheme.bigSheafUnitIso_hom_val_app_apply S T x

/-- The value of the big structure sheaf on an affine test scheme `h : Spec R ⟶ S` is `R`: the ring
equivalence `Γ(Spec R, 𝒪) ≃+* R` of `Scheme.ΓSpecIso`, on the scalar ring of the big-site modules
at `Spec R`. -/
noncomputable def bigRingCatSheafObjSpecRingEquiv (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    S.bigRingCatSheaf.obj.obj (op (Over.mk h)) ≃+* R :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

/-- **`(𝒪_S)^a(Spec R) = R`.** On an affine test scheme `h : Spec R ⟶ S`, the big-site module of
the structure sheaf has value `R`, semilinearly along `bigRingCatSheafObjSpecRingEquiv`. -/
noncomputable def bigSheafUnitObjSpecEquiv (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit S.Modules)).val.obj
      (op (Over.mk h)) ≃ₛₗ[RingHomClass.toRingHom (bigRingCatSheafObjSpecRingEquiv R h)] R :=
  (bigSheafUnitObjLinearEquiv (Over.mk h)).trans
    (bigRingCatSheafObjSpecRingEquiv R h).toSemilinearEquiv

/-- On sections, `bigSheafUnitObjSpecEquiv` is the identification `h^* 𝒪_S ≅ 𝒪_{Spec R}` on global
sections, followed by `Γ(Spec R, 𝒪) ≅ R`. -/
lemma bigSheafUnitObjSpecEquiv_apply (R : CommRingCat.{u}) (h : Spec R ⟶ S)
    (x : Γ((Scheme.Modules.pullback h).obj (MonoidalCategoryStruct.tensorUnit S.Modules), ⊤)) :
    bigSheafUnitObjSpecEquiv R h x =
      (Scheme.ΓSpecIso R).hom ((Scheme.Modules.pullbackObjUnitIso h).hom.app ⊤ x) :=
  congrArg (Scheme.ΓSpecIso R).hom (bigSheafUnitObjLinearEquiv_apply (Over.mk h) x)

/-- **`F^a(Spec L) = L` for `F = 𝒪_S`, `S = Spec k`.** For a commutative `k`-algebra `L`, the
big-site module of the structure sheaf of `Spec k` has value `L` on `Spec L ⟶ Spec k`. -/
noncomputable def bigSheafUnitObjSpecAlgebraEquiv (k L : Type u) [CommRing k] [CommRing L]
    [Algebra k L] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ≃ₛₗ[RingHomClass.toRingHom
        (bigRingCatSheafObjSpecRingEquiv (.of L) (Spec.map (CommRingCat.ofHom (algebraMap k L))))]
      L :=
  bigSheafUnitObjSpecEquiv (.of L) _

/-- **Evaluation at `Spec k` over itself is `k`.** -/
noncomputable def bigSheafUnitObjSpecSelfEquiv (k : Type u) [CommRing k] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (𝟙 (Spec (.of k))))) ≃ₛₗ[RingHomClass.toRingHom
        (bigRingCatSheafObjSpecRingEquiv (.of k) (𝟙 (Spec (.of k))))] k :=
  bigSheafUnitObjSpecEquiv (.of k) _

/-- **Over `Spec k`, evaluation at `Spec k[t]` is `k[t]`.** -/
noncomputable def bigSheafUnitObjSpecPolynomialEquiv (k : Type u) [CommRing k] :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of k)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))))) ≃ₛₗ[RingHomClass.toRingHom
        (bigRingCatSheafObjSpecRingEquiv (.of k[X])
          (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))))]
      k[X] :=
  bigSheafUnitObjSpecAlgebraEquiv k k[X]

/-- The Gaussian rationals `ℚ(i) = ℚ[X]/(X² + 1)`. -/
abbrev GaussianRat : Type := AdjoinRoot (X ^ 2 + 1 : ℚ[X])

/-- **`(𝒪_{Spec ℚ})^a(Spec ℚ(i)) = ℚ(i)`.** -/
noncomputable def bigSheafUnitObjSpecGaussianRatEquiv :
    (Scheme.Modules.bigSheaf (MonoidalCategoryStruct.tensorUnit (Spec (.of ℚ)).Modules)).val.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ GaussianRat))))) ≃ₛₗ[
        RingHomClass.toRingHom (bigRingCatSheafObjSpecRingEquiv (.of GaussianRat)
          (Spec.map (CommRingCat.ofHom (algebraMap ℚ GaussianRat))))] GaussianRat :=
  bigSheafUnitObjSpecAlgebraEquiv ℚ GaussianRat

/-- `ℚ(i)` is two-dimensional over `ℚ`. -/
theorem finrank_gaussianRat : Module.finrank ℚ GaussianRat = 2 := by
  have hm : (X ^ 2 + 1 : ℚ[X]).Monic := by monicity!
  rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim]
  compute_degree!

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
  rw [finrank_gaussianRat, Module.finrank_self] at this
  exact absurd this (by norm_num)

end TauCeti.AlgebraicGeometry.BigSheafUnitExamples
