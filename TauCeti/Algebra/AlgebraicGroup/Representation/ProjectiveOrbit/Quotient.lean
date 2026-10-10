/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Fibers
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Lifting
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LineFibers
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# Projective orbits represent homogeneous quotients

Let `G` be a reduced affine group of finite type over an algebraically closed field `k`,
let `N` be a closed subgroup, and let `m` be a vector in a finite-dimensional representation
whose matrix coefficients detect the left cosets of `N`, as Chevalley's coset criterion
provides. Then the fppf homogeneous quotient `G/N` is represented by the projective orbit
scheme of the line through `m`: its fppf sheaf of points is isomorphic to `G/N`, compatibly
with the projections from `G`. Every closed subgroup admits such a vector, so `G/N` is
represented by a scheme, locally closed in a projective space.

The orbit scheme defines an fppf sheaf on affine `k`-schemes because the fppf topology is
subcanonical. The orbit map from `G` is invariant under `N` and descends to `G/N`. The
descended map is locally injective because the fibers of the orbit map are exactly the left
cosets of `N` (`Comodule.projectiveOrbitMap_SpecMap_eq_iff_exists_units_matrixCoefficient`),
and it is locally surjective because every point of the orbit lifts to `G` after a faithfully
flat, finitely presented extension (`Comodule.exists_faithfullyFlat_lift_toProjectiveOrbit`).
A locally bijective morphism of sheaves is an isomorphism.

## Main declarations

* `Comodule.projectiveOrbitPointsSheaf`: the fppf sheaf of points of a projective orbit scheme.
* `Comodule.toProjectiveOrbitPoints`: the orbit map on points.
* `Comodule.fppfHomogeneousQuotientToProjectiveOrbitPoints`: the orbit map descended to `G/N`.
* `Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints`: **`G/N` is represented by the
  projective orbit scheme.**
* `HopfIdeal.exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints`: every closed subgroup
  has a projective orbit representing its homogeneous quotient.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and §§7.c–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.Comodule

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H]
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The fppf sheaf of points of the projective orbit scheme of a line: an affine `k`-scheme
`Spec A` is sent to the morphisms `Spec A ⟶ X` over `Spec k`, lifted to `Type (u + 1)` to sit
beside the fppf homogeneous quotient. -/
noncomputable def projectiveOrbitPointsSheaf (m : M) (hm : Module.IsUnimodular k m) :
    Sheaf (CommAlgCat.fppfTopology k) (Type (u + 1)) :=
  ⟨((algSpec (CommRingCat.of k)).op ⋙
      yoneda.obj (Over.mk (projectiveOrbitToSpec (H := H) m hm))) ⋙ uliftFunctor.{u + 1, u},
    (isSheaf_iff_isSheaf_of_type _ _).mpr <| Presieve.isSheaf_comp_uliftFunctor _ <|
      (isSheaf_iff_isSheaf_of_type _ _).mp <| (algSpec (CommRingCat.of k)).op_comp_isSheaf _ _
        ((Scheme.fppfTopology.over (Spec (CommRingCat.of k))).yoneda.obj
          (Over.mk (projectiveOrbitToSpec (H := H) m hm)))⟩

/-- The points of the projective orbit scheme over `Spec A` are its morphisms from `Spec A`
over the base field. -/
@[simp]
theorem projectiveOrbitPointsSheaf_obj (m : M) (hm : Module.IsUnimodular k m) :
    (projectiveOrbitPointsSheaf (H := H) m hm).obj =
      ((algSpec (CommRingCat.of k)).op ⋙
        yoneda.obj (Over.mk (projectiveOrbitToSpec (H := H) m hm))) ⋙
          uliftFunctor.{u + 1, u} :=
  (rfl)

/-- An algebra-valued group point followed by the orbit map lies over the base field. -/
theorem SpecMap_toProjectiveOrbit_projectiveOrbitToSpec (m : M)
    (hm : Module.IsUnimodular k m) {A : Type u} [CommRing A] [Algebra k A] (g : H →ₐ[k] A) :
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ toProjectiveOrbit (H := H) m hm) ≫
        projectiveOrbitToSpec (H := H) m hm =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  rw [Category.assoc, toProjectiveOrbit_projectiveOrbitToSpec, ← Spec.map_comp]
  congr 1
  ext x
  exact g.commutes x

/-- Changing the value algebra of a group point along `χ` precomposes its orbit point with
`Spec χ`. -/
private theorem SpecMap_toProjectiveOrbit_naturality (m : M) (hm : Module.IsUnimodular k m)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] (χ : A →ₐ[k] B)
    (g : H →ₐ[k] A) :
    Spec.map (CommRingCat.ofHom (χ.comp g).toRingHom) ≫ toProjectiveOrbit (H := H) m hm =
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ toProjectiveOrbit (H := H) m hm := by
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The orbit map on points: an `A`-valued group point `g` is sent to the point
`Spec A ⟶ Spec H ⟶ X` of the projective orbit scheme. -/
noncomputable def toProjectiveOrbitPoints (m : M) (hm : Module.IsUnimodular k m) :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (projectiveOrbitPointsSheaf (H := H) m hm).obj := by
  rw [projectiveOrbitPointsSheaf_obj]
  exact
    { app A := ↾fun g ↦ ULift.up <| Over.homMk
        (Spec.map (CommRingCat.ofHom g.down.ofConv.toRingHom) ≫ toProjectiveOrbit (H := H) m hm)
        (SpecMap_toProjectiveOrbit_projectiveOrbitToSpec m hm g.down.ofConv)
      naturality A B χ := by
        ext ⟨g⟩
        have h := SpecMap_toProjectiveOrbit_naturality m hm χ.unop.unop.hom g.ofConv
        rw [← WithConv.ofConv_toConv (χ.unop.unop.hom.comp g.ofConv),
          ← HopfAlgebra.mapPoints_apply (H := H) χ.unop.unop g] at h
        -- Both sides are `Spec` of the composite value-algebra map followed by the orbit map.
        exact congrArg ULift.up (Over.OverMorphism.ext h) }

/-- The orbit point of `g` is `Spec g` followed by the orbit map. -/
@[simp]
theorem toProjectiveOrbitPoints_app_apply (m : M) (hm : Module.IsUnimodular k m)
    (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (g : HopfAlgebra.points (R := k) (H := H) A.unop.unop) :
    dsimp% (toProjectiveOrbitPoints (H := H) m hm).app A (ULift.up g) =
      (projectiveOrbitPointsSheaf_obj (H := H) m hm).symm ▸
        ULift.up (Over.homMk
          (Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ toProjectiveOrbit (H := H) m hm)
          (SpecMap_toProjectiveOrbit_projectiveOrbitToSpec m hm g.ofConv)) :=
  (rfl)

/-- Two algebra-valued group points have the same orbit point exactly when their matrix
coefficients at `m` differ by one unit of the value algebra. -/
theorem toProjectiveOrbitPoints_app_eq_iff (m : M) (hm : Module.IsUnimodular k m)
    (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (g h : HopfAlgebra.points (R := k) (H := H) A.unop.unop) :
    dsimp% (toProjectiveOrbitPoints (H := H) m hm).app A (ULift.up g) =
        (toProjectiveOrbitPoints (H := H) m hm).app A (ULift.up h) ↔
      ∃ c : A.unop.unopˣ, ∀ φ : Module.Dual k M,
        h.ofConv (matrixCoefficient (C := H) φ m) =
          c * g.ofConv (matrixCoefficient (C := H) φ m) := by
  rw [← projectiveOrbitMap_SpecMap_eq_iff_exists_units_matrixCoefficient m hm,
    ← toProjectiveOrbit_projectiveOrbitι, ← Category.assoc, ← Category.assoc, cancel_mono]
  rw [toProjectiveOrbitPoints_app_apply, toProjectiveOrbitPoints_app_apply]
  exact ⟨fun h ↦ congrArg (fun x ↦ (ULift.down x).left) h,
    fun h ↦ congrArg ULift.up (Over.OverMorphism.ext h)⟩

/-- **Points of the orbit lift fppf locally to the group.** For a reduced group, the orbit map
on points is locally surjective for the fppf topology. -/
instance isLocallySurjective_toProjectiveOrbitPoints [_root_.IsReduced H] (m : M)
    (hm : Module.IsUnimodular k m) :
    Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology k)
      (toProjectiveOrbitPoints (H := H) m hm) where
  imageSieve_mem {U} s := by
    obtain ⟨y⟩ := s
    obtain ⟨B, φ, g, hflat, hfp, hg⟩ :=
      exists_faithfullyFlat_lift_toProjectiveOrbit (H := H) m hm U.unop y.left (Over.w y)
    refine GrothendieckTopology.superset_covering _ ?_
      (CommAlgCat.generate_singleton_op_mem_fppfTopology φ hflat hfp)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    refine ⟨ULift.up g, ?_⟩
    rw [toProjectiveOrbitPoints_app_apply]
    refine congrArg ULift.up (Over.OverMorphism.ext ?_)
    -- The restriction of `y` along `φ` is `Spec φ ≫ y`, which is the lifted orbit point.
    exact hg.trans (congrArg (· ≫ y.left) (algSpec_map_left_ofAlgHom (R := k) φ.hom).symm)

section Descent

variable (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
  (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
    (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
        CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual k M,
        h.ofConv (matrixCoefficient (C := H) φ m) =
          c * g.ofConv (matrixCoefficient (C := H) φ m))

include hcoset in
/-- The orbit map is invariant under right multiplication by a closed subgroup whose cosets are
detected by the matrix coefficients at `m`. -/
private theorem toProjectiveOrbitPoints_app_mul
    (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (g : HopfAlgebra.points (R := k) (H := H) A.unop.unop)
    (n : CommHopfAlgCat.quotientPointsSubgroup H I A.unop.unop) :
    (toProjectiveOrbitPoints (H := H) m hm).app A (ULift.up (g * n.val)) =
      (toProjectiveOrbitPoints (H := H) m hm).app A (ULift.up g) := by
  rw [toProjectiveOrbitPoints_app_eq_iff, ← hcoset, QuotientGroup.eq]
  simp

/-- The orbit map descended to the fppf homogeneous quotient `G/N`, for a vector `m` whose
matrix coefficients detect the left cosets of the closed subgroup `N` cut out by `I`. -/
noncomputable def fppfHomogeneousQuotientToProjectiveOrbitPoints :
    CommHopfAlgCat.fppfHomogeneousQuotient H I ⟶ projectiveOrbitPointsSheaf (H := H) m hm :=
  (CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv H I _).symm
    ⟨toProjectiveOrbitPoints m hm, toProjectiveOrbitPoints_app_mul I m hm hcoset⟩

/-- The descended orbit map restricts to the orbit map along the projection `G ⟶ G/N`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints :
    CommHopfAlgCat.fppfHomogeneousQuotientProjection H I ≫
        (fppfHomogeneousQuotientToProjectiveOrbitPoints I m hm hcoset).hom =
      toProjectiveOrbitPoints m hm :=
  CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv_symm_apply H I _ _ _

/-- **Projective orbits represent homogeneous quotients.** For a reduced finite-type group over
an algebraically closed field and a vector whose matrix coefficients detect the left cosets of a
closed subgroup `N`, the descended orbit map `G/N ⟶ X` is an isomorphism of fppf sheaves. -/
instance isIso_fppfHomogeneousQuotientToProjectiveOrbitPoints [_root_.IsReduced H] :
    IsIso (fppfHomogeneousQuotientToProjectiveOrbitPoints I m hm hcoset) := by
  let J := CommAlgCat.fppfTopology k
  let P := CommHopfAlgCat.homogeneousQuotientPresheaf H I
  let e := CommHopfAlgCat.homogeneousQuotientPresheafHomEquiv H I
    (projectiveOrbitPointsSheaf (H := H) m hm).obj
  let ψ := e.symm ⟨toProjectiveOrbitPoints m hm, toProjectiveOrbitPoints_app_mul I m hm hcoset⟩
  have hψ : CommHopfAlgCat.homogeneousQuotientPresheafProjection H I ≫ ψ =
      toProjectiveOrbitPoints m hm := by
    simpa only [e, CommHopfAlgCat.homogeneousQuotientPresheafHomEquiv_apply] using
      congrArg Subtype.val (e.apply_symm_apply
        ⟨toProjectiveOrbitPoints m hm, toProjectiveOrbitPoints_app_mul I m hm hcoset⟩)
  -- On the coset presheaf the orbit map is injective: its fibers are exactly the cosets.
  have hinj : Presheaf.IsLocallyInjective J ψ := by
    refine Presheaf.isLocallyInjective_of_injective J ψ fun A q₁ q₂ hq ↦ ?_
    obtain ⟨x₁, rfl⟩ := CommHopfAlgCat.homogeneousQuotientPresheafProjection_surjective H I A q₁
    obtain ⟨x₂, rfl⟩ := CommHopfAlgCat.homogeneousQuotientPresheafProjection_surjective H I A q₂
    have h := (congrArg (fun α ↦ α.app A x₁) hψ).symm.trans
      (hq.trans (congrArg (fun α ↦ α.app A x₂) hψ))
    have hc := (toProjectiveOrbitPoints_app_eq_iff m hm A x₁.down x₂.down).mp h
    exact (CommHopfAlgCat.homogeneousQuotientPresheafProjection_eq_iff H I A _ _).mpr
      (QuotientGroup.eq.mp ((hcoset A.unop.unop x₁.down x₂.down).mpr hc))
  -- The orbit map on `G/N` restricts to `ψ` along the unit of sheafification.
  have hfac : (toSheafify J P ≫ eqToHom (CommHopfAlgCat.fppfHomogeneousQuotient_obj H I).symm) ≫
      (fppfHomogeneousQuotientToProjectiveOrbitPoints I m hm hcoset).hom = ψ := by
    apply CommHopfAlgCat.homogeneousQuotientPresheaf_hom_ext
    rw [hψ, ← Category.assoc, ← CommHopfAlgCat.fppfHomogeneousQuotientProjection_def,
      fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints]
  refine (GrothendieckTopology.W_sheafToPresheaf_map_iff_isIso J _).mp
    ((J.W_iff_isLocallyBijective _).mpr ⟨?_, ?_⟩)
  · exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J ψ hfac
  · exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints I m hm hcoset)

/-- **The homogeneous quotient `G/N` is represented by a projective orbit.** For a reduced
finite-type group over an algebraically closed field and a vector `m` whose matrix coefficients
detect the left cosets of the closed subgroup `N`, the fppf quotient `G/N` is isomorphic to the
sheaf of points of the projective orbit scheme of the line through `m`. -/
noncomputable def fppfHomogeneousQuotientIsoProjectiveOrbitPoints [_root_.IsReduced H] :
    CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m hm :=
  asIso (fppfHomogeneousQuotientToProjectiveOrbitPoints I m hm hcoset)

/-- The forward map of the representing isomorphism is the descended orbit map. -/
@[simp]
theorem fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom [_root_.IsReduced H] :
    (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset).hom =
      fppfHomogeneousQuotientToProjectiveOrbitPoints I m hm hcoset :=
  (rfl)

end Descent

end TauCeti.Comodule

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [_root_.IsReduced H]

attribute [local instance] Comodule.exteriorPower

/-- **Homogeneous quotients are representable.** For every closed subgroup `N` of a reduced
affine group `G` of finite type over an algebraically closed field, there are a
finite-dimensional representation of `G` and a line in it whose projective orbit scheme
represents the fppf homogeneous quotient `G/N`. -/
theorem exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints (I : HopfIdeal k H) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m),
      Nonempty (CommHopfAlgCat.fppfHomogeneousQuotient H I ≅
        Comodule.projectiveOrbitPointsSheaf (H := H) m hm) := by
  have := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨V, n, hV, m, hm, hcoset⟩ :=
    I.exists_finite_subcomodule_exteriorPower_coset_matrixCoefficient.{u, u, u}
      (IsNoetherian.noetherian I.toIdeal)
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  exact ⟨⋀[k]^n V, inferInstance, inferInstance, inferInstance, inferInstance, m, hm,
    ⟨Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset⟩⟩

end TauCeti.HopfIdeal
