/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Fibers
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LineFibers
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Flat
import TauCeti.Algebra.Category.CommAlgCat.PointsSheaf

/-!
# Projective orbits represent homogeneous quotients

Let `G` be a reduced affine group of finite type over an algebraically closed field `k`,
let `N` be a closed subgroup, and let `m` be a vector in a finite-dimensional representation
whose matrix coefficients detect the left cosets of `N`, as Chevalley's coset criterion
provides. Then the fppf homogeneous quotient `G/N` is represented by the projective orbit
scheme of the line through `m`: its fppf sheaf of points is isomorphic to `G/N`, compatibly
with the projections from `G`. Every closed subgroup admits such a vector, so `G/N` is
represented by a scheme, locally closed in a projective space.

The orbit scheme defines an fppf sheaf on affine `k`-schemes, `CommAlgCat.pointsSheaf`, because
the fppf topology is subcanonical. The orbit map from `G` is invariant under `N` and descends to
`G/N`. The descended map is locally injective because the orbit-map fibers are exactly the left
cosets of `N` (`Comodule.projectiveOrbitMap_SpecMap_eq_iff_exists_units_matrixCoefficient`),
and it is locally surjective because `toProjectiveOrbit` is fppf
(`CommAlgCat.isLocallySurjective_pointsSheafFunctor_map`).
A locally bijective morphism of sheaves is an isomorphism.

## Main declarations

* `Comodule.projectiveOrbitPointsSheaf`: the fppf sheaf of points of a projective orbit scheme.
* `Comodule.toProjectiveOrbitPoints`: the orbit map on points.
* `Comodule.fppfHomogeneousQuotientToProjectiveOrbitPoints`: the orbit map descended to `G/N`.
* `Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints`: **`G/N` is represented by the
  projective orbit scheme.**
* `HopfIdeal.exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints`: every closed subgroup
  has a projective orbit representing its homogeneous quotient.
* `Comodule.mem_quotientPointsSubgroup_iff_projectiveOrbitMap_kernelPoint_eq`: for such a vector,
  the rational points of `N` are the stabilizer of the base point of the orbit.

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
noncomputable abbrev projectiveOrbitPointsSheaf (m : M) (hm : Module.IsUnimodular k m) :
    Sheaf (CommAlgCat.fppfTopology k) (Type (u + 1)) :=
  CommAlgCat.pointsSheaf (Over.mk (projectiveOrbitToSpec (H := H) m hm))

/-- The points of the projective orbit scheme over `Spec A` are its morphisms from `Spec A`
over the base field. -/
theorem projectiveOrbitPointsSheaf_obj (m : M) (hm : Module.IsUnimodular k m) :
    (projectiveOrbitPointsSheaf (H := H) m hm).obj =
      ((algSpec (CommRingCat.of k)).op ⋙
        yoneda.obj (Over.mk (projectiveOrbitToSpec (H := H) m hm))) ⋙
          uliftFunctor.{u + 1, u} :=
  (rfl)

/-- The sheaf of points of the projective orbit scheme is the fppf sheaf of points of the orbit
scheme over the base field. -/
theorem projectiveOrbitPointsSheaf_eq (m : M) (hm : Module.IsUnimodular k m) :
    projectiveOrbitPointsSheaf (H := H) m hm =
      CommAlgCat.pointsSheaf (Over.mk (projectiveOrbitToSpec (H := H) m hm)) :=
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

private noncomputable abbrev toProjectiveOrbitOver (m : M) (hm : Module.IsUnimodular k m) :
    (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k)) ⟶
      Over.mk (projectiveOrbitToSpec (H := H) m hm) :=
  Over.homMk (toProjectiveOrbit (H := H) m hm)
    (toProjectiveOrbit_projectiveOrbitToSpec m hm)

/-- The orbit map on points: an `A`-valued group point `g` is sent to the point
`Spec A ⟶ Spec H ⟶ X` of the projective orbit scheme. -/
noncomputable def toProjectiveOrbitPoints (m : M) (hm : Module.IsUnimodular k m) :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (projectiveOrbitPointsSheaf (H := H) m hm).obj :=
  CommHopfAlgCat.specPointsHomEquiv H (Over.mk (projectiveOrbitToSpec (H := H) m hm))
    (toProjectiveOrbitOver (H := H) m hm)

/-- The orbit point of `g` is `Spec g` followed by the orbit map. -/
@[simp]
theorem toProjectiveOrbitPoints_app_apply (m : M) (hm : Module.IsUnimodular k m)
    (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (g : HopfAlgebra.points (R := k) (H := H) A.unop.unop) :
    dsimp% (toProjectiveOrbitPoints (H := H) m hm).app A (ULift.up g) =
      ULift.up (Over.homMk
        (Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ toProjectiveOrbit (H := H) m hm)
        (SpecMap_toProjectiveOrbit_projectiveOrbitToSpec m hm g.ofConv)) :=
  (CommHopfAlgCat.specPointsHomEquiv_apply_app_apply H _ A g).trans <|
    congrArg ULift.up <| Over.OverMorphism.ext <|
      congrArg (· ≫ toProjectiveOrbit (H := H) m hm) (TauCeti.CommHopfAlgCat.mapMulEquiv_left g)

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

/-- `specPointsHomEquiv` sends `toProjectiveOrbit` over `Spec k` to `toProjectiveOrbitPoints`. -/
@[simp] theorem specPointsHomEquiv_toProjectiveOrbit (m : M) (hm : Module.IsUnimodular k m) :
    CommHopfAlgCat.specPointsHomEquiv H (Over.mk (projectiveOrbitToSpec (H := H) m hm))
        (Over.homMk (toProjectiveOrbit (H := H) m hm)
          (toProjectiveOrbit_projectiveOrbitToSpec m hm)) =
      toProjectiveOrbitPoints (H := H) m hm :=
  (rfl)

private instance isLocallySurjective_pointsSheafFunctor_map_toProjectiveOrbit
    [_root_.IsReduced H] (m : M) (hm : Module.IsUnimodular k m) :
    Sheaf.IsLocallySurjective
      ((TauCeti.CommAlgCat.pointsSheafFunctor k).map (toProjectiveOrbitOver (H := H) m hm)) := by
  have hp : (toProjectiveOrbitOver (H := H) m hm).left = toProjectiveOrbit (H := H) m hm :=
    Over.homMk_left _ _
  have : Flat (toProjectiveOrbitOver (H := H) m hm).left := by
    rw [hp]; exact (inferInstance : Flat (toProjectiveOrbit (H := H) m hm))
  have : Surjective (toProjectiveOrbitOver (H := H) m hm).left := by
    rw [hp]; exact (inferInstance : Surjective (toProjectiveOrbit (H := H) m hm))
  have : LocallyOfFinitePresentation (toProjectiveOrbitOver (H := H) m hm).left := by
    rw [hp]; exact (inferInstance : LocallyOfFinitePresentation (toProjectiveOrbit (H := H) m hm))
  exact TauCeti.CommAlgCat.isLocallySurjective_pointsSheafFunctor_map _

/-- **Points of the orbit lift fppf locally to the group.** For a reduced group, the orbit map
on points is locally surjective for the fppf topology. -/
instance isLocallySurjective_toProjectiveOrbitPoints [_root_.IsReduced H] (m : M)
    (hm : Module.IsUnimodular k m) :
    Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology k)
      (toProjectiveOrbitPoints (H := H) m hm) := by
  rw [← specPointsHomEquiv_toProjectiveOrbit, CommHopfAlgCat.specPointsHomEquiv_eq_comp,
    Presheaf.comp_isLocallySurjective_iff]
  exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).2
    (isLocallySurjective_pointsSheafFunctor_map_toProjectiveOrbit (H := H) m hm)

section Descent

private theorem mapMulEquiv_comp_toProjectiveOrbit_eq_iff (m : M) (hm : Module.IsUnimodular k m)
    (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A) :
    Spec.mapMulEquiv g ≫ toProjectiveOrbitOver (H := H) m hm =
      Spec.mapMulEquiv h ≫ toProjectiveOrbitOver (H := H) m hm ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual k M,
        h.ofConv (matrixCoefficient (C := H) φ m) =
          c * g.ofConv (matrixCoefficient (C := H) φ m) := by
  rw [← CommHopfAlgCat.specPointsHomEquiv_apply_app_apply_eq_iff H
    (toProjectiveOrbitOver (H := H) m hm) (op (op A)) g h]
  exact toProjectiveOrbitPoints_app_eq_iff (H := H) m hm (op (op A)) g h

variable (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
  (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
    (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
        CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual k M,
        h.ofConv (matrixCoefficient (C := H) φ m) =
          c * g.ofConv (matrixCoefficient (C := H) φ m))

include hcoset in
private theorem toProjectiveOrbit_mul_invariant :
    ∀ (A : CommAlgCat.{u} k) (g : HopfAlgebra.points (R := k) (H := H) A)
      (n : CommHopfAlgCat.quotientPointsSubgroup H I A),
      Spec.mapMulEquiv (g * n.val) ≫ toProjectiveOrbitOver (H := H) m hm =
        Spec.mapMulEquiv g ≫ toProjectiveOrbitOver (H := H) m hm := fun A g n ↦ by
  rw [mapMulEquiv_comp_toProjectiveOrbit_eq_iff, ← hcoset, QuotientGroup.eq]
  simp

include hcoset in
private theorem toProjectiveOrbit_coset_iff
    (A : CommAlgCat.{u} k) (g g' : HopfAlgebra.points (R := k) (H := H) A)
    (h : Spec.mapMulEquiv g ≫ toProjectiveOrbitOver (H := H) m hm =
      Spec.mapMulEquiv g' ≫ toProjectiveOrbitOver (H := H) m hm) :
    g⁻¹ * g' ∈ CommHopfAlgCat.quotientPointsSubgroup H I A :=
  QuotientGroup.eq.mp ((hcoset A g g').mpr
    ((mapMulEquiv_comp_toProjectiveOrbit_eq_iff m hm A g g').mp h))

/-- The orbit map descended to the fppf homogeneous quotient `G/N`, for a vector `m` whose
matrix coefficients detect the left cosets of the closed subgroup `N` cut out by `I`. -/
noncomputable def fppfHomogeneousQuotientToProjectiveOrbitPoints :
    CommHopfAlgCat.fppfHomogeneousQuotient H I ⟶ projectiveOrbitPointsSheaf (H := H) m hm :=
  CommHopfAlgCat.fppfHomogeneousQuotientDesc H I (toProjectiveOrbitOver (H := H) m hm)
    (toProjectiveOrbit_mul_invariant I m hm hcoset)

/-- The descended orbit map restricts to the orbit map along the projection `G ⟶ G/N`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints :
    CommHopfAlgCat.fppfHomogeneousQuotientProjection H I ≫
        (fppfHomogeneousQuotientToProjectiveOrbitPoints I m hm hcoset).hom =
      toProjectiveOrbitPoints m hm := by
  rw [fppfHomogeneousQuotientToProjectiveOrbitPoints,
    CommHopfAlgCat.fppfHomogeneousQuotientProjection_comp_desc,
    specPointsHomEquiv_toProjectiveOrbit]

/-- **Projective orbits represent homogeneous quotients.** For a reduced finite-type group over
an algebraically closed field and a vector whose matrix coefficients detect the left cosets of a
closed subgroup `N`, the descended orbit map `G/N ⟶ X` is an isomorphism of fppf sheaves. -/
instance isIso_fppfHomogeneousQuotientToProjectiveOrbitPoints [_root_.IsReduced H] :
    IsIso (fppfHomogeneousQuotientToProjectiveOrbitPoints I m hm hcoset) :=
  CommHopfAlgCat.isIso_fppfHomogeneousQuotientDesc H I _
    (toProjectiveOrbit_mul_invariant I m hm hcoset)
    (toProjectiveOrbit_coset_iff I m hm hcoset)

/-- **The homogeneous quotient `G/N` is represented by a projective orbit.** For a reduced
finite-type group over an algebraically closed field and a vector whose matrix coefficients
detect the left cosets of the closed subgroup `N`, the fppf quotient `G/N` is isomorphic to the
sheaf of points of the projective orbit scheme of the line through `m`. -/
noncomputable def fppfHomogeneousQuotientIsoProjectiveOrbitPoints [_root_.IsReduced H] :
    CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m hm :=
  CommHopfAlgCat.fppfHomogeneousQuotientIsoPointsSheaf H I _
    (toProjectiveOrbit_mul_invariant I m hm hcoset)
    (toProjectiveOrbit_coset_iff I m hm hcoset)

/-- The forward map of the representing isomorphism is the descended orbit map. -/
@[simp]
theorem fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom [_root_.IsReduced H] :
    (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset).hom =
      fppfHomogeneousQuotientToProjectiveOrbitPoints I m hm hcoset :=
  CommHopfAlgCat.fppfHomogeneousQuotientIsoPointsSheaf_hom H I _ _ _

end Descent

/-- For a reduced group `G` and Chevalley's representing isomorphism
`fppfHomogeneousQuotientIsoProjectiveOrbitPoints`, the descended quotient projection in
`Over (Spec k)` is `toProjectiveOrbit` over `Spec k`. -/
@[simp] theorem representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints
    [_root_.IsReduced H] (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) =
            c * g.ofConv (matrixCoefficient (C := H) φ m)) :
    CommHopfAlgCat.representedQuotientProjection H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset) =
      Over.homMk (toProjectiveOrbit (H := H) m hm) (toProjectiveOrbit_projectiveOrbitToSpec m hm) :=
  CommHopfAlgCat.representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf H I _
    (toProjectiveOrbit_mul_invariant I m hm hcoset)
    (toProjectiveOrbit_coset_iff I m hm hcoset)

/-- For a reduced group `G` and Chevalley's representing isomorphism, the underlying scheme morphism
of `representedQuotientProjection` is `toProjectiveOrbit`. -/
theorem representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints_left
    [_root_.IsReduced H] (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) =
            c * g.ofConv (matrixCoefficient (C := H) φ m)) :
    (CommHopfAlgCat.representedQuotientProjection H I
      (fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset)).left =
      toProjectiveOrbit (H := H) m hm :=
  congrArg Over.Hom.left
    (representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset)

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- If the matrix coefficients at `m` detect the left cosets of the rational points of the closed
subgroup `N`, then the rational points of `N` are exactly the stabilizer of the base point `[m]`
of the projective orbit. -/
theorem mem_quotientPointsSubgroup_iff_projectiveOrbitMap_kernelPoint_eq {I : HopfIdeal k H}
    {m : M} (hm : Module.IsUnimodular k m)
    (hcoset : ∀ g h : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k)) = QuotientGroup.mk h ↔
        ∃ c : kˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) = c * g.ofConv (matrixCoefficient (C := H) φ m))
    (a : WithConv (H →ₐ[k] k)) :
    a ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k) ↔
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
  have h := (hcoset 1 a).trans
    (projectiveOrbitMap_kernelPoint_eq_iff_exists_units_matrixCoefficient m hm 1 a).symm
  rw [QuotientGroup.eq, inv_one, one_mul, eq_comm] at h
  simpa [AlgHom.convOne_def] using h

end TauCeti.Comodule

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [_root_.IsReduced H]

attribute [local instance] Comodule.exteriorPower

/-- **Homogeneous quotients are representable.** For every closed subgroup `N` of a reduced
affine group `G` of finite type over an algebraically closed field, there are a
finite-dimensional representation of `G` and a line in it whose projective orbit scheme
represents the fppf homogeneous quotient `G/N` compatibly with the projections from `G`. -/
theorem exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints (I : HopfIdeal k H) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m)
      (e : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅
        Comodule.projectiveOrbitPointsSheaf (H := H) m hm),
      CommHopfAlgCat.representedQuotientProjection H I e =
        Over.homMk (Comodule.toProjectiveOrbit (H := H) m hm)
          (Comodule.toProjectiveOrbit_projectiveOrbitToSpec m hm) := by
  have := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨V, n, hV, m, hm, hcoset⟩ :=
    I.exists_finite_subcomodule_exteriorPower_coset_matrixCoefficient.{u, u, u}
      (IsNoetherian.noetherian I.toIdeal)
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  exact ⟨⋀[k]^n V, inferInstance, inferInstance, inferInstance, inferInstance, m, hm,
    Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset,
    Comodule.representedQuotientProjection_fppfHomogeneousQuotientIsoProjectiveOrbitPoints
      I m hm hcoset⟩

end TauCeti.HopfIdeal
