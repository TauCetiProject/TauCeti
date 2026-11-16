/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme

/-!
# Properness of represented homogeneous quotients

For a reduced affine group `G` of finite type over an algebraically closed field `k`, every closed
subgroup `N` has a projective orbit scheme representing the fppf homogeneous quotient `G / N`
(`TauCeti.Comodule.fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit`,
`TauCeti.HopfIdeal.exists_coset_matrixCoefficient_fppfHomogeneousQuotientIsoPointsSheaf`). Combining
this representation with the scheme-level quotient API from
`TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme` and the closed-orbit properness
characterization from `TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Scheme` yields:

* **Identification of the scheme quotient projection**: for a projective-orbit representation of
  `G / N`, the canonical morphism `Spec H ⟶ X` (`fppfHomogeneousQuotientSchemeProjection`) is
  `Comodule.toProjectiveOrbit` over `Spec k`.
* **Descent of properness along subgroup inclusions**: if `P ⊆ Q` (`J ≤ I`) and a scheme
  representing `G / P` is proper over `Spec k`, then any scheme representing `G / Q` is proper over
  `Spec k`.

## Main declarations

* `TauCeti.Comodule.toProjectiveOrbitPoints_comp_isoPointsSheaf`: composing
  `toProjectiveOrbitPoints` with `projectiveOrbitPointsSheafIsoPointsSheaf` recovers the Yoneda
  image of `toProjectiveOrbit`.
* `TauCeti.Comodule.fppfHomogeneousQuotientSchemeProjection_isoPointsSheafProjectiveOrbit`: for a
  projective orbit representation, `fppfHomogeneousQuotientSchemeProjection` is `toProjectiveOrbit`
  over `Spec k`.
* `CommHopfAlgCat.isProper_of_fppfHomogeneousQuotientIso_of_le`: properness over `Spec k` descends
  from `G / P` to `G / Q` along `J ≤ I`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 and §§7.e–7.f.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§6.8 and 11.2.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite WithConv

namespace TauCeti.Comodule

universe u

section RepresentingOrbit

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H]
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- Composing `toProjectiveOrbitPoints` with `projectiveOrbitPointsSheafIsoPointsSheaf` recovers
the Yoneda image of `toProjectiveOrbit` over `Spec k`. -/
@[simp]
theorem toProjectiveOrbitPoints_comp_isoPointsSheaf
    (m : M) (hm : Module.IsUnimodular k m) :
    toProjectiveOrbitPoints (H := H) m hm ≫
        (projectiveOrbitPointsSheafIsoPointsSheaf (H := H) m hm).hom.hom =
      CommHopfAlgCat.pointsPresheafToPointsSheafEquiv H
        (Over.mk (projectiveOrbitToSpec (H := H) m hm))
        (Over.homMk (toProjectiveOrbit (H := H) m hm)
          (toProjectiveOrbit_projectiveOrbitToSpec m hm)) := by
  ext A ⟨(g : HopfAlgebra.points (R := k) (H := H) A.unop.unop)⟩
  refine (projectiveOrbitPointsSheafIsoPointsSheaf_hom_app_toProjectiveOrbitPoints
    (H := H) m hm A g).trans ?_
  exact congrArg ULift.up (Over.OverMorphism.ext
    (CommHopfAlgCat.pointsPresheafToPointsSheafEquiv_apply_app_down_left H
      (Over.mk (projectiveOrbitToSpec (H := H) m hm))
      (Over.homMk (toProjectiveOrbit (H := H) m hm)
        (toProjectiveOrbit_projectiveOrbitToSpec m hm)) A g).symm)

/-- For the projective orbit representation of `G / N`, the canonical scheme quotient projection is
`toProjectiveOrbit` over `Spec k`. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeProjection_isoPointsSheafProjectiveOrbit [_root_.IsReduced H]
    (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) =
            c * g.ofConv (matrixCoefficient (C := H) φ m)) :
    CommHopfAlgCat.fppfHomogeneousQuotientSchemeProjection H I
        (fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit I m hm hcoset) =
      Over.homMk (toProjectiveOrbit (H := H) m hm)
        (toProjectiveOrbit_projectiveOrbitToSpec m hm) := by
  apply (CommHopfAlgCat.pointsPresheafToPointsSheafEquiv H _).injective
  rw [CommHopfAlgCat.pointsPresheafToPointsSheafEquiv_fppfHomogeneousQuotientSchemeProjection,
    fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit_hom,
    ObjectProperty.FullSubcategory.comp_hom,
    fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints_assoc,
    toProjectiveOrbitPoints_comp_isoPointsSheaf]

/-- The underlying scheme morphism of `fppfHomogeneousQuotientSchemeProjection` for a projective
orbit representation is `toProjectiveOrbit`. -/
theorem fppfHomogeneousQuotientSchemeProjection_isoPointsSheafProjectiveOrbit_left
    [_root_.IsReduced H] (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) =
            c * g.ofConv (matrixCoefficient (C := H) φ m)) :
    (CommHopfAlgCat.fppfHomogeneousQuotientSchemeProjection H I
        (fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit I m hm hcoset)).left =
      toProjectiveOrbit (H := H) m hm :=
  congrArg Over.Hom.left
    (fppfHomogeneousQuotientSchemeProjection_isoPointsSheafProjectiveOrbit I m hm hcoset)

end RepresentingOrbit

end TauCeti.Comodule

namespace CommHopfAlgCat

open TauCeti

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat.{u} k)
  [Algebra.FiniteType k H] [_root_.IsReduced H]

/-- **Properness descends along subgroup inclusions.** Let `G` be a reduced affine group of finite
type over an algebraically closed field `k`, and let `P ⊆ Q` (`J ≤ I`) be closed subgroups. If a
scheme `X` representing `G / P` is proper over `Spec k`, then any scheme `Y` representing `G / Q`
is proper over `Spec k`. -/
theorem isProper_of_fppfHomogeneousQuotientIso_of_le {I J : HopfIdeal k H}
    {X Y : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) [IsProper X.hom] :
    IsProper Y.hom := by
  obtain ⟨M, _, _, _, _, m₀, hm₀, _, ⟨eJ₀⟩⟩ :=
    J.exists_coset_matrixCoefficient_fppfHomogeneousQuotientIsoPointsSheaf
  let f := fppfHomogeneousQuotientSchemeMap H eI eJ₀ hJI
  have _ : Surjective f.left := surjective_fppfHomogeneousQuotientSchemeMap_left H eI eJ₀ hJI
  have hfhom : f.left ≫ Comodule.projectiveOrbitToSpec (H := H) m₀ hm₀ = X.hom := Over.w f
  have _ : UniversallyClosed (f.left ≫ Comodule.projectiveOrbitToSpec (H := H) m₀ hm₀) := by
    rw [hfhom]
    infer_instance
  have huc : UniversallyClosed (Comodule.projectiveOrbitToSpec (H := H) m₀ hm₀) :=
    UniversallyClosed.of_comp_surjective f.left _
  have _ : UniversallyClosed (Comodule.projectiveOrbitι (H := H) m₀ hm₀) := by
    rw [Comodule.projectiveOrbitToSpec_def] at huc
    exact UniversallyClosed.of_comp_of_isSeparated _
      (SymmetricAlgebra.projToSpec k (Module.Dual k M))
  have hproper₀ : IsProper (Over.mk (Comodule.projectiveOrbitToSpec (H := H) m₀ hm₀)).hom :=
    (Comodule.isProper_projectiveOrbitToSpec_iff_isClosed_range (H := H) m₀ hm₀).mpr
      (by simpa only [Comodule.range_projectiveOrbitι] using
        (Comodule.projectiveOrbitι (H := H) m₀ hm₀).isClosedMap.isClosed_range)
  exact (isProper_hom_iff_of_fppfHomogeneousQuotientIso H J eJ₀ eJ).mp hproper₀

end CommHopfAlgCat
