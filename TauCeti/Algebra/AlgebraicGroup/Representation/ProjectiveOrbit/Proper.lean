/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points

/-!
# Properness of projective orbits and represented homogeneous quotients

For a finite-dimensional representation of a finite-type affine group scheme `G` over an
algebraically closed field `k`, the projective orbit scheme of a line `[m]` embeds as a locally
closed subscheme of projective space via `Comodule.projectiveOrbitι`, and its structural morphism
`Comodule.projectiveOrbitToSpec` factors through `SymmetricAlgebra.projToSpec`. Since projective
space is proper and separated over `Spec k`, properness of the orbit scheme over `Spec k` is
equivalent both to closedness of its geometric image and to `projectiveOrbitι` being a closed
immersion. Neither reducedness, smoothness, nor connectedness of `G` is required for this
equivalence.

When `G` is reduced, every closed subgroup `N` has a projective orbit scheme representing the fppf
homogeneous quotient `G / N` (`Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints`). Combining
this representation with the scheme-level quotient API from
`TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme` yields:

* **Surjectivity of quotient projections**: for any scheme `X` over `Spec k` representing `G / N`,
  the canonical morphism `Spec H ⟶ X` is surjective, and for any inclusion of closed subgroups
  `P ⊆ Q` (`J ≤ I`), the induced morphism `X ⟶ Y` between representing schemes is surjective.
* **Descent of properness along subgroup inclusions**: if `P ⊆ Q` (`J ≤ I`) and a scheme
  representing `G / P` is proper over `Spec k`, then any scheme representing `G / Q` is proper over
  `Spec k`.

## Main declarations

* `TauCeti.Comodule.isClosedImmersion_projectiveOrbitι_iff_isClosed_range`: `projectiveOrbitι` is a
  closed immersion iff the orbit image is closed in projective space.
* `TauCeti.Comodule.isProper_projectiveOrbitToSpec_iff_isClosed_range`: the projective orbit scheme
  is proper over `Spec k` iff the orbit image is closed in projective space.
* `TauCeti.Comodule.fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit`: isomorphism from
  `fppfHomogeneousQuotient H I` directly to `CommAlgCat.pointsSheaf` of the projective orbit scheme.
* `CommHopfAlgCat.surjective_fppfHomogeneousQuotientSchemeProjection_left`: the canonical
  projection `Spec H ⟶ X` onto any scheme representing `G / N` is surjective.
* `CommHopfAlgCat.surjective_fppfHomogeneousQuotientSchemeMap_left`: the canonical morphism
  `X ⟶ Y` induced by `J ≤ I` between schemes representing `G / P` and `G / Q` is surjective.
* `CommHopfAlgCat.isProper_of_fppfHomogeneousQuotientIso_of_le`: properness over `Spec k`
  descends from `G / P` to `G / Q` along `J ≤ I`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 and §§7.e–7.f.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§6.8 and 11.2.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u

section ClosedRange

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The locally closed immersion of a projective orbit scheme into projective space is a closed
immersion if and only if the geometric orbit is closed in projective space. Neither reducedness nor
connectedness of the group is needed. -/
theorem isClosedImmersion_projectiveOrbitι_iff_isClosed_range
    (m : M) (hm : Module.IsUnimodular k m) :
    IsClosedImmersion (projectiveOrbitι (H := H) m hm) ↔
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  rw [IsClosedImmersion.iff_isPreimmersion, range_projectiveOrbitι, and_iff_right_iff_imp]
  intro _
  infer_instance

/-- **Properness of a projective orbit scheme.** The projective orbit scheme of a line `[m]` is
proper over `Spec k` if and only if the geometric orbit is closed in projective space. Neither
reducedness, smoothness, nor connectedness of the group is needed. -/
theorem isProper_projectiveOrbitToSpec_iff_isClosed_range
    (m : M) (hm : Module.IsUnimodular k m) :
    IsProper (projectiveOrbitToSpec (H := H) m hm) ↔
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  refine ⟨fun h ↦ ?_, isProper_projectiveOrbitToSpec_of_isClosed M m hm⟩
  have _ : IsProper (projectiveOrbitι (H := H) m hm) := by
    rwa [projectiveOrbitToSpec_def, IsProper.comp_iff] at h
  simpa only [range_projectiveOrbitι] using
    (projectiveOrbitι (H := H) m hm).isClosedMap.isClosed_range

/-- The projective orbit scheme of a line `[m]` is proper over `Spec k` if and only if its
inclusion into projective space is a closed immersion. -/
theorem isProper_projectiveOrbitToSpec_iff_isClosedImmersion_projectiveOrbitι
    (m : M) (hm : Module.IsUnimodular k m) :
    IsProper (projectiveOrbitToSpec (H := H) m hm) ↔
      IsClosedImmersion (projectiveOrbitι (H := H) m hm) :=
  (isProper_projectiveOrbitToSpec_iff_isClosed_range (H := H) m hm).trans
    (isClosedImmersion_projectiveOrbitι_iff_isClosed_range (H := H) m hm).symm

end ClosedRange

section RationalStabilizer

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- If the matrix coefficients at a unimodular vector `m` detect the left cosets of a closed
subgroup `N`, then the rational points of `N` are precisely the rational points fixing the base
point `[m]` of the projective orbit. -/
theorem mem_quotientPointsSubgroup_iff_projectiveOrbitMap_kernelPoint_eq
    (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) =
            c * g.ofConv (matrixCoefficient (C := H) φ m))
    (a : WithConv (H →ₐ[k] k)) :
    a ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k) ↔
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
  have h1 : (a ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k)) ↔
      (QuotientGroup.mk (1 : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
        HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k)) = QuotientGroup.mk a := by
    rw [QuotientGroup.eq, inv_one, one_mul]
  rw [h1, hcoset (CommAlgCat.of k k) 1 a]
  -- Unpack `CommAlgCat.of k k` as `k` so `span_pointsAction_eq_iff_exists_units_matrixCoefficient`
  -- matches the target type.
  change (∃ c : kˣ, ∀ φ : Module.Dual k M,
      a.ofConv (matrixCoefficient (C := H) φ m) =
        c * (1 : WithConv (H →ₐ[k] k)).ofConv (matrixCoefficient (C := H) φ m)) ↔ _
  have hact (g : WithConv (H →ₐ[k] k)) :
      TensorProduct.lid k M (pointsAction M g ((1 : k) ⊗ₜ[k] m)) =
        basePointsRepresentation M g m := by
    rw [basePointsRepresentation_apply, ← pointsAction_toLinearMap, LinearEquiv.coe_toLinearMap]
  rw [← span_pointsAction_eq_iff_exists_units_matrixCoefficient (R := k) (A := k) m hm 1 a,
    ← (Submodule.map_injective_of_injective (TensorProduct.lid k M).injective).eq_iff]
  simp only [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hact]
  rw [eq_comm, ← projectiveOrbitMap_kernelPoint_eq_iff_span_eq m hm m hm a 1, AlgHom.convOne_def]
  simp [Algebra.ofId_self]

end RationalStabilizer

section RepresentingOrbit

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H]
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- Canonical isomorphism identifying `projectiveOrbitPointsSheaf` with `CommAlgCat.pointsSheaf` of
the projective orbit scheme over `Spec k`. -/
noncomputable def projectiveOrbitPointsSheafIsoPointsSheaf
    (m : M) (hm : Module.IsUnimodular k m) :
    projectiveOrbitPointsSheaf (H := H) m hm ≅
      CommAlgCat.pointsSheaf (Over.mk (projectiveOrbitToSpec (H := H) m hm)) where
  hom := ⟨eqToHom ((projectiveOrbitPointsSheaf_obj (H := H) m hm).trans
    (CommAlgCat.pointsSheaf_obj _).symm)⟩
  inv := ⟨eqToHom ((CommAlgCat.pointsSheaf_obj _).trans
    (projectiveOrbitPointsSheaf_obj (H := H) m hm).symm)⟩
  hom_inv_id := by
    ext1
    simp
  inv_hom_id := by
    ext1
    simp

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
  have hrec : ∀ {P Q R : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)} (h₁ : P = Q) (h₂ : R = Q)
      (A : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ) (y : Q.obj A),
      (eqToHom (h₁.trans h₂.symm)).app A (h₁.symm ▸ y) = h₂.symm ▸ y := by
    rintro _ _ _ rfl rfl _ _
    rfl
  ext A ⟨(g : HopfAlgebra.points (R := k) (H := H) A.unop.unop)⟩
  have happ := congrArg
    ((eqToHom ((projectiveOrbitPointsSheaf_obj (H := H) m hm).trans
      (CommAlgCat.pointsSheaf_obj _).symm)).app A)
    (toProjectiveOrbitPoints_app_apply (H := H) m hm A g)
  refine happ.trans ((hrec
    (projectiveOrbitPointsSheaf_obj (H := H) m hm)
    (CommAlgCat.pointsSheaf_obj _) A _).trans ?_)
  exact congrArg ULift.up (Over.OverMorphism.ext
    (CommHopfAlgCat.pointsPresheafToPointsSheafEquiv_apply_app_down_left H
      (Over.mk (projectiveOrbitToSpec (H := H) m hm))
      (Over.homMk (toProjectiveOrbit (H := H) m hm)
        (toProjectiveOrbit_projectiveOrbitToSpec m hm)) A g).symm)

/-- **Projective orbit representation in `CommAlgCat.pointsSheaf` form.** When the matrix
coefficients at `m` detect the left cosets of `I` and `H` is reduced, the fppf homogeneous quotient
`G / N` is isomorphic to `CommAlgCat.pointsSheaf` of the projective orbit scheme over `Spec k`. -/
noncomputable def fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit [_root_.IsReduced H]
    (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (matrixCoefficient (C := H) φ m) =
            c * g.ofConv (matrixCoefficient (C := H) φ m)) :
    CommHopfAlgCat.fppfHomogeneousQuotient H I ≅
      CommAlgCat.pointsSheaf (Over.mk (projectiveOrbitToSpec (H := H) m hm)) :=
  fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m hm hcoset ≪≫
    projectiveOrbitPointsSheafIsoPointsSheaf (H := H) m hm

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
    fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit, Iso.trans_hom,
    ObjectProperty.FullSubcategory.comp_hom, fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom,
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
      toProjectiveOrbit (H := H) m hm := by
  rw [fppfHomogeneousQuotientSchemeProjection_isoPointsSheafProjectiveOrbit]
  rfl

end RepresentingOrbit

end TauCeti.Comodule

namespace CommHopfAlgCat

open TauCeti

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat.{u} k)
  [Algebra.FiniteType k H] [_root_.IsReduced H]

attribute [local instance] Comodule.exteriorPower

/-- **Surjectivity of the quotient projection.** For a reduced affine group `G` of finite type over
an algebraically closed field `k`, the canonical projection `Spec H ⟶ X` onto any scheme `X` over
`Spec k` representing `G / N` is surjective. -/
theorem surjective_fppfHomogeneousQuotientSchemeProjection_left (I : HopfIdeal k H)
    {X : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    Surjective (fppfHomogeneousQuotientSchemeProjection H I eI).left := by
  have := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨V, n, hV, m₀, hm₀, hcoset⟩ :=
    I.exists_finite_subcomodule_exteriorPower_coset_matrixCoefficient.{u, u, u}
      (IsNoetherian.noetherian I.toIdeal)
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let e₀ := Comodule.fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit I m₀ hm₀ hcoset
  have hcomp := congrArg Over.Hom.left
    (fppfHomogeneousQuotientSchemeProjection_comp_iso_hom H I e₀ eI)
  rw [Over.comp_left,
    Comodule.fppfHomogeneousQuotientSchemeProjection_isoPointsSheafProjectiveOrbit_left] at hcomp
  rw [← hcomp]
  have _ : IsIso (fppfHomogeneousQuotientSchemeIso H I e₀ eI).hom.left :=
    ((Over.forget (Spec (CommRingCat.of k))).mapIso
      (fppfHomogeneousQuotientSchemeIso H I e₀ eI)).isIso_hom
  infer_instance

/-- **Surjectivity of subgroup-induced quotient maps.** For an inclusion of closed subgroups
`P ⊆ Q` (`J ≤ I`) of a reduced finite-type affine group over an algebraically closed field `k`, the
induced morphism `X ⟶ Y` between any schemes representing `G / P` and `G / Q` is surjective. -/
theorem surjective_fppfHomogeneousQuotientSchemeMap_left {I J : HopfIdeal k H}
    {X Y : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    Surjective (fppfHomogeneousQuotientSchemeMap H eI eJ hJI).left := by
  have hsurj : Surjective
      ((fppfHomogeneousQuotientSchemeProjection H I eI).left ≫
        (fppfHomogeneousQuotientSchemeMap H eI eJ hJI).left) := by
    rw [← Over.comp_left, fppfHomogeneousQuotientSchemeProjection_comp_map]
    exact surjective_fppfHomogeneousQuotientSchemeProjection_left H J eJ
  exact Surjective.of_comp (fppfHomogeneousQuotientSchemeProjection H I eI).left
    (fppfHomogeneousQuotientSchemeMap H eI eJ hJI).left

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
  have := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨V, n, hV, m₀, hm₀, hcoset⟩ :=
    J.exists_finite_subcomodule_exteriorPower_coset_matrixCoefficient.{u, u, u}
      (IsNoetherian.noetherian J.toIdeal)
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let eJ₀ := Comodule.fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit J m₀ hm₀ hcoset
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
      (SymmetricAlgebra.projToSpec k (Module.Dual k (⋀[k]^n V)))
  have hproper₀ : IsProper (Over.mk (Comodule.projectiveOrbitToSpec (H := H) m₀ hm₀)).hom :=
    (Comodule.isProper_projectiveOrbitToSpec_iff_isClosed_range (H := H) m₀ hm₀).mpr
      (by simpa only [Comodule.range_projectiveOrbitι] using
        (Comodule.projectiveOrbitι (H := H) m₀ hm₀).isClosedMap.isClosed_range)
  exact (isProper_hom_iff_of_fppfHomogeneousQuotientIso H J eJ₀ eJ).mp hproper₀

end CommHopfAlgCat
