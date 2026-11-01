/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.PolynomialQuotient
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SchemeTheoreticallyDominant
public import TauCeti.RingTheory.MvPolynomial.Homogenization

/-!
# Projective closures of affine schemes of finite type

Let `J` be an ideal of `R[Y₀, …, Yₙ₋₁]` and `Jʰ` its homogenization with respect to `X₀`
(`Ideal.homogenization`). The projective scheme `Proj (R[X₀, …, Xₙ] ⧸ Jʰ)` is proper over
`Spec R`, and its standard chart `D₊(X₀)` is `Spec (R[Y₀, …, Yₙ₋₁] ⧸ J)`
(`Ideal.homogenizationAwayEquiv`). Since `Jʰ` is saturated with respect to `X₀`, the class of `X₀`
is a nonzerodivisor, so the chart is scheme-theoretically dense. This is the projective closure
`TauCeti.DenseCompactification.projectiveClosure J`, a dense compactification of
`Spec (R[Y₀, …, Yₙ₋₁] ⧸ J) ⟶ Spec R`. The construction keeps the scheme structure of the affine
scheme, including nilpotents, and needs no hypothesis on `R`.

Presenting the coordinate ring as a quotient of a polynomial ring, every morphism of finite type
between affine schemes has a dense compactification
(`TauCeti.nonempty_denseCompactification_of_isAffine`). This is the affine case of Nagata's
compactification theorem. In particular the compactifications of such a morphism, and its dense
compactifications, form nonempty cofiltered categories.

## Main definitions

* `TauCeti.DenseCompactification.projectiveClosure J`: the projective closure of
  `Spec (R[Y₀, …, Yₙ₋₁] ⧸ J)` as a dense compactification over `Spec R`.

## Main results

* `TauCeti.nonempty_denseCompactification_of_isAffine`: a morphism of finite type between affine
  schemes has a dense compactification.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Exercise I.2.9 and
  Proposition II.2.5.
* The Stacks Project, Section 38.33, *Nagata compactification* (tag 0F41).
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace TauCeti

namespace DenseCompactification

variable {R : Type u} [CommRing R] {n : ℕ} (J : Ideal (MvPolynomial (Fin n) R))

/-- **The projective closure of an affine scheme of finite type.** For an ideal `J` of
`R[Y₀, …, Yₙ₋₁]`, the projective scheme `Proj (R[X₀, …, Xₙ] ⧸ Jʰ)`, where `Jʰ` is the
homogenization of `J` with respect to `X₀`, together with the embedding of
`Spec (R[Y₀, …, Yₙ₋₁] ⧸ J)` as its standard chart `D₊(X₀)`, is a dense compactification of
`Spec (R[Y₀, …, Yₙ₋₁] ⧸ J) ⟶ Spec R`. -/
-- As for `projectiveLine.denseCompactification`, the ambient scheme and both maps must reduce
-- so that consumers can use the chart and the structure map without transports.
@[expose, implicit_reducible]
noncomputable def projectiveClosure :
    DenseCompactification
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ J)))) :=
  ⟨Compactification.ofHom
    (Spec.map (J.homogenizationAwayEquiv 0).toRingEquiv.toCommRingCatIso.hom ≫
      Proj.awayι _ _ ((J.homogenization 0).mk_X_mem_quotientGrading 0) one_pos)
    (Proj (J.homogenization 0).quotientGrading ↘ Spec (.of R)) (by
      rw [HomogeneousIdeal.over_proj_quotientGrading, Category.assoc, Proj.awayι_toSpecCoeff,
        ← Spec.map_comp]
      congr 1
      ext1
      exact (J.homogenizationAwayEquiv 0).toAlgHom.comp_algebraMap),
    (denseCompactificationProperty_iff _ _).mpr (by
      have := Proj.isSchemeTheoreticallyDominant_awayι _
        ((J.homogenization 0).mk_X_mem_quotientGrading 0) one_pos
        J.mk_X_mem_nonZeroDivisors_homogenization
      dsimp only [Compactification.j, Compactification.ofHom_obj_ι]
      infer_instance)⟩

/-- The ambient scheme of the projective closure is `Proj (R[X₀, …, Xₙ] ⧸ Jʰ)`. -/
@[simp]
theorem projectiveClosure_Xbar :
    (projectiveClosure J).obj.Xbar = Proj (J.homogenization 0).quotientGrading :=
  (rfl)

/-- The interior map of the projective closure is the standard chart `D₊(X₀)`, after identifying
its coordinate ring with `R[Y₀, …, Yₙ₋₁] ⧸ J`. -/
@[simp]
theorem projectiveClosure_j :
    (projectiveClosure J).obj.j =
      Spec.map (J.homogenizationAwayEquiv 0).toRingEquiv.toCommRingCatIso.hom ≫
        Proj.awayι _ _ ((J.homogenization 0).mk_X_mem_quotientGrading 0) one_pos :=
  (rfl)

/-- The proper map of the projective closure is the structure morphism of the projective
scheme. -/
@[simp]
theorem projectiveClosure_p :
    (projectiveClosure J).obj.p = (Proj (J.homogenization 0).quotientGrading ↘ Spec (.of R)) :=
  (rfl)

end DenseCompactification

/-- **Affine Nagata compactification.** A morphism of finite type between affine schemes has a
dense compactification. -/
theorem nonempty_denseCompactification_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X]
    [IsAffine S] [LocallyOfFiniteType f] : Nonempty (DenseCompactification f) := by
  -- Present the coordinate ring of the source as a quotient of a polynomial ring over that of the
  -- target and take the projective closure.
  have hf : f.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let := f.appTop.hom.toAlgebra
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let C := DenseCompactification.projectiveClosure (RingHom.ker π)
  refine ⟨⟨Compactification.ofHom
    (X.isoSpec.hom ≫ Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫ C.obj.j)
    (C.obj.p ≫ S.isoSpec.inv) ?_, ?_⟩⟩
  · -- The interior followed by the proper map is `Spec` of the structure map, then `f`.
    have hC : C.obj.j ≫ C.obj.p =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (MvPolynomial (Fin n) Γ(S, ⊤) ⧸
          RingHom.ker π))) := C.obj.obj.ι_π
    rw [Category.assoc, Category.assoc, reassoc_of% hC, ← Spec.map_comp_assoc]
    have he : CommRingCat.ofHom (algebraMap Γ(S, ⊤) _) ≫ e.toRingEquiv.toCommRingCatIso.hom =
        f.appTop := by
      ext1
      exact e.toAlgHom.comp_algebraMap
    rw [he, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [denseCompactificationProperty_iff]
    dsimp only [Compactification.j, Compactification.ofHom_obj_ι]
    infer_instance

/-- A morphism of finite type between affine schemes has a compactification, so its
compactifications and its dense compactifications form cofiltered categories. -/
instance {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] [LocallyOfFiniteType f] :
    Nonempty (Compactification f) :=
  (nonempty_denseCompactification_of_isAffine f).map (·.obj)

end TauCeti
