/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.Degree
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero

/-!
# The Abel–Jacobi maps land in `Pic⁰`

Let `f : X ⟶ S` be a smooth proper morphism of relative dimension one with geometrically
connected fibres. A relative effective Cartier divisor `D` on `X_T = T ×_S X` restricts, over a
point `ξ : Spec Ω ⟶ T` with values in a field, to an effective Cartier divisor `D_ξ` on the fibre,
which is a connected smooth proper curve over `Ω`; the line bundle `𝒪(D)` restricts to `𝒪(D_ξ)`,
whose degree is the rank of `D_ξ` over `Ω`
(`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf`). Since the rank
of `D` is preserved by base change, the fibre degree of the Abel map `D ↦ 𝒪(D)` at `ξ` is the rank
of `D` at the image of `ξ` (`relativePicardFiberDegree_abelMap_app`), and it is `d` for a divisor
in `Div^d_{X/S}`.

Consequently, for a section `x₀`, the Abel–Jacobi map of degree `d`, `D ↦ 𝒪(D - d • x₀_T)`, takes
values in the degree-zero Picard functor `Pic⁰_{X/S}`: both `D` and `d • x₀_T` have degree `d` on
every fibre. This gives the normalized Abel maps `Div^d_{X/S} ⟶ Pic⁰_{X/S}`
(`abelJacobiMapOfDegreeToPicZero`) and, in degree one, the Abel–Jacobi map `x ↦ 𝒪(Γₓ - x₀_T)`
from the functor of points of `X` to `Pic⁰_{X/S}` (`abelJacobiMapToPicZero`), on functors of
points. Representability of `Pic⁰_{X/S}` is not treated here.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_abelMap_app`: the fibre degree of `𝒪(D)` is
  the rank of `D`;
* `TauCeti.AlgebraicGeometry.abelJacobiMapOfDegree_app_mem_relativePicardDegreeZeroSubfunctor_obj`:
  `𝒪(D - d • x₀_T)` has degree zero on every fibre;
* `TauCeti.AlgebraicGeometry.abelJacobiMapOfDegreeToPicZero`: the Abel–Jacobi map of degree `d`
  as a natural transformation `Div^d_{X/S} ⟶ Pic⁰_{X/S}` into the degree-zero subfunctor;
* `TauCeti.AlgebraicGeometry.abelJacobiMapToPicZero`: the Abel–Jacobi map
  `Hom_S(-, X) ⟶ Pic⁰_{X/S}`.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3 (the Abel maps) and Section 9.5 (`Pic⁰`).
* J. S. Milne, *Jacobian varieties*, in *Arithmetic Geometry* (G. Cornell, J. H. Silverman,
  eds.), Springer, 1986, Sections 2 and 5 (the maps `D ↦ 𝒪(D - d P)` into the Jacobian).
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyConnected f]

/-- **The fibre degree of the Abel map is the degree of the divisor.** For a relative effective
Cartier divisor `D` on `X_T` and a point `ξ : Spec Ω ⟶ T` with values in a field, the line bundle
`𝒪(D)` has degree on the fibre over `ξ` equal to the rank of `D` over `T` at the image of `ξ`. -/
theorem relativePicardFiberDegree_abelMap_app {T : (Over S)ᵒᵖ} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.unop.left) (D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T)
    (x : Spec (.of Ω)) :
    relativePicardFiberDegree f ξ ((abelMap f).app T (ULift.up D)) =
      (D.1.subschemeι ≫ pullback.fst T.unop.hom f).finrank (ξ x) := by
  have hD := (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp D.2
  -- The fibre over `ξ` is the base change of `X_T ⟶ T` along `ξ`.
  let g : pullback (ξ ≫ T.unop.hom) f ⟶ pullback T.unop.hom f :=
    pullback.map _ _ _ _ ξ (𝟙 X) (𝟙 S) (by simp) (by simp)
  -- `(Over.pullback f).map (Over.homMk ξ)` is this `pullback.map` by definition.
  have hpb : IsPullback g (pullback.fst (ξ ≫ T.unop.hom) f) (pullback.fst T.unop.hom f) ξ :=
    isPullback_over_pullback_map_left f (Over.homMk ξ : Over.mk (ξ ≫ T.unop.hom) ⟶ T.unop)
  have hD' := hD.comap_of_isPullback hpb
  have := hD.flat
  have := hD.isFinite
  -- `𝒪(D)` restricts to `𝒪(D_ξ)` on the fibre.
  have hres : LineBundleClass.pullback g
      (LineBundleClass.mk hD.isEffectiveCartier.toInvertibleSheaf)⁻¹ =
        (LineBundleClass.mk hD'.isEffectiveCartier.toInvertibleSheaf)⁻¹ := by
    rw [← LineBundleClass.pullbackHom_apply, map_inv, LineBundleClass.pullbackHom_apply]
    exact congrArg (·⁻¹) (Scheme.IdealSheafData.IsEffectiveCartier.pullback_mk_toInvertibleSheaf
      hD.isEffectiveCartier hD'.isEffectiveCartier)
  -- The fibre is a connected smooth proper curve over `Ω`.
  let _ : (pullback (ξ ≫ T.unop.hom) f).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have : IsProper (pullback (ξ ≫ T.unop.hom) f ↘ Spec (.of Ω)) :=
    inferInstanceAs (IsProper (pullback.fst (ξ ≫ T.unop.hom) f))
  have : SmoothOfRelativeDimension 1 (pullback (ξ ≫ T.unop.hom) f ↘ Spec (.of Ω)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.fst (ξ ≫ T.unop.hom) f))
  have : IsIntegral (pullback (ξ ≫ T.unop.hom) f) :=
    GeometricallyIntegral.geometrically_isIntegral (ξ ≫ T.unop.hom) _ _
      (IsPullback.of_hasPullback (ξ ≫ T.unop.hom) f).flip
  rw [abelMap_app_apply, relativePicardFiberDegree_mk]
  refine (congrArg (LineBundleClass.eulerDegree Ω) hres).trans ?_
  rw [Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf Ω _
    hD'.isEffectiveCartier x]
  exact congrArg _ (D.1.finrank_comap_of_isPullback _ g _ ξ hpb x)

/-- A relative effective Cartier divisor of degree `d` has fibre degree `d` under the Abel map:
`𝒪(D)` has degree `d` on every fibre. -/
theorem relativePicardFiberDegree_abelMap_app_of_mem {d : ℕ} {T : (Over S)ᵒᵖ} {Ω : Type u}
    [Field Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left)
    {D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T}
    (hD : D ∈ (relativeEffectiveCartierDegreeSubfunctor f d).obj T) :
    relativePicardFiberDegree f ξ ((abelMap f).app T (ULift.up D)) = d := by
  -- The spectrum of a field has a point at which to evaluate the rank.
  obtain ⟨x⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  rw [relativePicardFiberDegree_abelMap_app f ξ D x,
    (mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff f).mp hD]

variable {x₀ : S ⟶ X} (hx₀ : x₀ ≫ f = 𝟙 S)

/-- **The Abel–Jacobi map of degree `d` takes values in `Pic⁰`**: for a divisor `D` of degree `d`,
the class of `𝒪(D - d • x₀_T)` has degree zero on every geometric fibre. -/
theorem abelJacobiMapOfDegree_app_mem_relativePicardDegreeZeroSubfunctor_obj (d : ℕ)
    {T : (Over S)ᵒᵖ} (D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T) :
    (abelJacobiMapOfDegree f hx₀ d).app T (ULift.up D) ∈
      (relativePicardDegreeZeroSubfunctor f).obj T := by
  refine (mem_relativePicardDegreeZeroSubfunctor_obj_iff f).mpr fun Ω _ _ ξ ↦ ?_
  -- `d • x₀_T` is a divisor of degree `d`, and the Abel map is multiplicative.
  have hpow : (abelMap f).app T (ULift.up ((graphDivisor f).app T (basePoint hx₀ T.unop))) ^ d =
      (abelMap f).app T (ULift.up ((graphDivisor f).app T (basePoint hx₀ T.unop) ^ d)) := by
    simp only [← abelMapMonoidHom_apply, map_pow]
  rw [abelJacobiMapOfDegree_app_apply, hpow, div_eq_mul_inv,
    relativePicardFiberDegree_mul_of_smooth, relativePicardFiberDegree_inv_of_smooth,
    relativePicardFiberDegree_abelMap_app_of_mem f ξ D.2,
    relativePicardFiberDegree_abelMap_app_of_mem f ξ
      (graphDivisor_basePoint_pow_mem_relativeEffectiveCartierDegreeSubfunctor_obj f hx₀ d T),
    add_neg_cancel]

/-- The image of the Abel–Jacobi map of degree `d` lies in the degree-zero subfunctor
`Pic⁰_{X/S}` of the relative Picard presheaf. -/
theorem range_abelJacobiMapOfDegree_le (d : ℕ) :
    Subfunctor.range (abelJacobiMapOfDegree f hx₀ d) ≤ relativePicardDegreeZeroSubfunctor f := by
  rintro T _ ⟨⟨D⟩, rfl⟩
  exact abelJacobiMapOfDegree_app_mem_relativePicardDegreeZeroSubfunctor_obj f hx₀ d D

/-- **The Abel–Jacobi map of degree `d` into `Pic⁰_{X/S}`**: the natural transformation from the
functor `Div^d_{X/S}` of relative effective Cartier divisors of degree `d` to the subfunctor
`Pic⁰_{X/S}` of classes of degree zero on every geometric fibre, sending `D` to the class of
`𝒪(D - d • x₀_T)`. Followed by the inclusion of `Pic⁰_{X/S}` it is `abelJacobiMapOfDegree`
(`abelJacobiMapOfDegreeToPicZero_ι`). -/
def abelJacobiMapOfDegreeToPicZero (d : ℕ) :
    (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor ⋙ uliftFunctor.{u + 1} ⟶
      (relativePicardDegreeZeroSubfunctor f).toFunctor :=
  Subfunctor.lift _ (range_abelJacobiMapOfDegree_le f hx₀ d)

/-- The Abel–Jacobi map of degree `d` into `Pic⁰_{X/S}`, followed by the inclusion of
`Pic⁰_{X/S}` into the relative Picard presheaf, is the Abel–Jacobi map of degree `d`. -/
@[reassoc (attr := simp)]
theorem abelJacobiMapOfDegreeToPicZero_ι (d : ℕ) :
    abelJacobiMapOfDegreeToPicZero f hx₀ d ≫ (relativePicardDegreeZeroSubfunctor f).ι =
      abelJacobiMapOfDegree f hx₀ d :=
  Subfunctor.lift_ι _ _

/-- **The Abel–Jacobi map into `Pic⁰_{X/S}`**: the natural transformation from the functor of
points `T ↦ Hom_S(T, X)` to the subfunctor `Pic⁰_{X/S}` of classes of degree zero on every
geometric fibre, sending a `T`-point `x` to the class of `𝒪(Γₓ - x₀_T)`. Followed by the inclusion
of `Pic⁰_{X/S}` it is `abelJacobiMap` (`abelJacobiMapToPicZero_ι`). -/
def abelJacobiMapToPicZero :
    yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1} ⟶
      (relativePicardDegreeZeroSubfunctor f).toFunctor :=
  Functor.whiskerRight (graphDivisorDegreeOne f) uliftFunctor.{u + 1} ≫
    abelJacobiMapOfDegreeToPicZero f hx₀ 1

/-- The Abel–Jacobi map into `Pic⁰_{X/S}`, followed by the inclusion of `Pic⁰_{X/S}` into the
relative Picard presheaf, is the Abel–Jacobi map `x ↦ 𝒪(Γₓ - x₀_T)`. -/
@[reassoc (attr := simp)]
theorem abelJacobiMapToPicZero_ι :
    abelJacobiMapToPicZero f hx₀ ≫ (relativePicardDegreeZeroSubfunctor f).ι =
      abelJacobiMap f hx₀ := by
  rw [abelJacobiMapToPicZero, Category.assoc, abelJacobiMapOfDegreeToPicZero_ι,
    whiskerRight_graphDivisorDegreeOne_comp_abelJacobiMapOfDegree_one]

end

end TauCeti.AlgebraicGeometry
