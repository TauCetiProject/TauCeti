/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Equation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism

/-!
# The Bosma–Lenstra addition morphism on points

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model and let `E ×_{Spec R} E ⟶ E` be the Bosma–Lenstra addition morphism
`WeierstrassCurve.additionMorphism`. This file computes the addition morphism on points.

Let `g : R →+* A` be a ring homomorphism and let `P` and `Q` be solutions of the projective
Weierstrass equation of `W.map g` with unit coordinates `Pᵢ` and `Qⱼ`, the homogeneous coordinates
of the `A`-points `projModelPoint W g P` and `projModelPoint W g Q` of `E`. If some coordinate of
the addition law `addXYZ P Q` (resp. `dblAddXYZ P Q`) is a unit, then the addition morphism sends
the pair of these points to the point with homogeneous coordinates `addXYZ P Q`
(resp. `dblAddXYZ P Q`).

When `g : R →+* K` goes to a field, `P` and `Q` are nonsingular, since `W` is elliptic. One of the
two laws then does not vanish at `P` and `Q`, and its value represents their sum `add P Q` in
Mathlib's projective group law on `W.map g`: the addition morphism sends the pair of `K`-points to
the point with homogeneous coordinates `add P Q`. For a curve over a field `K`, through the
identification `WeierstrassCurve.projModelPointsEquiv` of the sections of `E ⟶ Spec K` with the
points `W.toAffine.Point` of `W`, the addition morphism is the addition of these points.

## Main results

* `WeierstrassCurve.lift_projModelPoint_additionMorphism_of_isUnit_addXYZ` and
  `WeierstrassCurve.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ`: the addition
  morphism sends the pair of points with homogeneous coordinates `P` and `Q` to the point with
  homogeneous coordinates `addXYZ P Q` (resp. `dblAddXYZ P Q`), when one of its coordinates is a
  unit.
* `WeierstrassCurve.lift_projModelPoint_additionMorphism_eq_add`: for `g : R →+* K` to a field, the
  addition morphism sends the pair of `K`-points with homogeneous coordinates `P` and `Q` to the
  point with homogeneous coordinates their sum `add P Q`.
* `WeierstrassCurve.projModelPointsEquiv_lift_additionMorphism`: over a field `K`, the addition
  morphism agrees with the addition of the points `W.toAffine.Point` on the sections of
  `projModel W ⟶ Spec K`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/AdditionSpecPoints.lean`:
`SpecPoint.factors_blOpen`, within `lift_projModelPoint_additionMorphism_of_isUnit_addXYZ` and
`lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ`; `SpecPoint.arm_Z`, `SpecPoint.arm_Y`
and `mulModelHom_specPoints_atlas`, within `lift_projModelPoint_additionMorphism_eq_add`; and
`mulModelHom_specPoints`, as `lift_projModelPoint_additionMorphism_eq_add` and
`projModelPointsEquiv_lift_additionMorphism`.

The source works with the universal elliptic curve over a Jacobson domain, factors a field point of
`E ×_{Spec R} E` through the open set where one of the two laws is regular, splits the products of
charts into its `Z`- and `Y`-families, and transports the result to every curve by base change. It
states the agreement for the `K`-points of `E` over every field `K` that is an `R`-algebra. Here a
pair of points with unit coordinates, over any ring homomorphism, is factored directly through a
piece of the chart cover `WeierstrassCurve.additionCover`. The agreement with the group law is
stated on homogeneous coordinates for every `g : R →+* K` to a field, and on `W.toAffine.Point`
for a curve over the field `K` itself.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

variable {A : Type u} [CommRing A] {g : R →+* A} {P Q : Fin 3 → A}
  (hP : (W.toProjective.map g).Equation P) (hQ : (W.toProjective.map g).Equation Q)

-- The point with homogeneous coordinates `P` is `Spec α` followed by the chart `D₊(Xᵢ)`, for a
-- homomorphism `α` over `g` from the chart ring sending the universal point to `Pᵢ⁻¹ • P`.
private theorem exists_SpecMap_comp_chartι {i : Fin 3} (hi : IsUnit (P i)) :
    ∃ α : CommRingCat.of (W.toProjective.ChartRing i) ⟶ CommRingCat.of A,
      CommRingCat.ofHom (algebraMap R _) ≫ α = CommRingCat.ofHom g ∧
      α.hom ∘ W.toProjective.chartPoint i = hi.unit⁻¹ • P ∧
      Spec.map α ≫ W.chartι i = W.projModelPoint g hP hi := by
  let α := (W.toProjective.awayEvalHom g hP hi).comp
    (W.toProjective.awayEquivChartRing i).symm.toRingHom
  have hα : α.comp (algebraMap R _) = g := by
    rw [RingHom.comp_assoc, Projective.awayEquivChartRing_symm_comp_algebraMap,
      Projective.awayEvalHom_comp_algebraMap]
  have hαP : α ∘ W.toProjective.chartPoint i = hi.unit⁻¹ • P :=
    funext fun k ↦ by simp [α, Units.smul_def, mul_comm]
  refine ⟨CommRingCat.ofHom α, by rw [← CommRingCat.ofHom_comp, hα], hαP, ?_⟩
  -- the chart is the point with homogeneous coordinates the image of the universal point
  rw [W.chartι_eq_projModelPoint i, SpecMap_projModelPoint, projModelPoint_eq_projModelPoint_iff]
  exact ⟨hα, hi.unit⁻¹, hαP⟩

-- The pair of points with homogeneous coordinates `P` and `Q` is `Spec φ` followed by the product
-- of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)`, for a homomorphism `φ` over `g` taking the coordinates of
-- the two laws at the universal points to a common unit multiple of those at `P` and `Q`.
private theorem exists_SpecMap_comp_chartPairι {i j : Fin 3} (hi : IsUnit (P i))
    (hj : IsUnit (Q j)) :
    ∃ (φ : CommRingCat.of (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j) ⟶
      CommRingCat.of A) (w : Aˣ), CommRingCat.ofHom (algebraMap R _) ≫ φ = CommRingCat.ofHom g ∧
      φ.hom ∘ W.chartPairLaw i j =
        w • Sum.elim ((W.toProjective.map g).addXYZ P Q) ((W.toProjective.map g).dblAddXYZ P Q) ∧
      Spec.map φ ≫ W.chartPairι i j =
        pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
          ((W.projModelPoint_projModelOver g hP hi).trans
            (W.projModelPoint_projModelOver g hQ hj).symm) := by
  obtain ⟨α, hαg, hαP, hα⟩ := W.exists_SpecMap_comp_chartι hP hi
  obtain ⟨β, hβg, hβQ, hβ⟩ := W.exists_SpecMap_comp_chartι hQ hj
  have h := hαg.trans hβg.symm
  have hd := CommRingCat.isPushout_tensorProduct R (W.toProjective.ChartRing i)
    (W.toProjective.ChartRing j)
  -- `R → ChartRing i ⊗[R] ChartRing j` factors through the left inclusion
  have hφg : CommRingCat.ofHom (algebraMap R _) ≫ hd.desc α β h = CommRingCat.ofHom g :=
    (Category.assoc _ _ _).trans ((congrArg _ (hd.inl_desc α β h)).trans hαg)
  refine ⟨hd.desc α β h, (hi.unit⁻¹ * hj.unit⁻¹) ^ 2, hφg, ?_,
    by simp only [SpecMap_desc_chartPairι, hα, hβ]⟩
  -- along `φ`, the curve is `W.map g` and the universal points are `Pᵢ⁻¹ • P` and `Qⱼ⁻¹ • Q`, so
  -- the two laws at the universal points go to `(Pᵢ Qⱼ)⁻²` times the laws at `P` and `Q`
  rw [comp_chartPairLaw, hd.inl_desc, hd.inr_desc, hαg, CommRingCat.hom_ofHom, hαP, hβQ]
  ext (k | k) <;> simp [Units.smul_def, Projective.addXYZ_smul, Projective.dblAddXYZ_smul]

-- If the coordinate of index `k` of the two laws at `P` and `Q` is a unit, then the addition
-- morphism sends the pair of points with homogeneous coordinates `P` and `Q` to the point with
-- homogeneous coordinates the law selected by `k`.
private theorem lift_projModelPoint_additionMorphism [W.IsElliptic] {i j : Fin 3}
    (hi : IsUnit (P i)) (hj : IsUnit (Q j)) (k : Fin 3 ⊕ Fin 3)
    (hL : (W.toProjective.map g).Equation fun m ↦ Sum.elim ((W.toProjective.map g).addXYZ P Q)
      ((W.toProjective.map g).dblAddXYZ P Q) (k.map (fun _ ↦ m) (fun _ ↦ m)))
    (hk : IsUnit (Sum.elim ((W.toProjective.map g).addXYZ P Q)
      ((W.toProjective.map g).dblAddXYZ P Q) k)) :
    pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
        ((W.projModelPoint_projModelOver g hP hi).trans
          (W.projModelPoint_projModelOver g hQ hj).symm) ≫ W.additionMorphism =
      W.projModelPoint g hL (i := k.elim id id) (by cases k <;> exact hk) := by
  obtain ⟨φ, w, hφg, hφ, hφPQ⟩ := W.exists_SpecMap_comp_chartPairι hP hQ hi hj
  -- `φ` takes the law coordinate `chartPairLaw W i j k` to a unit, so it factors through the
  -- localization away from it, the piece of the chart cover indexed by `k`
  obtain ⟨ψ, rfl⟩ : ∃ ψ : CommRingCat.of (Localization.Away (W.chartPairLaw i j k)) ⟶ .of A,
      CommRingCat.ofHom (algebraMap _ _) ≫ ψ = φ :=
    ⟨_, CommRingCat.hom_ext <| IsLocalization.Away.lift_comp _
      (congrFun hφ k ▸ w.isUnit.mul hk : IsUnit ((φ.hom ∘ W.chartPairLaw i j) k))⟩
  obtain ⟨_, _, e⟩ := W.exists_SpecMap_additionOnPiece k ψ
  rw [← hφPQ, Category.assoc, Spec.map_comp_assoc, SpecMap_chartPairι_additionMorphism, e,
    projModelPoint_eq_projModelPoint_iff,
    IsScalarTower.algebraMap_eq R (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j)]
  -- `ψ` lies over `g`, and takes the law at the universal points to `w` times the law at `P`, `Q`
  exact ⟨congrArg CommRingCat.Hom.hom hφg, w, funext fun m ↦ congrFun hφ _⟩

variable {hP hQ}

/-- **The addition morphism on points, through the law `addXYZ`.** Let `P` and `Q` be solutions
of the projective Weierstrass equation of `W.map g`, for a ring homomorphism `g : R →+* A`, with
unit coordinates `Pᵢ` and `Qⱼ`. If the coordinate of index `m` of the addition law `addXYZ P Q`
attached to the line `Z = 0` is a unit, then the addition morphism `E ×_{Spec R} E ⟶ E` sends the
pair of `A`-points with homogeneous coordinates `P` and `Q` to the `A`-point with homogeneous
coordinates `addXYZ P Q`. -/
theorem lift_projModelPoint_additionMorphism_of_isUnit_addXYZ [W.IsElliptic] {i j m : Fin 3}
    (hi : IsUnit (P i)) (hj : IsUnit (Q j)) (hm : IsUnit ((W.toProjective.map g).addXYZ P Q m)) :
    pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
        ((W.projModelPoint_projModelOver g hP hi).trans
          (W.projModelPoint_projModelOver g hQ hj).symm) ≫ W.additionMorphism =
      W.projModelPoint g (hP.addXYZ hQ) hm :=
  -- for the index `.inl m`, the selected law `Sum.elim … (Sum.map … (.inl m))` unfolds to
  -- `addXYZ P Q`
  W.lift_projModelPoint_additionMorphism hP hQ hi hj (.inl m) (hP.addXYZ hQ) hm

/-- **The addition morphism on points, through the law `dblAddXYZ`.** Let `P` and `Q` be solutions
of the projective Weierstrass equation of `W.map g`, for a ring homomorphism `g : R →+* A`, with
unit coordinates `Pᵢ` and `Qⱼ`. If the coordinate of index `m` of the addition law `dblAddXYZ P Q`
attached to the line `Y = 0` is a unit, then the addition morphism `E ×_{Spec R} E ⟶ E` sends the
pair of `A`-points with homogeneous coordinates `P` and `Q` to the `A`-point with homogeneous
coordinates `dblAddXYZ P Q`. -/
theorem lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ [W.IsElliptic] {i j m : Fin 3}
    (hi : IsUnit (P i)) (hj : IsUnit (Q j)) (hm : IsUnit ((W.toProjective.map g).dblAddXYZ P Q m)) :
    pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
        ((W.projModelPoint_projModelOver g hP hi).trans
          (W.projModelPoint_projModelOver g hQ hj).symm) ≫ W.additionMorphism =
      W.projModelPoint g (hP.dblAddXYZ hQ) hm :=
  -- for the index `.inr m`, the selected law `Sum.elim … (Sum.map … (.inr m))` unfolds to
  -- `dblAddXYZ P Q`
  W.lift_projModelPoint_additionMorphism hP hQ hi hj (.inr m) (hP.dblAddXYZ hQ) hm

end CommRing

section Fibre

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open Projective in
/-- **The addition morphism on field-valued points.** Let `g : R →+* K` be a ring homomorphism to a
field, and let `P` and `Q` be solutions of the projective Weierstrass equation of `W.map g` with
unit coordinates `Pᵢ` and `Qⱼ`; as `W` is elliptic, they are nonsingular. Then the addition morphism
`E ×_{Spec R} E ⟶ E` sends the pair of `K`-points of `E` with homogeneous coordinates `P` and `Q` to
the `K`-point with homogeneous coordinates their sum `add P Q` in Mathlib's projective group law on
`W.map g`, read on any chart `D₊(Xₘ)` on which it has a unit coordinate. -/
theorem lift_projModelPoint_additionMorphism_eq_add [W.IsElliptic] {K : Type u} [Field K]
    {g : R →+* K} {P Q : Fin 3 → K} {hP : (W.toProjective.map g).Equation P}
    {hQ : (W.toProjective.map g).Equation Q} {i j m : Fin 3} (hi : IsUnit (P i))
    (hj : IsUnit (Q j)) (hm : IsUnit ((W.toProjective.map g).add P Q m)) :
    pullback.lift (W.projModelPoint g hP hi) (W.projModelPoint g hQ hj)
        ((W.projModelPoint_projModelOver g hP hi).trans
          (W.projModelPoint_projModelOver g hQ hj).symm) ≫ W.additionMorphism =
      W.projModelPoint g (nonsingular_add
        ((equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, hi.ne_zero⟩)).mp hP)
        ((equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨j, hj.ne_zero⟩)).mp hQ)).1
        hm := by
  -- a solution with a nonzero coordinate on an elliptic curve over a field is nonsingular
  have hP' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, hi.ne_zero⟩)).mp hP
  have hQ' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨j, hj.ne_zero⟩)).mp hQ
  -- one of the two laws at `P` and `Q` is nonzero, and represents their sum
  rcases addXYZ_ne_zero_or_dblAddXYZ_ne_zero hP' hQ' with h | h <;>
    obtain ⟨n, hn⟩ := Function.ne_iff.mp h
  · rw [W.lift_projModelPoint_additionMorphism_of_isUnit_addXYZ hi hj hn.isUnit,
      projModelPoint_eq_projModelPoint_iff]
    exact ⟨rfl, 1, by rw [one_smul, add_of_addXYZ_ne_zero h]⟩
  · rw [W.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ hi hj hn.isUnit,
      projModelPoint_eq_projModelPoint_iff]
    obtain ⟨u, hu⟩ := dblAddXYZ_equiv_add hP' hQ' h
    exact ⟨rfl, u, hu.symm⟩

end Fibre

section Field

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

-- Every section of the structure morphism of `projModel W` is the point with homogeneous
-- coordinates a nonsingular representative `P` with a unit coordinate, and corresponds to the point
-- `toAffine W P` of `W`.
private theorem exists_eq_projModelPoint
    (x : {g : Spec (.of K) ⟶ W.projModel // g ≫ W.projModelOver = 𝟙 _}) :
    ∃ (P : Fin 3 → K) (hP : W.toProjective.Nonsingular P) (i : Fin 3) (hi : IsUnit (P i)),
      x.1 = W.projModelPoint (RingHom.id K) hP.1 hi ∧
        W.projModelPointsEquiv x = Projective.Point.toAffine W.toProjective P := by
  -- the point at infinity and the affine points have such representatives
  obtain ⟨P, hP, i, hi, h⟩ : ∃ (P : Fin 3 → K) (hP : W.toProjective.Nonsingular P) (i : Fin 3)
      (hi : IsUnit (P i)), Projective.Point.toAffine W.toProjective P = W.projModelPointsEquiv x :=
    match W.projModelPointsEquiv x with
    | .zero => ⟨![0, 1, 0], Projective.nonsingular_zero, 1, by simp, Projective.Point.toAffine_zero⟩
    | .some a b h => ⟨![a, b, 1], (Projective.nonsingular_some a b).mpr h, 2, by simp,
        Projective.Point.toAffine_some ((Projective.nonsingular_some a b).mpr h)⟩
  exact ⟨P, hP, i, hi, congrArg Subtype.val (W.projModelPointsEquiv.injective
    ((W.projModelPointsEquiv_projModelPoint hP.1 hi).trans h)).symm, h.symm⟩

/-- **The addition morphism on field points.** Let `W` be an elliptic Weierstrass curve over a
field `K` and let `E = projModel W`. Through the identification `projModelPointsEquiv` of the
sections of the structure morphism `E ⟶ Spec K` with the points `W.toAffine.Point` of `W`, the
Bosma–Lenstra addition morphism `E ×_{Spec K} E ⟶ E` is the addition of `W.toAffine.Point`: it
sends the pair of sections `(x, y)` to the section corresponding to the sum of the points
corresponding to `x` and `y`. For points over an arbitrary homomorphism `g : R →+* K` to a field,
given by homogeneous coordinates, see `lift_projModelPoint_additionMorphism_eq_add`. -/
@[simp]
theorem projModelPointsEquiv_lift_additionMorphism [DecidableEq K]
    (x y : {g : Spec (.of K) ⟶ W.projModel // g ≫ W.projModelOver = 𝟙 _}) :
    W.projModelPointsEquiv ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ W.additionMorphism,
      by rw [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc, x.2]⟩ =
      W.projModelPointsEquiv x + W.projModelPointsEquiv y := by
  obtain ⟨P, hP, i, hi, hx, hxP⟩ := W.exists_eq_projModelPoint x
  obtain ⟨Q, hQ, j, hj, hy, hyQ⟩ := W.exists_eq_projModelPoint y
  -- their sum `add P Q` is nonsingular, so it has a unit coordinate
  have hPQ := Projective.nonsingular_add hP hQ
  have hne : W.toProjective.add P Q ≠ 0 := fun h ↦ by
    simp [h, Projective.nonsingular_iff] at hPQ
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hne
  rw [hxP, hyQ, ← Projective.Point.toAffine_add hP hQ]
  -- the pair `(x, y)` is the pair of points with homogeneous coordinates `P` and `Q`, which the
  -- addition morphism sends to the point with homogeneous coordinates `add P Q`
  simp [hx, hy, W.lift_projModelPoint_additionMorphism_eq_add (g := RingHom.id K) (hP := hP.1)
    (hQ := hQ.1) hi hj hm.isUnit]

end Field

end WeierstrassCurve
