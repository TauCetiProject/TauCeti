/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Map
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

/-!
# Right multiplication between fppf homogeneous quotients

Let `G` be an affine group over a commutative ring `R`, let `P` and `Q` be closed subgroups cut
out by Hopf ideals `I` and `J`, and let `g` be an `R`-point of `G`. The map `x ↦ xgQ` from `G` to
the fppf homogeneous quotient `G/Q` descends to a morphism of sheaves

```text
G/P ⟶ G/Q,    xP ↦ xgQ,
```

exactly when `g⁻¹Pg ⊆ Q`, that is, when `P` lies in the conjugate `gQg⁻¹` cut out by
`J.conjugate g`. Equivalently, the `R`-point `gQ` of `G/Q` is fixed by every point of `P` over
every algebra. The descended morphism sends the base point `eP` to `gQ`, commutes with left
translation by `R`-points, depends on `g` only through the coset `gQ`, and composes by
multiplying the points. For `g = 1` it is the projection `G/P ⟶ G/Q` induced by `P ⊆ Q`.

The fixed-point criterion is scheme-theoretic: it quantifies over points with values in every
algebra, and no reducedness, smoothness or finiteness hypothesis is imposed. It rests on the fact
that `G(A) → (G/Q)(A)` identifies exactly the left cosets of `Q(A)`, for every algebra `A`.

## Main declarations

* `CommHopfAlgCat.fppfHomogeneousQuotientRightMul`: the morphism `G/P ⟶ G/Q`, `xP ↦ xgQ`.
* `CommHopfAlgCat.fppfHomogeneousQuotientRightMul_eq_iff`: its characterization by the
  projection from `G`.
* `CommHopfAlgCat.fppfHomogeneousQuotientRightMul_mul_of_mem`: it depends only on `gQ`.
* `CommHopfAlgCat.conjugate_le_iff_forall_fppfHomogeneousQuotientProjection_app_mul_eq`: the point
  `gQ` is fixed by `P` exactly when `g⁻¹Pg ⊆ Q`.
* `CommHopfAlgCat.exists_fppfHomogeneousQuotientProjection_comp_eq_iff`: `x ↦ xgQ` descends to
  `G/P` exactly when `g⁻¹Pg ⊆ Q`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, quotient sheaves and homogeneous spaces.
-/

public section

open CategoryTheory Opposite

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

variable {I J K : HopfIdeal R H}

private theorem pointsRightMul_comp_projection_invariant
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (h : J.conjugate g ≤ I) (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
    (n : quotientPointsSubgroup H I A.unop.unop) :
    (pointsRightMul H g ≫ fppfHomogeneousQuotientProjection H J).app A (ULift.up (x * n.val)) =
      (pointsRightMul H g ≫ fppfHomogeneousQuotientProjection H J).app A (ULift.up x) := by
  refine (fppfHomogeneousQuotientProjection_app_eq_iff H J A _ _).mpr ?_
  have hn := (extendPoint_inv_mul_mul_mem_quotientPointsSubgroup_iff J g _ (n.val⁻¹)).mpr
    (quotientPointsSubgroup_le_of_le H h _ (inv_mem n.property))
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hn

/-- For closed subgroups `P` and `Q` cut out by `I` and `J`, and a ground-ring point `g` with
`g⁻¹Pg ⊆ Q`, the morphism `G/P ⟶ G/Q` of fppf homogeneous quotients sending `xP` to `xgQ`.
The hypothesis says that the conjugate `gQg⁻¹`, cut out by `J.conjugate g`, contains `P`. -/
def fppfHomogeneousQuotientRightMul
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (h : J.conjugate g ≤ I) :
    fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J :=
  (fppfHomogeneousQuotientHomEquiv H I _).symm
    ⟨pointsRightMul H g ≫ fppfHomogeneousQuotientProjection H J,
      pointsRightMul_comp_projection_invariant H g h⟩

/-- The morphism `xP ↦ xgQ` is characterized by its composite with the projection from `G`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_rightMul
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (h : J.conjugate g ≤ I) :
    fppfHomogeneousQuotientProjection H I ≫ (fppfHomogeneousQuotientRightMul H g h).hom =
      pointsRightMul H g ≫ fppfHomogeneousQuotientProjection H J :=
  fppfHomogeneousQuotientHomEquiv_symm_apply H I _ _ _

/-- On projected group points, the morphism `xP ↦ xgQ` is right multiplication by the
extension of `g`. -/
@[simp]
theorem fppfHomogeneousQuotientRightMul_app_projection
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (h : J.conjugate g ≤ I)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (fppfHomogeneousQuotientRightMul H g h).hom.app A
        ((fppfHomogeneousQuotientProjection H I).app A (ULift.up x)) =
      (fppfHomogeneousQuotientProjection H J).app A
        (ULift.up (x * HopfAlgebra.extendPoint H A.unop.unop g)) :=
  congrArg (fun f ↦ f.app A (ULift.up x)) (fppfHomogeneousQuotientProjection_comp_rightMul H g h)

/-- **Evaluation at the base point.** The morphism `xP ↦ xgQ` sends the base point `eP` to
the rational point `gQ`. -/
theorem fppfHomogeneousQuotientRightMul_app_basePoint
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (h : J.conjugate g ≤ I) :
    (fppfHomogeneousQuotientRightMul H g h).hom.app (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of R R)))
          (ULift.up 1)) =
      (fppfHomogeneousQuotientProjection H J).app (op (op (CommAlgCat.of R R))) (ULift.up g) :=
  (fppfHomogeneousQuotientRightMul_app_projection H g h _ 1).trans
    (congrArg (fun y ↦ (fppfHomogeneousQuotientProjection H J).app _ (ULift.up y))
      (by rw [one_mul, HopfAlgebra.extendPoint_self]))

/-- For the identity point, `xP ↦ xQ` is the projection induced by the inclusion `P ⊆ Q`. -/
@[simp]
theorem fppfHomogeneousQuotientRightMul_one (h : J.conjugate 1 ≤ I) :
    fppfHomogeneousQuotientRightMul H 1 h =
      fppfHomogeneousQuotientMap H (by rwa [HopfIdeal.conjugate_one] at h) := by
  apply fppfHomogeneousQuotient_hom_ext
  rw [fppfHomogeneousQuotientProjection_comp_rightMul, pointsRightMul_one, Category.id_comp,
    fppfHomogeneousQuotientProjection_comp_map]

/-- The morphisms `xP ↦ xgQ` and `yQ ↦ yg'S` compose to `xP ↦ xgg'S`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientRightMul_comp
    {g g' : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)}
    (h : J.conjugate g ≤ I) (h' : K.conjugate g' ≤ J) :
    fppfHomogeneousQuotientRightMul H g h ≫ fppfHomogeneousQuotientRightMul H g' h' =
      fppfHomogeneousQuotientRightMul H (g * g')
        (by rw [HopfIdeal.conjugate_mul]; exact (HopfIdeal.conjugate_mono g h').trans h) := by
  apply fppfHomogeneousQuotient_hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    fppfHomogeneousQuotientProjection_comp_rightMul_assoc,
    fppfHomogeneousQuotientProjection_comp_rightMul, pointsRightMul_comp_pointsRightMul_assoc]

/-- Right multiplication by a ground-ring point of `P` induces the identity of `G/P`. -/
@[simp]
theorem fppfHomogeneousQuotientRightMul_of_mem
    {q : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)}
    (hq : q ∈ quotientPointsSubgroup H I (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientRightMul H q
        (HopfIdeal.conjugate_eq_self_of_mem_quotientPointsSubgroup I hq).le = 𝟙 _ := by
  apply fppfHomogeneousQuotient_hom_ext
  rw [fppfHomogeneousQuotientProjection_comp_rightMul, ObjectProperty.FullSubcategory.id_hom,
    Category.comp_id]
  ext A ⟨(x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
  refine (fppfHomogeneousQuotientProjection_app_eq_iff H I A _ _).mpr ?_
  have hqA :
      HopfAlgebra.extendPoint H A.unop.unop q ∈ quotientPointsSubgroup H I A.unop.unop := by
    rw [HopfAlgebra.extendPoint_apply, ← AlgHom.mapValue_apply]
    exact mapValue_mem_quotientPointsSubgroup H I _ hq
  simpa only [mul_inv_rev, inv_mul_cancel_right] using inv_mem hqA

/-- **Independence of the representative.** The morphism `xP ↦ xgQ` depends only on the coset
`gQ`: replacing `g` by `gq` for a ground-ring point `q` of `Q` gives the same morphism. -/
theorem fppfHomogeneousQuotientRightMul_mul_of_mem
    {g q : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)}
    (h : J.conjugate g ≤ I) (hq : q ∈ quotientPointsSubgroup H J (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientRightMul H (g * q)
        (by rwa [HopfIdeal.conjugate_mul,
          HopfIdeal.conjugate_eq_self_of_mem_quotientPointsSubgroup J hq]) =
      fppfHomogeneousQuotientRightMul H g h := by
  rw [← fppfHomogeneousQuotientRightMul_comp H h
    (HopfIdeal.conjugate_eq_self_of_mem_quotientPointsSubgroup J hq).le,
    fppfHomogeneousQuotientRightMul_of_mem H hq, Category.comp_id]

/-- The morphism `xP ↦ xgQ` is the unique sheaf morphism `G/P ⟶ G/Q` whose composite with
the projection from `G` is `x ↦ xgQ`. -/
theorem fppfHomogeneousQuotientRightMul_eq_iff
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (h : J.conjugate g ≤ I)
    (f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J) :
    f = fppfHomogeneousQuotientRightMul H g h ↔
      fppfHomogeneousQuotientProjection H I ≫ f.hom =
        pointsRightMul H g ≫ fppfHomogeneousQuotientProjection H J := by
  constructor
  · rintro rfl
    exact fppfHomogeneousQuotientProjection_comp_rightMul H g h
  · intro hf
    apply fppfHomogeneousQuotient_hom_ext
    rw [hf, fppfHomogeneousQuotientProjection_comp_rightMul]

/-- The morphisms `xP ↦ xgQ` commute with left translation by ground-ring points. -/
@[reassoc]
theorem fppfHomogeneousQuotientTranslation_hom_comp_rightMul
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (h : J.conjugate g ≤ I)
    (t : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientTranslation H I t).hom ≫ fppfHomogeneousQuotientRightMul H g h =
      fppfHomogeneousQuotientRightMul H g h ≫ (fppfHomogeneousQuotientTranslation H J t).hom := by
  apply fppfHomogeneousQuotient_hom_ext
  ext A ⟨(x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, TypeCat.Fun.toFun_apply]
  -- Translate first or multiply on the right first: both give `t * x * g`.
  refine (congrArg _ (fppfHomogeneousQuotientTranslation_hom_app_projection H I t A x)).trans ?_
  refine (fppfHomogeneousQuotientRightMul_app_projection H g h A _).trans ?_
  refine Eq.trans ?_ (congrArg _ (fppfHomogeneousQuotientRightMul_app_projection H g h A x)).symm
  rw [mul_assoc]
  exact (fppfHomogeneousQuotientTranslation_hom_app_projection H J t A _).symm

/-- **Fixed points of `P` on `G/Q`.** The ground-ring point `gQ` of `G/Q` is fixed by the
closed subgroup `P`, in the sense that `pgQ = gQ` for every point `p` of `P` over every
algebra, exactly when `g⁻¹Pg ⊆ Q`, that is, when `P` lies in the conjugate cut out by
`J.conjugate g`. -/
theorem conjugate_le_iff_forall_fppfHomogeneousQuotientProjection_app_mul_eq
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    J.conjugate g ≤ I ↔
      ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (p : HopfAlgebra.points (R := R) (H := H) A.unop.unop),
        p ∈ quotientPointsSubgroup H I A.unop.unop →
          (fppfHomogeneousQuotientProjection H J).app A
              (ULift.up (p * HopfAlgebra.extendPoint H A.unop.unop g)) =
            (fppfHomogeneousQuotientProjection H J).app A
              (ULift.up (HopfAlgebra.extendPoint H A.unop.unop g)) := by
  constructor
  · intro h A p hp
    refine (fppfHomogeneousQuotientProjection_app_eq_iff H J A _ _).mpr ?_
    have hp' := (extendPoint_inv_mul_mul_mem_quotientPointsSubgroup_iff J g _ p⁻¹).mpr
      (quotientPointsSubgroup_le_of_le H h _ (inv_mem hp))
    simpa only [mul_inv_rev, mul_assoc] using hp'
  · intro hfix
    refine (HopfIdeal.le_iff_forall_quotientPointsSubgroup_le _ _).mpr fun A p hp ↦ ?_
    refine (extendPoint_inv_mul_mul_mem_quotientPointsSubgroup_iff J g A p).mp ?_
    have hp' := (fppfHomogeneousQuotientProjection_app_eq_iff H J (op (op A)) _ _).mp
      (hfix (op (op A)) p⁻¹ (inv_mem hp))
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hp'

/-- **Equivariant descent.** The map `x ↦ xgQ` from `G` descends to a morphism
`G/P ⟶ G/Q` exactly when `g⁻¹Pg ⊆ Q`; the descended morphism is then
`fppfHomogeneousQuotientRightMul`. -/
theorem exists_fppfHomogeneousQuotientProjection_comp_eq_iff
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (∃ f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J,
        fppfHomogeneousQuotientProjection H I ≫ f.hom =
          pointsRightMul H g ≫ fppfHomogeneousQuotientProjection H J) ↔
      J.conjugate g ≤ I := by
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun h ↦
    ⟨_, fppfHomogeneousQuotientProjection_comp_rightMul H g h⟩⟩
  refine (conjugate_le_iff_forall_fppfHomogeneousQuotientProjection_app_mul_eq H g).mpr
    fun A p hp ↦ ?_
  -- Evaluate both sides of `hf` at a lifted point; composites of components apply in turn.
  have hval (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
      f.hom.app A ((fppfHomogeneousQuotientProjection H I).app A (ULift.up x)) =
        (fppfHomogeneousQuotientProjection H J).app A
          (ULift.up (x * HopfAlgebra.extendPoint H A.unop.unop g)) :=
    congrArg (fun φ ↦ φ.app A (ULift.up x)) hf
  -- `p` and `1` have the same image in `G/P`, hence the same image under `f`.
  have hp1 : (fppfHomogeneousQuotientProjection H I).app A (ULift.up p) =
      (fppfHomogeneousQuotientProjection H I).app A
        (ULift.up (1 : HopfAlgebra.points (R := R) (H := H) A.unop.unop)) :=
    (fppfHomogeneousQuotientProjection_app_eq_iff H I A _ _).mpr
      (by simpa only [mul_one] using inv_mem hp)
  have hp1g := (hval p).symm.trans ((congrArg _ hp1).trans (hval 1))
  rwa [one_mul] at hp1g

end

end CommHopfAlgCat
