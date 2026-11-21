/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Action
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.RightMul
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.RationalPoints

/-!
# Equivariant morphisms between homogeneous quotients

Let `G` be an affine group over a commutative ring `R`, and let `P` and `Q` be closed subgroups
cut out by Hopf ideals `I` and `J`. A morphism `f : G/P ⟶ G/Q` of fppf homogeneous quotients is
`G`-equivariant when it commutes with the left action of `G`
(`CommHopfAlgCat.fppfHomogeneousQuotientAction`) on points with values in every algebra.

**Evaluation at the base point** identifies the `G`-equivariant morphisms `G/P ⟶ G/Q` with the
`R`-points `y` of `G/Q` fixed by `P`, meaning that `p • y = y` for every point `p` of `P` with
values in any algebra. The morphism attached to `y` is the descent of the orbit map `x ↦ x • y`,
which is right `P`-invariant because `y` is fixed by `P`. Here `y` need not lift to an `R`-point
of `G`. When it does, `y = gQ`, the point is fixed exactly when `g⁻¹Pg ⊆ Q`, and the morphism is
`xP ↦ xgQ`, `CommHopfAlgCat.fppfHomogeneousQuotientRightMul`. Over an algebraically closed field
every rational point of `G/Q` lifts, so every `G`-equivariant morphism `G/P ⟶ G/Q` is of this
form, for a `g` unique up to right multiplication by `Q(k)`.

The fixed-point condition is scheme-theoretic: it quantifies over points with values in every
algebra, and no finiteness, smoothness or reducedness hypothesis is imposed.

## Main declarations

* `CommHopfAlgCat.IsFppfHomogeneousQuotientEquivariant`: `G`-equivariance of `G/P ⟶ G/Q`.
* `CommHopfAlgCat.fppfHomogeneousQuotientFixedPoints`: the `R`-points of `G/Q` fixed by `P`.
* `CommHopfAlgCat.fppfHomogeneousQuotientEquivariantEquiv`: evaluation at the base point is a
  bijection from equivariant morphisms to fixed points.
* `CommHopfAlgCat.projection_mem_fppfHomogeneousQuotientFixedPoints_iff`: `gQ` is fixed by `P`
  exactly when `g⁻¹Pg ⊆ Q`.
* `CommHopfAlgCat.isFppfHomogeneousQuotientEquivariant_of_app_projection_mul`: a morphism is
  equivariant as soon as it commutes with left multiplication on cosets.
* `CommHopfAlgCat.isFppfHomogeneousQuotientEquivariant_map`,
  `CommHopfAlgCat.isFppfHomogeneousQuotientEquivariant_rightMul`: the projections `G/P ⟶ G/Q`
  and the morphisms `xP ↦ xgQ` are equivariant.
* `CommHopfAlgCat.isFppfHomogeneousQuotientEquivariant_iff_exists_eq_rightMul`: over an
  algebraically closed field, the equivariant morphisms are the morphisms `xP ↦ xgQ` with
  `g⁻¹Pg ⊆ Q`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 (the quotient universal property).
-/

public section

open CategoryTheory Opposite Limits

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{u} R} {I J : HopfIdeal R H}

/-- A morphism `G/P ⟶ G/Q` of fppf homogeneous quotients is `G`-equivariant when it commutes with
the left action of points of `G` with values in every algebra. -/
def IsFppfHomogeneousQuotientEquivariant
    (f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J) : Prop :=
  ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
    (z : (fppfHomogeneousQuotient H I).obj.obj A), f.hom.app A (x • z) = x • f.hom.app A z

variable (H I J) in
/-- The `R`-points of `G/Q` fixed by the closed subgroup `P` cut out by `I`: the points `y` with
`p • y = y` for every point `p` of `P` with values in any algebra `A`, where `y` is extended to
`A` along its structure map. -/
def fppfHomogeneousQuotientFixedPoints :
    Set ((fppfHomogeneousQuotient H J).obj.obj (op (op (CommAlgCat.of R R)))) :=
  {y | ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (p : HopfAlgebra.points (R := R) (H := H) A.unop.unop),
    p ∈ quotientPointsSubgroup H I A.unop.unop →
      p • (fppfHomogeneousQuotient H J).obj.map
          (CommAlgCat.isInitialSelf.op.op.to A) y =
        (fppfHomogeneousQuotient H J).obj.map
          (CommAlgCat.isInitialSelf.op.op.to A) y}

/-- Membership in the fixed points, unfolded. -/
theorem mem_fppfHomogeneousQuotientFixedPoints_iff
    (y : (fppfHomogeneousQuotient H J).obj.obj (op (op (CommAlgCat.of R R)))) :
    y ∈ fppfHomogeneousQuotientFixedPoints H I J ↔
      ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (p : HopfAlgebra.points (R := R) (H := H) A.unop.unop),
        p ∈ quotientPointsSubgroup H I A.unop.unop →
          p • (fppfHomogeneousQuotient H J).obj.map (CommAlgCat.isInitialSelf.op.op.to A) y =
            (fppfHomogeneousQuotient H J).obj.map (CommAlgCat.isInitialSelf.op.op.to A) y :=
  Iff.rfl

/-- **Equivariance from cosets.** A morphism `G/P ⟶ G/Q` is equivariant as soon as it commutes
with left multiplication on the images of points of `G`. -/
theorem isFppfHomogeneousQuotientEquivariant_of_app_projection_mul
    {f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J}
    (hf : ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (x g : HopfAlgebra.points (R := R) (H := H) A.unop.unop),
      f.hom.app A ((fppfHomogeneousQuotientProjection H I).app A (ULift.up (x * g))) =
        x • f.hom.app A ((fppfHomogeneousQuotientProjection H I).app A (ULift.up g))) :
    IsFppfHomogeneousQuotientEquivariant f := by
  intro A x z
  refine eq_of_forall_fppfHomogeneousQuotient_map_eq_projection H I
    (fppfHomogeneousQuotient H J) z fun B b g hg ↦ ?_
  rw [← NatTrans.naturality_apply, map_smul_fppfHomogeneousQuotient, hg,
    smul_fppfHomogeneousQuotientProjection_app, hf, map_smul_fppfHomogeneousQuotient,
    ← NatTrans.naturality_apply, hg]

variable (H) in
/-- **The projections are equivariant.** For closed subgroups `P ⊆ Q`, the projection
`G/P ⟶ G/Q` commutes with the action of `G`. -/
theorem isFppfHomogeneousQuotientEquivariant_map (hJI : J ≤ I) :
    IsFppfHomogeneousQuotientEquivariant (fppfHomogeneousQuotientMap H hJI) :=
  isFppfHomogeneousQuotientEquivariant_of_app_projection_mul fun A x g ↦ by
    have hπ (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :=
      congrArg (fun α ↦ α.app A (ULift.up g)) (fppfHomogeneousQuotientProjection_comp_map H hJI)
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hπ
    rw [hπ, hπ, smul_fppfHomogeneousQuotientProjection_app]

/-- An equivariant morphism sends the image of `x` to `x` acting on the image of the base point
`eP`, extended to the value algebra of `x`. -/
theorem IsFppfHomogeneousQuotientEquivariant.app_projection
    {f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J}
    (hf : IsFppfHomogeneousQuotientEquivariant f) (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    f.hom.app A ((fppfHomogeneousQuotientProjection H I).app A (ULift.up x)) =
      x • (fppfHomogeneousQuotient H J).obj.map
        (CommAlgCat.isInitialSelf.op.op.to A)
        (f.hom.app (op (op (CommAlgCat.of R R)))
          ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of R R)))
            (ULift.up (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))))) := by
  rw [← NatTrans.naturality_apply, fppfHomogeneousQuotient_map_projection_app_of_base, map_one,
    ← hf, smul_fppfHomogeneousQuotientProjection_app, mul_one]

/-- The base point of an equivariant morphism is fixed by `P`. -/
theorem IsFppfHomogeneousQuotientEquivariant.app_projection_one_mem
    {f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J}
    (hf : IsFppfHomogeneousQuotientEquivariant f) :
    f.hom.app (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of R R)))
          (ULift.up (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)))) ∈
      fppfHomogeneousQuotientFixedPoints H I J := by
  refine (mem_fppfHomogeneousQuotientFixedPoints_iff _).mpr fun A p hp ↦ ?_
  have h₁ := hf.app_projection A 1
  rw [one_smul] at h₁
  rw [← hf.app_projection, ← h₁,
    (fppfHomogeneousQuotientProjection_app_eq_iff H I A p 1).mpr (by simpa using hp)]

/-- The orbit map `x ↦ x • y` of an `R`-point `y` of `G/Q`, with `y` extended to the value
algebra of `x`. -/
private def orbitMap (y : (fppfHomogeneousQuotient H J).obj.obj (op (op (CommAlgCat.of R R)))) :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ (fppfHomogeneousQuotient H J).obj where
  app A := ↾fun x ↦ HSMul.hSMul (α := HopfAlgebra.points (R := R) (H := H) A.unop.unop) x.down
    ((fppfHomogeneousQuotient H J).obj.map (CommAlgCat.isInitialSelf.op.op.to A) y)
  naturality {A B} f := by
    ext ⟨x⟩
    -- Both sides act by the image of `x` on `y` extended to `B`.
    refine Eq.trans ?_ (map_smul_fppfHomogeneousQuotient H J f x _).symm
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, IsInitial.to_comp]
    -- The left side is the orbit map at `B`, applied to the image of `x`.
    rfl

private theorem orbitMap_app
    (y : (fppfHomogeneousQuotient H J).obj.obj (op (op (CommAlgCat.of R R))))
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (orbitMap y).app A (ULift.up x) =
      x • (fppfHomogeneousQuotient H J).obj.map (CommAlgCat.isInitialSelf.op.op.to A) y :=
  (rfl)

/-- The orbit map of a point fixed by `P` descends to `G/P`. -/
private def fixedPointHom (y : fppfHomogeneousQuotientFixedPoints H I J) :
    fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J :=
  (fppfHomogeneousQuotientHomEquiv H I _).symm ⟨orbitMap y.1, fun A g n ↦ by
    rw [orbitMap_app, orbitMap_app, mul_smul,
      (mem_fppfHomogeneousQuotientFixedPoints_iff _).mp y.2 A n.1 n.2]⟩

private theorem fixedPointHom_app_projection (y : fppfHomogeneousQuotientFixedPoints H I J)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (fixedPointHom y).hom.app A ((fppfHomogeneousQuotientProjection H I).app A (ULift.up x)) =
      x • (fppfHomogeneousQuotient H J).obj.map (CommAlgCat.isInitialSelf.op.op.to A) y.1 := by
  rw [← orbitMap_app, ← fppfHomogeneousQuotientHomEquiv_symm_apply H I _ (orbitMap y.1)]
  -- The component of a composite applies the two components in turn.
  rfl

private theorem isFppfHomogeneousQuotientEquivariant_fixedPointHom
    (y : fppfHomogeneousQuotientFixedPoints H I J) :
    IsFppfHomogeneousQuotientEquivariant (fixedPointHom y) :=
  isFppfHomogeneousQuotientEquivariant_of_app_projection_mul fun A x g ↦ by
    rw [fixedPointHom_app_projection, fixedPointHom_app_projection, mul_smul]

variable (I J) in
/-- **Evaluation at the base point.** The `G`-equivariant morphisms `G/P ⟶ G/Q` correspond to the
`R`-points of `G/Q` fixed by `P`, by evaluating at the base point `eP`. The inverse sends a fixed
point `y` to the morphism `xP ↦ x • y`. -/
def fppfHomogeneousQuotientEquivariantEquiv :
    {f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J //
        IsFppfHomogeneousQuotientEquivariant f} ≃
      fppfHomogeneousQuotientFixedPoints H I J where
  toFun f := ⟨_, f.2.app_projection_one_mem⟩
  invFun y := ⟨fixedPointHom y, isFppfHomogeneousQuotientEquivariant_fixedPointHom y⟩
  left_inv f := by
    refine Subtype.ext (fppfHomogeneousQuotient_hom_ext H I ?_)
    ext A ⟨x⟩
    exact (fixedPointHom_app_projection _ A x).trans (f.2.app_projection A x).symm
  right_inv y := by
    refine Subtype.ext ?_
    refine (fixedPointHom_app_projection y _ 1).trans ?_
    rw [IsInitial.to_self, CategoryTheory.Functor.map_id]
    exact one_smul (HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) y.1

/-- Evaluation at the base point applies the morphism to `eP`. -/
@[simp]
theorem fppfHomogeneousQuotientEquivariantEquiv_apply
    (f : {f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J //
      IsFppfHomogeneousQuotientEquivariant f}) :
    (fppfHomogeneousQuotientEquivariantEquiv I J f).1 =
      f.1.hom.app (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of R R)))
          (ULift.up (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)))) :=
  (rfl)

/-- The equivariant morphism attached to a fixed point `y` sends the image of `x` to `x • y`, with
`y` extended to the value algebra of `x`. -/
@[simp]
theorem fppfHomogeneousQuotientEquivariantEquiv_symm_app_projection
    (y : fppfHomogeneousQuotientFixedPoints H I J) (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% ((fppfHomogeneousQuotientEquivariantEquiv I J).symm y).1.hom.app A
        ((fppfHomogeneousQuotientProjection H I).app A (ULift.up x)) =
      x • (fppfHomogeneousQuotient H J).obj.map
        (CommAlgCat.isInitialSelf.op.op.to A) y.1 :=
  fixedPointHom_app_projection y A x

/-- **Uniqueness.** Two equivariant morphisms `G/P ⟶ G/Q` that agree at the base point `eP` are
equal. -/
theorem IsFppfHomogeneousQuotientEquivariant.ext
    {f₁ f₂ : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J}
    (hf₁ : IsFppfHomogeneousQuotientEquivariant f₁)
    (hf₂ : IsFppfHomogeneousQuotientEquivariant f₂)
    (h : f₁.hom.app (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of R R)))
          (ULift.up (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)))) =
      f₂.hom.app (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of R R)))
          (ULift.up (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))))) :
    f₁ = f₂ := by
  have h' : fppfHomogeneousQuotientEquivariantEquiv I J ⟨f₁, hf₁⟩ =
      fppfHomogeneousQuotientEquivariantEquiv I J ⟨f₂, hf₂⟩ :=
    Subtype.ext h
  exact congrArg Subtype.val ((fppfHomogeneousQuotientEquivariantEquiv I J).injective h')

variable (H) in
/-- **Fixed cosets.** The image `gQ` of an `R`-point `g` of `G` is fixed by `P` exactly when
`g⁻¹Pg ⊆ Q`, that is, when `P` lies in the conjugate cut out by `J.conjugate g`. -/
theorem projection_mem_fppfHomogeneousQuotientFixedPoints_iff
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientProjection H J).app (op (op (CommAlgCat.of R R))) (ULift.up g) ∈
        fppfHomogeneousQuotientFixedPoints H I J ↔
      J.conjugate g ≤ I := by
  rw [conjugate_le_iff_forall_fppfHomogeneousQuotientProjection_app_mul_eq]
  refine forall₂_congr fun A p ↦ imp_congr_right fun _ ↦ ?_
  rw [fppfHomogeneousQuotient_map_projection_app_of_base,
    smul_fppfHomogeneousQuotientProjection_app]

variable (H) in
/-- The morphism `xP ↦ xgQ` is `G`-equivariant. -/
theorem isFppfHomogeneousQuotientEquivariant_rightMul
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (h : J.conjugate g ≤ I) :
    IsFppfHomogeneousQuotientEquivariant (fppfHomogeneousQuotientRightMul H g h) :=
  isFppfHomogeneousQuotientEquivariant_of_app_projection_mul fun A x g' ↦ by
    rw [fppfHomogeneousQuotientRightMul_app_projection,
      fppfHomogeneousQuotientRightMul_app_projection, smul_fppfHomogeneousQuotientProjection_app,
      mul_assoc]

/-- **Equivariant morphisms over an algebraically closed field.** Over an algebraically closed
field `k`, the `G`-equivariant morphisms `G/P ⟶ G/Q` are exactly the morphisms `xP ↦ xgQ` for the
`k`-points `g` of `G` with `g⁻¹Pg ⊆ Q`. By
`fppfHomogeneousQuotientRightMul_eq_fppfHomogeneousQuotientRightMul_iff` the coset `gQ(k)` is
determined by the morphism. -/
theorem isFppfHomogeneousQuotientEquivariant_iff_exists_eq_rightMul {k : Type u} [Field k]
    [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k} {I J : HopfIdeal k H}
    {f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J} :
    IsFppfHomogeneousQuotientEquivariant f ↔
      ∃ (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) (h : J.conjugate g ≤ I),
        f = fppfHomogeneousQuotientRightMul H g h := by
  refine ⟨fun hf ↦ ?_, fun ⟨g, h, hfg⟩ ↦ hfg ▸ isFppfHomogeneousQuotientEquivariant_rightMul H g h⟩
  -- The base point of `f` is a rational point of `G/Q`, hence a coset `gQ`.
  obtain ⟨⟨g⟩, hg⟩ := fppfHomogeneousQuotientProjection_app_surjective H J
    (f.hom.app (op (op (CommAlgCat.of k k)))
      ((fppfHomogeneousQuotientProjection H I).app (op (op (CommAlgCat.of k k)))
        (ULift.up (1 : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)))))
  have h : J.conjugate g ≤ I :=
    (projection_mem_fppfHomogeneousQuotientFixedPoints_iff H g).mp
      (hg ▸ hf.app_projection_one_mem)
  exact ⟨g, h, hf.ext (isFppfHomogeneousQuotientEquivariant_rightMul H g h)
    (hg.symm.trans (fppfHomogeneousQuotientRightMul_app_projection_one H g h).symm)⟩

end

end CommHopfAlgCat
