/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Presheaf

/-!
# Pointwise quotients by scheme-theoretic kernels

For a morphism `f : H ⟶ K` of commutative Hopf algebras, the induced affine-group
morphism goes in the opposite direction, from the group represented by `K` to the group
represented by `H`. Its scheme-theoretic kernel is cut out by `kernelHopfIdeal f`.

This file proves the pointwise first-isomorphism comparison. The kernel Hopf ideal is normal,
so the pointwise quotient by it is defined. Precomposition with `f` then descends to a natural
map

```text
K(A) / ker(f)(A) ⟶ H(A),
```

and this map is injective for every value algebra `A`. It is an isomorphism whenever the map
on `A`-points is surjective. Thus the pointwise quotient identifies naturally with the image
of the represented morphism; the remaining representability step in the fppf first
isomorphism theorem is to prove local, rather than pointwise, surjectivity under the usual
flatness hypotheses.

## Main declarations

* `TauCeti.CommHopfAlgCat.isNormal_kernelHopfIdeal`: every scheme-theoretic kernel is normal.
* `TauCeti.CommHopfAlgCat.kernelPointwiseQuotientMap`: the comparison from the pointwise
  quotient by the kernel to the target points.
* `TauCeti.CommHopfAlgCat.kernelPointwiseQuotientNatTrans`: these comparisons, bundled as a
  natural transformation.
* `TauCeti.CommHopfAlgCat.kernelPointwiseQuotientMap_injective`: the comparison is
  pointwise injective.
* `TauCeti.CommHopfAlgCat.kernelPointwiseQuotientIso`: under pointwise surjectivity, the
  comparison is an isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 14--15.

-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R]
variable {H K : _root_.CommHopfAlgCat.{v} R}

private theorem quotientPointsSubgroup_le_mapPointsFunctor_ker (f : H ⟶ K)
    (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup K (kernelHopfIdeal f) A ≤ ((mapPointsFunctor f).app A).hom.ker := by
  intro g hg
  -- Membership in the kernel uses the underlying monoid hom, while `g` is a point in the
  -- subgroup carrier; expose the definitionally equal functor-of-points types for rewriting.
  exact show (mapPointsFunctor f).app A
      (show (HopfAlgebra.pointsFunctor (R := R) (H := K)).obj A from g) = 1 from by
    rw [mapPointsFunctor_app_apply]
    exact (mapPointsFunctor_app_eq_one_iff f A g).2 hg

/-- At a value algebra `A`, precomposition with `f` descends from source points to the quotient
by the scheme-theoretic kernel. -/
noncomputable def kernelPointwiseQuotientMap (f : H ⟶ K) (A : CommAlgCat.{w} R) :
    pointwiseQuotientGroup K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A ⟶
      HopfAlgebra.points (R := R) (H := H) A :=
  pointwiseQuotientLift K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A
    (HopfAlgebra.points (R := R) (H := H) A) ((mapPointsFunctor f).app A)
      (quotientPointsSubgroup_le_mapPointsFunctor_ker f A)

/-- The kernel-quotient comparison sends the class of a source point to its image under `f`. -/
@[simp]
theorem kernelPointwiseQuotientMap_mk (f : H ⟶ K) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := K) A) :
    kernelPointwiseQuotientMap f A
        (pointwiseQuotientMk K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A g) =
      (mapPointsFunctor f).app A g := by
  exact pointwiseQuotientLift_mk K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A
    (HopfAlgebra.points (R := R) (H := H) A) ((mapPointsFunctor f).app A) _ g

/-- The kernel-quotient comparisons are natural in the value algebra. -/
theorem mapPointwiseQuotient_comp_kernelPointwiseQuotientMap (f : H ⟶ K)
    {A B : CommAlgCat.{w} R} (χ : A ⟶ B) :
    mapPointwiseQuotient K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) χ ≫
        kernelPointwiseQuotientMap f B =
      kernelPointwiseQuotientMap f A ≫ HopfAlgebra.mapPoints (H := H) χ := by
  let _ : (quotientPointsSubgroup K (kernelHopfIdeal f) A).Normal :=
    quotientPointsSubgroup_normal K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A
  let _ : (quotientPointsSubgroup K (kernelHopfIdeal f) B).Normal :=
    quotientPointsSubgroup_normal K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) B
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro q
  obtain ⟨g, rfl⟩ := pointwiseQuotientMk_surjective K (kernelHopfIdeal f)
    (isNormal_kernelHopfIdeal f) A q
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, mapPointwiseQuotient_mk,
    kernelPointwiseQuotientMap_mk, kernelPointwiseQuotientMap_mk]
  exact congrArg (fun h ↦ h g) ((mapPointsFunctor f).naturality χ)

/-- The kernel-quotient comparisons, bundled as a natural transformation from the pointwise
quotient presheaf to the target functor of points. -/
noncomputable def kernelPointwiseQuotientNatTrans (f : H ⟶ K) :
    pointwiseQuotientFunctor K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A :=
    eqToHom (pointwiseQuotientFunctor_obj K (kernelHopfIdeal f)
      (isNormal_kernelHopfIdeal f) A) ≫ kernelPointwiseQuotientMap f A ≫
        eqToHom (HopfAlgebra.pointsFunctor_obj (H := H) A).symm
  naturality {A B} χ := by
    rw [pointwiseQuotientFunctor_map]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [HopfAlgebra.pointsFunctor_map_eqToHom]
    slice_lhs 2 3 => rw [mapPointwiseQuotient_comp_kernelPointwiseQuotientMap]
    simp only [Category.assoc]

/-- A component of the natural kernel-quotient comparison is the corresponding pointwise map. -/
@[simp]
theorem kernelPointwiseQuotientNatTrans_app (f : H ⟶ K) (A : CommAlgCat.{w} R) :
    (kernelPointwiseQuotientNatTrans f).app A =
      eqToHom (pointwiseQuotientFunctor_obj K (kernelHopfIdeal f)
        (isNormal_kernelHopfIdeal f) A) ≫ kernelPointwiseQuotientMap f A ≫
          eqToHom (HopfAlgebra.pointsFunctor_obj (H := H) A).symm := by
  rfl

/-- The natural kernel-quotient comparison factors the map on points through the pointwise
quotient projection. -/
@[reassoc]
theorem pointwiseQuotientProjection_comp_kernelPointwiseQuotientNatTrans (f : H ⟶ K) :
    pointwiseQuotientProjection K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) ≫
        kernelPointwiseQuotientNatTrans f =
      mapPointsFunctor f := by
  apply HopfAlgebra.pointsFunctor_hom_ext
  intro A g
  -- The source of the composite is presented by `pointsFunctor_obj`; expose its underlying
  -- point so that the component lemmas can rewrite the categorical wrappers explicitly.
  change ((pointwiseQuotientProjection K (kernelHopfIdeal f)
      (isNormal_kernelHopfIdeal f) ≫ kernelPointwiseQuotientNatTrans f).app A)
      (show (HopfAlgebra.pointsFunctor (R := R) (H := K)).obj A from g) = _
  rw [NatTrans.comp_app_apply, pointwiseQuotientProjection_app]
  -- `pointwiseQuotientFunctor_obj` presents the intermediate functor object as the concrete
  -- quotient group; this conversion exposes the two inverse `eqToHom` transports.
  change (kernelPointwiseQuotientNatTrans f).app A
      ((pointwiseQuotientMk K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A ≫
        eqToHom (pointwiseQuotientFunctor_obj K (kernelHopfIdeal f)
          (isNormal_kernelHopfIdeal f) A).symm)
            (show HopfAlgebra.points (R := R) (H := K) A from g)) = _
  rw [kernelPointwiseQuotientNatTrans_app]
  simp only [← ConcreteCategory.comp_apply]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [ConcreteCategory.comp_apply]
  rw [kernelPointwiseQuotientMap_mk]
  exact ConcreteCategory.congr_hom (eqToHom_refl _ _) ((mapPointsFunctor f).app A g)

/-- The comparison from the quotient by the scheme-theoretic kernel to target points is
injective over every value algebra. -/
theorem kernelPointwiseQuotientMap_injective (f : H ⟶ K) (A : CommAlgCat.{w} R) :
    Function.Injective (kernelPointwiseQuotientMap f A) := by
  let _ : (quotientPointsSubgroup K (kernelHopfIdeal f) A).Normal :=
    quotientPointsSubgroup_normal K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A
  have hker : quotientPointsSubgroup K (kernelHopfIdeal f) A =
      ((mapPointsFunctor f).app A).hom.ker := by
    ext g
    exact (mapPointsFunctor_app_eq_one_iff f A g).symm
  have hlift : (fun q ↦ kernelPointwiseQuotientMap f A q) =
      QuotientGroup.lift (quotientPointsSubgroup K (kernelHopfIdeal f) A)
        ((mapPointsFunctor f).app A).hom
          (quotientPointsSubgroup_le_mapPointsFunctor_ker f A) := by
    funext q
    obtain ⟨g, rfl⟩ := pointwiseQuotientMk_surjective K (kernelHopfIdeal f)
      (isNormal_kernelHopfIdeal f) A q
    rw [kernelPointwiseQuotientMap_mk, pointwiseQuotientMk_apply]
    -- `lift_mk'` uses the functor-object presentation of the source points, whereas `g` has
    -- the concrete `HopfAlgebra.points` type; no rewriting lemma connects these definitionally
    -- equal types, so expose that coercion at the argument of the lift.
    exact (QuotientGroup.lift_mk' (quotientPointsSubgroup K (kernelHopfIdeal f) A)
      (quotientPointsSubgroup_le_mapPointsFunctor_ker f A)
        (show (HopfAlgebra.pointsFunctor (R := R) (H := K)).obj A from g)).symm
  -- A `GrpCat` morphism and its underlying `QuotientGroup.lift` coerce to definitionally equal
  -- functions; there is no propositional equality to rewrite, so expose that common function.
  change Function.Injective (fun q ↦ kernelPointwiseQuotientMap f A q)
  rw [hlift]
  exact (QuotientGroup.injective_lift_iff
    (quotientPointsSubgroup K (kernelHopfIdeal f) A) ((mapPointsFunctor f).app A).hom
      (quotientPointsSubgroup_le_mapPointsFunctor_ker f A)).2 hker

/-- Every component of the natural kernel-quotient comparison is a monomorphism of groups. -/
instance kernelPointwiseQuotientMap_mono (f : H ⟶ K) (A : CommAlgCat.{w} R) :
    Mono (kernelPointwiseQuotientMap f A) :=
  ConcreteCategory.mono_of_injective _ (kernelPointwiseQuotientMap_injective f A)

/-- The natural kernel-quotient comparison is a monomorphism. -/
instance kernelPointwiseQuotientNatTrans_mono (f : H ⟶ K) :
    Mono (kernelPointwiseQuotientNatTrans f) := by
  have : ∀ A, Mono ((kernelPointwiseQuotientNatTrans f).app A) := by
    intro A
    rw [kernelPointwiseQuotientNatTrans_app]
    infer_instance
  exact NatTrans.mono_of_mono_app _

/-- The kernel-quotient comparison is surjective exactly when the original map on points is
surjective. -/
theorem kernelPointwiseQuotientMap_surjective_iff (f : H ⟶ K) (A : CommAlgCat.{w} R) :
    Function.Surjective (kernelPointwiseQuotientMap f A) ↔
      Function.Surjective ((mapPointsFunctor f).app A) := by
  let _ : (quotientPointsSubgroup K (kernelHopfIdeal f) A).Normal :=
    quotientPointsSubgroup_normal K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A
  have hcomp : kernelPointwiseQuotientMap f A ∘
      pointwiseQuotientMk K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A =
        (mapPointsFunctor f).app A := by
    funext g
    exact kernelPointwiseQuotientMap_mk f A g
  calc
    Function.Surjective (kernelPointwiseQuotientMap f A) ↔
        Function.Surjective (kernelPointwiseQuotientMap f A ∘
          pointwiseQuotientMk K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A) :=
      (Function.Surjective.of_comp_iff _ (pointwiseQuotientMk_surjective K
        (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A)).symm
    _ ↔ Function.Surjective ((mapPointsFunctor f).app A) := by
      rw [hcomp]
      rfl

/-- The kernel-quotient comparison is an isomorphism exactly when `f` is surjective on points
over the chosen value algebra. -/
theorem kernelPointwiseQuotientMap_isIso_iff (f : H ⟶ K) (A : CommAlgCat.{w} R) :
    IsIso (kernelPointwiseQuotientMap f A) ↔
      Function.Surjective ((mapPointsFunctor f).app A) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro hbijective
    exact (kernelPointwiseQuotientMap_surjective_iff f A).1 hbijective.2
  · intro hsurjective
    exact ⟨kernelPointwiseQuotientMap_injective f A,
      (kernelPointwiseQuotientMap_surjective_iff f A).2 hsurjective⟩

/-- A surjective map on `A`-points induces an isomorphism from the pointwise kernel quotient to
the target group of `A`-points. -/
theorem kernelPointwiseQuotientMap_isIso (f : H ⟶ K) (A : CommAlgCat.{w} R)
    (hsurj : Function.Surjective ((mapPointsFunctor f).app A)) :
    IsIso (kernelPointwiseQuotientMap f A) :=
  (kernelPointwiseQuotientMap_isIso_iff f A).2 hsurj

/-- **Pointwise first isomorphism theorem for affine groups.** If the morphism represented by
`f` is surjective on `A`-points, the target group of points is isomorphic to the pointwise
quotient of source points by the scheme-theoretic kernel. -/
noncomputable def kernelPointwiseQuotientIso (f : H ⟶ K) (A : CommAlgCat.{w} R)
    (hsurj : Function.Surjective ((mapPointsFunctor f).app A)) :
    pointwiseQuotientGroup K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) A ≅
      HopfAlgebra.points (R := R) (H := H) A := by
  let _ : IsIso (kernelPointwiseQuotientMap f A) :=
    kernelPointwiseQuotientMap_isIso f A hsurj
  exact asIso (kernelPointwiseQuotientMap f A)

/-- The forward map of the pointwise first-isomorphism equivalence is the canonical
kernel-quotient comparison. -/
@[simp]
theorem kernelPointwiseQuotientIso_hom (f : H ⟶ K)
    (A : CommAlgCat.{w} R) (hsurj : Function.Surjective ((mapPointsFunctor f).app A)) :
    (kernelPointwiseQuotientIso f A hsurj).hom = kernelPointwiseQuotientMap f A := by
  rfl

end TauCeti.CommHopfAlgCat
