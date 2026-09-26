/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Presheaf
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.FiniteStability

/-!
# The fppf first isomorphism theorem for affine groups

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over `R`. Contravariantly it
represents a homomorphism `Spec K ⟶ Spec H` of affine groups whose scheme-theoretic kernel is cut
out by `kernelHopfIdeal f`. The pointwise comparison `K(A) / ker(f)(A) ⟶ H(A)` is injective for
every value algebra `A`, but it is surjective only when `f` is surjective on `A`-points.

This file sheafifies that comparison. If the coordinate map `f` is faithfully flat and of finite
presentation, every `A`-point `y` of `Spec H` lifts to a point of `Spec K` after the fppf cover
`A ⟶ A ⊗[H] K`, so the comparison is locally surjective as well as injective. Its
sheafification is therefore an isomorphism

```text
Spec K / ker(f) ≅ Spec H
```

of group objects in fppf sheaves. In other words, a faithfully flat finitely presented
homomorphism of affine groups exhibits its target as the fppf quotient of its source by its
kernel, and that quotient is representable. Under this isomorphism the quotient projection is the
morphism of fppf points induced by `f`.

## Main declarations

* `TauCeti.CommHopfAlgCat.kernelFppfQuotientHom`: the comparison from the fppf quotient by the
  kernel to the fppf points of the target.
* `TauCeti.CommHopfAlgCat.fppfQuotientProjection_comp_kernelFppfQuotientHom`: the comparison
  carries the quotient projection to the morphism `pointsFppfGroupObjectMap f` induced by `f`.
* `TauCeti.CommHopfAlgCat.isIso_kernelFppfQuotientHom`: the comparison is an isomorphism when
  `f` is faithfully flat and of finite presentation.
* `TauCeti.CommHopfAlgCat.kernelFppfQuotientIso`: **the fppf first isomorphism theorem**.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 14--15.
-/

public section

open CategoryTheory Opposite WithConv
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]
variable {H K : _root_.CommHopfAlgCat.{u} R}

/-- The universe-lifted pointwise kernel-quotient comparison `K(A) / ker(f)(A) ⟶ H(A)`, as a
natural transformation of group-valued presheaves on the affine fppf site. -/
private noncomputable abbrev kernelPointwiseQuotientPresheafNatTrans (f : H ⟶ K) :
    pointwiseQuotientPresheaf K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) ⋙
        GrpCat.uliftFunctor.{u + 1, u} ⟶
      HopfAlgebra.pointsGroupPresheaf H ⋙ GrpCat.uliftFunctor.{u + 1, u} :=
  Functor.whiskerRight
    (Functor.whiskerLeft (unopUnop (CommAlgCat.{u} R)) (kernelPointwiseQuotientNatTrans f))
    GrpCat.uliftFunctor.{u + 1, u}

/-- The pointwise kernel-quotient comparison as a morphism of group objects in type-valued
presheaves, with source presented as `pointwiseQuotientPresheafGrp`. -/
private noncomputable def kernelPointwiseQuotientPresheafGrpHom (f : H ⟶ K) :
    pointwiseQuotientPresheafGrp K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) ⟶
      pointsPresheafGrp H :=
  eqToHom (pointwiseQuotientPresheafGrp_def K _ _) ≫
    groupFunctorGrpMap (kernelPointwiseQuotientPresheafNatTrans f)

/-- The comparison from the fppf quotient of `Spec K` by the kernel of `f` to the fppf points of
`Spec H`, obtained by sheafifying the pointwise kernel-quotient comparison. -/
noncomputable def kernelFppfQuotientHom (f : H ⟶ K) :
    fppfQuotientSheaf K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) ⟶
      pointsFppfGroupObject H := by
  let F := presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
  let _ : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts F
  exact eqToHom (fppfQuotientSheaf_def K _ _) ≫
    F.mapGrp.map (kernelPointwiseQuotientPresheafGrpHom f)

private theorem pointwiseQuotientPresheafGrpProjection_comp_kernelPointwiseQuotientPresheafGrpHom
    (f : H ⟶ K) :
    pointwiseQuotientPresheafGrpProjection K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) ≫
        kernelPointwiseQuotientPresheafGrpHom f =
      pointsPresheafGrpMap f := by
  have hnat : Functor.whiskerRight (pointwiseQuotientPresheafProjection K (kernelHopfIdeal f)
        (isNormal_kernelHopfIdeal f)) GrpCat.uliftFunctor.{u + 1, u} ≫
      kernelPointwiseQuotientPresheafNatTrans f =
      Functor.whiskerRight (Functor.whiskerLeft (unopUnop (CommAlgCat.{u} R))
        (mapPointsFunctor f)) GrpCat.uliftFunctor.{u + 1, u} := by
    rw [← Functor.whiskerRight_comp, ← Functor.whiskerLeft_comp,
      pointwiseQuotientProjection_comp_kernelPointwiseQuotientNatTrans]
  -- The presentations of the presheaf group objects agree only up to unfolding, so the
  -- associativity and rewriting steps are chained as equalities rather than by `rw`.
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ groupFunctorGrpMap (kernelPointwiseQuotientPresheafNatTrans f))
    (pointwiseQuotientPresheafGrpProjection_comp_eqToHom K _ _)).trans ?_
  refine Eq.trans ?_ (congrArg groupFunctorGrpMap hnat)
  -- Composition of the group-object maps attached to natural transformations is computed
  -- componentwise, where it is composition of functions.
  rfl

/-- The fppf kernel-quotient comparison carries the quotient projection `Spec K ⟶ Spec K / ker f`
to the morphism of fppf points induced by `f`. -/
@[reassoc (attr := simp)]
theorem fppfQuotientProjection_comp_kernelFppfQuotientHom (f : H ⟶ K) :
    fppfQuotientProjection K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) ≫
        kernelFppfQuotientHom f =
      pointsFppfGroupObjectMap f := by
  let F := presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
  let _ : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts F
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ F.mapGrp.map (kernelPointwiseQuotientPresheafGrpHom f))
    (fppfQuotientProjection_comp_eqToHom K _ _)).trans ?_
  refine (F.mapGrp.map_comp _ _).symm.trans ?_
  exact congrArg F.mapGrp.map
    (pointwiseQuotientPresheafGrpProjection_comp_kernelPointwiseQuotientPresheafGrpHom f)

/-- Over the faithfully flat, finitely presented base change `A ⟶ A ⊗[H] K`, every `A`-point of
`Spec H` lifts to a point of `Spec K`. -/
private theorem exists_faithfullyFlat_lift (f : H ⟶ K)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hfp : f.hom.toAlgHom.toRingHom.FinitePresentation)
    {A : CommAlgCat.{u} R} (y : H →ₐ[R] A) :
    ∃ (B : CommAlgCat.{u} R) (φ : A ⟶ B) (z : K →ₐ[R] B),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.toRingHom.FinitePresentation ∧
        z.comp f.hom.toAlgHom = φ.hom.comp y := by
  let _ : Algebra H A := y.toRingHom.toAlgebra
  let _ : Algebra H K := f.hom.toAlgHom.toRingHom.toAlgebra
  have : Module.FaithfullyFlat H K := hflat
  have : Algebra.FinitePresentation H K := hfp
  let _ : Algebra R (A ⊗[H] K) :=
    ((algebraMap A (A ⊗[H] K)).comp (algebraMap R A)).toAlgebra
  -- The pushout square `H ⟶ A ⟶ A ⊗[H] K ⟵ K ⟵ H`, evaluated at `h`.
  have hsq (h : H) : (1 : A) ⊗ₜ[H] f.hom.toAlgHom h = y h ⊗ₜ[H] (1 : K) :=
    (RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := H) (A := A) (B := K)) h).symm
  let φ : A →ₐ[R] A ⊗[H] K :=
    { Algebra.TensorProduct.includeLeftRingHom with commutes' := fun _ ↦ rfl }
  let z : K →ₐ[R] A ⊗[H] K :=
    { Algebra.TensorProduct.includeRight.toRingHom with
      commutes' := fun r ↦ by
        -- Unfold `includeRight` and the `R`-algebra structure on `A ⊗[H] K`, which was defined
        -- through `includeLeft`, to their values on pure tensors.
        change (1 : A) ⊗ₜ[H] algebraMap R K r = algebraMap R A r ⊗ₜ[H] (1 : K)
        rw [← f.hom.toAlgHom.commutes r, hsq, AlgHom.commutes] }
  refine ⟨CommAlgCat.of R (A ⊗[H] K), CommAlgCat.ofHom φ, z, ?_, ?_, ?_⟩
  · exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  · exact RingHom.finitePresentation_algebraMap.2 inferInstance
  · exact AlgHom.ext hsq

/-- If `f` is faithfully flat and of finite presentation, the comparison from the fppf quotient
of `Spec K` by the kernel of `f` to the fppf points of `Spec H` is an isomorphism of group objects
in fppf sheaves. -/
theorem isIso_kernelFppfQuotientHom (f : H ⟶ K)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hfp : f.hom.toAlgHom.toRingHom.FinitePresentation) :
    IsIso (kernelFppfQuotientHom f) := by
  let J := CommAlgCat.fppfTopology R
  let F := presheafToSheaf J (Type (u + 1))
  let _ : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts F
  let β := Functor.whiskerRight (kernelPointwiseQuotientPresheafNatTrans f) (forget GrpCat.{u + 1})
  have hinjB (B : CommAlgCat.{u} R) :
      Function.Injective ((kernelPointwiseQuotientNatTrans f).app B) := by
    have : Mono ((kernelPointwiseQuotientNatTrans f).app B) := by
      rw [kernelPointwiseQuotientNatTrans_app]
      infer_instance
    exact (GrpCat.mono_iff_injective _).1 this
  have hinj : Presheaf.IsLocallyInjective J β :=
    Presheaf.isLocallyInjective_of_injective J β fun A x y hxy ↦
      ULift.ext _ _ (hinjB _ (congrArg ULift.down hxy))
  have hsurj : Presheaf.IsLocallySurjective J β := by
    constructor
    intro U s
    obtain ⟨B, φ, z, hφflat, hφfp, hz⟩ := exists_faithfullyFlat_lift f hflat hfp s.down.ofConv
    refine J.superset_covering ?_
      (CommAlgCat.generate_singleton_op_mem_fppfTopology φ hφflat hφfp)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    let zB : (HopfAlgebra.pointsFunctor (R := R) (H := K)).obj B := toConv z
    refine ⟨ULift.up ((pointwiseQuotientProjection K (kernelHopfIdeal f)
      (isNormal_kernelHopfIdeal f)).app B zB), ULift.ext _ _ ?_⟩
    have key := congrArg (fun α ↦ α.app B zB)
      (pointwiseQuotientProjection_comp_kernelPointwiseQuotientNatTrans f)
    refine key.trans ?_
    rw [mapPointsFunctor_app_apply, ofConv_toConv, hz]
    rfl
  have hβ : IsIso (F.map β) :=
    (J.W_iff β).1 (J.W_of_isLocallyBijective β)
  have hG : IsIso (F.mapGrp.map (groupFunctorGrpMap (kernelPointwiseQuotientPresheafNatTrans f))) :=
    -- The underlying morphism of the group-object map is the sheafified presheaf map `F.map β`.
    let g := F.mapGrp.map (groupFunctorGrpMap (kernelPointwiseQuotientPresheafNatTrans f))
    have : IsIso ((Mon.forget (Sheaf J (Type (u + 1)))).map
        ((Grp.forget₂Mon (Sheaf J (Type (u + 1)))).map g)) := hβ
    have := isIso_of_reflects_iso ((Grp.forget₂Mon (Sheaf J (Type (u + 1)))).map g)
      (Mon.forget (Sheaf J (Type (u + 1))))
    isIso_of_reflects_iso g (Grp.forget₂Mon (Sheaf J (Type (u + 1))))
  have e : F.mapGrp.map (kernelPointwiseQuotientPresheafGrpHom f) =
      F.mapGrp.map (eqToHom (pointwiseQuotientPresheafGrp_def K _ _)) ≫
        F.mapGrp.map (groupFunctorGrpMap (kernelPointwiseQuotientPresheafNatTrans f)) :=
    F.mapGrp.map_comp _ _
  have : IsIso (F.mapGrp.map (kernelPointwiseQuotientPresheafGrpHom f)) :=
    e ▸ IsIso.comp_isIso' inferInstance hG
  have : IsIso (eqToHom (fppfQuotientSheaf_def K _ _) ≫
      F.mapGrp.map (kernelPointwiseQuotientPresheafGrpHom f)) := inferInstance
  exact this

/-- **The fppf first isomorphism theorem for affine groups.** If `f : H ⟶ K` is faithfully flat
and of finite presentation, then the fppf quotient of `Spec K` by the kernel of the represented
homomorphism `Spec K ⟶ Spec H` is represented by `Spec H`. -/
noncomputable def kernelFppfQuotientIso (f : H ⟶ K)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hfp : f.hom.toAlgHom.toRingHom.FinitePresentation) :
    fppfQuotientSheaf K (kernelHopfIdeal f) (isNormal_kernelHopfIdeal f) ≅
      pointsFppfGroupObject H :=
  have := isIso_kernelFppfQuotientHom f hflat hfp
  asIso (kernelFppfQuotientHom f)

/-- The forward map of the fppf first isomorphism is the kernel-quotient comparison. -/
@[simp]
theorem kernelFppfQuotientIso_hom (f : H ⟶ K)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hfp : f.hom.toAlgHom.toRingHom.FinitePresentation) :
    (kernelFppfQuotientIso f hflat hfp).hom = kernelFppfQuotientHom f :=
  (rfl)

end TauCeti.CommHopfAlgCat
