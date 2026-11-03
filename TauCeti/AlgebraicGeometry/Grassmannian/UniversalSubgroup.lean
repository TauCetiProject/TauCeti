/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
public import TauCeti.AlgebraicGeometry.Grassmannian.FiniteLocallyFree
public import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# The universal subgroup over the Hopf-ideal locus

Let `H` be a commutative Hopf algebra over a commutative ring `R`, so that `Spec H` is an affine
group scheme over `Spec R`, and let `L ⊆ G(k, H)` be the closed subscheme of Hopf ideals of the
Grassmannian scheme (`Module.Grassmannian.schemeHopfIdealLocus`). The universal family
`Z ⟶ L` over it (`Module.Grassmannian.schemeHopfIdealLocusFamily`) is finite locally free of rank
`k`, and its fibre over a point `N` of `L` is `Spec ((A ⊗[R] H) ⧸ N)`. This file proves that `Z`
is a closed subgroup scheme of the base change `Spec H ×_{Spec R} L` of `Spec H` to `L`
(`Module.Grassmannian.schemeHopfIdealLocusGrp`): the universal subgroup
`Module.Grassmannian.universalSubgroup R H k`, finite locally free of rank `k` over `L`.

The proof applies the closed-subgroup criterion
`TauCeti.GroupScheme.grpObjOfClosedImmersion`: the ideal sheaf of `Z` must vanish on the identity,
on the multiplication of two points of `Z`, and on the inverse of a point of `Z`. Each condition
says that a morphism `f : T ⟶ Spec H ×_{Spec R} L` factors through `Z`. This is local on `T`
(`AlgebraicGeometry.Scheme.Hom.iInf_ker_openCover_map_comp`), so it suffices to treat the
restrictions of `f` to affine opens `Spec C ⟶ T`. There, `f` is a point `N` of the Hopf-ideal
locus over `C` together with a `C`-point `x` of `Spec H`, and it factors through `Z` exactly when
`N.evalIdeal x = ⊥` (`Module.Grassmannian.schemeUniversalIdeal_le_ker_toPullbackHom_iff`). On
points, the group law of the base change is that of `Spec H`
(`TauCeti.GroupScheme.baseChangePointMulEquiv`), which is the convolution product of algebra maps
(`AlgebraicGeometry.Spec.mapMulEquiv`). So the three conditions become the facts that the points
`x` with `N.evalIdeal x = ⊥` contain the identity and are stable under convolution and the antipode
(`Module.Grassmannian.evalIdeal_counit_eq_bot`, `Module.Grassmannian.evalIdeal_convMul_eq_bot` and
`Module.Grassmannian.evalIdeal_comp_antipode_eq_bot`). These hold because `N` is a Hopf ideal.

The scheme-level statements use Mathlib's `hopfSpec`, which requires the base ring and the Hopf
algebra to lie in the same universe. The construction is over the Grassmannian of `H` over an
affine base `Spec R`; compatibility of the universal subgroup with base change and the relative
version over a non-affine base are not treated here.

## Main definitions

* `Module.Grassmannian.schemeHopfIdealLocusGrp R H k`: the base change of the group scheme
  `Spec H` to the closed subscheme of Hopf ideals.
* `Module.Grassmannian.schemeHopfIdealLocusFamilyToGrp R H k`: the inclusion of the universal family
  over the Hopf-ideal locus into this base change, a closed immersion.
* `Module.Grassmannian.universalSubgroup R H k`: the universal family as a closed subgroup scheme
  of the base change, identified with the universal family by
  `Module.Grassmannian.universalSubgroupIso`.

## Main results

* `Module.Grassmannian.ker_schemeHopfIdealLocusFamilyToGrp_left_le_one`,
  `Module.Grassmannian.ker_schemeHopfIdealLocusFamilyToGrp_left_le_mul` and
  `Module.Grassmannian.ker_schemeHopfIdealLocusFamilyToGrp_left_le_inv`: the identity, the product
  of two points of the universal family and the inverse of a point of the universal family factor
  through the universal family.
* The resulting group structure on the universal family (an instance), for which
  `Module.Grassmannian.schemeHopfIdealLocusFamilyToGrp` is a homomorphism
  (`Module.Grassmannian.isMonHom_schemeHopfIdealLocusFamilyToGrp`).
* `Module.Grassmannian.isFinite_universalSubgroup`, `Module.Grassmannian.flat_universalSubgroup`,
  `Module.Grassmannian.locallyOfFinitePresentation_universalSubgroup` and
  `Module.Grassmannian.finrank_universalSubgroup`: the universal subgroup is finite locally free of
  constant rank `k` over the closed subscheme of Hopf ideals.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.1 and §1.3, for finite
  locally free subgroup schemes and the closed-subgroup criterion.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (Springer, 1979), §2.1, for closed
  subgroup schemes of affine group schemes as quotients by Hopf ideals.
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  the Grassmannian and its universal quotient.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite Scheme.IdealSheafData
  MonoidalCategory CartesianMonoidalCategory MonObj

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {H : Type u} [CommRing H] [HopfAlgebra R H] {k : ℕ}

variable (R H k) in
-- exposed so that its underlying scheme is the fibre product `Spec H ×_{Spec R} L`
/-- The base change `Spec H ×_{Spec R} L` of the affine group scheme `Spec H` to the closed
subscheme `L` of Hopf ideals of the Grassmannian scheme `G(k, H)`, as a group scheme over `L`. Its
underlying scheme is the fibre product of `Spec H ⟶ Spec R` and `L ⟶ Spec R`. -/
@[expose] noncomputable def schemeHopfIdealLocusGrp :
    Grp (Over (schemeHopfIdealLocus R H k).subscheme) :=
  (Over.pullback ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k)).mapGrp.obj
    ((hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R H)))

section Inclusion

variable (R H k) in
/-- The inclusion of the universal family over the Hopf-ideal locus into
`Spec H ×_{Spec R} L`: its second component is the projection to `L`, and its first component is
the projection of the universal quotient closed subscheme to `Spec H`. -/
private noncomputable def familyToPullback :
    schemeHopfIdealLocusFamily R H k ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) :=
  pullback.lift (schemeHopfIdealLocusFamilyι R H k ≫ (schemeUniversalIdeal R H k).subschemeι ≫
    pullback.snd _ _) (schemeHopfIdealLocusFamilyHom R H k) <| by
      rw [Category.assoc, Category.assoc, ← pullback.condition]
      exact (isPullback_schemeHopfIdealLocusFamily R H k).w_assoc _

@[reassoc]
private theorem familyToPullback_fst :
    familyToPullback R H k ≫ pullback.fst _ _ =
      schemeHopfIdealLocusFamilyι R H k ≫ (schemeUniversalIdeal R H k).subschemeι ≫
        pullback.snd _ _ :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem familyToPullback_snd :
    familyToPullback R H k ≫ pullback.snd _ _ = schemeHopfIdealLocusFamilyHom R H k :=
  pullback.lift_snd _ _ _

variable (R H k) in
/-- The base change of the inclusion `L ⟶ G(k, H)` along
`G(k, H) ×_{Spec R} Spec H ⟶ G(k, H)`, from `Spec H ×_{Spec R} L` to
`G(k, H) ×_{Spec R} Spec H`. -/
private noncomputable def pullbackToGrassmannian :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) ⟶
      pullback (toSpec R H k) (Spec.map (CommRingCat.ofHom (algebraMap R H))) :=
  pullback.lift (pullback.snd _ _ ≫ (schemeHopfIdealLocus R H k).subschemeι) (pullback.fst _ _)
    ((Category.assoc _ _ _).trans pullback.condition.symm)

@[reassoc]
private theorem pullbackToGrassmannian_fst :
    pullbackToGrassmannian R H k ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ (schemeHopfIdealLocus R H k).subschemeι :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem pullbackToGrassmannian_snd :
    pullbackToGrassmannian R H k ≫ pullback.snd _ _ = pullback.fst _ _ :=
  pullback.lift_snd _ _ _

private instance : IsClosedImmersion (pullbackToGrassmannian R H k) := by
  have h : IsPullback (pullbackToGrassmannian R H k) (pullback.snd _ _) (pullback.fst _ _)
      (schemeHopfIdealLocus R H k).subschemeι := by
    refine IsPullback.of_right ?_ pullbackToGrassmannian_fst (IsPullback.of_hasPullback _ _).flip
    rw [pullbackToGrassmannian_snd]
    exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback h.flip inferInstance

private theorem familyToPullback_pullbackToGrassmannian :
    familyToPullback R H k ≫ pullbackToGrassmannian R H k =
      schemeHopfIdealLocusFamilyι R H k ≫ (schemeUniversalIdeal R H k).subschemeι := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullbackToGrassmannian_fst, familyToPullback_snd_assoc, Category.assoc]
    exact (isPullback_schemeHopfIdealLocusFamily R H k).w.symm
  · rw [Category.assoc, pullbackToGrassmannian_snd, familyToPullback_fst, Category.assoc]

private instance isClosedImmersion_familyToPullback :
    IsClosedImmersion (familyToPullback R H k) := by
  have : IsClosedImmersion (familyToPullback R H k ≫ pullbackToGrassmannian R H k) := by
    rw [familyToPullback_pullbackToGrassmannian]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullbackToGrassmannian R H k)

variable (R H k) in
/-- The inclusion of the universal family over the Hopf-ideal locus into the base change
`Spec H ×_{Spec R} L` of `Spec H`, as a morphism over `L`. It is a closed immersion, and a
homomorphism for the group structure on the universal family
(`Module.Grassmannian.isMonHom_schemeHopfIdealLocusFamilyToGrp`). -/
noncomputable def schemeHopfIdealLocusFamilyToGrp :
    Over.mk (schemeHopfIdealLocusFamilyHom R H k) ⟶ (schemeHopfIdealLocusGrp R H k).X :=
  Over.homMk (familyToPullback R H k) familyToPullback_snd

private theorem schemeHopfIdealLocusFamilyToGrp_left_eq :
    (schemeHopfIdealLocusFamilyToGrp R H k).left = familyToPullback R H k :=
  Over.homMk_left _ _

/-- The component in `Spec H` of the inclusion of the universal family into
`Spec H ×_{Spec R} L` is the projection of the universal quotient closed subscheme to
`Spec H`. -/
@[simp, reassoc]
theorem schemeHopfIdealLocusFamilyToGrp_left_fst :
    (schemeHopfIdealLocusFamilyToGrp R H k).left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) =
      schemeHopfIdealLocusFamilyι R H k ≫ (schemeUniversalIdeal R H k).subschemeι ≫
        pullback.snd _ _ := by
  rw [schemeHopfIdealLocusFamilyToGrp_left_eq]
  exact familyToPullback_fst

/-- The component in `L` of the inclusion of the universal family into `Spec H ×_{Spec R} L` is
the projection of the universal family to `L`. -/
@[simp, reassoc]
theorem schemeHopfIdealLocusFamilyToGrp_left_snd :
    (schemeHopfIdealLocusFamilyToGrp R H k).left ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) =
      schemeHopfIdealLocusFamilyHom R H k := by
  rw [schemeHopfIdealLocusFamilyToGrp_left_eq]
  exact familyToPullback_snd

/-- The inclusion of the universal family into `Spec H ×_{Spec R} L` is a closed immersion. -/
instance isClosedImmersion_schemeHopfIdealLocusFamilyToGrp_left :
    IsClosedImmersion (schemeHopfIdealLocusFamilyToGrp R H k).left := by
  rw [schemeHopfIdealLocusFamilyToGrp_left_eq]
  exact isClosedImmersion_familyToPullback

end Inclusion

section Criterion

/-- A `C`-point of `Spec H ×_{Spec R} L`, given by a point `N` of the Grassmannian functor and a
`C`-point `x` of `Spec H`, lies in the universal family exactly when `N.evalIdeal x = ⊥`. -/
private theorem ker_familyToPullback_le_ker_iff {C : Type u} [CommRing C] [Algebra R C]
    (N : G(k, C ⊗[R] H; C)) (x : H →ₐ[R] C)
    (g : Spec (.of C) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k))
    (h₁ : g ≫ pullback.snd _ _ ≫ (schemeHopfIdealLocus R H k).subschemeι = toSchemeHom N)
    (h₂ : g ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (x : H →+* C))) :
    (familyToPullback R H k).ker ≤ g.ker ↔ N.evalIdeal x = ⊥ := by
  have hg : g ≫ pullbackToGrassmannian R H k = toPullbackHom N x :=
    pullback.hom_ext (by rw [Category.assoc, pullbackToGrassmannian_fst, h₁, toPullbackHom_fst])
      (by rw [Category.assoc, pullbackToGrassmannian_snd, h₂, toPullbackHom_snd])
  rw [← schemeUniversalIdeal_le_ker_toPullbackHom_iff, ← hg]
  constructor
  · intro h
    rw [← IsClosedImmersion.lift_fac (familyToPullback R H k) g h, Category.assoc,
      familyToPullback_pullbackToGrassmannian, ← Category.assoc]
    conv_lhs => rw [← ker_subschemeι (schemeUniversalIdeal R H k)]
    exact Scheme.Hom.le_ker_comp _ _
  · intro h
    rw [← ker_subschemeι (schemeUniversalIdeal R H k)] at h
    -- `g` factors through the universal quotient closed subscheme, hence through its base change
    -- to the closed subscheme of Hopf ideals
    let m := (isPullback_schemeHopfIdealLocusFamily R H k).lift (IsClosedImmersion.lift _ _ h)
      (g ≫ pullback.snd _ _) (by
        rw [IsClosedImmersion.lift_fac_assoc, Category.assoc, pullbackToGrassmannian_fst,
          Category.assoc])
    have hm : m ≫ familyToPullback R H k = g := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, familyToPullback_fst, IsPullback.lift_fst_assoc,
          IsClosedImmersion.lift_fac_assoc, Category.assoc, pullbackToGrassmannian_snd]
      · rw [Category.assoc, familyToPullback_snd, IsPullback.lift_snd]
    have := Scheme.Hom.le_ker_comp m (familyToPullback R H k)
    rwa [hm] at this

/-- The composite of a point of `Spec H ×_{Spec R} L` with `Spec H ⟶ Spec R` is that of its
projection to `L`. -/
private theorem fst_comp_specMap {T : Over (schemeHopfIdealLocus R H k).subscheme}
    (p : T ⟶ (schemeHopfIdealLocusGrp R H k).X) :
    (p.left ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R H)) =
    T.hom ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k := by
  have h {X : Scheme.{u}} (f : X ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k)) :
      (f ≫ pullback.fst _ _) ≫ Spec.map (CommRingCat.ofHom (algebraMap R H)) =
        (f ≫ pullback.snd _ _) ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  exact (h p.left).trans (congrArg (· ≫ _) (Over.w p))

/-- The product of two points of `Spec H ×_{Spec R} L` projects to the product in `Spec H` of
their projections. -/
private theorem mul_left_fst {T : Over (schemeHopfIdealLocus R H k).subscheme}
    (p q : T ⟶ (schemeHopfIdealLocusGrp R H k).X) :
    (p * q).left ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) =
      pullback.lift (p.left ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k))
        (q.left ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k))
        ((fst_comp_specMap p).trans (fst_comp_specMap q).symm) ≫
        μ[((hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R H))).X].left :=
  -- the structure morphism of `Spec H` over `Spec R` is `Spec` of the algebra map by definition
  TauCeti.GroupScheme.pullback_mapGrp_mul_left_fst _ _ _ p q

/-- The identity point of `Spec H ×_{Spec R} L` projects to the identity of `Spec H`. -/
private theorem one_left_fst {T : Over (schemeHopfIdealLocus R H k).subscheme} :
    (1 : T ⟶ (schemeHopfIdealLocusGrp R H k).X).left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) =
      T.hom ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H)) :=
  (TauCeti.GroupScheme.pullback_mapGrp_one_left_fst _ _ T).trans <| by
    simp only [Category.assoc]
    -- the identity of `hopfSpec` is `Spec` of the counit by definition
    rfl

/-- The inverse of a point of `Spec H ×_{Spec R} L` projects to the antipode of its projection
to `Spec H`. -/
private theorem inv_left_fst {T : Over (schemeHopfIdealLocus R H k).subscheme}
    (p : T ⟶ (schemeHopfIdealLocusGrp R H k).X) :
    p⁻¹.left ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) =
      p.left ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) ≫
        Spec.map (CommRingCat.ofHom (HopfAlgebra.antipodeAlgHom R H)) :=
  -- the inverse of `hopfSpec` is `Spec` of the antipode by definition
  TauCeti.GroupScheme.pullback_mapGrp_inv_left_fst _ _ T p

/-- A `C`-point of the universal family over the point `N` of the Hopf-ideal locus is a `C`-point
`y` of `Spec H` with `N.evalIdeal y = ⊥`. -/
private theorem exists_family_point {C : CommRingCat.{u}} [Algebra R C] (N : G(k, C ⊗[R] H; C))
    (hN : N.hopfIdealLocus = ⊥) (g : Spec C ⟶ schemeHopfIdealLocusFamily R H k)
    (hg : g ≫ schemeHopfIdealLocusFamilyHom R H k =
      (schemeHopfIdealLocusHomEquiv R H k C ⟨N, hN⟩).1) :
    ∃ y : H →ₐ[R] C, g ≫ familyToPullback R H k ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (y : H →+* C)) ∧ N.evalIdeal y = ⊥ := by
  have h₁ : (g ≫ familyToPullback R H k) ≫ pullback.snd _ _ ≫
      (schemeHopfIdealLocus R H k).subschemeι = toSchemeHom N := by
    rw [Category.assoc, familyToPullback_snd_assoc, reassoc_of% hg,
      schemeHopfIdealLocusHomEquiv_apply_comp_subschemeι]
  -- the ring map of the projection to `Spec H` is an `R`-algebra map, as `g` lies over `Spec R`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ familyToPullback R H k ≫ pullback.fst _ _)
  have hφR : CommRingCat.ofHom (algebraMap R H) ≫ φ = CommRingCat.ofHom (algebraMap R C) :=
    Spec.map_injective <| by
      rw [Spec.map_comp, hφ, Category.assoc, Category.assoc, pullback.condition,
        reassoc_of% h₁, toSchemeHom_toSpec]
  let y : H →ₐ[R] C := { φ.hom with commutes' := fun r ↦ congr(($hφR).hom r) }
  -- the underlying ring map of `y` is `φ`
  have hy : g ≫ familyToPullback R H k ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (y : H →+* C)) := hφ.symm
  refine ⟨y, hy, (ker_familyToPullback_le_ker_iff N y (g ≫ familyToPullback R H k) h₁ ?_).1
    (Scheme.Hom.le_ker_comp _ _)⟩
  rw [Category.assoc, hy]

/-- **Locality of the criterion.** A point `p` of `Spec H ×_{Spec R} L` with values in `T` lies in
the universal family as soon as, over every affine scheme `Spec C ⟶ T` lying over a point `N` of
the Hopf-ideal locus, its projection to `Spec H` is a point `x` with `N.evalIdeal x = ⊥`. -/
private theorem ker_familyToPullback_le_of_forall
    {T : Over (schemeHopfIdealLocus R H k).subscheme}
    (p : T ⟶ (schemeHopfIdealLocusGrp R H k).X) [QuasiCompact p.left]
    (h : ∀ (C : CommRingCat.{u}) [Algebra R C] (N : G(k, C ⊗[R] H; C))
      (hN : N.hopfIdealLocus = ⊥) (g : Spec C ⟶ T.left),
      g ≫ T.hom = (schemeHopfIdealLocusHomEquiv R H k C ⟨N, hN⟩).1 →
      ∃ x : H →ₐ[R] C, g ≫ p.left ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) =
        Spec.map (CommRingCat.ofHom (x : H →+* C)) ∧ N.evalIdeal x = ⊥) :
    (familyToPullback R H k).ker ≤ p.left.ker := by
  rw [← p.left.iInf_ker_openCover_map_comp T.left.affineCover]
  refine le_iInf fun j ↦ ?_
  suffices ∀ (C : CommRingCat.{u}) (g : Spec C ⟶ T.left),
      (familyToPullback R H k).ker ≤ (g ≫ p.left).ker from this _ _
  intro C g
  -- the point `N` of the Hopf-ideal locus over `C` through which `g` passes
  let _ : Algebra R C := (Spec.preimage
    (g ≫ T.hom ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k)).hom.toAlgebra
  have hgR : (g ≫ T.hom) ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [Category.assoc]
    exact (Spec.map_preimage _).symm
  let N := (schemeHopfIdealLocusHomEquiv R H k C).symm ⟨g ≫ T.hom, hgR⟩
  have hgN : (schemeHopfIdealLocusHomEquiv R H k C ⟨N.1, N.2⟩).1 = g ≫ T.hom := by
    rw [Subtype.coe_eta, Equiv.apply_symm_apply]
  obtain ⟨x, hx, hxN⟩ := h C N.1 N.2 g hgN.symm
  refine (ker_familyToPullback_le_ker_iff N.1 x (g ≫ p.left) ?_ ?_).2 hxN
  · -- `rw` cannot see through the type of `p.left`, so reassociate by unification
    refine (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) (Over.w_assoc p _)).trans ?_)
    rw [← Category.assoc, ← hgN, schemeHopfIdealLocusHomEquiv_apply_comp_subschemeι]
  · exact (Category.assoc _ _ _).trans hx

/-- A point of `Spec H ×_{Spec R} L` with values in a scheme quasi-compact over `L` is
quasi-compact, as `Spec H ×_{Spec R} L ⟶ L` is affine. -/
private theorem quasiCompact_left {T : Over (schemeHopfIdealLocus R H k).subscheme}
    (p : T ⟶ (schemeHopfIdealLocusGrp R H k).X) [QuasiCompact T.hom] : QuasiCompact p.left := by
  have hp : p.left ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) = T.hom := Over.w p
  have : QuasiCompact (p.left ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k)) := hp ▸ inferInstance
  have hs : QuasiSeparated (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k)) := inferInstance
  exact @QuasiCompact.of_comp _ _ _ p.left _ this hs

/-- The identity section of `Spec H ×_{Spec R} L` factors through the universal family. -/
theorem ker_schemeHopfIdealLocusFamilyToGrp_left_le_one :
    (schemeHopfIdealLocusFamilyToGrp R H k).left.ker ≤
      η[(schemeHopfIdealLocusGrp R H k).X].left.ker := by
  have h1 : η[(schemeHopfIdealLocusGrp R H k).X] =
      (1 : 𝟙_ (Over (schemeHopfIdealLocus R H k).subscheme) ⟶
        (schemeHopfIdealLocusGrp R H k).X) := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  rw [h1]
  have : QuasiCompact (𝟙_ (Over (schemeHopfIdealLocus R H k).subscheme)).hom := by
    rw [Over.tensorUnit_hom]
    exact inferInstanceAs (QuasiCompact (𝟙 _))
  have := quasiCompact_left (1 : 𝟙_ (Over (schemeHopfIdealLocus R H k).subscheme) ⟶
    (schemeHopfIdealLocusGrp R H k).X)
  rw [schemeHopfIdealLocusFamilyToGrp_left_eq]
  refine ker_familyToPullback_le_of_forall _ fun C _ N hN g hg ↦
    ⟨(Algebra.ofId R C).comp (Bialgebra.counitAlgHom R H), ?_, evalIdeal_counit_eq_bot N hN⟩
  refine (congrArg (g ≫ ·) one_left_fst).trans ?_
  -- the structure morphism of the unit object of `Over L` is the identity of `L`
  have hg₀ : g = (schemeHopfIdealLocusHomEquiv R H k C ⟨N, hN⟩).1 := by
    simpa [Over.tensorUnit_hom] using hg
  refine (congrArg (g ≫ ·) (Category.id_comp _)).trans ?_
  rw [hg₀, reassoc_of% (schemeHopfIdealLocusHomEquiv R H k C ⟨N, hN⟩).2, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, AlgHom.comp_toRingHom, Algebra.toRingHom_ofId]

/-- The inverse of the inclusion of the universal family factors through the universal family. -/
theorem ker_schemeHopfIdealLocusFamilyToGrp_left_le_inv :
    (schemeHopfIdealLocusFamilyToGrp R H k).left.ker ≤
      (schemeHopfIdealLocusFamilyToGrp R H k ≫ ι[(schemeHopfIdealLocusGrp R H k).X]).left.ker := by
  rw [← Hom.inv_def]
  have : QuasiCompact (Over.mk (schemeHopfIdealLocusFamilyHom R H k)).hom :=
    inferInstanceAs (QuasiCompact (schemeHopfIdealLocusFamilyHom R H k))
  have := quasiCompact_left (schemeHopfIdealLocusFamilyToGrp R H k)⁻¹
  rw [schemeHopfIdealLocusFamilyToGrp_left_eq]
  refine ker_familyToPullback_le_of_forall _ fun C _ N hN g hg ↦ ?_
  obtain ⟨y, hy, hyN⟩ := exists_family_point N hN g hg
  refine ⟨y.comp (HopfAlgebra.antipodeAlgHom R H), ?_, evalIdeal_comp_antipode_eq_bot N hN hyN⟩
  refine (congrArg (g ≫ ·) (inv_left_fst _)).trans ?_
  have := congrArg (· ≫ Spec.map (CommRingCat.ofHom (HopfAlgebra.antipodeAlgHom R H : H →+* H))) hy
  simp only [Category.assoc] at this
  refine this.trans ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_toRingHom]

/-- The product of the two projections of the square of the universal family factors through the
universal family. -/
theorem ker_schemeHopfIdealLocusFamilyToGrp_left_le_mul :
    (schemeHopfIdealLocusFamilyToGrp R H k).left.ker ≤ ((schemeHopfIdealLocusFamilyToGrp R H k ⊗ₘ
      schemeHopfIdealLocusFamilyToGrp R H k) ≫ μ[(schemeHopfIdealLocusGrp R H k).X]).left.ker := by
  rw [← lift_fst_comp_snd_comp, ← Hom.mul_def]
  have : QuasiCompact (Over.mk (schemeHopfIdealLocusFamilyHom R H k) ⊗
      Over.mk (schemeHopfIdealLocusFamilyHom R H k)).hom := by
    rw [Over.tensorObj_hom]
    exact inferInstanceAs (QuasiCompact (pullback.fst (schemeHopfIdealLocusFamilyHom R H k)
      (schemeHopfIdealLocusFamilyHom R H k) ≫ schemeHopfIdealLocusFamilyHom R H k))
  have := quasiCompact_left (fst _ _ ≫ schemeHopfIdealLocusFamilyToGrp R H k *
    snd _ _ ≫ schemeHopfIdealLocusFamilyToGrp R H k)
  rw [schemeHopfIdealLocusFamilyToGrp_left_eq]
  refine ker_familyToPullback_le_of_forall _ fun C _ N hN g hg ↦ ?_
  obtain ⟨y₁, hy₁, hN₁⟩ := exists_family_point N hN (g ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans hg)
  obtain ⟨y₂, hy₂, hN₂⟩ := exists_family_point N hN (g ≫ pullback.snd _ _)
    ((Category.assoc _ _ _).trans ((congrArg (g ≫ ·)
      (pullback.condition (f := schemeHopfIdealLocusFamilyHom R H k)
        (g := schemeHopfIdealLocusFamilyHom R H k)).symm).trans hg))
  refine ⟨_, ?_, evalIdeal_convMul_eq_bot N hN hN₁ hN₂⟩
  -- the product of two `C`-points of `Spec H` is the convolution product of their algebra maps
  have hw (y : H →ₐ[R] C) : Spec.map (CommRingCat.ofHom (y : H →+* C)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R H)) =
        Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  have h : pullback.lift (Spec.map (CommRingCat.ofHom (y₁ : H →+* C)))
      (Spec.map (CommRingCat.ofHom (y₂ : H →+* C))) ((hw y₁).trans (hw y₂).symm) ≫
        μ[((hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R H))).X].left =
      Spec.map (CommRingCat.ofHom
        ((WithConv.toConv y₁ * WithConv.toConv y₂).ofConv : H →+* C)) := by
    have hmul := congrArg Over.Hom.left (map_mul (Spec.mapMulEquiv (R := R) (S := H) (T := C))
      (WithConv.toConv y₁) (WithConv.toConv y₂))
    rw [Hom.mul_def, Over.comp_left, Over.lift_left] at hmul
    -- the underlying morphism of `Spec.mapMulEquiv f` is `Spec.map f` by definition, and the
    -- multiplication of `(Spec H).asOver (Spec R)` is that of `hopfSpec` by definition; the points
    -- cannot be rewritten inside `pullback.lift`, whose compatibility proof mentions them
    exact hmul.symm
  refine (congrArg (g ≫ ·) (mul_left_fst _ _)).trans
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)).trans h)
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    simp only [Over.comp_left, Over.fst_left, schemeHopfIdealLocusFamilyToGrp_left_eq]
    exact hy₁
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    simp only [Over.comp_left, Over.snd_left, schemeHopfIdealLocusFamilyToGrp_left_eq]
    exact hy₂

end Criterion

/-- The universal family over the Hopf-ideal locus is a group scheme over the closed subscheme of
Hopf ideals: the group law of `Spec H ×_{Spec R} L` restricts to it. -/
noncomputable instance : GrpObj (Over.mk (schemeHopfIdealLocusFamilyHom R H k)) :=
  TauCeti.GroupScheme.grpObjOfClosedImmersion (schemeHopfIdealLocusFamilyToGrp R H k)
    ker_schemeHopfIdealLocusFamilyToGrp_left_le_one ker_schemeHopfIdealLocusFamilyToGrp_left_le_mul
    ker_schemeHopfIdealLocusFamilyToGrp_left_le_inv

/-- The inclusion of the universal family into `Spec H ×_{Spec R} L` is a homomorphism of group
schemes over the closed subscheme of Hopf ideals. -/
instance isMonHom_schemeHopfIdealLocusFamilyToGrp :
    IsMonHom (schemeHopfIdealLocusFamilyToGrp R H k) :=
  TauCeti.GroupScheme.isMonHom_grpObjOfClosedImmersion _ _ _ _

private instance : IsClosedImmersion (Grp.homMk
    (A := Grp.mk (Over.mk (schemeHopfIdealLocusFamilyHom R H k)))
    (schemeHopfIdealLocusFamilyToGrp R H k)).hom.hom.left := by
  rw [Grp.homMk_hom_hom]
  infer_instance

variable (R H k) in
/-- **The universal subgroup over the Hopf-ideal locus.** The universal family over the closed
subscheme `L` of Hopf ideals of `G(k, H)`, as a closed subgroup scheme of the base change
`Spec H ×_{Spec R} L` of `Spec H` (`Module.Grassmannian.universalSubgroupIso`). Its fibre over a
point `N` of `L` is the subgroup scheme `Spec ((A ⊗[R] H) ⧸ N)`
(`Module.Grassmannian.isPullback_schemeHopfIdealLocusFamilyHom`), and it is finite locally free of
rank `k` over `L` (`Module.Grassmannian.finrank_universalSubgroup`). -/
noncomputable def universalSubgroup :
    TauCeti.ClosedSubgroupScheme (schemeHopfIdealLocusGrp R H k) :=
  TauCeti.ClosedSubgroupScheme.mk
    (Grp.homMk (A := Grp.mk (Over.mk (schemeHopfIdealLocusFamilyHom R H k)))
      (schemeHopfIdealLocusFamilyToGrp R H k))

variable (R H k) in
/-- The universal subgroup is the universal family over the Hopf-ideal locus with its group
structure. -/
noncomputable def universalSubgroupIso :
    ((universalSubgroup R H k).1 : Grp (Over (schemeHopfIdealLocus R H k).subscheme)) ≅
      Grp.mk (Over.mk (schemeHopfIdealLocusFamilyHom R H k)) :=
  TauCeti.ClosedSubgroupScheme.mkIso _

/-- Under `Module.Grassmannian.universalSubgroupIso`, the inclusion of the universal subgroup is
the inclusion of the universal family. -/
@[reassoc (attr := simp)]
theorem universalSubgroupIso_inv_arrow :
    (universalSubgroupIso R H k).inv ≫ (universalSubgroup R H k).1.arrow =
      Grp.homMk (schemeHopfIdealLocusFamilyToGrp R H k) :=
  TauCeti.ClosedSubgroupScheme.mkIso_inv_comp_arrow _

/-- The universal subgroup is finite locally free of rank `k`, read off from the universal family
through the canonical isomorphism `TauCeti.ClosedSubgroupScheme.mkIso`. -/
private theorem finiteLocallyFree_universalSubgroup :
    IsFinite ((universalSubgroup R H k).1 :
        Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom ∧
      AlgebraicGeometry.Flat ((universalSubgroup R H k).1 :
        Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom ∧
      LocallyOfFinitePresentation ((universalSubgroup R H k).1 :
        Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom ∧
      ∀ s, (((universalSubgroup R H k).1 :
        Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom).finrank s = k :=
  (TauCeti.finiteLocallyFree_iff_of_iso ((Grp.forget _).mapIso (universalSubgroupIso R H k))).2
    ⟨inferInstanceAs (IsFinite (schemeHopfIdealLocusFamilyHom R H k)),
      inferInstanceAs (AlgebraicGeometry.Flat (schemeHopfIdealLocusFamilyHom R H k)),
      inferInstanceAs (LocallyOfFinitePresentation (schemeHopfIdealLocusFamilyHom R H k)),
      finrank_schemeHopfIdealLocusFamilyHom⟩

/-- The universal subgroup is finite over the closed subscheme of Hopf ideals. -/
instance isFinite_universalSubgroup :
    IsFinite ((universalSubgroup R H k).1 :
      Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom :=
  finiteLocallyFree_universalSubgroup.1

/-- The universal subgroup is flat over the closed subscheme of Hopf ideals. -/
instance flat_universalSubgroup :
    AlgebraicGeometry.Flat ((universalSubgroup R H k).1 :
      Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom :=
  finiteLocallyFree_universalSubgroup.2.1

/-- The universal subgroup is locally of finite presentation over the closed subscheme of Hopf
ideals. -/
instance locallyOfFinitePresentation_universalSubgroup :
    LocallyOfFinitePresentation ((universalSubgroup R H k).1 :
      Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom :=
  finiteLocallyFree_universalSubgroup.2.2.1

/-- The universal subgroup has constant rank `k` over the closed subscheme of Hopf ideals. -/
theorem finrank_universalSubgroup (s : (schemeHopfIdealLocus R H k).subscheme) :
    (((universalSubgroup R H k).1 :
      Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom).finrank s = k :=
  finiteLocallyFree_universalSubgroup.2.2.2 s

end Module.Grassmannian
