/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.CharTwo
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.ChangeOfGroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast

/-!
# The Evens norm at index one

For a compact open subgroup `U` of index one in a topological group `G`, the Evens norm
`N_U^G : Hⁿ(U, A) → H^{1 · n}(G, A)` is the identity, read through restriction to `U`, which is
then an isomorphism. This holds both for the norm `OpenSubgroup.evensNorm` with trivial `𝔽₂`
coefficients and for the norm `OpenSubgroup.evensNormCharTwo` with coefficients in a discrete
commutative `G`-ring `A` in which `2 = 0`: restricting the norm of a class gives the class back
(`OpenSubgroup.trivialF2ResMap_evensNorm_of_index_eq_one`,
`OpenSubgroup.res_evensNormCharTwo_of_index_eq_one`), and the norm of the restriction of a class
is the class itself (`OpenSubgroup.evensNorm_trivialF2ResMap_of_index_eq_one`,
`OpenSubgroup.evensNormCharTwo_res_of_index_eq_one`). All hold up to the transport of degrees
`n = 1 · n`. This is the degenerate case of the norm in the index, beside the degree-zero cases
`OpenSubgroup.tensorNormCocycleClass_eq_degreeZeroClass` and
`OpenSubgroup.evensNormCharTwo_degreeZeroClass`.

With the transversal `{1}`, the tensor-induced total resolution of any coefficients has a single
tensor factor, on which an element of `U` acts by itself. Reading off that factor is a morphism of
complexes of `U`-representations from the restriction to `U` of the tensor-induced resolution to
the total resolution of the coefficients. It carries the diagonal tensor of a cocycle `z` to `z`
and lies over reading off the single factor of the tensor-induced coefficients. For `𝔽₂` that is
the identification of the tensor-induced coefficients with `𝔽₂`, and for `A` it is Evens's twisted
multiplication, since the only representative is `1`. So restriction sends the norm of the class
of `z` to the class of `z` (`TopRep.ResolutionContraction.map_gradedCohomologyClass`).

## Main results

* `OpenSubgroup.trivialF2ResMap_evensNorm_of_index_eq_one`: at index one, `res_U ∘ N_U^G` is the
  identity of `Hⁿ(U, 𝔽₂)`.
* `OpenSubgroup.evensNorm_trivialF2ResMap_of_index_eq_one`: at index one, `N_U^G ∘ res_U` is the
  identity of `Hⁿ(G, 𝔽₂)`.
* `OpenSubgroup.res_evensNormCharTwo_of_index_eq_one`: at index one, `res_U ∘ N_U^G` is the
  identity of `Hⁿ(U, A)` for a discrete commutative `G`-ring `A` with `2 = 0`.
* `OpenSubgroup.evensNormCharTwo_res_of_index_eq_one`: at index one, `N_U^G ∘ res_U` is the
  identity of `Hⁿ(G, A)` for such `A`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–5.
-/

public section

namespace OpenSubgroup

open TauCeti CategoryTheory
open scoped TensorProduct

universe u

section Group

variable {G : Type u} [Group G] [TopologicalSpace G] {U : OpenSubgroup G}
  (hU : U.toSubgroup.index = 1)

/-- The transversal `{1}` of a subgroup of index one. -/
private noncomputable def oneTransversal : U.toSubgroup.LeftTransversal :=
  ⟨{1}, Subgroup.isComplement_singleton_left.2 (by
    rw [Subgroup.index_eq_one.1 hU, Subgroup.coe_top])⟩

/-- Every representative of the transversal `{1}` is `1`. -/
private theorem leftTransversalRep_oneTransversal (x : G ⧸ U.toSubgroup) :
    Subgroup.leftTransversalRep U.toSubgroup (oneTransversal hU) x = 1 :=
  Set.mem_singleton_iff.1 (Subgroup.leftTransversalRep_mem U.toSubgroup (oneTransversal hU) x)

/-- For the transversal `{1}`, the transversal word of `g` is `g` itself. -/
private theorem monomialHom_oneTransversal_left (g : G) (x : G ⧸ U.toSubgroup) :
    ((U.toSubgroup.monomialHom (oneTransversal hU) g).left x : G) = g := by
  rw [Subgroup.monomialHom_left]
  simp [lWord_def, leftTransversalRep_oneTransversal hU]

end Group

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : OpenSubgroup G} [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]

open scoped TopRep.GradedResolution

/-- The trivial `𝔽₂` coefficients of `U`, as a smooth discrete representation. -/
private noncomputable abbrev coeffs : SmoothDiscreteTopRep.{0, u, u} ℤ U.toSubgroup :=
  ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩

/-- The total resolution of the coefficients `X`, as the discrete representation that is
tensor-induced. -/
private noncomputable abbrev resolutionRep (X : SmoothDiscreteTopRep.{0, u, u} ℤ U.toSubgroup) :
    DiscreteRep.{0, u, u} ℤ U.toSubgroup :=
  (ofSmoothDiscrete ℤ U.toSubgroup).obj (smoothGradedResolutionFunctor.obj X)

-- Instance search would pick `AddCommGroup.toIntModule`, which is not the module structure that
-- tensor induction is formed with.
private noncomputable local instance {X : SmoothDiscreteTopRep.{0, u, u} ℤ U.toSubgroup} :
    Module ℤ (resolutionRep X).V :=
  (resolutionRep X).module

variable (hU : U.toSubgroup.index = 1) (X : SmoothDiscreteTopRep.{0, u, u} ℤ U.toSubgroup)

/-- The tensor-induced total resolution of `X` for the transversal `{1}`. -/
private noncomputable abbrev inducedResolution : TopRep ℤ G :=
  ((smoothTensorInducedGradedResolutionFunctor U.toSubgroup U.isOpen' (oneTransversal hU)).obj
    X).obj

/-- An element of `U` acts on the single factor of the tensor-induced resolution by itself. -/
private theorem subsingletonEquiv_ρ (u : U.toSubgroup) (x : (inducedResolution hU X).V) :
    haveI := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
    PiTensorProduct.subsingletonEquiv (R := ℤ)
        (s := fun _ : G ⧸ U.toSubgroup ↦ (resolutionRep X).V) (QuotientGroup.mk 1)
        ((inducedResolution hU X).ρ u x) =
      X.obj.gradedResolutionTopRep.ρ u
        (PiTensorProduct.subsingletonEquiv (R := ℤ)
          (s := fun _ : G ⧸ U.toSubgroup ↦ (resolutionRep X).V) (QuotientGroup.mk 1) x) := by
  have := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
  obtain ⟨y, rfl⟩ := PiTensorProduct.exists_eq_tprod_of_subsingleton (QuotientGroup.mk 1) x
  have hword : (U.toSubgroup.monomialHom (oneTransversal hU) (u : G)).left (QuotientGroup.mk 1) =
      u := Subtype.ext (monomialHom_oneTransversal_left hU _ _)
  refine (congrArg (PiTensorProduct.subsingletonEquiv (QuotientGroup.mk 1))
    (smoothTensorInducedGradedResolutionFunctor_obj_ρ_apply _ _ _ _ (u : G) _)).trans ?_
  rw [Subgroup.tensorInducedRepresentation_apply_tprod,
    PiTensorProduct.subsingletonEquiv_apply_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod,
    hword]
  exact (ofSmoothDiscrete_obj_ρ_apply ℤ U.toSubgroup _ u y).trans
    (smoothGradedResolutionFunctor_obj_obj_ρ_apply _ u y)

/-- Reading off the single tensor factor, as a morphism of `U`-representations from the
restriction to `U` of the tensor-induced resolution to the total resolution of the
coefficients. -/
private noncomputable def indexOneProj :
    TopRep.res ((ContinuousMonoidHom.subgroupSubtype U.toSubgroup : U.toSubgroup →ₜ* G) :
        U.toSubgroup →* G) (inducedResolution hU X) ⟶
      X.obj.gradedResolutionTopRep :=
  haveI := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
  haveI := ((smoothTensorInducedGradedResolutionFunctor U.toSubgroup U.isOpen'
    (oneTransversal hU)).obj X).property.discreteTopology
  let e := (PiTensorProduct.subsingletonEquiv (R := ℤ)
    (s := fun _ : G ⧸ U.toSubgroup ↦ (resolutionRep X).V)
    (QuotientGroup.mk 1)).toAddEquiv
  -- Instance search would pick `AddCommGroup.toIntModule` on the target carrier, which is not
  -- the module structure of the topological representation.
  letI : Module ℤ X.obj.gradedResolutionTopRep.V := TopRep.hV2 _
  { hom' :=
    { toContinuousLinearMap :=
        ⟨(e.toIntLinearEquiv (modM := TopRep.hV2 _) (modM₂ := TopRep.hV2 _)).toLinearMap,
          continuous_of_discreteTopology⟩
      isIntertwining' u := by
        ext x
        exact subsingletonEquiv_ρ hU X u x } }

private theorem indexOneProj_apply (x : (inducedResolution hU X).V) :
    haveI := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
    (indexOneProj hU X).hom x =
      PiTensorProduct.subsingletonEquiv (R := ℤ)
        (s := fun _ : G ⧸ U.toSubgroup ↦ (resolutionRep X).V) (QuotientGroup.mk 1) x :=
  (rfl)

variable [Fintype (G ⧸ U.toSubgroup)]

/-- Reading off the single factor commutes with the differentials: on one factor, the slot sum
of the total differential is that differential. -/
private theorem indexOneProj_comp_differential :
    (TopRep.resFunctor ((ContinuousMonoidHom.subgroupSubtype U.toSubgroup : U.toSubgroup →ₜ* G) :
        U.toSubgroup →* G)).map
        (smoothTensorInducedGradedResolutionDifferential U.toSubgroup U.isOpen' (oneTransversal hU)
          X).hom ≫ indexOneProj hU X =
      indexOneProj hU X ≫ X.obj.gradedResolutionTopRepDifferential := by
  classical
  -- Instance search would pick `AddCommGroup.toIntModule` on the target carrier, which is not
  -- the module structure of the topological representation.
  let : Module ℤ X.obj.gradedResolutionTopRep.V := TopRep.hV2 _
  have := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
  ext x
  rw [ContIntertwiningMap.toContinuousLinearMap_apply,
    ContIntertwiningMap.toContinuousLinearMap_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, indexOneProj_apply, indexOneProj_apply]
  -- Restriction along `U → G` does not change the underlying map of the differential.
  exact (congrArg _ (smoothTensorInducedGradedResolutionDifferential_apply _ _ _ _ x)).trans <|
    (PiTensorProduct.subsingletonEquiv_slotSum (QuotientGroup.mk 1)
      (fun _ ↦ X.obj.gradedResolutionDifferential) x).trans
      (TopRep.gradedResolutionTopRepDifferential_apply _ _).symm

/-- Reading off the single factor lies over reading off the single factor of the tensor-induced
coefficients: on a pure tensor, both augmentations are the augmentation of that factor. -/
private theorem indexOneProj_ι_apply [LinearOrder (G ⧸ U.toSubgroup)]
    (hX : ∀ a : X.obj.V, a + a = 0) :
    haveI := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
    letI : Module ℤ ((ofSmoothDiscrete ℤ U.toSubgroup).obj X).V :=
      ((ofSmoothDiscrete ℤ U.toSubgroup).obj X).module
    ∀ x, (indexOneProj hU X).hom
        ((smoothTensorInducedGradedResolutionContraction U.toSubgroup U.isOpen' (oneTransversal hU)
          X hX).ι.hom x).val =
      ((TopRep.gradedResolutionContraction X.property).ι.hom
        (PiTensorProduct.subsingletonEquiv (R := ℤ)
          (s := fun _ : G ⧸ U.toSubgroup ↦ ((ofSmoothDiscrete ℤ U.toSubgroup).obj X).V)
          (QuotientGroup.mk 1) x)).val := by
  let : Module ℤ ((ofSmoothDiscrete ℤ U.toSubgroup).obj X).V :=
    ((ofSmoothDiscrete ℤ U.toSubgroup).obj X).module
  have := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
  intro x
  obtain ⟨a, rfl⟩ := PiTensorProduct.exists_eq_tprod_of_subsingleton (QuotientGroup.mk 1) x
  let : Module ℤ X.obj.V := TopRep.hV2 _
  rw [indexOneProj_apply]
  -- The carriers here agree only up to unfolding, so `rw` cannot see through them: the steps
  -- are chained as equations instead. On a pure tensor, the augmentation of the tensor-induced
  -- resolution is the augmentation of the single factor.
  refine (congrArg (PiTensorProduct.subsingletonEquiv _)
    ((smoothTensorInducedGradedResolutionContraction_ι_apply _ _ _ _ _ _).trans
      (PiTensorProduct.map_tprod _ _))).trans <|
    (PiTensorProduct.subsingletonEquiv_apply_tprod _ _).trans <|
    (TopRep.gradedResolutionContraction_ι_apply X.property _).symm.trans ?_
  exact congrArg (fun v ↦ ((TopRep.gradedResolutionContraction X.property).ι.hom v).val)
    (PiTensorProduct.subsingletonEquiv_apply_tprod (R := ℤ) (QuotientGroup.mk 1)
      (fun _ : G ⧸ U.toSubgroup ↦ a)).symm

omit [CompactSpace U.toSubgroup] [Fintype (G ⧸ U.toSubgroup)] in
/-- Reading off the single factor of the tensor-induced trivial `𝔽₂` coefficients is their
identification with the trivial `𝔽₂` coefficients: both multiply out a single factor. -/
private theorem subsingletonEquiv_eq_smoothTensorInducedTrivialF2Iso
    (x : ((toSmoothDiscrete ℤ G).obj (DiscreteRep.tensorInduced U.toSubgroup U.isOpen'
      (oneTransversal hU) ((ofSmoothDiscrete ℤ U.toSubgroup).obj (coeffs (U := U))))).obj.V) :
    haveI := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
    letI : Module ℤ ((ofSmoothDiscrete ℤ U.toSubgroup).obj (coeffs (U := U))).V :=
      ((ofSmoothDiscrete ℤ U.toSubgroup).obj (coeffs (U := U))).module
    PiTensorProduct.subsingletonEquiv (R := ℤ)
        (s := fun _ : G ⧸ U.toSubgroup ↦
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj (coeffs (U := U))).V)
        (QuotientGroup.mk 1) x =
      (((TopRep.resFunctor (U.toSubgroup.subtype)).map
        (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' (oneTransversal hU)).hom.hom ≫
          eqToHom (res_trivialF2_hom _)).hom x) := by
  let := Fintype.ofFinite (G ⧸ U.toSubgroup)
  let : Module ℤ (DiscreteRep.trivialF2 U.toSubgroup).V :=
    (DiscreteRep.trivialF2 U.toSubgroup).module
  have := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
  obtain ⟨a, rfl⟩ := PiTensorProduct.exists_eq_tprod_of_subsingleton (QuotientGroup.mk 1) x
  refine (PiTensorProduct.subsingletonEquiv_apply_tprod _ _).trans ?_
  apply (trivialF2Equiv U.toSubgroup).injective
  refine Eq.symm ((congrArg (trivialF2Equiv U.toSubgroup)
    (TopRep.eqToHom_hom_apply (res_trivialF2_hom _) _)).trans
      ((trivialF2Equiv_cast _ _ _).trans ?_))
  refine (smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod G _ _ _ _).trans ?_
  -- The product is over the `Fintype` instance of the coefficient identification.
  convert Fintype.prod_subsingleton (fun _ ↦ trivialF2Equiv U.toSubgroup a)
    (QuotientGroup.mk 1 : G ⧸ U.toSubgroup)

/-- **The Evens norm at index one, after restriction**: for a compact open subgroup `U` of index
one, restricting the norm `N_U^G x ∈ H^{1 · n}(G, 𝔽₂)` back to `U` gives `x`. -/
theorem trivialF2ResMap_evensNorm_of_index_eq_one {n : ℕ}
    (x : continuousCohomology n (trivialF2 U.toSubgroup)) :
    trivialF2ResMap G U.toSubgroup (Fintype.card (G ⧸ U.toSubgroup) * n) (U.evensNorm x) =
      (ContinuousCohomology.degreeCast (trivialF2 U.toSubgroup)
        (by rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hU, one_mul])).hom x := by
  have := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
  obtain ⟨z, hz, rfl⟩ := TopRep.exists_cochainClass_eq x
  let : LinearOrder (G ⧸ U.toSubgroup) :=
    LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U.toSubgroup)).injective
  -- The norm is the class of the diagonal tensor, with the transversal `{1}`, followed by the
  -- identification of the tensor-induced coefficients. Restriction absorbs that identification.
  rw [evensNorm_cochainClass U (oneTransversal hU), tensorNormCocycleClass_def,
    smoothTensorInducedDiagonalClass_eq, ← trivialF2Map_subgroupSubtype, trivialF2Map_def]
  have hcomp := ConcreteCategory.congr_hom
    (ContinuousCohomology.map_comp_coeffMap (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
      ((TopRep.resFunctor (U.toSubgroup.subtype)).map
        (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' (oneTransversal hU)).hom.hom ≫
        eqToHom (res_trivialF2_hom _))
      (eqToHom (res_trivialF2_hom _))
      (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' (oneTransversal hU)).hom.hom
      (𝟙 _) (Category.comp_id _).symm (Fintype.card (G ⧸ U.toSubgroup) * n))
  rw [ContinuousCohomology.coeffMap_id, Category.comp_id] at hcomp
  refine (hcomp _).symm.trans ?_
  -- Reading off the single factor carries the diagonal tensor to the cocycle itself.
  refine (TopRep.ResolutionContraction.map_gradedCohomologyClass _ _
    (TopRep.gradedResolutionContraction (isSmoothDiscrete_trivialF2 U.toSubgroup)) _
    (indexOneProj hU coeffs) ?_ (indexOneProj_comp_differential hU coeffs)
    (fun x ↦ (indexOneProj_ι_apply hU coeffs _ x).trans
      (congrArg (fun v ↦ ((TopRep.gradedResolutionContraction
        (isSmoothDiscrete_trivialF2 U.toSubgroup)).ι.hom v).val)
        (subsingletonEquiv_eq_smoothTensorInducedTrivialF2Iso hU x))) _ _ _).trans
    (TopRep.gradedCohomologyClass_eq_degreeCast_cochainClass _ _ z hz _ ?_ _ _ _)
  · exact PiTensorProduct.isHomogeneous_subsingletonEquiv (QuotientGroup.mk 1)
  · exact (indexOneProj_apply hU coeffs _).trans
      (PiTensorProduct.subsingletonEquiv_apply_tprod _ _)

/-- **The Evens norm at index one**: for a compact open subgroup `U` of index one, the norm of
the restriction to `U` of a class `y ∈ Hⁿ(G, 𝔽₂)` is `y`, in degree `1 · n = n`. -/
theorem evensNorm_trivialF2ResMap_of_index_eq_one {n : ℕ}
    (y : continuousCohomology n (trivialF2 G)) :
    U.evensNorm (trivialF2ResMap G U.toSubgroup n y) =
      (ContinuousCohomology.degreeCast (trivialF2 G)
        (by rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hU, one_mul])).hom y := by
  apply trivialF2ResMap_injective_of_index_eq_one hU
  rw [trivialF2ResMap_evensNorm_of_index_eq_one hU]
  rw [← ConcreteCategory.comp_apply,
    ContinuousCohomology.degreeCast_naturality (trivialF2ResMap G U.toSubgroup),
    ConcreteCategory.comp_apply]

section CharTwo

variable (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [ContinuousSMul G A] (hA : ∀ a : A, a + a = 0)

/-- The coefficients `A` of `U`, as a smooth discrete representation. -/
private noncomputable abbrev ringCoeffs : SmoothDiscreteTopRep.{0, u, u} ℤ U.toSubgroup :=
  ⟨ofDiscreteModule ℤ U.toSubgroup A, ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A⟩

omit [CompactSpace U.toSubgroup] [Fintype (G ⧸ U.toSubgroup)] in
/-- Reading off the single factor of the tensor-induced ring `⨂_{G ⧸ U} A` is Evens's twisted
multiplication for the transversal `{1}`: both send `a` to `a`. -/
private theorem subsingletonEquiv_eq_smoothTensorInducedMulHom
    (x : ((toSmoothDiscrete ℤ G).obj (DiscreteRep.tensorInduced U.toSubgroup U.isOpen'
      (oneTransversal hU) ((ofSmoothDiscrete ℤ U.toSubgroup).obj (ringCoeffs (U := U) A)))).obj.V) :
    haveI := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
    letI : Module ℤ ((ofSmoothDiscrete ℤ U.toSubgroup).obj (ringCoeffs (U := U) A)).V :=
      ((ofSmoothDiscrete ℤ U.toSubgroup).obj (ringCoeffs (U := U) A)).module
    PiTensorProduct.subsingletonEquiv (R := ℤ)
        (s := fun _ : G ⧸ U.toSubgroup ↦
          ((ofSmoothDiscrete ℤ U.toSubgroup).obj (ringCoeffs (U := U) A)).V)
        (QuotientGroup.mk 1) x =
      ((TopRep.resFunctor (U.toSubgroup.subtype)).map
        (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A (oneTransversal hU)).hom).hom
        x := by
  let := Fintype.ofFinite (G ⧸ U.toSubgroup)
  have := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
  refine Eq.symm ((smoothTensorInducedMulHom_hom_hom_apply (R := ℤ) U.toSubgroup U.isOpen' A
    (oneTransversal hU) x).trans ?_)
  rw [U.toSubgroup.tensorInducedMulAlgHom_eq_subsingletonAlgEquiv_of_rep_eq_one ℤ A
    (oneTransversal hU) (QuotientGroup.mk 1) (leftTransversalRep_oneTransversal hU _)]
  exact congrArg (fun e ↦ e x)
    (PiTensorProduct.subsingletonAlgEquiv_toLinearEquiv (R := ℤ)
      (QuotientGroup.mk 1) (fun _ : G ⧸ U.toSubgroup ↦ A))

/-- **The Evens norm in characteristic two at index one, after restriction**: for a compact open
subgroup `U` of index one and a discrete commutative `G`-ring `A` with `2 = 0`, restricting the norm
`N_U^G x ∈ H^{1 · n}(G, A)` back to `U` gives `x`. -/
theorem res_evensNormCharTwo_of_index_eq_one {n : ℕ}
    (x : continuousCohomology n (ofDiscreteModule ℤ U.toSubgroup A)) :
    ContinuousCohomology.res U.toSubgroup (ofDiscreteModule ℤ G A)
        (Fintype.card (G ⧸ U.toSubgroup) * n) (U.evensNormCharTwo A hA x) =
      (ContinuousCohomology.degreeCast (ofDiscreteModule ℤ U.toSubgroup A)
        (by rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hU, one_mul])).hom x := by
  have := QuotientGroup.subsingleton_iff.2 (Subgroup.index_eq_one.1 hU)
  obtain ⟨z, hz, rfl⟩ := TopRep.exists_cochainClass_eq x
  let : LinearOrder (G ⧸ U.toSubgroup) :=
    LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U.toSubgroup)).injective
  -- The norm is the class of the diagonal tensor, with the transversal `{1}`, pushed forward along
  -- the twisted multiplication. Restriction absorbs the twisted multiplication.
  rw [evensNormCharTwo_cochainClass U A hA (oneTransversal hU),
    smoothTensorInducedDiagonalClass_eq, ContinuousCohomology.res_def]
  have hcomp := ContinuousCohomology.map_comp_coeffMap (X' := ofDiscreteModule ℤ G A)
    (Y := TopRep.res (U.toSubgroup.subtype) (ofDiscreteModule ℤ G A))
    (Y' := TopRep.res (U.toSubgroup.subtype) (ofDiscreteModule ℤ G A))
    (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
    ((TopRep.resFunctor (U.toSubgroup.subtype)).map
      (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A (oneTransversal hU)).hom)
    (𝟙 (TopRep.res (U.toSubgroup.subtype) (ofDiscreteModule ℤ G A)))
    (smoothTensorInducedMulHom.{0, u, 0} U.toSubgroup U.isOpen' A (oneTransversal hU)).hom
    (𝟙 (TopRep.res (U.toSubgroup.subtype) (ofDiscreteModule ℤ G A)))
    ((Category.comp_id _).trans (Category.comp_id _).symm) (Fintype.card (G ⧸ U.toSubgroup) * n)
  rw [ContinuousCohomology.coeffMap_id, Category.comp_id] at hcomp
  rw [← ConcreteCategory.comp_apply, ← hcomp]
  -- Reading off the single factor carries the diagonal tensor to the cocycle itself.
  refine (TopRep.ResolutionContraction.map_gradedCohomologyClass _ _
    (TopRep.gradedResolutionContraction (ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A)) _
    (indexOneProj hU (ringCoeffs A)) ?_ (indexOneProj_comp_differential hU (ringCoeffs A))
    (fun x ↦ (indexOneProj_ι_apply hU (ringCoeffs A) _ x).trans
      (congrArg (fun v ↦ ((TopRep.gradedResolutionContraction
        (ofDiscreteModule_isSmoothDiscrete ℤ U.toSubgroup A)).ι.hom v).val)
        (subsingletonEquiv_eq_smoothTensorInducedMulHom hU A x))) _ _ _).trans
    (TopRep.gradedCohomologyClass_eq_degreeCast_cochainClass _ _ z hz _ ?_ _ _ _)
  · exact PiTensorProduct.isHomogeneous_subsingletonEquiv (QuotientGroup.mk 1)
  · exact (indexOneProj_apply hU (ringCoeffs A) _).trans
      (PiTensorProduct.subsingletonEquiv_apply_tprod _ _)

/-- **The Evens norm in characteristic two at index one**: for a compact open subgroup `U` of
index one and a discrete commutative `G`-ring `A` with `2 = 0`, the norm of the restriction to `U`
of a class `y ∈ Hⁿ(G, A)` is `y`, in degree `1 · n = n`. -/
theorem evensNormCharTwo_res_of_index_eq_one {n : ℕ}
    (y : continuousCohomology n (ofDiscreteModule ℤ G A)) :
    (U.evensNormCharTwo A hA (ContinuousCohomology.res U.toSubgroup (ofDiscreteModule ℤ G A) n y) :
        continuousCohomology (Fintype.card (G ⧸ U.toSubgroup) * n) (ofDiscreteModule ℤ G A)) =
      (ContinuousCohomology.degreeCast (ofDiscreteModule ℤ G A)
        (by rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hU, one_mul])).hom y := by
  apply ContinuousCohomology.res_injective_of_index_eq_one hU
  -- Restriction commutes with the transport of degrees; the restriction of `ofDiscreteModule ℤ G A`
  -- to `U` is `ofDiscreteModule ℤ U A` by definition (`TauCeti.res_ofDiscreteModule`).
  refine (res_evensNormCharTwo_of_index_eq_one hU A hA _).trans ?_
  rw [← ConcreteCategory.comp_apply, ← ContinuousCohomology.degreeCast_naturality,
    ConcreteCategory.comp_apply]
  rfl

end CharTwo

end OpenSubgroup
