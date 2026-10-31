/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.ChangeOfGroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast

/-!
# The Evens norm at index one

For a compact open subgroup `U` of index one in a topological group `G`, the Evens norm
`N_U^G : Hⁿ(U, 𝔽₂) → H^{1 · n}(G, 𝔽₂)` is the identity, read through restriction to `U`, which is
then an isomorphism: restricting the norm of a class gives the class back
(`OpenSubgroup.trivialF2ResMap_evensNorm_of_index_eq_one`), and the norm of the restriction of a
class is the class itself (`OpenSubgroup.evensNorm_trivialF2ResMap_of_index_eq_one`). Both hold
up to the transport of degrees `n = 1 · n`. This is the degenerate case of the norm in the index,
beside the degree-zero case `OpenSubgroup.tensorNormCocycleClass_eq_degreeZeroClass`.

With the transversal `{1}`, the tensor-induced total resolution has a single tensor factor, on
which an element of `U` acts by itself. Reading off that factor is a morphism of complexes of
`U`-representations from the restriction to `U` of the tensor-induced resolution to the total
resolution of the coefficients. It carries the diagonal tensor of a cocycle `z` to `z` and lies
over the identification of the tensor-induced coefficients with the coefficients, so restriction
sends the norm of the class of `z` to the class of `z`
(`TopRep.ResolutionContraction.map_gradedCohomologyClass`).

## Main results

* `OpenSubgroup.trivialF2ResMap_evensNorm_of_index_eq_one`: at index one, `res_U ∘ N_U^G` is the
  identity of `Hⁿ(U, 𝔽₂)`.
* `OpenSubgroup.evensNorm_trivialF2ResMap_of_index_eq_one`: at index one, `N_U^G ∘ res_U` is the
  identity of `Hⁿ(G, 𝔽₂)`.

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

include hU in
private theorem mem_of_index_eq_one (g : G) : g ∈ U.toSubgroup := by
  simp [Subgroup.index_eq_one.1 hU]

include hU in
private theorem card_quotient_eq_one [Fintype (G ⧸ U.toSubgroup)] :
    Fintype.card (G ⧸ U.toSubgroup) = 1 := by
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hU]

include hU in
private theorem subsingleton_quotient : Subsingleton (G ⧸ U.toSubgroup) :=
  Subgroup.index_eq_one.1 hU ▸ QuotientGroup.subsingleton_quotient_top

/-- The transversal `{1}` of a subgroup of index one. -/
private noncomputable def oneTransversal : U.toSubgroup.LeftTransversal :=
  ⟨{1}, Subgroup.isComplement_singleton_left.2 (by
    rw [Subgroup.index_eq_one.1 hU, Subgroup.coe_top])⟩

/-- For the transversal `{1}`, the transversal word of `g` is `g` itself. -/
private theorem monomialHom_oneTransversal_left (g : G) (x : G ⧸ U.toSubgroup) :
    ((U.toSubgroup.monomialHom (oneTransversal hU) g).left x : G) = g := by
  have hr (y : G ⧸ U.toSubgroup) :
      Subgroup.leftTransversalRep U.toSubgroup (oneTransversal hU) y = 1 :=
    Set.mem_singleton_iff.1 (Subgroup.leftTransversalRep_mem U.toSubgroup (oneTransversal hU) y)
  rw [Subgroup.monomialHom_left]
  simp [lWord_def, hr]

end Group

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : OpenSubgroup G} [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  (hU : U.toSubgroup.index = 1)

-- Tensor induction uses the direct-sum scalar action of the total resolution, rather than
-- the fallback integer action on its underlying additive group.
private noncomputable local instance : Module ℤ (trivialF2 U.toSubgroup).gradedResolutionModule :=
  @DirectSum.instModule ℤ _ ℕ
    (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).V)
    (fun _ ↦ inferInstance) (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).hV2)

/-- The trivial `𝔽₂` coefficients of `U`, as a smooth discrete representation. -/
private noncomputable abbrev coeffs : SmoothDiscreteTopRep.{0, u, u} ℤ U.toSubgroup :=
  ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩

/-- The total resolution of the coefficients, as the discrete representation that is
tensor-induced. -/
private noncomputable abbrev resolutionRep : DiscreteRep.{0, u, u} ℤ U.toSubgroup :=
  (ofSmoothDiscrete ℤ U.toSubgroup).obj (smoothGradedResolutionFunctor.obj (coeffs (U := U)))

-- Instance search would pick `AddCommGroup.toIntModule`, which is not the module structure that
-- tensor induction is formed with.
private noncomputable local instance : Module ℤ (resolutionRep (U := U)).V :=
  (resolutionRep (U := U)).module

/-- The tensor-induced total resolution for the transversal `{1}`. -/
private noncomputable abbrev inducedResolution : TopRep ℤ G :=
  ((smoothTensorInducedGradedResolutionFunctor U.toSubgroup U.isOpen' (oneTransversal hU)).obj
    (coeffs (U := U))).obj

/-- An element of `U` acts on the single factor of the tensor-induced resolution by itself. -/
private theorem subsingletonEquiv_ρ (u : U.toSubgroup) (x : (inducedResolution hU).V) :
    haveI := subsingleton_quotient hU
    PiTensorProduct.subsingletonEquiv (R := ℤ)
        (s := fun _ : G ⧸ U.toSubgroup ↦ (resolutionRep (U := U)).V) (QuotientGroup.mk 1)
        ((inducedResolution hU).ρ u x) =
      (trivialF2 U.toSubgroup).gradedResolutionTopRep.ρ u
        (PiTensorProduct.subsingletonEquiv (R := ℤ)
          (s := fun _ : G ⧸ U.toSubgroup ↦ (resolutionRep (U := U)).V) (QuotientGroup.mk 1) x) := by
  have := subsingleton_quotient hU
  obtain ⟨y, rfl⟩ : ∃ y, x = PiTensorProduct.tprod ℤ fun _ : G ⧸ U.toSubgroup ↦ y :=
    ⟨_, ((PiTensorProduct.subsingletonEquiv (QuotientGroup.mk 1)).symm_apply_apply x).symm.trans
      (PiTensorProduct.subsingletonEquiv_symm_apply' _ _)⟩
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
        U.toSubgroup →* G) (inducedResolution hU) ⟶
      (trivialF2 U.toSubgroup).gradedResolutionTopRep :=
  haveI := subsingleton_quotient hU
  haveI := ((smoothTensorInducedGradedResolutionFunctor U.toSubgroup U.isOpen'
    (oneTransversal hU)).obj (coeffs (U := U))).property.discreteTopology
  let e := (PiTensorProduct.subsingletonEquiv (R := ℤ)
    (s := fun _ : G ⧸ U.toSubgroup ↦ (resolutionRep (U := U)).V)
    (QuotientGroup.mk 1)).toAddEquiv
  -- Instance search would pick `AddCommGroup.toIntModule` on the target carrier, which is not
  -- the module structure of the topological representation.
  letI : Module ℤ (trivialF2 U.toSubgroup).gradedResolutionTopRep.V := TopRep.hV2 _
  { hom' :=
    { toContinuousLinearMap :=
        ⟨(e.toIntLinearEquiv (modM := TopRep.hV2 _) (modM₂ := TopRep.hV2 _)).toLinearMap,
          continuous_of_discreteTopology⟩
      isIntertwining' u := by
        ext x
        exact subsingletonEquiv_ρ hU u x } }

private theorem indexOneProj_apply (x : (inducedResolution hU).V) :
    haveI := subsingleton_quotient hU
    (indexOneProj hU).hom x =
      PiTensorProduct.subsingletonEquiv (R := ℤ)
        (s := fun _ : G ⧸ U.toSubgroup ↦ (resolutionRep (U := U)).V) (QuotientGroup.mk 1) x :=
  (rfl)

omit [U.toSubgroup.FiniteIndex] in
/-- The class of a homogeneous cocycle, included in the total resolution, transported to an equal
degree. -/
private theorem gradedCohomologyClass_eq_degreeCast_cochainClass {n k : ℕ} (hk : n = k)
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z = 0)
    (y : (trivialF2 U.toSubgroup).gradedResolutionTopRep.V)
    (hy : y = (trivialF2 U.toSubgroup).cochainToGradedResolution n z) (hy' hinv hdy) :
    (TopRep.gradedResolutionContraction
      (isSmoothDiscrete_trivialF2 U.toSubgroup)).gradedCohomologyClass (n := k) y hy' hinv hdy =
      (ContinuousCohomology.degreeCast (trivialF2 U.toSubgroup) hk).hom
        ((trivialF2 U.toSubgroup).cochainClass n z hz) := by
  subst hk
  rw [TopRep.cochainToGradedResolution_apply] at hy
  subst hy
  rw [ContinuousCohomology.degreeCast_rfl, Iso.refl_hom, ConcreteCategory.id_apply]
  exact TopRep.gradedCohomologyClass_gradedResolutionContraction
    (isSmoothDiscrete_trivialF2 U.toSubgroup) z (congrArg Subtype.val hz)

variable [Fintype (G ⧸ U.toSubgroup)]

/-- **The Evens norm at index one, after restriction**: for a compact open subgroup `U` of index
one, restricting the norm `N_U^G x ∈ H^{1 · n}(G, 𝔽₂)` back to `U` gives `x`. -/
theorem trivialF2ResMap_evensNorm_of_index_eq_one {n : ℕ}
    (x : continuousCohomology n (trivialF2 U.toSubgroup)) :
    trivialF2ResMap G U.toSubgroup (Fintype.card (G ⧸ U.toSubgroup) * n) (U.evensNorm x) =
      (ContinuousCohomology.degreeCast (trivialF2 U.toSubgroup)
        (by rw [card_quotient_eq_one hU, one_mul])).hom x := by
  have := subsingleton_quotient hU
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
    (indexOneProj hU) ?_ ?_ ?_ _ _ _).trans
    (gradedCohomologyClass_eq_degreeCast_cochainClass _ z hz _ ?_ _ _ _)
  · exact PiTensorProduct.isHomogeneous_subsingletonEquiv (QuotientGroup.mk 1)
  · classical
    -- Instance search would pick `AddCommGroup.toIntModule` on the target carrier, which is not
    -- the module structure of the topological representation.
    let : Module ℤ (trivialF2 U.toSubgroup).gradedResolutionTopRep.V := TopRep.hV2 _
    refine TopRep.hom_ext (ContIntertwiningMap.ext (ContinuousLinearMap.ext fun x ↦ ?_))
    -- On a single factor, the slot sum of the total differential is that differential.
    exact (indexOneProj_apply hU _).trans
      ((congrArg _ (smoothTensorInducedGradedResolutionDifferential_apply _ _ _ _ x)).trans
        ((PiTensorProduct.subsingletonEquiv_slotSum (QuotientGroup.mk 1)
          (fun _ ↦ (coeffs (U := U)).obj.gradedResolutionDifferential) x).trans
          (TopRep.gradedResolutionTopRepDifferential_apply _ _).symm))
  swap
  · exact (indexOneProj_apply hU _).trans (PiTensorProduct.subsingletonEquiv_apply_tprod _ _)
  -- It lies over the identification of the coefficients: both multiply out a single factor.
  let : Module ℤ (DiscreteRep.trivialF2 U.toSubgroup).V :=
    (DiscreteRep.trivialF2 U.toSubgroup).module
  let : Module ℤ (coeffs (U := U)).obj.V := TopRep.hV2 _
  intro x
  obtain ⟨a, rfl⟩ : ∃ a, x = PiTensorProduct.tprod ℤ fun _ : G ⧸ U.toSubgroup ↦ a :=
    ⟨_, ((PiTensorProduct.subsingletonEquiv (QuotientGroup.mk 1)).symm_apply_apply x).symm.trans
      (PiTensorProduct.subsingletonEquiv_symm_apply' _ _)⟩
  rw [indexOneProj_apply]
  refine (congrArg (PiTensorProduct.subsingletonEquiv _)
    ((smoothTensorInducedGradedResolutionContraction_ι_apply _ _ _ _ _ _).trans
      (PiTensorProduct.map_tprod _ _))).trans <|
    (PiTensorProduct.subsingletonEquiv_apply_tprod _ _).trans <|
    (congrArg _ ?_).trans (TopRep.gradedResolutionContraction_ι_apply _ _).symm
  apply (trivialF2Equiv U.toSubgroup).injective
  refine Eq.symm ((congrArg (trivialF2Equiv U.toSubgroup)
    (TopRep.eqToHom_hom_apply (res_trivialF2_hom _) _)).trans
      ((trivialF2Equiv_cast _ _ _).trans ?_))
  refine (smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod G _ _ _ _).trans ?_
  -- The product is over the `Fintype` instance of the coefficient identification.
  convert Fintype.prod_subsingleton (fun _ ↦ trivialF2Equiv U.toSubgroup a)
    (QuotientGroup.mk 1 : G ⧸ U.toSubgroup)

omit [CompactSpace U.toSubgroup] [U.toSubgroup.FiniteIndex] [Fintype (G ⧸ U.toSubgroup)] in
include hU in
/-- At index one, restriction is injective: corestricting the identity of `G` to `U` gives it a
left inverse. -/
private theorem trivialF2ResMap_injective (n : ℕ) :
    Function.Injective (trivialF2ResMap G U.toSubgroup n) := by
  let ι : G →ₜ* U.toSubgroup :=
    ⟨(MonoidHom.id G).codRestrict U.toSubgroup (mem_of_index_eq_one hU),
      continuous_id.subtype_mk _⟩
  have hι : (ContinuousMonoidHom.subgroupSubtype U.toSubgroup).comp ι = ContinuousMonoidHom.id G :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  refine Function.LeftInverse.injective (g := trivialF2Map ι n) fun a ↦ ?_
  rw [← trivialF2Map_subgroupSubtype, ← ConcreteCategory.comp_apply, ← trivialF2Map_comp, hι,
    trivialF2Map_id, ConcreteCategory.id_apply]

omit [CompactSpace U.toSubgroup] [U.toSubgroup.FiniteIndex] [Fintype (G ⧸ U.toSubgroup)] in
private theorem trivialF2ResMap_degreeCast {n k : ℕ} (h : n = k)
    (y : continuousCohomology n (trivialF2 G)) :
    trivialF2ResMap G U.toSubgroup k ((ContinuousCohomology.degreeCast (trivialF2 G) h).hom y) =
      (ContinuousCohomology.degreeCast (trivialF2 U.toSubgroup) h).hom
        (trivialF2ResMap G U.toSubgroup n y) := by
  subst h
  simp

/-- **The Evens norm at index one**: for a compact open subgroup `U` of index one, the norm of
the restriction to `U` of a class `y ∈ Hⁿ(G, 𝔽₂)` is `y`, in degree `1 · n = n`. -/
theorem evensNorm_trivialF2ResMap_of_index_eq_one {n : ℕ}
    (y : continuousCohomology n (trivialF2 G)) :
    U.evensNorm (trivialF2ResMap G U.toSubgroup n y) =
      (ContinuousCohomology.degreeCast (trivialF2 G)
        (by rw [card_quotient_eq_one hU, one_mul])).hom y := by
  apply trivialF2ResMap_injective hU
  rw [trivialF2ResMap_evensNorm_of_index_eq_one hU, trivialF2ResMap_degreeCast]

end OpenSubgroup
