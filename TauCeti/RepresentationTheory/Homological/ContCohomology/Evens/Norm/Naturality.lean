/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.ChangeOfGroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast
public import TauCeti.RepresentationTheory.Tensor.Induction.Naturality.Basic

/-!
# Naturality of the Evens norm in the group

Let `φ : H → G` be a continuous homomorphism, let `U ≤ G` and `V ≤ H` be compact open subgroups of
finite index such that `φ` restricts to `ψ : V → U`, and suppose that `φ` induces a bijection
`e : H ⧸ V ≃ G ⧸ U` of coset spaces. Then the Evens norm commutes with pulling back:
```
φ^* (N_U^G x) = N_V^H (ψ^* x)      in H^{l n}(H, 𝔽₂),   l = [G : U] = [H : V],
```
for every `x ∈ Hⁿ(U, 𝔽₂)` (`OpenSubgroup.trivialF2Map_evensNorm`). The main case is inflation:
for a normal subgroup `N ≤ U`, the quotient map `G → G ⧸ N` identifies `G ⧸ U` with the cosets of
the image of `U`, so inflating the norm from `G ⧸ N` is the norm of the inflated class
(`OpenSubgroup.trivialF2Map_quotientMkContinuousMonoidHom_evensNorm`). No closedness of `N` is
needed.

The norm of the class of a cocycle `z` is the class of the diagonal tensor `z ⊗ ⋯ ⊗ z` in the
tensor induction of the total coinduced resolution. Relabelling the tensor factors along `e`
(`Subgroup.tensorInducedMapEquiv`) and pulling each factor back along `ψ`
(`TopRep.gradedResolutionMap`) is a morphism of complexes from the restriction along `φ` of the
tensor-induced resolution for `U` to the one for `V`. It preserves the total degree, commutes with
the slot-sum differentials, and lies over the corresponding comparison of the tensor-induced
coefficients, which in turn lies over the identity of `𝔽₂` because both identifications multiply
the factors. It carries the diagonal tensor of `z` to the diagonal tensor of the pullback of `z`,
so `TopRep.ResolutionContraction.map_gradedCohomologyClass` computes the pullback of the norm.

## Main results

* `OpenSubgroup.trivialF2Map_evensNorm`: the Evens norm is natural in the group.
* `OpenSubgroup.trivialF2Map_quotientMkContinuousMonoidHom_evensNorm`: the Evens norm commutes
  with inflation.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–5.
-/

public section

namespace OpenSubgroup

open TauCeti CategoryTheory
open scoped TensorProduct

universe u

-- Instance search would pick `AddCommGroup.toIntModule`, which is not the module structure that
-- tensor induction is formed with.
attribute [local instance 1100] DiscreteRep.module

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {U : OpenSubgroup G} {V : OpenSubgroup H}
  (φ : H →ₜ* G) (ψ : V.toSubgroup →ₜ* U.toSubgroup) (hψ : ∀ v, (ψ v : G) = φ v)
  {e : H ⧸ V.toSubgroup ≃ G ⧸ U.toSubgroup} (he : ∀ h : H, e h = (φ h : G ⧸ U.toSubgroup))
  (s : V.toSubgroup.LeftTransversal)

section Comparison

variable [U.toSubgroup.FiniteIndex] [V.toSubgroup.FiniteIndex]
  {A : DiscreteRep.{0, u, u} ℤ U.toSubgroup} {B : DiscreteRep.{0, u, u} ℤ V.toSubgroup}
  (Φ : Representation.IntertwiningMap (A.ρ.comp (ψ : V.toSubgroup →* U.toSubgroup)) B.ρ)

/-- Tensor induction compared along `φ`, as an intertwining map: relabel the tensor factors along
`e` and apply `Φ` to each of them. -/
private noncomputable def tensorComparison :
    Representation.IntertwiningMap
      ((U.toSubgroup.tensorInducedRepresentation (s.map (φ : H →* G) e he) A.ρ).comp
        (φ : H →* G))
      (V.toSubgroup.tensorInducedRepresentation s B.ρ) :=
  (Φ.tensorInduced s).comp
    (Subgroup.tensorInducedMapEquiv (φ : H →* G) (ψ : V.toSubgroup →* U.toSubgroup) hψ e he s
      A.ρ).symm.toIntertwiningMap

omit [IsTopologicalGroup G] [IsTopologicalGroup H] [U.toSubgroup.FiniteIndex]
  [V.toSubgroup.FiniteIndex] in
/-- The comparison relabels the factors along `e` and applies `Φ` to each one. -/
private theorem tensorComparison_toLinearMap :
    (tensorComparison φ ψ hψ he s Φ).toLinearMap =
      PiTensorProduct.map (fun _ ↦ Φ.toLinearMap) ∘ₗ
        (PiTensorProduct.reindex ℤ (fun _ ↦ A.V) e.symm).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro m
  simp [tensorComparison]

/-- The comparison of discrete tensor inductions along `φ`, as a morphism of topological
`H`-representations from the restriction along `φ`. -/
private noncomputable def tensorComparisonHom :
    TopRep.res (φ : H →* G) ((toSmoothDiscrete ℤ G).obj
        (DiscreteRep.tensorInduced U.toSubgroup U.isOpen' (s.map (φ : H →* G) e he) A)).obj ⟶
      ((toSmoothDiscrete ℤ H).obj (DiscreteRep.tensorInduced V.toSubgroup V.isOpen' s B)).obj where
  hom' :=
    { toContinuousLinearMap :=
        ⟨{ toFun := tensorComparison φ ψ hψ he s Φ
           map_add' := map_add _
           map_smul' := (tensorComparison φ ψ hψ he s Φ).toLinearMap.map_smul },
          continuous_of_discreteTopology⟩
      isIntertwining' h := by
        ext x
        exact Representation.IntertwiningMap.isIntertwining _ _
          (tensorComparison φ ψ hψ he s Φ) h x }

private theorem tensorComparisonHom_apply (x : ⨂[ℤ] _ : G ⧸ U.toSubgroup, A.V) :
    (tensorComparisonHom φ ψ hψ he s Φ).hom x =
      PiTensorProduct.map (fun _ ↦ Φ.toLinearMap)
        (PiTensorProduct.reindex ℤ (fun _ ↦ A.V) e.symm x) :=
  LinearMap.congr_fun (tensorComparison_toLinearMap φ ψ hψ he s Φ) x

end Comparison

section Resolution

-- Tensor induction uses the direct-sum scalar action of the total resolution, rather than
-- the fallback integer action on its underlying additive group.
private noncomputable local instance (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] : Module ℤ (trivialF2 K).gradedResolutionModule :=
  @DirectSum.instModule ℤ _ ℕ
    (fun n ↦ (TopRep.resolutionX (trivialF2 K) (n + 1)).V)
    (fun _ ↦ inferInstance) (fun n ↦ (TopRep.resolutionX (trivialF2 K) (n + 1)).hV2)

/-- The trivial `𝔽₂` coefficients, as a smooth discrete representation. -/
private noncomputable abbrev coeffs (K : Type u) [Group K] [TopologicalSpace K] :
    SmoothDiscreteTopRep.{0, u, u} ℤ K :=
  ⟨trivialF2 K, isSmoothDiscrete_trivialF2 K⟩

/-- The total resolution of the coefficients, as the discrete representation that is
tensor-induced. -/
private noncomputable abbrev resolutionRep (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] : DiscreteRep.{0, u, u} ℤ K :=
  (ofSmoothDiscrete ℤ K).obj (smoothGradedResolutionFunctor.obj (coeffs K))

/-- Pulling back along `ψ`, as an intertwining map of the coefficients. -/
private noncomputable def coeffPullback :
    Representation.IntertwiningMap
      ((DiscreteRep.trivialF2 U.toSubgroup).ρ.comp (ψ : V.toSubgroup →* U.toSubgroup))
      (DiscreteRep.trivialF2 V.toSubgroup).ρ where
  toLinearMap := ((trivialF2Equiv U.toSubgroup).trans
    (trivialF2Equiv V.toSubgroup).symm).toIntLinearEquiv
      (modM := (DiscreteRep.trivialF2 U.toSubgroup).module)
      (modM₂ := (DiscreteRep.trivialF2 V.toSubgroup).module).toLinearMap
  isIntertwining' v := by
    ext x
    exact congrArg _ (congrArg _ (trivialF2_ρ_apply_apply U.toSubgroup _ x)) |>.trans
      (trivialF2_ρ_apply_apply V.toSubgroup v _).symm

/-- Pulling back along `ψ` does not change the underlying element of `𝔽₂`. -/
private theorem coeffPullback_apply (a : (DiscreteRep.trivialF2 U.toSubgroup).V) :
    trivialF2Equiv V.toSubgroup (coeffPullback ψ a) = trivialF2Equiv U.toSubgroup a :=
  (trivialF2Equiv V.toSubgroup).apply_symm_apply _

variable [CompactSpace U.toSubgroup] [CompactSpace V.toSubgroup]

/-- Pulling back along `ψ`, as an intertwining map of the total resolutions. -/
private noncomputable def resolutionPullback :
    Representation.IntertwiningMap
      ((resolutionRep U.toSubgroup).ρ.comp (ψ : V.toSubgroup →* U.toSubgroup))
      (resolutionRep V.toSubgroup).ρ where
  toLinearMap := TopRep.gradedResolutionMap ψ (eqToHom (res_trivialF2_hom _))
  isIntertwining' v := by
    ext x
    exact TopRep.gradedResolutionMap_equivariant ψ _ v x

/-- Pulling back along `ψ` carries the augmentation of the coefficients of `U` to that of `V`. -/
private theorem resolutionPullback_augmentation (a : (DiscreteRep.trivialF2 U.toSubgroup).V) :
    resolutionPullback ψ ((trivialF2 U.toSubgroup).gradedResolutionAugmentation a) =
      (trivialF2 V.toSubgroup).gradedResolutionAugmentation (coeffPullback ψ a) := by
  refine (TopRep.gradedResolutionMap_augmentation ψ _ a).trans (congrArg _ ?_)
  apply (trivialF2Equiv V.toSubgroup).injective
  exact ((congrArg (trivialF2Equiv V.toSubgroup) (TopRep.eqToHom_hom_apply
    (res_trivialF2_hom (ψ : V.toSubgroup →* U.toSubgroup)) a)).trans
    (trivialF2Equiv_cast U.toSubgroup _ a)).trans
    (coeffPullback_apply ψ a).symm

/-- Pulling back along `ψ` carries an included homogeneous cochain to the included pullback of
the cochain. -/
private theorem resolutionPullback_cochainToGradedResolution {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n) :
    resolutionPullback ψ ((trivialF2 U.toSubgroup).cochainToGradedResolution n z) =
      (trivialF2 V.toSubgroup).cochainToGradedResolution n
        (((ContinuousCohomology.cochainsMap ψ (eqToHom (res_trivialF2_hom _))).f n).hom z) := by
  classical
  rw [TopRep.cochainToGradedResolution_apply, TopRep.cochainToGradedResolution_apply]
  exact TopRep.gradedResolutionMap_lof ψ _ n _

variable [U.toSubgroup.FiniteIndex] [V.toSubgroup.FiniteIndex]

/-- The comparison of the tensor-induced total resolutions carries the diagonal tensor of an
included cochain to the diagonal tensor of its pullback. -/
private theorem resolutionComparison_tprod {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n) :
    (tensorComparisonHom φ ψ hψ he s (resolutionPullback ψ)).hom
        (PiTensorProduct.tprod ℤ fun _ ↦ (trivialF2 U.toSubgroup).cochainToGradedResolution n z) =
      PiTensorProduct.tprod ℤ fun _ ↦ (trivialF2 V.toSubgroup).cochainToGradedResolution n
        (((ContinuousCohomology.cochainsMap ψ (eqToHom (res_trivialF2_hom _))).f n).hom z) :=
  (tensorComparisonHom_apply φ ψ hψ he s _ _).trans <|
    ((congrArg _ (PiTensorProduct.reindex_tprod _ _)).trans (PiTensorProduct.map_tprod _ _)).trans
      (congrArg _ (funext fun _ ↦ resolutionPullback_cochainToGradedResolution ψ z))

variable [Fintype (G ⧸ U.toSubgroup)] [Fintype (H ⧸ V.toSubgroup)]

/-- The comparison of the tensor-induced total resolutions preserves the total degree. -/
private theorem isHomogeneous_resolutionComparison :
    TauCeti.LinearMap.IsHomogeneous
      (tensorComparisonHom φ ψ hψ he s (resolutionPullback ψ)).hom.toLinearMap
      (smoothTensorInducedGradedResolutionPiece U.toSubgroup U.isOpen' (s.map (φ : H →* G) e he)
        (coeffs U.toSubgroup))
      (smoothTensorInducedGradedResolutionPiece V.toSubgroup V.isOpen' s
        (coeffs V.toSubgroup)) 0 := by
  have h1 := PiTensorProduct.isHomogeneous_reindex (R := ℤ)
    (M := fun _ ↦ (resolutionRep U.toSubgroup).V)
    (ℳ := fun _ ↦ (trivialF2 U.toSubgroup).gradedResolutionPiece) e.symm
  have h2 := PiTensorProduct.isHomogeneous_map (ι := H ⧸ V.toSubgroup)
    (ℳ := fun _ ↦ (trivialF2 V.toSubgroup).gradedResolutionPiece)
    (𝒩 := fun _ ↦ (trivialF2 U.toSubgroup).gradedResolutionPiece)
    (g := fun _ ↦ (resolutionPullback ψ).toLinearMap)
    (fun _ ↦ TopRep.isHomogeneous_gradedResolutionMap ψ (eqToHom (res_trivialF2_hom _)))
  rw [Finset.sum_const_zero] at h2
  have h := h2.comp h1
  rw [add_zero] at h
  exact TauCeti.LinearMap.isHomogeneous_def.2 fun p x hx ↦
    (congrArg (· ∈ _) (tensorComparisonHom_apply φ ψ hψ he s _ x)).mpr (h.map_mem hx)

/-- The comparison of the tensor-induced total resolutions commutes with the differentials: both
are slot sums of the total differential, which commutes with relabelling the factors and with
pulling back along `ψ`. -/
private theorem resolutionComparison_differential :
    (TopRep.resFunctor (φ : H →* G)).map
        (smoothTensorInducedGradedResolutionDifferential U.toSubgroup U.isOpen'
          (s.map (φ : H →* G) e he) (coeffs U.toSubgroup)).hom ≫
      tensorComparisonHom φ ψ hψ he s (resolutionPullback ψ) =
    tensorComparisonHom φ ψ hψ he s (resolutionPullback ψ) ≫
      (smoothTensorInducedGradedResolutionDifferential V.toSubgroup V.isOpen' s
        (coeffs V.toSubgroup)).hom := by
  classical
  have hΨ : (trivialF2 V.toSubgroup).gradedResolutionDifferential ∘ₗ
      (resolutionPullback ψ).toLinearMap =
        (resolutionPullback ψ).toLinearMap ∘ₗ
          (trivialF2 U.toSubgroup).gradedResolutionDifferential :=
    LinearMap.ext fun x ↦ (TopRep.gradedResolutionMap_differential ψ _ x).symm
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro x
  have h := (LinearMap.congr_fun (PiTensorProduct.slotSum_comp_map (ι := H ⧸ V.toSubgroup)
    (fun _ ↦ (resolutionPullback ψ).toLinearMap) fun _ ↦ hΨ)
    (PiTensorProduct.reindex ℤ (fun _ ↦ (resolutionRep U.toSubgroup).V) e.symm x)).symm
  have h' := LinearMap.congr_fun (PiTensorProduct.slotSum_comp_reindex
    (fun _ : G ⧸ U.toSubgroup ↦ (trivialF2 U.toSubgroup).gradedResolutionDifferential) e.symm) x
  simp only [LinearMap.comp_apply] at h h'
  -- Composition in `TopRep` evaluates to composition of the underlying maps.
  change (tensorComparisonHom φ ψ hψ he s (resolutionPullback ψ)).hom
      ((smoothTensorInducedGradedResolutionDifferential U.toSubgroup U.isOpen'
        (s.map (φ : H →* G) e he) (coeffs U.toSubgroup)).hom.hom x) =
    (smoothTensorInducedGradedResolutionDifferential V.toSubgroup V.isOpen' s
      (coeffs V.toSubgroup)).hom.hom
        ((tensorComparisonHom φ ψ hψ he s (resolutionPullback ψ)).hom x)
  rw [smoothTensorInducedGradedResolutionDifferential_apply]
  exact (tensorComparisonHom_apply φ ψ hψ he s _ _).trans <|
    (congrArg (PiTensorProduct.map fun _ ↦ (resolutionPullback ψ).toLinearMap) h'.symm).trans <|
      h.trans <| (congrArg _ (tensorComparisonHom_apply φ ψ hψ he s _ x).symm).trans
        (smoothTensorInducedGradedResolutionDifferential_apply V.toSubgroup V.isOpen' s
          (coeffs V.toSubgroup) _).symm

/-- Every element of the trivial `𝔽₂` coefficients is its own additive inverse. -/
private theorem trivialF2_add_self (K : Type u) [Group K] [TopologicalSpace K]
    (a : (coeffs K).obj.V) : a + a = 0 := by
  simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero K a

/-- The comparison of the tensor-induced total resolutions lies over the comparison of the
tensor-induced coefficients: it carries the augmentation of the contraction for `U` to that for
`V`. -/
private theorem resolutionComparison_ι [LinearOrder (G ⧸ U.toSubgroup)]
    [LinearOrder (H ⧸ V.toSubgroup)]
    (x : ((toSmoothDiscrete ℤ G).obj (DiscreteRep.tensorInduced U.toSubgroup U.isOpen'
      (s.map (φ : H →* G) e he) (DiscreteRep.trivialF2 U.toSubgroup))).obj.V) :
    (tensorComparisonHom φ ψ hψ he s (resolutionPullback ψ)).hom
        ((smoothTensorInducedGradedResolutionContraction U.toSubgroup U.isOpen'
          (s.map (φ : H →* G) e he) (coeffs U.toSubgroup)
          (trivialF2_add_self U.toSubgroup)).ι.hom x).1 =
      ((smoothTensorInducedGradedResolutionContraction V.toSubgroup V.isOpen' s
          (coeffs V.toSubgroup) (trivialF2_add_self V.toSubgroup)).ι.hom
        ((tensorComparisonHom φ ψ hψ he s (coeffPullback ψ)).hom x)).1 := by
  have key : PiTensorProduct.map (fun _ ↦ (resolutionPullback ψ).toLinearMap) ∘ₗ
      (PiTensorProduct.reindex ℤ (fun _ ↦ (resolutionRep U.toSubgroup).V) e.symm).toLinearMap ∘ₗ
        PiTensorProduct.map (fun _ ↦ (coeffs U.toSubgroup).obj.gradedResolutionAugmentation) =
      PiTensorProduct.map (fun _ ↦ (coeffs V.toSubgroup).obj.gradedResolutionAugmentation) ∘ₗ
        PiTensorProduct.map (fun _ ↦ (coeffPullback ψ).toLinearMap) ∘ₗ
          (PiTensorProduct.reindex ℤ (fun _ ↦ (DiscreteRep.trivialF2 U.toSubgroup).V)
            e.symm).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    -- Both sides are the pure tensor of the augmented, pulled-back factors, relabelled along `e`.
    refine ((congrArg _ ((congrArg _ (PiTensorProduct.map_tprod _ m)).trans
      (PiTensorProduct.reindex_tprod _ _))).trans (PiTensorProduct.map_tprod _ _)).trans ?_
    refine Eq.trans ?_ ((congrArg _ ((congrArg _ (PiTensorProduct.reindex_tprod _ m)).trans
      (PiTensorProduct.map_tprod _ _))).trans (PiTensorProduct.map_tprod _ _)).symm
    exact congrArg _ (funext fun i ↦ resolutionPullback_augmentation ψ _)
  rw [smoothTensorInducedGradedResolutionContraction_ι_apply,
    smoothTensorInducedGradedResolutionContraction_ι_apply]
  exact (tensorComparisonHom_apply φ ψ hψ he s _ _).trans ((LinearMap.congr_fun key x).trans
    (congrArg _ (tensorComparisonHom_apply φ ψ hψ he s _ x).symm))

omit [CompactSpace U.toSubgroup] [CompactSpace V.toSubgroup] [Fintype (G ⧸ U.toSubgroup)]
  [Fintype (H ⧸ V.toSubgroup)] in
/-- The comparison of the tensor-induced coefficients lies over the identity of `𝔽₂`: both
identifications with the trivial coefficients multiply the tensor factors, and relabelling the
factors along `e` does not change their product. -/
private theorem coeffComparison_trivialF2Iso :
    (TopRep.resFunctor (φ : H →* G)).map
        (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen'
          (s.map (φ : H →* G) e he)).hom.hom ≫
      eqToHom (res_trivialF2_hom (φ : H →* G)) =
    tensorComparisonHom φ ψ hψ he s (coeffPullback ψ) ≫
      (smoothTensorInducedTrivialF2Iso H V.toSubgroup V.isOpen' s).hom.hom := by
  classical
  -- Instance search would pick `AddCommGroup.toIntModule` on the target carrier, which is not
  -- the module structure of the topological representation.
  let : Module ℤ (trivialF2 H).V := TopRep.hV2 _
  refine TopRep.hom_ext (ContIntertwiningMap.ext (ContinuousLinearMap.ext fun x ↦ ?_))
  -- Composition in `TopRep` evaluates to composition of the underlying maps.
  change (eqToHom (res_trivialF2_hom (φ : H →* G))).hom
      ((smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen'
        (s.map (φ : H →* G) e he)).hom.hom.hom x) =
    (smoothTensorInducedTrivialF2Iso H V.toSubgroup V.isOpen' s).hom.hom.hom
      ((tensorComparisonHom φ ψ hψ he s (coeffPullback ψ)).hom x)
  apply (trivialF2Equiv H).injective
  refine ((congrArg (trivialF2Equiv H) (TopRep.eqToHom_hom_apply
    (res_trivialF2_hom (φ : H →* G)) _)).trans (trivialF2Equiv_cast G _ _)).trans ?_
  -- Both sides are additive in `x`; on a pure tensor both multiply the factors.
  have htprod (m : G ⧸ U.toSubgroup → (DiscreteRep.trivialF2 U.toSubgroup).V) :
      trivialF2Equiv G ((smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen'
          (s.map (φ : H →* G) e he)).hom.hom.hom (PiTensorProduct.tprod ℤ m)) =
        trivialF2Equiv H ((smoothTensorInducedTrivialF2Iso H V.toSubgroup V.isOpen' s).hom.hom.hom
          ((tensorComparisonHom φ ψ hψ he s (coeffPullback ψ)).hom
            (PiTensorProduct.tprod ℤ m))) := by
    have hm : (tensorComparisonHom φ ψ hψ he s (coeffPullback ψ)).hom
        (PiTensorProduct.tprod ℤ m) = PiTensorProduct.tprod ℤ fun j ↦ coeffPullback ψ (m (e j)) :=
      (tensorComparisonHom_apply φ ψ hψ he s _ _).trans
        ((congrArg _ (PiTensorProduct.reindex_tprod _ m)).trans (PiTensorProduct.map_tprod _ _))
    rw [hm, smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod,
      smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod]
    -- The identification of the coefficients of `G` multiplies over its own enumeration of the
    -- cosets, which `convert` identifies with ours.
    convert (Fintype.prod_equiv e
      (fun j ↦ trivialF2Equiv V.toSubgroup (coeffPullback ψ (m (e j))))
      (fun i ↦ trivialF2Equiv U.toSubgroup (m i)) fun j ↦ coeffPullback_apply ψ (m (e j))).symm
      using 3
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    -- Absorb the scalar into one factor, so that the pure-tensor case applies.
    obtain ⟨i⟩ := (inferInstance : Nonempty (G ⧸ U.toSubgroup))
    have hr := (PiTensorProduct.tprod ℤ).map_update_smul m i r (m i)
    rw [Function.update_eq_self] at hr
    rw [← hr]
    exact htprod _
  | add x y hx hy =>
    refine ((congrArg (trivialF2Equiv G) (map_add _ x y)).trans (map_add _ _ _)).trans ?_
    refine Eq.trans ?_ ((congrArg (trivialF2Equiv H) ((congrArg _ (map_add _ x y)).trans
      (map_add _ _ _))).trans (map_add _ _ _)).symm
    exact congrArg₂ (· + ·) hx hy

end Resolution

/-- A class read on a graded contracted complex, in two equal degrees. -/
private theorem coeffMap_gradedCohomologyClass_degreeCast {R : Type} [Ring R] [TopologicalSpace R]
    {X Y M : TopRep.{u} R G} {ℳ : ℤ → Submodule R M.V} {hρ : ∀ n g x, x ∈ ℳ n → M.ρ g x ∈ ℳ n}
    {d : M ⟶ M} {hd : TauCeti.LinearMap.IsHomogeneous d.hom.toLinearMap ℳ ℳ 1} {hdd : d ≫ d = 0}
    (c : TopRep.ResolutionContraction X (M.gradedCochainComplex ℳ hρ d hd hdd))
    (b : X ⟶ Y) {k k' : ℕ} (h : k = k') {z z' : M.V} (hzz : z' = z) (hz : z ∈ ℳ k)
    (hz' : z' ∈ ℳ k') (hinv : ∀ g, M.ρ g z = z) (hinv' : ∀ g, M.ρ g z' = z') (hdz : d.hom z = 0)
    (hdz' : d.hom z' = 0) :
    ContinuousCohomology.coeffMap b k' (c.gradedCohomologyClass z' hz' hinv' hdz') =
      (ContinuousCohomology.degreeCast Y h).hom
        (ContinuousCohomology.coeffMap b k (c.gradedCohomologyClass z hz hinv hdz)) := by
  subst h hzz
  simp

variable [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup] [Fintype (G ⧸ U.toSubgroup)]
  [V.toSubgroup.FiniteIndex] [CompactSpace V.toSubgroup] [Fintype (H ⧸ V.toSubgroup)]

include hψ he in
/-- **Naturality of the Evens norm.** Let `φ : H → G` be a continuous homomorphism restricting to
`ψ : V → U` on compact open subgroups of finite index, and inducing a bijection
`e : H ⧸ V ≃ G ⧸ U`. Then pulling back the norm `N_U^G x` along `φ` gives the norm of the
pullback of `x` along `ψ`: `φ^* (N_U^G x) = N_V^H (ψ^* x)`, after transporting the degree
`[H : V] n` to `[G : U] n`. -/
theorem trivialF2Map_evensNorm {n : ℕ} (x : continuousCohomology n (trivialF2 U.toSubgroup)) :
    trivialF2Map φ (Fintype.card (G ⧸ U.toSubgroup) * n) (U.evensNorm x) =
      (ContinuousCohomology.degreeCast (trivialF2 H)
        (by rw [Fintype.card_congr e])).hom (V.evensNorm (trivialF2Map ψ n x)) := by
  classical
  obtain ⟨z, hz, rfl⟩ := TopRep.exists_cochainClass_eq x
  let s : V.toSubgroup.LeftTransversal := default
  let : LinearOrder (G ⧸ U.toSubgroup) :=
    LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U.toSubgroup)).injective
  let : LinearOrder (H ⧸ V.toSubgroup) :=
    LinearOrder.lift' _ (Fintype.equivFin (H ⧸ V.toSubgroup)).injective
  have : LocallyCompactSpace H :=
    (isCompact_iff_compactSpace.2
      ‹CompactSpace V.toSubgroup›).locallyCompactSpace_of_mem_nhds_of_group
        (V.isOpen'.mem_nhds V.one_mem)
  rw [evensNorm_cochainClass U (s.map (φ : H →* G) e he), trivialF2Map_def ψ,
    TauCeti.ContinuousCohomology.map_cochainClass, evensNorm_cochainClass V s,
    tensorNormCocycleClass_def, tensorNormCocycleClass_def, smoothTensorInducedDiagonalClass_eq,
    smoothTensorInducedDiagonalClass_eq]
  -- Pulling back along `φ` commutes with the identifications of the tensor-induced coefficients.
  have hsq := TauCeti.ContinuousCohomology.map_comp_coeffMap φ
    (tensorComparisonHom φ ψ hψ he s (coeffPullback ψ)) (eqToHom (res_trivialF2_hom (φ : H →* G)))
    (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' (s.map (φ : H →* G) e he)).hom.hom
    (smoothTensorInducedTrivialF2Iso H V.toSubgroup V.isOpen' s).hom.hom
    (coeffComparison_trivialF2Iso φ ψ hψ he s) (Fintype.card (G ⧸ U.toSubgroup) * n)
  rw [trivialF2Map_def]
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans <|
    (ConcreteCategory.congr_hom hsq.symm _).trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  -- The comparison of the tensor-induced resolutions lies over the comparison of the
  -- coefficients and carries the diagonal tensor of `z` to that of its pullback.
  refine (congrArg (ContinuousCohomology.coeffMap
    (smoothTensorInducedTrivialF2Iso H V.toSubgroup V.isOpen' s).hom.hom _)
    (TopRep.ResolutionContraction.map_gradedCohomologyClass φ _ _ _
      (tensorComparisonHom φ ψ hψ he s (resolutionPullback ψ))
      (isHomogeneous_resolutionComparison φ ψ hψ he s)
      (resolutionComparison_differential φ ψ hψ he s)
      (resolutionComparison_ι φ ψ hψ he s) _ _ _)).trans ?_
  exact coeffMap_gradedCohomologyClass_degreeCast _ _ (by rw [Fintype.card_congr e])
    (resolutionComparison_tprod φ ψ hψ he s z) _ _ _ _ _ _

omit [V.toSubgroup.FiniteIndex] [CompactSpace V.toSubgroup] [Fintype (H ⧸ V.toSubgroup)] in
/-- **The Evens norm commutes with inflation.** For a normal subgroup `N` contained in `U`,
inflating to `G` the norm from the image `U / N` of `U` in `G ⧸ N` gives the norm from `U` of the
inflated class: `infl (N_{U/N}^{G/N} x) = N_U^G (infl x)`, after transporting the degree along
`[G ⧸ N : U / N] = [G : U]`. -/
theorem trivialF2Map_quotientMkContinuousMonoidHom_evensNorm {N : Subgroup G} [N.Normal]
    (hNU : N ≤ U.toSubgroup)
    [(Subgroup.quotientOpenSubgroup N U).toSubgroup.FiniteIndex]
    [CompactSpace (Subgroup.quotientOpenSubgroup N U).toSubgroup]
    [Fintype ((G ⧸ N) ⧸ (Subgroup.quotientOpenSubgroup N U).toSubgroup)] {n : ℕ}
    (x : continuousCohomology n (trivialF2 (Subgroup.quotientOpenSubgroup N U).toSubgroup)) :
    trivialF2Map (Subgroup.quotientMkContinuousMonoidHom N)
        (Fintype.card ((G ⧸ N) ⧸ (Subgroup.quotientOpenSubgroup N U).toSubgroup) * n)
        ((Subgroup.quotientOpenSubgroup N U).evensNorm x) =
      (ContinuousCohomology.degreeCast (trivialF2 G)
        (by rw [Fintype.card_congr ((QuotientGroup.quotientEquivQuotientMapOfLE hNU).trans
          (Subgroup.quotientEquivOfEq
            (Subgroup.toSubgroup_quotientOpenSubgroup N U).symm))])).hom
        (U.evensNorm (trivialF2Map ⟨Subgroup.quotientOpenSubgroupMap N U,
          Subgroup.continuous_quotientOpenSubgroupMap N U⟩ n x)) :=
  trivialF2Map_evensNorm (U := Subgroup.quotientOpenSubgroup N U) (V := U)
    (Subgroup.quotientMkContinuousMonoidHom N)
    ⟨Subgroup.quotientOpenSubgroupMap N U, Subgroup.continuous_quotientOpenSubgroupMap N U⟩
    (fun u ↦ (Subgroup.coe_quotientOpenSubgroupMap N U u).trans
      (Subgroup.quotientMkContinuousMonoidHom_apply N u).symm)
    (e := (QuotientGroup.quotientEquivQuotientMapOfLE hNU).trans
      (Subgroup.quotientEquivOfEq (Subgroup.toSubgroup_quotientOpenSubgroup N U).symm))
    (fun g ↦ by
      rw [Equiv.trans_apply, QuotientGroup.quotientEquivQuotientMapOfLE_mk,
        Subgroup.quotientEquivOfEq_mk, Subgroup.quotientMkContinuousMonoidHom_apply]) x

end OpenSubgroup
