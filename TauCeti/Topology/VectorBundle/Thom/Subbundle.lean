/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Subbundle
public import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv

/-!
# Thom pairs of subbundles spanned by local frames, in every universe

Let `V` be a family of subspaces of the fibres of a real vector bundle `E → B`. With the topology
of a subspace of the total space of `E` (`TauCeti.subbundleTopology`), its total space does not
depend on the model-fibre parameter, so the identity of the fibres identifies the Thom pairs
`(V, V₀)` for any two model fibres (`TauCeti.subbundleThomPairIso`).

When `V` has continuous local frames indexed by a finite type `ι` near every point
(`TauCeti.HasLocalSubbundleFrames`), it is a vector bundle with model fibre `ι → ℝ`
(`TauCeti.HasLocalSubbundleFrames.vectorBundle`). For `ι = Fin r` this model fibre lies in `Type`,
while the base and the fibres may lie in any universe `w`, and the vanishing of the homology of a
Thom pair below the rank (`TauCeti.isZero_singularHomology_thomPair`) needs the model fibre in the
universe `w`. The same subspaces also have local frames indexed by `ULift ι`
(`TauCeti.HasLocalSubbundleFrames.of_equiv`), which make them a vector bundle with model fibre
`ULift ι → ℝ` in the universe `w`, and `TauCeti.subbundleThomPairIso` transports the vanishing back.

## Main results

* `TauCeti.continuous_subbundle_mk'_refl`: the identity of the fibres is continuous between the
  total spaces of `V` for two model-fibre parameters.
* `TauCeti.subbundleThomPairIso`: the Thom pair of a family of subspaces does not depend on the
  model-fibre parameter.
* `TauCeti.isZero_singularHomology_thomPair_of_hasLocalSubbundleFrames`: the homology of the Thom
  pair of a subbundle spanned by local frames vanishes below the rank, over any base.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module

universe w v u

namespace TauCeti

section ThomPair

variable {B : Type w} [TopologicalSpace B] (F : Type*) {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] (V : Π b, Submodule ℝ (E b)) (F₁ F₂ : Type*)

omit [TopologicalSpace B] in
/-- The identity of the fibres of a family `V` of subspaces of the fibres of `E` is continuous
from the total space of `V` for the model-fibre parameter `F₁` to the one for `F₂`, both with the
topology induced from the total space of `E` (`TauCeti.subbundleTopology`). It is stated with the
identity equivalences of the fibres, in the form taken by `TauCeti.thomPairMapOfFiberwise`. -/
theorem continuous_subbundle_mk'_refl :
    letI := subbundleTopology F (F' := F₁) V
    letI := subbundleTopology F (F' := F₂) V
    Continuous fun v : TotalSpace F₁ (fun b ↦ V b) ↦
      TotalSpace.mk' F₂ (E := fun b ↦ V b) v.proj (ContinuousLinearEquiv.refl ℝ (V v.proj) v.snd) :=
  letI := subbundleTopology F (F' := F₁) V
  letI := subbundleTopology F (F' := F₂) V
  (isEmbedding_totalSpace_subbundle F F₂ V).continuous_iff.2 <| by
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_refl', id] using
      (isEmbedding_totalSpace_subbundle F F₁ V).continuous

/-- **The Thom pair of a family of subspaces does not depend on the model fibre.** For a family `V`
of subspaces of the fibres of `E`, the total spaces for two model-fibre parameters `F₁` and `F₂`
both carry the topology induced from the total space of `E` (`TauCeti.subbundleTopology`), so the
identity of the fibres is an isomorphism between the Thom pairs `(V, V₀)` for `F₁` and for `F₂`. -/
def subbundleThomPairIso :
    letI := subbundleTopology F (F' := F₁) V
    letI := subbundleTopology F (F' := F₂) V
    thomPair F₁ (fun b ↦ V b) ≅ thomPair F₂ (fun b ↦ V b) :=
  letI := subbundleTopology F (F' := F₁) V
  letI := subbundleTopology F (F' := F₂) V
  have h₁₂ := continuous_subbundle_mk'_refl F V F₁ F₂
  have h₂₁ := continuous_subbundle_mk'_refl F V F₂ F₁
  { hom := thomPairMapOfFiberwise (g := ContinuousMap.id B)
      (φ := fun b ↦ ContinuousLinearEquiv.refl ℝ (V b)) h₁₂
    inv := thomPairMapOfFiberwise (g := ContinuousMap.id B)
      (φ := fun b ↦ ContinuousLinearEquiv.refl ℝ (V b)) h₂₁
    -- Each composite sends `v` to `⟨v.proj, refl (refl v.snd)⟩`, which is `v` by
    -- `ContinuousLinearEquiv.refl_apply` and `TotalSpace.eta`.
    hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
      ((congrArg _ (thomPairMapOfFiberwise_fst_apply h₁₂ v)).trans
        (thomPairMapOfFiberwise_fst_apply h₂₁ _)).trans <|
        (congrArg (TotalSpace.mk' F₁ v.proj)
          ((ContinuousLinearEquiv.refl_apply ℝ (V v.proj) _).trans
            (ContinuousLinearEquiv.refl_apply ℝ (V v.proj) _))).trans (TotalSpace.eta v))
    inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
      ((congrArg _ (thomPairMapOfFiberwise_fst_apply h₂₁ v)).trans
        (thomPairMapOfFiberwise_fst_apply h₁₂ _)).trans <|
        (congrArg (TotalSpace.mk' F₂ v.proj)
          ((ContinuousLinearEquiv.refl_apply ℝ (V v.proj) _).trans
            (ContinuousLinearEquiv.refl_apply ℝ (V v.proj) _))).trans (TotalSpace.eta v)) }

/-- The isomorphism `subbundleThomPairIso` is the identity on vectors. -/
@[simp]
theorem subbundleThomPairIso_hom_fst_apply
    (v : letI := subbundleTopology F (F' := F₁) V
      (thomPair F₁ fun b ↦ V b).fst) :
    letI := subbundleTopology F (F' := F₁) V
    letI := subbundleTopology F (F' := F₂) V
    TopPair.Hom.fst (subbundleThomPairIso F V F₁ F₂).hom v =
      TotalSpace.mk' F₂ (E := fun b ↦ V b) v.proj v.snd :=
  letI := subbundleTopology F (F' := F₁) V
  letI := subbundleTopology F (F' := F₂) V
  thomPairMapOfFiberwise_fst_apply _ v

/-- The inverse of `subbundleThomPairIso` is the identity on vectors. -/
@[simp]
theorem subbundleThomPairIso_inv_fst_apply
    (v : letI := subbundleTopology F (F' := F₂) V
      (thomPair F₂ fun b ↦ V b).fst) :
    letI := subbundleTopology F (F' := F₁) V
    letI := subbundleTopology F (F' := F₂) V
    TopPair.Hom.fst (subbundleThomPairIso F V F₁ F₂).inv v =
      TotalSpace.mk' F₁ (E := fun b ↦ V b) v.proj v.snd :=
  letI := subbundleTopology F (F' := F₁) V
  letI := subbundleTopology F (F' := F₂) V
  thomPairMapOfFiberwise_fst_apply _ v

end ThomPair

section Vanishing

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] {V : Π b, Submodule ℝ (E b)}

/-- **The homology of the Thom pair of a subbundle spanned by local frames vanishes below the
rank.** For a family `V` of subspaces of the fibres of a real vector bundle with continuous local
frames indexed by a finite type `ι` near every point, the relative homology of `(V, V₀)` vanishes in
degrees below `card ι`, with coefficients in an abelian category with exact filtered colimits. The
base is arbitrary, and the base and the fibres lie in any common universe, although the model fibre
`ι → ℝ` lies in `Type`. -/
theorem isZero_singularHomology_thomPair_of_hasLocalSubbundleFrames
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]
    (hV : HasLocalSubbundleFrames F ι V) (R : C) {n : ℕ} (hn : n < Fintype.card ι) :
    letI := subbundleTopology F (F' := ι → ℝ) V
    IsZero ((thomPair (ι → ℝ) fun b ↦ V b).singularHomology R n) := by
  let _ := subbundleTopology F (F' := ι → ℝ) V
  -- The same subspaces form a vector bundle with model fibre `ULift ι → ℝ`, in the universe `w`.
  have hV' := hV.of_equiv Equiv.ulift.{w}.symm
  let _ := subbundleTopology F (F' := ULift.{w} ι → ℝ) V
  let _ := hV'.fiberBundle
  have := hV'.vectorBundle
  exact (TauCeti.isZero_singularHomology_thomPair (F := ULift.{w} ι → ℝ) (E := fun b ↦ V b) R
    (by simpa using hn)).of_iso (TopPair.singularHomologyMapIso R (subbundleThomPairIso F V _ _) n)

end Vanishing

end TauCeti
