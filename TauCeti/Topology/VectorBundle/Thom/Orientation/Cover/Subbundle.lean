/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Subbundle
public import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.Descent

/-!
# The twisted Thom isomorphism for subbundles spanned by local frames, in every universe

Let `E → B` be a real vector bundle over a compact base and let `V` be a family of subspaces of its
fibres with continuous local frames indexed by a finite type `ι` near every point
(`TauCeti.HasLocalSubbundleFrames`). With the topology of a subspace of the total space of `E`,
`V` is a vector bundle with model fibre `ι → ℝ` (`TauCeti.HasLocalSubbundleFrames.vectorBundle`).
For every commutative ring `k`, `ℤ` included, this file gives its Thom isomorphism with
coefficients twisted by its orientation local system `o(V)`, with no orientation of `V`:

`Hₚ₊ᵣ(V, V₀; k) ≅ Hₚ(B; o(V) ⊗ k)`, where `r = card ι`

(`nonempty_singularHomology_thomPair_iso_twistedHomology_of_hasLocalSubbundleFrames`, in the
namespace `TauCeti.VectorBundleOrientationCover`).

The Thom isomorphism over a compact base
(`nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`, in the same namespace)
needs the model fibre in the universe of the base and of the fibres. For `ι = Fin r` the model
fibre `Fin r → ℝ` lies in `Type`, while the base and the fibres may lie in any universe `w`. The
same subspaces also have local frames indexed by `ULift ι`
(`TauCeti.HasLocalSubbundleFrames.of_equiv`), which make them a vector bundle with model fibre
`ULift ι → ℝ` in the universe `w`. The two bundle structures have the same total space and the
same topology, so the identity of the fibres identifies their Thom pairs
(`TauCeti.subbundleThomPairIso`) and their orientation local systems
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise`), and the Thom isomorphism
of the second structure is one of the first.

This is the form in which the negative normal bundles of the critical submanifolds of a Morse–Bott
function, which are spanned by local frames indexed by `Fin r`, enter the homology across a
critical level.

## Main results

* `TauCeti.subbundleThomPairIso`: the Thom pair of a family of subspaces does not depend on the
  model-fibre parameter.
* `TauCeti.isZero_singularHomology_thomPair_of_hasLocalSubbundleFrames`: the homology of the Thom
  pair of a subbundle spanned by local frames vanishes below the rank, over any base.
* `nonempty_singularHomology_thomPair_iso_twistedHomology_of_hasLocalSubbundleFrames`, in the
  namespace `TauCeti.VectorBundleOrientationCover`: over a compact base,
  `Hₚ₊ᵣ(V, V₀; k) ≅ Hₚ(B; o(V) ⊗ k)` for every commutative ring `k`, with the base, the fibres and
  `k` in any common universe.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module TauCeti.LocalCoefficientSystem

universe w v u

namespace TauCeti

section ThomPair

variable {B : Type w} [TopologicalSpace B] (F : Type*) {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] (V : Π b, Submodule ℝ (E b)) (F₁ F₂ : Type*)

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
  have h₁₂ : Continuous fun v : TotalSpace F₁ (fun b ↦ V b) ↦
      TotalSpace.mk' F₂ (E := fun b ↦ V b) v.proj (ContinuousLinearEquiv.refl ℝ (V v.proj) v.snd) :=
    (isEmbedding_totalSpace_subbundle F F₂ V).continuous_iff.2
      (isEmbedding_totalSpace_subbundle F F₁ V).continuous
  have h₂₁ : Continuous fun v : TotalSpace F₂ (fun b ↦ V b) ↦
      TotalSpace.mk' F₁ (E := fun b ↦ V b) v.proj (ContinuousLinearEquiv.refl ℝ (V v.proj) v.snd) :=
    (isEmbedding_totalSpace_subbundle F F₁ V).continuous_iff.2
      (isEmbedding_totalSpace_subbundle F F₂ V).continuous
  { hom := thomPairMapOfFiberwise (g := ContinuousMap.id B)
      (φ := fun b ↦ ContinuousLinearEquiv.refl ℝ (V b)) h₁₂
    inv := thomPairMapOfFiberwise (g := ContinuousMap.id B)
      (φ := fun b ↦ ContinuousLinearEquiv.refl ℝ (V b)) h₂₁
    hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
      (congrArg _ (thomPairMapOfFiberwise_fst_apply h₁₂ v)).trans
        (thomPairMapOfFiberwise_fst_apply h₂₁ _))
    inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
      (congrArg _ (thomPairMapOfFiberwise_fst_apply h₂₁ v)).trans
        (thomPairMapOfFiberwise_fst_apply h₁₂ _)) }

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

namespace VectorBundleOrientationCover

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] {V : Π b, Submodule ℝ (E b)}

/-- **The twisted Thom isomorphism for a subbundle spanned by local frames.** Let `E → B` be a real
vector bundle over a compact base, and let `V` be a family of subspaces of its fibres with
continuous local frames indexed by a finite type `ι` near every point, made a vector bundle of rank
`r = card ι` with model fibre `ι → ℝ` by the topology of a subspace of the total space of `E`. Let
`k` be any commutative ring, for instance `ℤ`. Then `Hₚ₊ᵣ(V, V₀; k) ≅ Hₚ(B; o(V) ⊗ k)` in every
degree `p`, where `o(V)` is the orientation local system of `V`. No orientation of `V` is assumed,
and the base, the fibres and `k` lie in any common universe, although the model fibre lies in
`Type`. -/
theorem nonempty_singularHomology_thomPair_iso_twistedHomology_of_hasLocalSubbundleFrames
    [CompactSpace B] (hV : HasLocalSubbundleFrames F ι V) (k : Type w) [CommRing k] (p : ℕ) :
    letI := subbundleTopology F (F' := ι → ℝ) V
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    Nonempty ((thomPair (ι → ℝ) fun b ↦ V b).singularHomology (ModuleCat.of k k)
        (p + Fintype.card ι) ≅
      twistedHomology (signLocalSystem (ι → ℝ) (fun b ↦ V b) k
        (finrank_fintype_fun_eq_card ℝ).symm) p) := by
  let _ := subbundleTopology F (F' := ι → ℝ) V
  let _ := hV.fiberBundle
  have := hV.vectorBundle
  -- The same subspaces form a vector bundle with model fibre `ULift ι → ℝ`, in the universe `w`.
  have hV' := hV.of_equiv Equiv.ulift.{w}.symm
  let _ := subbundleTopology F (F' := ULift.{w} ι → ℝ) V
  let _ := hV'.fiberBundle
  have := hV'.vectorBundle
  have hι' : Fintype.card ι = finrank ℝ (ULift.{w} ι → ℝ) := by simp
  obtain ⟨e⟩ := nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace
    (F := ULift.{w} ι → ℝ) (E := fun b ↦ V b) hι' k p
  -- The identity of the fibres identifies the orientation local systems of the two structures.
  have hφ : Continuous fun v : TotalSpace (ι → ℝ) (fun b ↦ V b) ↦
      TotalSpace.mk' (ULift.{w} ι → ℝ) (E := fun b ↦ V b) v.proj
        (ContinuousLinearEquiv.refl ℝ (V v.proj) v.snd) :=
    (isEmbedding_totalSpace_subbundle F (ULift.{w} ι → ℝ) V).continuous_iff.2
      (isEmbedding_totalSpace_subbundle F (ι → ℝ) V).continuous
  exact ⟨TopPair.singularHomologyMapIso _ (subbundleThomPairIso F V _ _) _ ≪≫
    eqToIso (by rw [hι']) ≪≫ e ≪≫ (HomologicalComplex.homologyFunctor _ _ p).mapIso
      (twistedChainComplexCoefficientIso (signLocalSystemIsoOfFiberwise k hι' _
        (φ := fun b ↦ ContinuousLinearEquiv.refl ℝ (V b)) hφ))⟩

end VectorBundleOrientationCover

end TauCeti
