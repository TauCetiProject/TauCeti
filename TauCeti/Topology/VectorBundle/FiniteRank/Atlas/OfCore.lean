/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback.Basic

/-!
# Fixed-rank embedding into variable-rank bundle atlases

Constant-rank point-indexed cores `C : FiniteRankBundleCore 𝕜 X` embed into variable-rank bundle
atlases via `ofCore C`, whose reconstructed total space is homeomorphic over `X` to
`C.core.TotalSpace` (`ofCoreTotalSpaceHomeomorph`). This induces the additive, faithful functor
`ofCoreFunctor 𝕜 X : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X`, which is unconditionally
fully faithful over a complete field (`fullyFaithfulOfCoreFunctor`) and whose essential image
consists precisely of the globally constant-rank atlases (`mem_essImage_ofCoreFunctor_iff`).

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology VectorBundleCore TauCeti.VariableRankBundle

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

section OfCore
variable (C : FiniteRankBundleCore 𝕜 X)
/-- Inclusion of the `m`-stratum of `LocallyConstant.const X C.rank` into `X`. -/
def constStratumInclusion (m : ℕ) : C({x : X // LocallyConstant.const X C.rank x = m}, X) :=
  ⟨Subtype.val, continuous_subtypeVal⟩
/-- Coordinate core on the `m`-stratum of `LocallyConstant.const X C.rank`: the pullback of `C`
when `C.rank = m`, and the trivial core on the empty stratum otherwise. -/
def constStratumCharts (m : ℕ) :
    VectorBundleCore 𝕜 {x : X // LocallyConstant.const X C.rank x = m} (Fin m → 𝕜)
      {x : X // LocallyConstant.const X C.rank x = m} :=
  let S := {x : X // LocallyConstant.const X C.rank x = m}
  if h : C.rank = m then
    h.rec (motive := fun k _ ↦ VectorBundleCore 𝕜 S (Fin k → 𝕜) S)
      (C.pullback (constStratumInclusion C m)).core
  else (FiniteRankBundleCore.trivial 𝕜 S m).core
@[simp] theorem constStratumCharts_self :
    constStratumCharts C C.rank = (C.pullback (constStratumInclusion C C.rank)).core :=
  dite_eq_left rfl

/-- Embed a constant-rank point-indexed core as a variable-rank bundle atlas of constant rank. -/
-- Expose the rank projection so `(ofCore C).Fiber` reduces to `C`'s coordinate fibre.
@[expose, implicit_reducible] def ofCore : FiniteRankAtlas 𝕜 X where
  rank := LocallyConstant.const X C.rank
  charts := constStratumCharts C
  indexAt_eq m x := by
    by_cases h : C.rank = m
    · subst h; rw [constStratumCharts_self C]
      exact (C.pullback (constStratumInclusion C C.rank)).indexAt_eq x
    · exact False.elim (h x.property)
@[simp] theorem rank_ofCore : (ofCore C).rank = LocallyConstant.const X C.rank := by rfl
theorem rank_ofCore_apply (x : X) : (ofCore C).rank x = C.rank := by rfl
@[simp] theorem charts_ofCore_self :
    (ofCore C).charts C.rank = (C.pullback (constStratumInclusion C C.rank)).core :=
  constStratumCharts_self C

private def chartsOfCoreSelfPkg :
    { e : ((ofCore C).charts C.rank).TotalSpace ≃ₜ C.core.TotalSpace //
      (∀ q, e q = ⟨q.proj.val, q.snd⟩) ∧ (∀ r, e.symm r = ⟨⟨r.proj, rfl⟩, r.snd⟩) } :=
  let inc := constStratumInclusion C C.rank
  let S := {x : X // (ofCore C).rank x = C.rank}
  let aux : ∀ (Z : VectorBundleCore 𝕜 S (Fin C.rank → 𝕜) S), Z = (C.pullback inc).core →
      { e : Z.TotalSpace ≃ₜ C.core.TotalSpace //
        (∀ q, e q = ⟨q.proj.val, q.snd⟩) ∧ (∀ r, e.symm r = ⟨⟨r.proj, rfl⟩, r.snd⟩) } := by
    rintro _ rfl
    exact ⟨{ toFun q := ⟨q.proj.val, q.snd⟩, invFun r := ⟨⟨r.proj, rfl⟩, r.snd⟩
             left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl, right_inv := fun ⟨_, _⟩ ↦ rfl
             continuous_toFun := (C.continuous_pullbackLift inc).congr fun ⟨_, _⟩ ↦
               C.pullbackLift_mk inc _ _
             continuous_invFun := (C.continuous_core_pullback_iff inc).2
               ⟨C.core.continuous_proj.subtype_mk fun _ ↦ rfl, continuous_id.congr fun ⟨x, v⟩ ↦
                 (C.pullbackLift_mk inc ⟨x, rfl⟩ v).symm⟩ }, fun _ ↦ rfl, fun _ ↦ rfl⟩
  aux ((ofCore C).charts C.rank) (charts_ofCore_self C)

/-- The reconstructed total space of `ofCore C` is homeomorphic over `X` to `C.core.TotalSpace`. -/
def ofCoreTotalSpaceHomeomorph : TotalSpace Unit (ofCore C).Fiber ≃ₜ C.core.TotalSpace :=
  let pkg := chartsOfCoreSelfPkg C
  totalSpaceHomeomorphOfConstStratum (ofCore C) (fun _ ↦ rfl) pkg.val
    (fun _ ↦ Equiv.refl _) (fun x v ↦ pkg.property.1 ⟨⟨x, rfl⟩, v⟩)
    (fun x v ↦ pkg.property.2 ⟨x, v⟩)
@[simp] theorem ofCoreTotalSpaceHomeomorph_apply (p : TotalSpace Unit (ofCore C).Fiber) :
    ofCoreTotalSpaceHomeomorph C p = ⟨p.proj, p.snd⟩ :=
  totalSpaceHomeomorphOfConstStratum_apply _ _ _ _ _ _ p
@[simp] theorem ofCoreTotalSpaceHomeomorph_symm_apply (p : C.core.TotalSpace) :
    (ofCoreTotalSpaceHomeomorph C).symm p = ⟨p.proj, p.snd⟩ :=
  totalSpaceHomeomorphOfConstStratum_symm_apply _ _ _ _ _ _ p
end OfCore

variable (𝕜 X) in
/-- The additive embedding of constant-rank point-indexed cores into variable-rank bundle
atlases. -/
-- Expose the object map so `(ofCoreFunctor 𝕜 X).obj C` reduces to `ofCore C` in morphism types.
@[expose, implicit_reducible]
def ofCoreFunctor : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj := ofCore
  map {C₁ C₂} f :=
    { fiberMap x := (f.fiberMap x).toLinearMap
      continuous_totalSpaceMap := ((ofCoreTotalSpaceHomeomorph C₂).symm.continuous.comp
        (f.continuous_totalSpaceMap.comp (ofCoreTotalSpaceHomeomorph C₁).continuous)).congr
        fun ⟨x, v⟩ ↦ by
          dsimp only [Function.comp_apply]
          rw [ofCoreTotalSpaceHomeomorph_apply, f.totalSpaceMap_mk x v,
            ofCoreTotalSpaceHomeomorph_symm_apply]; rfl }
  -- `LocallyConstant.const` is semireducible, so `rfl` unifies `(ofCore _).Fiber x` with
  -- `Fin _.rank → 𝕜` after `simp` normalizes the fibrewise linear maps.
  map_id _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp; rfl
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp; rfl
@[simp] theorem ofCoreFunctor_obj (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreFunctor 𝕜 X).obj C = ofCore C := by rfl
@[simp] theorem fiberMap_ofCoreFunctor_map {C₁ C₂ : FiniteRankBundleCore 𝕜 X}
    (f : C₁ ⟶ C₂) (x : X) :
    ((ofCoreFunctor 𝕜 X).map f).fiberMap x = (f.fiberMap x).toLinearMap := by rfl
instance : (ofCoreFunctor 𝕜 X).Additive where
  -- Unify `((ofCoreFunctor 𝕜 X).obj _).Fiber x` with `Fin _.rank → 𝕜` via `LocallyConstant.const`.
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp; rfl
instance : (ofCoreFunctor 𝕜 X).Faithful where
  map_injective {C₁ C₂} _ _ h := FiniteRankBundleCore.hom_ext fun x ↦ ContinuousLinearMap.ext
    fun v ↦ congrArg (fun k : ofCore C₁ ⟶ ofCore C₂ ↦ k.fiberMap x v) h

private theorem continuous_ofCorePreimageSection [CompleteSpace 𝕜]
    {C₁ C₂ : FiniteRankBundleCore 𝕜 X} (g : ofCore C₁ ⟶ ofCore C₂) :
    Continuous fun x ↦ TotalSpace.mk' ((Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜))
      (E := fun y ↦ C₁.core.Fiber y →L[𝕜] C₂.core.Fiber y) x
      (g.fiberMap x).toContinuousLinearMap :=
  (continuous_hom_bundle_iff (E₁ := C₁.core.Fiber) (E₂ := C₂.core.Fiber)
    (fun x ↦ (g.fiberMap x).toContinuousLinearMap)).2 <|
    ((ofCoreTotalSpaceHomeomorph C₂).continuous.comp (g.continuous_totalSpaceMap.comp
      (ofCoreTotalSpaceHomeomorph C₁).symm.continuous)).congr fun ⟨x, v⟩ ↦ by
        dsimp only [Function.comp_apply]
        rw [ofCoreTotalSpaceHomeomorph_symm_apply, ofCoreTotalSpaceHomeomorph_apply]; rfl
/-- Over a complete scalar field, `ofCoreFunctor` is fully faithful. -/
def fullyFaithfulOfCoreFunctor [CompleteSpace 𝕜] : (ofCoreFunctor 𝕜 X).FullyFaithful where
  preimage g := CoordinateHom.ofContinuous _ (continuous_ofCorePreimageSection g)
  map_preimage {C₁ C₂} g := hom_ext fun x ↦ LinearMap.ext fun v ↦
    congrArg (fun T : (Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜) ↦ T v)
      (congrFun (CoordinateHom.fiberMap_ofContinuous (Z := C₁.core) (W := C₂.core) _
        (continuous_ofCorePreimageSection g)) x)
  preimage_map {C₁ C₂} f := FiniteRankBundleCore.hom_ext fun x ↦
    congrFun (CoordinateHom.fiberMap_ofContinuous (Z := C₁.core) (W := C₂.core) _
      (continuous_ofCorePreimageSection ((ofCoreFunctor 𝕜 X).map f))) x
instance [CompleteSpace 𝕜] : (ofCoreFunctor 𝕜 X).Full := fullyFaithfulOfCoreFunctor.full

/-- A variable-rank bundle atlas lies in the essential image of `ofCoreFunctor` if and only if its
locally constant rank function is globally constant. -/
theorem mem_essImage_ofCoreFunctor_iff (A : FiniteRankAtlas 𝕜 X) :
    (ofCoreFunctor 𝕜 X).essImage A ↔ ∃ n : ℕ, A.rank = LocallyConstant.const X n := by
  refine ⟨fun ⟨C, ⟨e⟩⟩ ↦ ⟨C.rank, e.symm.variableRankBundle_rank_eq.trans (rank_ofCore C)⟩, ?_⟩
  rintro ⟨n, hn⟩
  have hnx (x : X) : rank A x = n := congrFun (congrArg DFunLike.coe hn) x
  let inc := constRankInclusion (V := A) hnx
  let C : FiniteRankBundleCore 𝕜 X := (A.stratumCore n).pullback inc
  refine ⟨C, ⟨isoOfTotalSpaceHomeomorph (fun x ↦ LinearEquiv.funCongrLeft 𝕜 𝕜 (finCongr (hnx x)))
    ((ofCoreTotalSpaceHomeomorph C).trans
      (((A.stratumCore n).pullbackHomeomorph inc).trans (constRankTotalSpaceHomeomorph A hnx).symm))
    fun x v ↦ by
      rw [Homeomorph.trans_apply, ofCoreTotalSpaceHomeomorph_apply, Homeomorph.trans_apply,
        FiniteRankBundleCore.pullbackHomeomorph_apply, constRankTotalSpaceHomeomorph_symm_apply]
      exact TotalSpace.ext rfl (heq_of_eq (funext fun i ↦ congrArg v (Fin.ext rfl)))⟩⟩

end TauCeti.FiniteRankAtlas
