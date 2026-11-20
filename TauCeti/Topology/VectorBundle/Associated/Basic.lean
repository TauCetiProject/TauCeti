/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Basic
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Vector structures on associated bundles

A continuous linear action on a finite-dimensional normed space makes the existing associated
bundle into a native `VectorBundle`, with its original topology and atlas. A point of the
principal fibre identifies the model vector space linearly with the associated fibre; changing
that point acts by the given representation, with the convention `[p g, v] = [p, g v]`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public section

noncomputable section

open Bundle MulOpposite Set

namespace TauCeti.AssociatedBundle

variable {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]

-- `AssociatedBundle G P F b` is the core's fibre, a type synonym of `F`.
-- These instances deliberately reuse the model's addition, zero and scalar multiplication.
instance instAddCommGroup (b : B) : AddCommGroup (AssociatedBundle G P F b) :=
  inferInstanceAs (AddCommGroup F)

instance instModule (b : B) : Module 𝕜 (AssociatedBundle G P F b) :=
  inferInstanceAs (Module 𝕜 F)

/-- Addition is continuous for the existing associated-fibre topology. This delegate keeps
native bundle-metric constructions from having to unfold the fibre presentation. -/
instance instIsTopologicalAddGroup (b : B) : IsTopologicalAddGroup (AssociatedBundle G P F b) :=
  inferInstanceAs (IsTopologicalAddGroup F)

/-- Fixed scalar multiplication is continuous for the associated fibre's native module and
topology, as required by the native Riemannian-metric installation API. -/
instance instContinuousConstSMul (b : B) :
    ContinuousConstSMul 𝕜 (AssociatedBundle G P F b) :=
  inferInstanceAs (ContinuousConstSMul 𝕜 F)

/-- Associated-bundle charts are linear when the structure-group action is linear. -/
instance localTriv_isLinear (b : B) :
    ((associatedBundleCore G P F).localTriv b).IsLinear 𝕜 where
  linear x _ := by
    refine ⟨?_, ?_⟩
    · intro v w
      simp only [FiberBundleCore.localTriv_apply]
      rw [associatedBundleCore_coordChange (F := F) _ _ x (v + w),
        associatedBundleCore_coordChange (F := F) _ _ x v,
        associatedBundleCore_coordChange (F := F) _ _ x w]
      exact smul_add _ _ _
    · intro r v
      simp only [FiberBundleCore.localTriv_apply]
      rw [associatedBundleCore_coordChange (F := F) _ _ x (r • v),
        associatedBundleCore_coordChange (F := F) _ _ x v]
      -- The fibre module is the model module. Specify `F` to select the given
      -- commuting group action on the model rather than on the fibre synonym.
      exact @SMulCommClass.smul_comm G 𝕜 F _ _ ‹SMulCommClass G 𝕜 F› _ r v

/-- A linear action in finite dimension upgrades the associated fibre bundle to a vector
bundle without changing its topology or its chosen trivializations. -/
instance instVectorBundle [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    VectorBundle 𝕜 F (AssociatedBundle G P F) where
  trivialization_linear' e he := by
    obtain ⟨b, rfl⟩ := he
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨b, rfl⟩ := he
    obtain ⟨b', rfl⟩ := he'
    let e := (associatedBundleCore G P F).localTriv b
    let e' := (associatedBundleCore G P F).localTriv b'
    apply continuousOn_clm_apply.mpr
    intro v
    refine ((e.continuousOn_coordChange e').comp
      (continuousOn_id.prodMk (continuousOn_const (c := v)))
      (fun _ hx ↦ ⟨hx, mem_univ _⟩)).congr fun b hb ↦ ?_
    exact e.coordChangeL_apply' e' hb v

/-- Classes in a fixed principal frame respect addition. -/
@[simp]
theorem mk_add {b : B} (p : P b) (v w : F) :
    mk G p (v + w) = mk G p v + mk G p w := by
  simp only [mk_def, smul_add]
  -- The remaining equality identifies the fibre addition with the model addition,
  -- as specified by `instAddCommGroup`.
  rfl

variable (𝕜 G) in
/-- Each principal frame identifies the model with the associated fibre by a continuous
linear equivalence. This uses the existing associated-bundle class map. -/
def mkContinuousLinearEquiv {b : B} (p : P b) :
    F ≃L[𝕜] AssociatedBundle G P F b where
  toFun := mk G p
  -- Associated fibres have the model's topology and linear structure by construction.
  invFun x := @HSMul.hSMul G F F _ (trivializationAt G P b ⟨b, p⟩).2⁻¹ x
  left_inv v := by rw [mk_def]; exact inv_smul_smul _ v
  right_inv x := by
    rw [mk_def]
    -- View `x` in the model `F`, of which the fibre is a type synonym.
    exact @smul_inv_smul G F _ _ _ x
  map_add' := mk_add p
  map_smul' r v := by
    simp only [mk_def]
    -- The fibre scalar multiplication is the model's by `instModule`; specify `F`
    -- so instance search uses the given commuting action on the model.
    exact @SMulCommClass.smul_comm G 𝕜 F _ _ ‹SMulCommClass G 𝕜 F› _ r v
  continuous_toFun := by
    have h := continuous_const_smul (T := F) (trivializationAt G P b ⟨b, p⟩).2
    exact h.congr fun v ↦ (mk_def p v).symm
  continuous_invFun := continuous_const_smul (T := F) _

/-- The frame identification is the quotient class map. -/
@[simp]
theorem mkContinuousLinearEquiv_apply {b : B} (p : P b) (v : F) :
    mkContinuousLinearEquiv 𝕜 G p v = mk G p v := (rfl)

/-- Classes in a fixed principal frame respect scalar multiplication. -/
@[simp]
theorem mk_smul_scalar {b : B} (p : P b) (r : 𝕜) (v : F) :
    mk G p (r • v) = r • mk G p v :=
  by simpa only [mkContinuousLinearEquiv_apply] using
    (mkContinuousLinearEquiv 𝕜 G p).map_smul r v

/-- The zero class is independent of the principal frame. -/
@[simp]
theorem mk_zero {b : B} (p : P b) : mk G p (0 : F) = 0 := by
  simp only [mk_def, smul_zero]
  -- `instAddCommGroup` uses the model zero as the fibre zero.
  rfl

/-- Changing a principal frame transforms the vector coordinate by the division element. -/
@[simp]
theorem mkContinuousLinearEquiv_symm_apply_mk {b : B} (p q : P b) (v : F) :
    (mkContinuousLinearEquiv 𝕜 G p).symm (mk G q v) =
      PrincipalBundle.division G p q • v := by
  apply (mkContinuousLinearEquiv 𝕜 G p).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, mkContinuousLinearEquiv_apply]
  exact ((mk_eq_mk_iff (p := p) (q := q)).mpr rfl).symm

/-- In a local associated chart the linear transition acts by the principal transition. -/
theorem coordChangeL_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    {i j b : B} (hb : b ∈ (trivializationAt G P i).baseSet ∩
      (trivializationAt G P j).baseSet) (v : F) :
    (trivializationAt F (AssociatedBundle G P F) i).coordChangeL 𝕜
      (trivializationAt F (AssociatedBundle G P F) j) b v =
        (trivializationAt G P i).coordChange (trivializationAt G P j) b 1 • v := by
  rw [Trivialization.coordChangeL_apply']
  · rw [trivializationAt_eq_localTriv, trivializationAt_eq_localTriv]
    simp only [FiberBundleCore.localTriv_symm_apply, FiberBundleCore.localTriv_apply]
    rw [FiberBundleCore.coordChange_comp, associatedBundleCore_coordChange]
    simp only [FiberBundleCore.baseSet_at, associatedBundleCore_localTriv_baseSet,
      associatedBundleCore_indexAt]
    exact ⟨⟨hb.1, mem_baseSet_trivializationAt G P b⟩, hb.2⟩
  · simpa only [baseSet_trivializationAt] using hb

end TauCeti.AssociatedBundle
