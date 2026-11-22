/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Defs
public import TauCeti.Condensed.Light.LocallyConstant
public import TauCeti.Condensed.Light.NullSequence.Basic

import TauCeti.Topology.Compactification.OnePoint.Finsupp

/-!
# Discrete coefficients of the marked null sequence

A locally constant section of the convergent sequence that vanishes at infinity
has finite support. Thus maps from the reduced free module into a discrete light
condensed module are finitely supported sequences of coefficients. The marked
shift acts on these coefficients by dropping the zeroth term.
-/

public section

open CategoryTheory LightCondensed OnePoint Filter TauCeti
open scoped Topology

universe u

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{u} R)

private noncomputable def discreteSectionsEquivFinsupp :
    (LocallyConstant.evalₗ R sequenceInfty :
      LocallyConstant liftedSequence.{u} M →ₗ[R] M).ker ≃+
      (ℕ →₀ M) := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  letI : ContinuousConstSMul R M := ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let e := TauCeti.OnePoint.finsuppLinearEquivKerEvalInfty ℕ R M
  let a :
      (LocallyConstant.evalₗ R sequenceInfty :
        LocallyConstant liftedSequence.{u} M →ₗ[R] M).ker ≃+
      (ContinuousMap.evalCLM R (∞ : OnePoint ℕ) : C(OnePoint ℕ, M) →L[R] M).ker :=
    { toFun := fun s ↦ ⟨⟨s.val ∘ liftedSequenceEquiv.symm,
        s.val.continuous.comp liftedSequenceEquiv.symm.continuous⟩, by
        refine LinearMap.mem_ker.mpr ?_
        have hs : s.val sequenceInfty = 0 := LinearMap.mem_ker.mp s.property
        simpa only [ContinuousLinearMap.coe_coe, ContinuousMap.evalCLM_apply, ContinuousMap.coe_mk,
          Function.comp_apply, liftedSequenceEquiv_symm_apply_infty] using hs⟩
      invFun := fun f ↦ ⟨⟨f.val ∘ liftedSequenceEquiv,
        (IsLocallyConstant.iff_continuous _).mpr
          (f.val.continuous.comp liftedSequenceEquiv.continuous)⟩, by
        have hf : f.val ∞ = 0 := LinearMap.mem_ker.mp f.property
        apply LinearMap.mem_ker.mpr
        simpa only [LocallyConstant.evalₗ_apply, LocallyConstant.coe_mk,
          Function.comp_apply, liftedSequenceEquiv_apply_infty] using hf⟩
      left_inv := fun s ↦ by
        apply Subtype.ext
        ext x
        simp
      right_inv := fun f ↦ by
        apply Subtype.ext
        ext x
        simp
      map_add' := fun f g ↦ by
        apply Subtype.ext
        ext x
        rfl }
  exact a.trans e.toAddEquiv.symm

private lemma discreteSectionsEquivFinsupp_apply
    (s : (LocallyConstant.evalₗ R sequenceInfty :
      LocallyConstant liftedSequence.{u} M →ₗ[R] M).ker) (n : ℕ) :
    discreteSectionsEquivFinsupp M s n = s.val (sequencePoint n) := by
  simp [discreteSectionsEquivFinsupp]

/-- Maps from the marked null sequence into the locally constant realization of a discrete
module are parametrized by the finitely supported coefficient sequences in that module. -/
noncomputable def nullSeqHomEquivFinsupp :
    (nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) ≃+ (ℕ →₀ M) := by
  let D := (LightCondMod.LocallyConstant.functor R).obj M
  let sections := LightCondMod.LocallyConstant.sectionsEquiv M liftedSequence.{u}
  have hrestrict (s : D.obj.obj (Opposite.op liftedSequence.{u}))
      (x : LightProfinite.of PUnit.{u + 1}) :
      LightCondMod.LocallyConstant.sectionsEquiv M _ (D.obj.map inftyPoint.op s) x =
        sections s sequenceInfty :=
    (LightCondMod.LocallyConstant.sectionsEquiv_map_apply M inftyPoint s x).trans
      (congrArg (sections s) (inftyPoint_apply x))
  have mem_ker_iff (s : D.obj.obj (Opposite.op liftedSequence.{u})) :
      s ∈ (D.obj.map inftyPoint.op).hom.toAddMonoidHom.ker ↔
        sections s ∈ (LocallyConstant.evalₗ R sequenceInfty).ker := by
    rw [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe,
      LinearMap.mem_ker, LocallyConstant.evalₗ_apply]
    constructor
    · intro hs
      rw [← hrestrict s PUnit.unit, hs]
      simp only [map_zero, LocallyConstant.zero_apply]
    · intro hs
      apply (LightCondMod.LocallyConstant.sectionsEquiv M _).injective
      ext x
      simpa only [map_zero, LocallyConstant.zero_apply] using (hrestrict s x).trans hs
  let e : (D.obj.map inftyPoint.op).hom.toAddMonoidHom.ker ≃+
      (LocallyConstant.evalₗ R sequenceInfty :
        LocallyConstant liftedSequence.{u} M →ₗ[R] M).ker :=
    { toEquiv := sections.toEquiv.subtypeEquiv mem_ker_iff
      map_add' := fun s t ↦ Subtype.ext (map_add sections s.val t.val) }
  exact (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) D).trans
    (e.trans (discreteSectionsEquivFinsupp M))

lemma nullSeqHomEquivFinsupp_apply
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) :
    M.nullSeqHomEquivFinsupp g n =
      LightCondMod.LocallyConstant.sectionsEquiv M liftedSequence.{u}
        (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) _ g).val (sequencePoint n) := by
  exact discreteSectionsEquivFinsupp_apply M _ n

/-- The map represented by finitely supported coefficients has the prescribed finite values. -/
lemma reducedLightFreeHomEquiv_nullSeqHomEquivFinsupp_symm_apply
    (a : ℕ →₀ M) (n : ℕ) :
    LightCondMod.LocallyConstant.sectionsEquiv M liftedSequence.{u}
      (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) _
        (M.nullSeqHomEquivFinsupp.symm a)).val (sequencePoint n) = a n := by
  rw [← nullSeqHomEquivFinsupp_apply, AddEquiv.apply_symm_apply]

/-- A map of discrete coefficient modules acts coefficientwise on null sequences. -/
@[simp]
lemma nullSeqHomEquivFinsupp_postcomp {N : ModuleCat.{u} R} (f : M ⟶ N)
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) :
    N.nullSeqHomEquivFinsupp (g ≫ (LightCondMod.LocallyConstant.functor R).map f) =
      Finsupp.mapRange f.hom (map_zero f.hom) (M.nullSeqHomEquivFinsupp g) := by
  ext n
  simp only [Finsupp.mapRange_apply, nullSeqHomEquivFinsupp_apply,
    reducedLightFreeHomEquiv_postcomp_val]
  exact LightCondMod.LocallyConstant.sectionsEquiv_map_app_apply M f liftedSequence _ _

/-- Precomposition with the marked shift takes the coefficient at n + 1 to n. -/
@[simp↓]
lemma nullSeqHomEquivFinsupp_nullShift
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) :
    nullSeqHomEquivFinsupp M (nullShift R ≫ g) n = nullSeqHomEquivFinsupp M g (n + 1) := by
  rw [nullSeqHomEquivFinsupp_apply, nullSeqHomEquivFinsupp_apply,
    reducedLightFreeHomEquiv_nullShift_val,
    LightCondMod.LocallyConstant.sectionsEquiv_map_apply, natShift_apply_sequencePoint]

end ModuleCat
