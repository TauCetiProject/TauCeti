/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Discrete.Module
public import Mathlib.Data.Finsupp.Defs
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
    {s : LocallyConstant liftedSequence.{u} M // s sequenceInfty = 0} ≃ (ℕ →₀ M) := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  letI : ContinuousConstSMul R M := ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let e := TauCeti.OnePoint.finsuppLinearEquivKerEvalInfty ℕ R M
  let a : {s : LocallyConstant liftedSequence.{u} M // s sequenceInfty = 0} ≃
      (ContinuousMap.evalCLM R (∞ : OnePoint ℕ) : C(OnePoint ℕ, M) →L[R] M).ker :=
    { toFun := fun s ↦ ⟨⟨s.val ∘ liftedSequenceEquiv.symm,
        s.val.continuous.comp liftedSequenceEquiv.symm.continuous⟩, by
        simpa using s.property⟩
      invFun := fun f ↦ ⟨⟨f.val ∘ liftedSequenceEquiv,
        (IsLocallyConstant.iff_continuous _).mpr
          (f.val.continuous.comp liftedSequenceEquiv.continuous)⟩, by
        have hf : f.val ∞ = 0 := f.property
        simpa using hf⟩
      left_inv := fun s ↦ by
        apply Subtype.ext
        ext x
        simp
      right_inv := fun f ↦ by
        apply Subtype.ext
        ext x
        simp }
  exact a.trans e.toEquiv.symm

private lemma discreteSectionsEquivFinsupp_apply
    (s : {s : LocallyConstant liftedSequence.{u} M // s sequenceInfty = 0}) (n : ℕ) :
    discreteSectionsEquivFinsupp M s n = s.val (sequencePoint n) := by
  simp [discreteSectionsEquivFinsupp]

private noncomputable def nullSeqHomEquivFinsuppEquiv :
    (nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) ≃ (ℕ →₀ M) := by
  let D := (LightCondMod.LocallyConstant.functor R).obj M
  let e : (D.obj.map inftyPoint.op).hom.toAddMonoidHom.ker ≃
      {s : LocallyConstant liftedSequence.{u} M // s sequenceInfty = 0} :=
    Equiv.subtypeEquivRight fun (s : LocallyConstant liftedSequence.{u} M) ↦ by
      have hval (x : LightProfinite.of PUnit.{u + 1}) :
          DFunLike.coe (F := LocallyConstant (LightProfinite.of PUnit.{u + 1}) M)
            (D.obj.map inftyPoint.op s) x = s sequenceInfty :=
        congrArg s (inftyPoint_apply x)
      refine ⟨fun h ↦ ?_, fun h ↦ LocallyConstant.ext fun x ↦ (hval x).trans h⟩
      have hs : D.obj.map inftyPoint.op s = 0 := h
      rw [← hval PUnit.unit, hs]
      rfl
  exact (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) D).toEquiv.trans
    (e.trans (discreteSectionsEquivFinsupp M))

private lemma nullSeqHomEquivFinsuppEquiv_apply
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) :
    nullSeqHomEquivFinsuppEquiv M g n =
      LocallyConstant.evalₗ R (sequencePoint n)
        (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) _ g).val := by
  exact discreteSectionsEquivFinsupp_apply M _ n

/-- Maps from the marked null sequence into the locally constant realization of a discrete
module are parametrized by the finitely supported coefficient sequences in that module. -/
noncomputable def nullSeqHomEquivFinsupp :
    (nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) ≃+ (ℕ →₀ M) where
  toEquiv := nullSeqHomEquivFinsuppEquiv M
  map_add' g h := by
    ext n
    simp only [Equiv.toFun_as_coe]
    rw [nullSeqHomEquivFinsuppEquiv_apply, Finsupp.add_apply,
      nullSeqHomEquivFinsuppEquiv_apply, nullSeqHomEquivFinsuppEquiv_apply,
      map_add, AddSubgroup.coe_add]
    exact (LocallyConstant.evalₗ R (sequencePoint n)).map_add _ _

lemma nullSeqHomEquivFinsupp_apply
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) :
    M.nullSeqHomEquivFinsupp g n =
      DFunLike.coe (F := LocallyConstant liftedSequence.{u} M)
        (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) _ g).val (sequencePoint n) :=
  nullSeqHomEquivFinsuppEquiv_apply M g n

/-- A map of discrete coefficient modules acts coefficientwise on null sequences. -/
lemma nullSeqHomEquivFinsupp_postcomp {N : ModuleCat.{u} R} (f : M ⟶ N)
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) :
    N.nullSeqHomEquivFinsupp (g ≫ (LightCondMod.LocallyConstant.functor R).map f) =
      Finsupp.mapRange f.hom (map_zero f.hom) (M.nullSeqHomEquivFinsupp g) := by
  ext n
  simp only [Finsupp.mapRange_apply, nullSeqHomEquivFinsupp_apply,
    reducedLightFreeHomEquiv_postcomp_val]
  rfl

/-- Precomposition with the marked shift takes the coefficient at n + 1 to n. -/
@[simp↓]
lemma nullSeqHomEquivFinsupp_nullShift
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) :
    nullSeqHomEquivFinsupp M (nullShift R ≫ g) n = nullSeqHomEquivFinsupp M g (n + 1) := by
  rw [nullSeqHomEquivFinsupp_apply, nullSeqHomEquivFinsupp_apply,
    reducedLightFreeHomEquiv_nullShift_val]
  exact congrArg _ (natShift_apply_coe n)

end ModuleCat
