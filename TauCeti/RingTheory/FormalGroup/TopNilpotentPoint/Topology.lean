/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint.Hom

/-!
# The topology on convergent formal-group points

The topologically nilpotent points of a formal group inherit the subspace topology of their
coefficient algebra. With this topology they form a Hausdorff topological group. Both evaluation
of formal-group homomorphisms and change of coefficient algebra are continuous; a formal-group
isomorphism therefore gives a homeomorphism on points.

Continuity uses congruences modulo open ideals, not a uniform bound on the nilpotence of all
points. A fixed series preserves such congruences because each of its monomials does and the
ideal is closed. This also works when the topology is linear but not adic.
-/

public section

namespace FormalGroup.TopNilpotentPoint

variable {R : Type*} [CommRing R] {F : FormalGroup R}

section Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The topology on convergent points is the topology induced by their coordinates. -/
instance : TopologicalSpace (F.TopNilpotentPoint A) :=
  TopologicalSpace.induced val inferInstance

/-- Taking the coordinate embeds the space of convergent points into the coefficient ring. -/
theorem isEmbedding_val : Topology.IsEmbedding (val : F.TopNilpotentPoint A → A) :=
  .induced (fun _ _ h ↦ TopNilpotentPoint.ext h)

@[continuity, fun_prop]
theorem continuous_val : Continuous (val : F.TopNilpotentPoint A → A) :=
  isEmbedding_val.continuous

instance [T2Space A] : T2Space (F.TopNilpotentPoint A) := isEmbedding_val.t2Space

end Topology

variable {A : Type*} [CommRing A] [Algebra R A] [UniformSpace A] [IsUniformAddGroup A]
  [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- Formal addition is continuous for the subspace topology on convergent points. -/
instance : ContinuousAdd (F.TopNilpotentPoint A) where
  continuous_add := by
    let _ : UniformSpace R := ⊥
    apply isEmbedding_val.continuous_iff.mpr
    simp only [Function.comp_def, val_add_eq_eval₂]
    apply MvPowerSeries.continuous_eval₂_of_continuous continuous_of_discreteTopology
    · intro i
      fin_cases i
      · exact continuous_val.comp continuous_fst
      · exact continuous_val.comp continuous_snd
    · intro x
      exact MvPowerSeries.hasEval_finTwo x.1.hasEval x.2.hasEval

/-- Formal negation is continuous for the subspace topology on convergent points. -/
instance : ContinuousNeg (F.TopNilpotentPoint A) where
  continuous_neg := by
    let _ : UniformSpace R := ⊥
    apply isEmbedding_val.continuous_iff.mpr
    simp only [Function.comp_def, val_neg_eq_eval₂, PowerSeries.eval₂]
    exact MvPowerSeries.continuous_eval₂_of_continuous continuous_of_discreteTopology
      (fun _ ↦ continuous_val) (fun x ↦ PowerSeries.hasEval x.hasEval) F.addInvX

/-- Convergent points form a topological group, without a commutativity assumption on the law. -/
instance : IsTopologicalAddGroup (F.TopNilpotentPoint A) where

variable {B : Type*} [CommRing B] [Algebra R B] [UniformSpace B] [IsUniformAddGroup B]
  [CompleteSpace B] [T2Space B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- The action of a continuous coefficient-algebra map on points is continuous. -/
@[continuity, fun_prop]
theorem continuous_map (φ : A →A[R] B) : Continuous (map F φ) := by
  apply isEmbedding_val.continuous_iff.mpr
  simp only [Function.comp_def, val_map]
  exact φ.cont.comp (continuous_val (F := F))

end FormalGroup.TopNilpotentPoint

namespace TauCeti

variable {R : Type*} [CommRing R] {F G : FormalGroup R}
variable {A : Type*} [CommRing A] [Algebra R A] [UniformSpace A] [IsUniformAddGroup A]
  [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- Evaluation of a formal-group homomorphism is continuous as the point varies. -/
@[continuity, fun_prop]
theorem FormalGroupHom.continuous_toTopNilpotentPointHom (f : FormalGroupHom F G) :
    Continuous (f.toTopNilpotentPointHom A) := by
  let _ : UniformSpace R := ⊥
  apply FormalGroup.TopNilpotentPoint.isEmbedding_val.continuous_iff.mpr
  simp only [Function.comp_def, FormalGroupHom.val_toTopNilpotentPointHom, PowerSeries.eval₂]
  exact MvPowerSeries.continuous_eval₂_of_continuous continuous_of_discreteTopology
    (fun _ ↦ FormalGroup.TopNilpotentPoint.continuous_val)
    (fun x ↦ PowerSeries.hasEval x.hasEval) f.toPowerSeries

/-- A formal-group isomorphism gives a homeomorphism on topologically nilpotent points. -/
noncomputable def FormalGroupIso.toTopNilpotentPointHomeomorph (f : FormalGroupIso F G)
    (A : Type*) [CommRing A] [Algebra R A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A] :
    F.TopNilpotentPoint A ≃ₜ G.TopNilpotentPoint A where
  toEquiv := (f.toTopNilpotentPointEquiv A).toEquiv
  continuous_toFun := f.toHom.continuous_toTopNilpotentPointHom.congr
    (fun x ↦ (f.toTopNilpotentPointEquiv_apply x).symm)
  continuous_invFun := f.invHom.continuous_toTopNilpotentPointHom.congr
    (fun x ↦ (f.toTopNilpotentPointEquiv_symm_apply x).symm)

@[simp]
theorem FormalGroupIso.toTopNilpotentPointHomeomorph_apply (f : FormalGroupIso F G)
    (x : F.TopNilpotentPoint A) :
    f.toTopNilpotentPointHomeomorph A x = f.toTopNilpotentPointEquiv A x := (rfl)

@[simp]
theorem FormalGroupIso.toTopNilpotentPointHomeomorph_symm_apply (f : FormalGroupIso F G)
    (x : G.TopNilpotentPoint A) :
    (f.toTopNilpotentPointHomeomorph A).symm x = (f.toTopNilpotentPointEquiv A).symm x := (rfl)

end TauCeti
