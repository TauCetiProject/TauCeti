/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import TauCeti.RingTheory.Huber.BanachModule.SplitExact

/-!
# Checks for split exactness of completed tensor products

These checks use the standard split sequence `U → U × Q → Q`, verify preservation of
its continuous retraction and section on the entire completions, and distinguish the
ordered summands using lifted multiplication. The component formulas retain subtraction
signs, and a zero summand contributes nothing.
-/

public section

open Function TauCeti.Huber.BanachModule

section Generic

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {U : Type*} [AddCommGroup U] [Module A U] [TopologicalSpace U]
  {V : Type*} [AddCommGroup V] [Module A V] [TopologicalSpace V]
  {Q : Type*} [AddCommGroup Q] [Module A Q] [TopologicalSpace Q]
  {W : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W]

/-- The standard split sequence remains exact, with no Banach hypotheses on the factors. -/
example : Exact
    (CompletedTensor.map (ContinuousLinearMap.inl A U Q) (.id A W))
    (CompletedTensor.map (ContinuousLinearMap.snd A U Q) (.id A W)) := by
  apply CompletedTensor.exact_of_split
    (ContinuousLinearMap.fst A U Q) (ContinuousLinearMap.inr A U Q)
  · ext u
    simp
  · intro v
    simp

/-- Retractions survive completed tensoring, and hence give injective completed maps. -/
example {i : U →L[A] V} {r : V →L[A] U} (hri : r.comp i = .id A U) :
    LeftInverse (CompletedTensor.map r (.id A W)) (CompletedTensor.map i (.id A W)) := by
  have h : (CompletedTensor.map r (.id A W)).comp (CompletedTensor.map i (.id A W)) =
      ContinuousLinearMap.id A (CompletedTensor A U W) := by
    rw [← CompletedTensor.map_comp, hri, ContinuousLinearMap.id_comp, CompletedTensor.map_id]
  intro x
  exact DFunLike.congr_fun h x

/-- Sections survive completed tensoring, and hence give surjective completed maps. -/
example {p : V →L[A] Q} {s : Q →L[A] V} (hps : p.comp s = .id A Q) :
    RightInverse (CompletedTensor.map s (.id A W)) (CompletedTensor.map p (.id A W)) := by
  have h : (CompletedTensor.map p (.id A W)).comp (CompletedTensor.map s (.id A W)) =
      ContinuousLinearMap.id A (CompletedTensor A Q W) := by
    rw [← CompletedTensor.map_comp, hps, ContinuousLinearMap.id_comp, CompletedTensor.map_id]
  intro x
  exact DFunLike.congr_fun h x

/-- The product comparison preserves both components and their signs. -/
example (u u' : U) (q q' : Q) (w w' : W) :
    CompletedTensor.prodLeft
      (CompletedTensor.tmul A (U × Q) W (u, q) w -
        CompletedTensor.tmul A (U × Q) W (u', q') w') =
      (CompletedTensor.tmul A U W u w - CompletedTensor.tmul A U W u' w',
        CompletedTensor.tmul A Q W q w - CompletedTensor.tmul A Q W q' w') := by
  simp

/-- The inverse comparison need not use the same second factor in its two components. -/
example (u : U) (q : Q) (w w' : W) :
    CompletedTensor.prodLeft.symm
      (CompletedTensor.tmul A U W u w, -CompletedTensor.tmul A Q W q w') =
      CompletedTensor.tmul A (U × Q) W (u, 0) w -
        CompletedTensor.tmul A (U × Q) W (0, q) w' := by
  simp [sub_eq_add_neg]

/-- A zero second summand gives no contribution, even for arbitrary completed tensors. -/
example (x : CompletedTensor A U W) :
    CompletedTensor.prodLeft.symm (x, (0 : CompletedTensor A Q W)) =
      CompletedTensor.map (ContinuousLinearMap.inl A U Q) (.id A W) x := by
  simp

end Generic

section OrderedSummands

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T2Space A] [Nontrivial A]

/-- The two inclusions in the product comparison are ordered, not interchangeable. -/
example : CompletedTensor.tmul A (A × A) A (1, 0) 1 ≠
    CompletedTensor.tmul A (A × A) A (0, 1) 1 := by
  intro h
  have htensor : CompletedTensor.tmul A A A 1 1 = 0 := by
    simpa using congrArg (fun z : CompletedTensor A (A × A) A ↦
      (CompletedTensor.prodLeft z).1) h
  -- Lifted multiplication detects the nonzero elementary tensor after completion.
  have := congrArg
    (CompletedTensor.lift (LinearMap.mul A A) (continuous_mul.congr fun _ ↦ by simp)) htensor
  simp at this

end OrderedSummands
