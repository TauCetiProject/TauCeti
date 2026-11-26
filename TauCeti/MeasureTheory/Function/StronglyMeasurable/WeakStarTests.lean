/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.StronglyMeasurable.ScalarTests
public import TauCeti.Analysis.LocallyConvex.WeakDual.Separating
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Weak-star dense scalar tests and the norm-Borel σ-algebra

On a separable Banach space, a linear family of continuous functionals generates the norm-Borel
σ-algebra exactly when it is weak-star dense. Thus the scalar tests used in Pettis measurability
can equivalently be specified by weak-star density. Linearity matters for the equivalence with
density; separation is the precise condition for an arbitrary family of tests.

The necessity of separation needs neither completeness nor separability: a family that fails
to distinguish a vector from zero cannot generate the Borel σ-algebra. Sufficiency uses the
existing separable complete-space scalar-test theorem, and the density comparison uses the
weak-star double-annihilator theorem.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, §1.1.a, Theorem 1.1.6 and Corollary 1.1.10.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Any family of continuous functionals generating the norm-Borel σ-algebra separates points.
This implication does not require a complete or separable target. -/
theorem separating_of_evalMeasurableSpace_eq_borel {T : Set (StrongDual 𝕜 X)}
    (hT : evalMeasurableSpace T = borel X) :
    ∀ x : X, (∀ y ∈ T, y x = 0) → x = 0 := by
  intro x hx
  borelize X
  let f : Bool → X := fun b ↦ if b then x else 0
  have hf : Measurable[⊥, evalMeasurableSpace T] f := by
    apply measurable_evalMeasurableSpace_iff.2
    intro y hy
    have heq : (fun b ↦ y (f b)) = fun _ ↦ 0 := by
      funext b
      cases b <;> simp [f, hx y hy]
    rw [heq]
    exact measurable_const
  rw [hT] at hf
  obtain ⟨c, hc⟩ := eq_const_of_measurable_bot hf
  have ht := congrFun hc true
  have hf := congrFun hc false
  simpa [f] using ht.trans hf.symm

/-- On a separable Banach space, scalar evaluations from an arbitrary family generate the
norm-Borel σ-algebra exactly when the family separates points. -/
theorem evalMeasurableSpace_eq_borel_iff_separating [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {T : Set (StrongDual 𝕜 X)} :
    evalMeasurableSpace T = borel X ↔ ∀ x : X, (∀ y ∈ T, y x = 0) → x = 0 :=
  ⟨separating_of_evalMeasurableSpace_eq_borel, evalMeasurableSpace_eq_borel_of_separating⟩

end TauCeti

namespace Submodule

open TauCeti

variable {X : Type*} [NormedAddCommGroup X]

/-- On a separable real or complex Banach space, a linear family of scalar tests generates the
norm-Borel σ-algebra exactly when it is weak-star dense in the continuous dual. -/
theorem evalMeasurableSpace_eq_borel_iff_dense_toWeakDual {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (Y : Submodule 𝕜 (StrongDual 𝕜 X)) :
    evalMeasurableSpace (Y : Set (StrongDual 𝕜 X)) = borel X ↔
      Dense (StrongDual.toWeakDual '' (Y : Set (StrongDual 𝕜 X))) := by
  rw [evalMeasurableSpace_eq_borel_iff_separating, Y.dense_toWeakDual_iff]
  rfl

end Submodule
