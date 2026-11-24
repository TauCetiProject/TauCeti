/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Invertibility of pullback on holomorphic stalks

For a function analytic near a point, pullback on holomorphic stalks is an isomorphism
exactly when the derivative is nonzero. In fact, surjectivity alone suffices: a preimage of
the coordinate germ provides a holomorphic left inverse, so the chain rule forces a nonzero
derivative. Conversely, the analytic inverse function theorem supplies a local analytic inverse,
along which pullback is bijective (`stalkPullback_bijective`).

These criteria concern the native structure-sheaf stalks, including their entire germ maps,
not merely their residue fields. They recognize inverses of maps on branches of nodal curves.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §1 (holomorphic local coordinates).
-/

public noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.holomorphicStructureSheaf

variable {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)

/-- For a nonzero derivative, the analytic local inverse makes pullback bijective. -/
private theorem stalkPullback_bijective_of_deriv_ne_zero (hne : deriv f a ≠ 0) :
    Function.Bijective (stalkPullback (eventually_contMDiffAt_of_analyticAt hf)) :=
  stalkPullback_bijective _ (eventually_contMDiffAt_of_analyticAt (hf.analyticAt_localInverse hne))
    (hf.hasStrictDerivAt.eventually_left_inverse hne)
    (hf.hasStrictDerivAt.eventually_right_inverse hne)

/-- Pullback on holomorphic stalks is surjective exactly when the branch derivative is nonzero.
Surjectivity of the residue-field map alone would not suffice. -/
theorem stalkPullback_surjective_iff :
    Function.Surjective (stalkPullback (eventually_contMDiffAt_of_analyticAt hf)) ↔
      deriv f a ≠ 0 := by
  constructor
  · intro hsurj
    obtain ⟨c, hc⟩ := exists_toFilterGerm_eq_of_analyticAt (analyticAt_id (z := a))
    obtain ⟨t, ht⟩ := hsurj c
    obtain ⟨u, hua, hut⟩ := exists_toFilterGerm_eq_analyticAt (f a) t
    have hcomp := congrArg (toFilterGerm 𝓘(ℂ) ℂ a (𝓝 a) le_rfl) ht
    rw [toFilterGerm_stalkPullback, hut, hc, Germ.coe_compTendsto, Germ.coe_eq] at hcomp
    have hchain := hua.differentiableAt.hasDerivAt.comp a hf.differentiableAt.hasDerivAt
    have hder := hchain.congr_of_eventuallyEq hcomp.symm
    have hmul := hder.unique (hasDerivAt_id a)
    intro hz
    simp [hz] at hmul
  · exact fun hne ↦ (stalkPullback_bijective_of_deriv_ne_zero hf hne).2

/-- A local analytic map induces an isomorphism of holomorphic stalks exactly when its
derivative is nonzero. -/
theorem stalkPullback_bijective_iff :
    Function.Bijective (stalkPullback (eventually_contMDiffAt_of_analyticAt hf)) ↔
      deriv f a ≠ 0 :=
  ⟨fun h ↦ (stalkPullback_surjective_iff hf).mp h.2, stalkPullback_bijective_of_deriv_ne_zero hf⟩

/-- The holomorphic-stalk isomorphism induced by an analytic map with nonzero derivative. -/
def stalkPullbackEquivOfDerivNeZero (hf0 : deriv f a ≠ 0) :
    (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a) ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a :=
  stalkPullbackEquiv (eventually_contMDiffAt_of_analyticAt hf)
    (eventually_contMDiffAt_of_analyticAt (hf.analyticAt_localInverse hf0))
    (hf.hasStrictDerivAt.eventually_left_inverse hf0)
    (hf.hasStrictDerivAt.eventually_right_inverse hf0)

/-- The stalk isomorphism acts by pullback of holomorphic germs. -/
theorem stalkPullbackEquivOfDerivNeZero_apply (hf0 : deriv f a ≠ 0)
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a)) :
    stalkPullbackEquivOfDerivNeZero hf hf0 s =
      stalkPullback (eventually_contMDiffAt_of_analyticAt hf) s :=
  stalkPullbackEquiv_apply (eventually_contMDiffAt_of_analyticAt hf)
    (eventually_contMDiffAt_of_analyticAt (hf.analyticAt_localInverse hf0))
    (hf.hasStrictDerivAt.eventually_left_inverse hf0)
    (hf.hasStrictDerivAt.eventually_right_inverse hf0) s

/-- The stalk isomorphism induced by a nonzero derivative preserves evaluation. -/
@[simp]
theorem eval_stalkPullbackEquivOfDerivNeZero (hf0 : deriv f a ≠ 0)
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a)) :
    eval 𝓘(ℂ) ℂ a (stalkPullbackEquivOfDerivNeZero hf hf0 s) = eval 𝓘(ℂ) ℂ (f a) s := by
  rw [stalkPullbackEquivOfDerivNeZero, eval_stalkPullbackEquiv]

/-- The inverse stalk isomorphism induced by a nonzero derivative preserves evaluation. -/
@[simp]
theorem eval_stalkPullbackEquivOfDerivNeZero_symm (hf0 : deriv f a ≠ 0)
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    eval 𝓘(ℂ) ℂ (f a) ((stalkPullbackEquivOfDerivNeZero hf hf0).symm s) =
      eval 𝓘(ℂ) ℂ a s := by
  rw [stalkPullbackEquivOfDerivNeZero, eval_stalkPullbackEquiv_symm]

/-- On function germs, the stalk isomorphism is composition with the analytic map. -/
@[simp]
theorem toFilterGerm_stalkPullbackEquivOfDerivNeZero (hf0 : deriv f a ≠ 0)
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a)) :
    toFilterGerm 𝓘(ℂ) ℂ a (𝓝 a) le_rfl (stalkPullbackEquivOfDerivNeZero hf hf0 s) =
      (toFilterGerm 𝓘(ℂ) ℂ (f a) (𝓝 (f a)) le_rfl s).compTendsto f
        hf.continuousAt.tendsto := by
  rw [stalkPullbackEquivOfDerivNeZero, toFilterGerm_stalkPullbackEquiv]

/-- On function germs, the inverse stalk isomorphism is composition with the analytic local
inverse supplied by the inverse function theorem. -/
@[simp]
theorem toFilterGerm_stalkPullbackEquivOfDerivNeZero_symm (hf0 : deriv f a ≠ 0)
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    toFilterGerm 𝓘(ℂ) ℂ (f a) (𝓝 (f a)) le_rfl
        ((stalkPullbackEquivOfDerivNeZero hf hf0).symm s) =
      (toFilterGerm 𝓘(ℂ) ℂ a (𝓝 a) le_rfl s).compTendsto
        (hf.hasStrictDerivAt.localInverse f (deriv f a) a hf0)
        (by simpa only [(hf.hasStrictDerivAt.eventually_left_inverse hf0).self_of_nhds] using
          (hf.analyticAt_localInverse hf0).continuousAt.tendsto) := by
  rw [stalkPullbackEquivOfDerivNeZero, toFilterGerm_stalkPullbackEquiv_symm]

end TauCeti.holomorphicStructureSheaf
