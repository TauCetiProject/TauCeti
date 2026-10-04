/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Basic
import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
import TauCeti.Topology.Algebra.Algebra.Norm
import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng

/-!
# Continuity of relative adele norms

The placewise relative norms define continuous maps of finite, infinite, and full adele rings.
For finite adeles, coordinatewise continuity alone is insufficient: the restricted-product
topology is finer than the product topology.

These continuity results induce continuous norm maps on ideles with their units topology,
and hence on idele classes.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension NumberField.LiesOver RestrictedProduct Valued

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

-- `FiniteAdeleRing` is a type synonym for the restricted product, with a different function
-- coercion. This identity bridges its evaluation with evaluation on a principal stage.
private theorem finiteAdeleNorm_inclusion_apply {S : Set (HeightOneSpectrum (𝓞 L))}
    (hS : Filter.cofinite ≤ Filter.principal S)
    (x : Πʳ w : HeightOneSpectrum (𝓞 L),
      [w.adicCompletion L, w.adicCompletionIntegers L]_[Filter.principal S])
    (v : HeightOneSpectrum (𝓞 K)) :
    (finiteAdeleNorm K L (RestrictedProduct.inclusion _ _ hS x) :
      Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) v =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K) (x w.1) :=
  finiteAdeleNorm_apply _ _

/-- The relative norm of finite adeles is continuous for the restricted-product topology. -/
@[continuity, fun_prop]
theorem continuous_finiteAdeleNorm : Continuous (finiteAdeleNorm K L) := by
  refine RestrictedProduct.continuous_dom.mpr ?_
  intro S hS
  let T := (HeightOneSpectrum.under (𝓞 K) '' Sᶜ)ᶜ
  have hT : Filter.cofinite ≤ Filter.principal T := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite] at hS ⊢
    simpa only [T, compl_compl] using hS.image (HeightOneSpectrum.under (𝓞 K))
  refine (TauCeti.continuous_restrictedProduct_iff_of_forall_mem hT ?_).mpr ?_
  · intro x v hv
    erw [Function.comp_apply, finiteAdeleNorm_inclusion_apply]
    apply finprod_norm_mem_adicCompletionIntegers K L x v
    intro w hwv
    have hw : w ∈ S := by
      by_contra hw
      exact hv ⟨w, hw, hwv⟩
    exact Filter.eventually_principal.mp x.2 w hw
  · refine continuous_pi fun v ↦ ?_
    refine Continuous.congr ?_ fun x ↦ (finiteAdeleNorm_inclusion_apply K L hS x v).symm
    refine continuous_finprod (fun w ↦ ?_) (locallyFinite_of_finite _)
    let := isModuleTopologyOfFiniteDimensional (𝕜 := v.adicCompletion K)
      (E := w.1.adicCompletion L)
    exact (TauCeti.continuous_algebraNorm (v.adicCompletion K) (w.1.adicCompletion L)).comp
      (RestrictedProduct.continuous_eval w.1)

omit [NumberField K] in
/-- The relative norm of infinite adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteAdeleNorm : Continuous (infiniteAdeleNorm K L) := by
  refine continuous_pi fun v ↦ ?_
  simp only [infiniteAdeleNorm_apply]
  refine continuous_finprod (fun w ↦ ?_) (locallyFinite_of_finite _)
  let := isModuleTopologyOfFiniteDimensional (𝕜 := v.Completion) (E := w.1.Completion)
  exact (TauCeti.continuous_algebraNorm v.Completion w.1.Completion).comp
    (continuous_apply w.1)

/-- The relative norm of full adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_adeleNorm : Continuous (adeleNorm K L) :=
  ((continuous_infiniteAdeleNorm K L).prodMap (continuous_finiteAdeleNorm K L)).congr fun x ↦
    (Prod.ext (adeleNorm_fst x) (adeleNorm_snd x)).symm

end TauCeti.GlobalNumberFields
