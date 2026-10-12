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
    -- Normalize the `RestrictedProduct` evaluation to the `FiniteAdeleRing` evaluation
    -- in the norm's component formula; the type synonym has a different `DFunLike` instance.
    have h := (finiteAdeleNorm_apply (RestrictedProduct.inclusion _ _ hS x) v).trans
      (congrArg finprod (funext fun w ↦ congrArg (Algebra.norm (v.adicCompletion K))
        (RestrictedProduct.inclusion_apply _ _ hS w.1)))
    refine (congrArg (· ∈ v.adicCompletionIntegers K) h).mpr
      (finprod_norm_mem_adicCompletionIntegers K L x v ?_)
    intro w hwv
    have hw : w ∈ S := by
      by_contra hw
      exact hv ⟨w, hw, hwv⟩
    exact Filter.eventually_principal.mp x.2 w hw
  · refine continuous_pi fun v ↦ ?_
    refine Continuous.congr ?_ fun x ↦
      ((finiteAdeleNorm_apply (RestrictedProduct.inclusion _ _ hS x) v).trans
        (congrArg finprod (funext fun w ↦ congrArg (Algebra.norm (v.adicCompletion K))
          (RestrictedProduct.inclusion_apply _ _ hS w.1)))).symm
    refine continuous_finprod (fun w ↦ ?_) (locallyFinite_of_finite _)
    exact (TauCeti.continuous_algebraNorm_of_finiteDimensional
      (v.adicCompletion K) (w.1.adicCompletion L)).comp
        (RestrictedProduct.continuous_eval w.1)

omit [NumberField K] in
/-- The relative norm of infinite adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteAdeleNorm : Continuous (infiniteAdeleNorm K L) := by
  refine continuous_pi fun v ↦ ?_
  simp only [infiniteAdeleNorm_apply]
  refine continuous_finprod (fun w ↦ ?_) (locallyFinite_of_finite _)
  exact (TauCeti.continuous_algebraNorm_of_finiteDimensional v.Completion w.1.Completion).comp
    (continuous_apply w.1)

/-- The relative norm of full adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_adeleNorm : Continuous (adeleNorm K L) :=
  ((continuous_infiniteAdeleNorm K L).prodMap (continuous_finiteAdeleNorm K L)).congr fun x ↦
    (Prod.ext (adeleNorm_fst x) (adeleNorm_snd x)).symm

end TauCeti.GlobalNumberFields
