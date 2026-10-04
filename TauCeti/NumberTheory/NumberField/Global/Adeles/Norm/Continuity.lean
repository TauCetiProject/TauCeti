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
topology is finer than the product topology. On each principal stage, the norm takes values in
one principal stage downstairs, since local norms preserve completed integer rings. Only the
places below the finitely many unrestricted source coordinates must be excluded.

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
  -- Repackage the principal-stage inclusion with the finite-adele type synonym as codomain.
  let inc : (Πʳ w : HeightOneSpectrum (𝓞 L),
      [w.adicCompletion L, w.adicCompletionIntegers L]_[Filter.principal S]) →
      FiniteAdeleRing (𝓞 L) L := fun x ↦
    ⟨(RestrictedProduct.inclusion _ _ hS x).1, (RestrictedProduct.inclusion _ _ hS x).2⟩
  suffices Continuous (finiteAdeleNorm K L ∘ inc) from this
  let T := (HeightOneSpectrum.under (𝓞 K) '' Sᶜ)ᶜ
  have hT : Filter.cofinite ≤ Filter.principal T := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite] at hS ⊢
    simpa only [T, compl_compl] using hS.image (HeightOneSpectrum.under (𝓞 K))
  refine (TauCeti.continuous_restrictedProduct_iff_of_forall_mem hT ?_).mpr ?_
  · intro x v hv
    -- The restricted-product criterion uses its own function coercion; identify it with
    -- the finite-adele coercion before using the public component formula.
    change finiteAdeleNorm K L (inc x) v ∈
      v.adicCompletionIntegers K
    rw [finiteAdeleNorm_apply]
    refine finprod_induction _ (one_mem _) (fun _ _ ↦ mul_mem) fun w ↦ ?_
    apply HeightOneSpectrum.norm_mem_adicCompletionIntegers v w.1
    have hw : w.1 ∈ S := by
      by_contra hw
      exact hv ⟨w.1, hw, HeightOneSpectrum.ext w.2.over.symm⟩
    exact Filter.eventually_principal.mp x.2 w.1 hw
  · refine continuous_pi fun v ↦ ?_
    -- Identify evaluation in the restricted-product type synonym with adele evaluation.
    change Continuous fun x ↦ finiteAdeleNorm K L (inc x) v
    simp only [finiteAdeleNorm_apply]
    refine continuous_finprod (fun w ↦ ?_) (locallyFinite_of_finite _)
    let := isModuleTopologyOfFiniteDimensional (𝕜 := v.adicCompletion K)
      (E := w.1.adicCompletion L)
    exact (TauCeti.continuous_algebraNorm (v.adicCompletion K) (w.1.adicCompletion L)).comp
      ((RestrictedProduct.continuous_eval w.1).comp (RestrictedProduct.continuous_inclusion hS))

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
  (((continuous_infiniteAdeleNorm K L).comp continuous_fst).prodMk
    ((continuous_finiteAdeleNorm K L).comp continuous_snd)).congr fun x ↦
      (Prod.ext (adeleNorm_fst x) (adeleNorm_snd x)).symm

end TauCeti.GlobalNumberFields
