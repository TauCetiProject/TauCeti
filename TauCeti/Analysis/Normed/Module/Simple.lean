/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.RingTheory.Semisimple.DoubleCentralizer

/-!
# Simple Banach modules

Every algebraic module map out of a simple Banach module over a Banach algebra is
continuous, provided the target action is continuous. In particular, algebraic
isomorphisms between such modules are homeomorphisms: a compatible complete
module norm is unique up to equivalence.

Over the complex numbers every module endomorphism is a scalar. This is the
scalar-commutant form of Rickart's theorem, used to turn algebraic Jacobson
density into density over the complex scalars. The finite interpolation theorem
`LinearIndependent.exists_smul_eq_of_completeSpace` makes this specialization
using the algebraic `LinearIndependent.exists_smul_eq`. Simplicity here is algebraic:
having no proper closed invariant subspace alone is not the hypothesis.

The automatic-continuity argument uses Mathlib's open mapping theorem on the
surjective orbit map at a nonzero vector. The scalar conclusion then uses
nonemptiness of the spectrum of a bounded complex operator and Schur's lemma.

## References

* C. E. Rickart, *General Theory of Banach Algebras*, Theorem 2.6.26.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, simple Banach modules.
-/

public section

namespace LinearMap

variable {𝕜 A E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [Module A E] [IsScalarTower 𝕜 A E] [ContinuousSMul A E] [IsSimpleModule A E]
  [TopologicalSpace F] [AddCommGroup F] [Module A F] [ContinuousSMul A F]

include 𝕜 in
/-- An algebraic module map from a simple Banach module over a Banach algebra into
a topological module on which the algebra acts continuously is continuous.
The target need not be complete, normed or simple. -/
theorem continuous_of_isSimpleModule (f : E →ₗ[A] F) : Continuous f := by
  have := IsSimpleModule.nontrivial A E
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have horbit : ⇑((LinearMap.toSpanSingleton A E x).restrictScalars 𝕜) =
      fun a : A ↦ a • x := by
    ext a
    rw [LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply]
  let q : A →L[𝕜] E :=
    { (LinearMap.toSpanSingleton A E x).restrictScalars 𝕜 with
      cont := by
        rw [LinearMap.toFun_eq_coe, horbit]
        exact continuous_id.smul continuous_const }
  have hq (a : A) : q a = a • x := by
    simp [q, LinearMap.toSpanSingleton_apply]
  apply (q.isQuotientMap (IsSimpleModule.toSpanSingleton_surjective A hx)).continuous_iff.mpr
  have h : f ∘ q = fun a : A ↦ a • f x := by
    funext a
    simpa only [Function.comp_apply, hq] using f.map_smul a x
  rw [h]
  exact continuous_id.smul continuous_const

end LinearMap

namespace LinearEquiv

variable {𝕜 A E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [Module A E] [IsScalarTower 𝕜 A E] [ContinuousSMul A E] [IsSimpleModule A E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [Module A F] [IsScalarTower 𝕜 A F] [ContinuousSMul A F]

include 𝕜 in
/-- An algebraic equivalence of simple Banach modules is a homeomorphism. In
particular, compatible Banach module norms on the same module are equivalent. -/
theorem isHomeomorph_of_isSimpleModule (f : E ≃ₗ[A] F) : IsHomeomorph f := by
  have : IsSimpleModule A F := f.isSimpleModule_iff.mp inferInstance
  exact f.isHomeomorph_iff.mpr
    ⟨f.toLinearMap.continuous_of_isSimpleModule (𝕜 := 𝕜),
      f.symm.toLinearMap.continuous_of_isSimpleModule (𝕜 := 𝕜)⟩

end LinearEquiv

namespace LinearMap

variable {A E : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [Module A E] [IsScalarTower ℂ A E] [ContinuousSMul A E] [IsSimpleModule A E]

/-- **Rickart's scalar-commutant theorem**: every algebraic endomorphism of a
simple complex Banach module is multiplication by a unique complex scalar. -/
theorem existsUnique_eq_smul_of_isSimpleModule (f : E →ₗ[A] E) :
    ∃! c : ℂ, ∀ x : E, f x = c • x := by
  have := IsSimpleModule.nontrivial A E
  let T : E →L[ℂ] E :=
    { f.restrictScalars ℂ with cont := f.continuous_of_isSimpleModule (𝕜 := ℂ) }
  -- Bundling the restricted linear map with continuity preserves its values.
  have hT (x : E) : T x = f x := rfl
  obtain ⟨c, hc⟩ := spectrum.nonempty T
  let g : E →ₗ[A] E := c • LinearMap.id - f
  have hg : g = 0 := by
    by_contra hg
    have hbij := g.bijective_of_ne_zero hg
    apply hc
    have hcoe : ⇑(algebraMap ℂ (E →L[ℂ] E) c - T) = ⇑g := by
      ext x
      simp [g, hT]
    rw [spectrum.mem_resolventSet_iff, ContinuousLinearMap.isUnit_iff_bijective, hcoe]
    exact hbij
  have heq : ∀ x : E, f x = c • x := by
    intro x
    exact (sub_eq_zero.mp (LinearMap.congr_fun hg x)).symm
  refine ⟨c, heq, fun d hd ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact (smul_left_injective ℂ hx) ((hd x).symm.trans (heq x))

end LinearMap

namespace IsSimpleModule

variable {A E : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [Module A E] [IsScalarTower ℂ A E] [ContinuousSMul A E] [IsSimpleModule A E]

/-- **Rickart's scalar-commutant theorem**: the scalar map from the complex numbers
to the algebraic endomorphism ring of a simple Banach module is bijective. -/
theorem algebraMap_end_bijective_of_completeSpace :
    Function.Bijective (algebraMap ℂ (Module.End A E)) := by
  have := IsSimpleModule.nontrivial A E
  refine ⟨(algebraMap ℂ (Module.End A E)).injective, fun f ↦ ?_⟩
  obtain ⟨c, hc, -⟩ := f.existsUnique_eq_smul_of_isSimpleModule
  exact ⟨c, LinearMap.ext fun x ↦ by
    simpa only [Module.algebraMap_end_apply] using (hc x).symm⟩

end IsSimpleModule

namespace LinearIndependent

variable {A E : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [Module A E] [IsScalarTower ℂ A E] [ContinuousSMul A E] [IsSimpleModule A E]

/-- **Complex Jacobson density**: one algebra element prescribes arbitrary values
on any finite complex-linearly independent family in a simple Banach module. -/
theorem exists_smul_eq_of_completeSpace {ι : Type*} [Finite ι] {v : ι → E}
    (hv : LinearIndependent ℂ v) (w : ι → E) :
    ∃ a : A, ∀ i, a • v i = w i := by
  have hv' : LinearIndependent (Module.End A E) v := by
    simpa only [Function.comp_def, AddMonoidHom.id_apply] using
      hv.map_of_surjective_injective (algebraMap ℂ (Module.End A E))
        (AddMonoidHom.id E) IsSimpleModule.algebraMap_end_bijective_of_completeSpace.surjective
        (fun _ h ↦ by simpa only [AddMonoidHom.id_apply] using h)
        (fun _ _ ↦ by
          simp only [AddMonoidHom.id_apply, Module.End.smul_def, Module.algebraMap_end_apply])
  exact hv'.exists_smul_eq w

end LinearIndependent
