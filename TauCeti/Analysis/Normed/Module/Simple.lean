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

Every element acting with infinite-dimensional range has a left multiple that kills a
vector it does not kill while keeping infinite-dimensional range,
`IsSimpleModule.exists_mul_smul_eq_zero`. Iterating this gives sequences of products with
strictly increasing kernels, as used for separating ideals.

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
  let q : A →L[𝕜] E := (ContinuousLinearMap.id 𝕜 A).smulRight x
  have hq (a : A) : q a = a • x := by
    simp [q]
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

namespace IsSimpleModule

variable {A E : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [Module A E] [IsScalarTower ℂ A E] [ContinuousSMul A E] [IsSimpleModule A E]

/-- If `p` acts on a simple complex Banach module with infinite-dimensional range, then some
left multiple `b * p` kills a vector that `p` does not kill, and `b * p` still acts with
infinite-dimensional range. The factor `b` is `1 - f` for a finite-rank action `f` when some
element acts with nonzero finite rank, and otherwise comes from complex Jacobson density. -/
theorem exists_mul_smul_eq_zero (p : A)
    (hp : ¬ FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E p))) :
    ∃ b : A, ∃ x : E, p • x ≠ 0 ∧ (b * p) • x = 0 ∧
      ¬ FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E (b * p))) := by
  obtain ⟨x, hx⟩ : ∃ x : E, p • x ≠ 0 := by
    by_contra! h
    have h0 : Algebra.lsmul ℂ ℂ E p = 0 := LinearMap.ext fun y ↦ by simpa using h y
    rw [h0, LinearMap.range_zero] at hp
    exact hp inferInstance
  by_cases hfin : ∃ s : A, ∃ ξ : E, s • ξ ≠ 0 ∧
      FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E s))
  · -- Some `s` has nonzero finite rank. Transitivity gives `f = a * s * c` of finite rank
    -- fixing `p • x`; then `b = 1 - f` kills `p • x` and has finite-dimensional kernel.
    obtain ⟨s, ξ, hsξ, hs⟩ := hfin
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hsξ (p • x)
    obtain ⟨c, hc⟩ := IsSimpleModule.toSpanSingleton_surjective A hx ξ
    rw [LinearMap.toSpanSingleton_apply] at ha hc
    have hf : (a * s * c) • p • x = p • x := by rw [mul_smul, mul_smul, hc, ha]
    have hfin : FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E (a * s * c))) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := (LinearMap.range (Algebra.lsmul ℂ ℂ E s)).map (Algebra.lsmul ℂ ℂ E a)) ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨s • c • y, ⟨c • y, Algebra.lsmul_apply ..⟩, by simp⟩
    refine ⟨1 - a * s * c, x, hx, by rw [mul_smul, sub_smul, one_smul, hf, sub_self],
      fun h ↦ hp ?_⟩
    rw [← Submodule.fg_iff_finiteDimensional] at h ⊢
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Algebra.lsmul ℂ ℂ E (1 - a * s * c)) ?_ ?_
    · rwa [← LinearMap.range_comp, ← Module.End.mul_eq_comp, ← map_mul]
    · rw [Submodule.fg_iff_finiteDimensional]
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range (Algebra.lsmul ℂ ℂ E (a * s * c))) ?_
      rintro y ⟨-, hy⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Algebra.lsmul_apply, sub_smul, one_smul,
        sub_eq_zero] at hy
      exact ⟨y, (Algebra.lsmul_apply ..).trans hy.symm⟩
  · -- Every nonzero element has infinite rank. Density on `p • x` and an independent vector
    -- `p • y` of the range of `p` gives `b` killing the first and fixing the second.
    push Not at hfin
    obtain ⟨w, hwR, hw⟩ : ∃ w ∈ LinearMap.range (Algebra.lsmul ℂ ℂ E p), w ∉ ℂ ∙ (p • x) := by
      by_contra! h
      have heq : LinearMap.range (Algebra.lsmul ℂ ℂ E p) = ℂ ∙ (p • x) :=
        le_antisymm h ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨x, Algebra.lsmul_apply ..⟩)
      rw [heq] at hp
      exact hp inferInstance
    obtain ⟨y, rfl⟩ := hwR
    rw [Algebra.lsmul_apply] at hw
    have hli : LinearIndependent ℂ ![p • x, p • y] :=
      (LinearIndependent.pair_iff' hx).2 fun r hr ↦
        hw (Submodule.mem_span_singleton.2 ⟨r, hr⟩)
    obtain ⟨b, hb⟩ := hli.exists_smul_eq_of_completeSpace (A := A) ![0, p • y]
    have hy : p • y ≠ 0 := fun h ↦ hw (h ▸ Submodule.zero_mem _)
    have hb1 : b • p • y = p • y := by simpa using hb 1
    refine ⟨b, x, hx, by simpa [mul_smul] using hb 0, hfin _ y ?_⟩
    rwa [mul_smul, hb1]

end IsSimpleModule
