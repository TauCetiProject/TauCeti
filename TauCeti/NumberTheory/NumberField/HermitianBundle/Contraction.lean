/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Dual
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Submodule
public import TauCeti.NumberTheory.NumberField.HermitianBundle.TensorProduct
public import Mathlib.RingTheory.PicardGroup

import TauCeti.NumberTheory.NumberField.HermitianBundle.Line
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# The contraction of a hermitian line with its dual is an isometry

Let `(E, h)` be a hermitian line over the ring of integers `𝓞 K` of a number field: `E` an
invertible `𝓞 K`-module. The contraction `E^∨ ⊗ E ≃ 𝓞 K`, `f ⊗ s ↦ f s`
(`Module.Invertible.linearEquiv`), is an isometry from `Ē^∨ ⊗ Ē` to the trivial hermitian line
`Ō_K`. Both sides are lines, so it suffices to compare one norm: at `f ⊗ s` with `f s ≠ 0` the
norms are `‖f‖_σ ‖s‖_σ` and `|σ(f s)|`, which agree by
`TauCeti.HermitianMetric.norm_dual_one_tmul_mul_norm`. Hence `Ē^∨` is an inverse of `Ē` for the
tensor product of hermitian lines.

## Main definitions

* `TauCeti.HermitianMetric.isometryEquivDualTmul`: the contraction `Ē^∨ ⊗ Ē ≃ Ō_K` as an
  isometry.

## Main results

* `TauCeti.HermitianMetric.comap_trivial_contraction`: the pullback of the trivial metric along
  the contraction is the tensor product metric on `E^∨ ⊗ E`.
* `TauCeti.HermitianMetric.isometryEquivDualTmul_apply`: the isometry sends `f ⊗ s` to `f s`.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.3, p. 147.
-/

public noncomputable section

open scoped TensorProduct nonZeroDivisors
open NumberField NumberField.ComplexEmbedding

namespace TauCeti.HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  (h : HermitianMetric K E)

/-- **The pullback of `Ō_K` along the contraction `E^∨ ⊗ E ≃ 𝓞 K` is `Ē^∨ ⊗ Ē`**, for a
hermitian line `Ē`. -/
theorem comap_trivial_contraction [Module.Invertible (𝓞 K) E] :
    (trivial K).comap (Module.Invertible.linearEquiv (𝓞 K) E).toLinearMap
      (Module.Invertible.linearEquiv (𝓞 K) E).injective = h.dual.tmul h := by
  set ψ := Module.Invertible.linearEquiv (𝓞 K) E
  have := Module.Invertible.nontrivial (𝓞 K) E
  obtain ⟨s, hs⟩ := exists_ne (0 : E)
  obtain ⟨f, hfs⟩ := Module.Projective.exists_dual_ne_zero (𝓞 K) hs
  have hψ : ψ (f ⊗ₜ s) = f s := Module.Invertible.linearEquiv_tmul f s
  have hι : IsBaseChange K ((Algebra.linearMap (𝓞 K) K).comp ψ.toLinearMap) :=
    IsBaseChange.comp_equiv ψ _
      (IsLocalizedModule.isBaseChange (𝓞 K)⁰ K (Algebra.linearMap (𝓞 K) K))
  refine ext_of_norm_eq hι (x₀ := f ⊗ₜ s) ?_ fun σ ↦ ?_
  · simpa [hψ] using hfs
  · rw [norm_comap, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hψ, norm_trivial_tmul,
      norm_tmul_tmul, h.norm_dual_one_tmul_mul_norm σ
        (Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] E))]

/-- **The contraction of a hermitian line with its dual is an isometry** `Ē^∨ ⊗ Ē ≃ Ō_K`,
`f ⊗ s ↦ f s`. -/
def isometryEquivDualTmul [Module.Invertible (𝓞 K) E] :
    IsometryEquiv (h.dual.tmul h) (trivial K) where
  toLinearEquiv := Module.Invertible.linearEquiv (𝓞 K) E
  form_tmul σ x y := by
    rw [← h.comap_trivial_contraction, comap_form_tmul, LinearEquiv.coe_coe]

@[simp]
theorem isometryEquivDualTmul_apply [Module.Invertible (𝓞 K) E] (f : Module.Dual (𝓞 K) E)
    (s : E) : h.isometryEquivDualTmul (f ⊗ₜ s) = f s :=
  Module.Invertible.linearEquiv_tmul f s

end TauCeti.HermitianMetric
