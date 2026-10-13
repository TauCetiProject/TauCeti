/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.InnerProductSpace.SpectralCutoff
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan

/-!
# The converse min–max localization on Hilbert spaces

For a bounded operator `T : E →L[𝕜] F` out of a Hilbert space, every strict lower bound
`r < aₙ(T)` of the `n`-th approximation number is beaten by a uniform coercivity bound for `T` on
the span of `n + 1` linearly independent vectors. Equivalently, `aₙ(T)` is the supremum of the
coercivity constants of `T` on `(n + 1)`-dimensional subspaces, the Hilbert-space form of the
Courant–Fischer max–min principle. This is the property `TauCeti.HasMinMaxLowerBound 𝕜 E F`, and
it yields the Ky Fan triangle inequality `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)` for the approximation
numbers in arbitrary dimension.

The proof works with the positive operator `A = T† T`, whose Rayleigh form is `‖T x‖²`. Choose
`r < c < aₙ(T)` and let `B⁺` be the positive part of `B = A - c²`, defined by the continuous
functional calculus. On the kernel of `B⁺` the Rayleigh form of `B` is nonpositive
(`ContinuousLinearMap.re_inner_nonpos_of_posPart_apply_eq_zero`), so `T` has norm at most `c`
there; since `B⁺` is self-adjoint, that kernel is the orthogonal complement of the range of `B⁺`.
If the range had rank at most `n`, the orthogonal-tail bound
`ContinuousLinearMap.singularValue_le_nnnorm_comp_orthogonal` would give `aₙ(T) ≤ c`. So the range
has rank greater than `n`, and on it the Rayleigh form of `B` is nonnegative
(`ContinuousLinearMap.re_inner_nonneg_of_mem_range_posPart`), that is, `T` is `c`-coercive. The
target need not be complete: the adjoint is taken after composing `T` with the isometric embedding
of `F` into its completion.

The source carries the continuous functional calculus
`ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint` as a hypothesis, as in Mathlib's
`ContinuousLinearMap.instStarOrderedRingRCLike`. Mathlib provides it on every complex Hilbert
space, so over `ℂ` both results below hold for every complete source.

## Main declarations

* `TauCeti.HasMinMaxLowerBound.of_completeSpace`: a Hilbert space with the continuous functional
  calculus has the converse min–max localization property towards every inner product space.
* `ContinuousLinearMap.kyFanGauge_add_le`: the Ky Fan triangle inequality
  `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)` for operators out of such a space.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II.
-/

public section

open RCLike
open scoped InnerProduct InnerProductSpace NNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

namespace TauCeti

open ContinuousLinearMap

/-- **Converse min–max localization on Hilbert spaces.** If `E` is a Hilbert space carrying the
continuous functional calculus (for instance any complex Hilbert space), then for every bounded
`T : E →L[𝕜] F` into an inner product space and every `0 ≤ r < aₙ(T)`, the map `T` is
`s`-coercive with `r < s` on the span of `n + 1` linearly independent vectors. -/
theorem HasMinMaxLowerBound.of_completeSpace : HasMinMaxLowerBound 𝕜 E F := by
  refine hasMinMaxLowerBound_iff.mpr fun T n r hr0 hr ↦ ?_
  obtain ⟨c, hrc, hca⟩ := exists_between hr
  have hc0 : 0 ≤ c := hr0.trans hrc.le
  -- Compose with the completion of `F` so that `T` has an adjoint; norms are unchanged.
  set T' : E →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL.comp T
  set A : E →L[𝕜] E := T'† ∘L T'
  have hA : IsSelfAdjoint A := T'.isPositive_adjoint_comp_self.isSelfAdjoint
  -- The Rayleigh form of `B = T† T - c²` is `‖T x‖² - c² ‖x‖²`.
  set B : E →L[𝕜] E := A - algebraMap ℝ (E →L[𝕜] E) (c ^ 2)
  have hB : IsSelfAdjoint B := hA.sub (cfc_const (c ^ 2) A ▸ cfc_predicate _ A)
  have hTB : ∀ x, re ⟪B x, x⟫_𝕜 = ‖T x‖ ^ 2 - c ^ 2 * ‖x‖ ^ 2 := fun x ↦ by
    rw [sub_apply, inner_sub_left, map_sub, Algebra.algebraMap_eq_smul_one,
      ← algebraMap_smul 𝕜 (c ^ 2) (1 : E →L[𝕜] E), smul_apply, one_apply_eq_self, inner_smul_left,
      RCLike.algebraMap_eq_ofReal, conj_ofReal, re_ofReal_mul, inner_self_eq_norm_sq,
      ← T'.apply_norm_sq_eq_inner_adjoint_left]
    simp [T']
  have := instStarOrderedRingRCLike (𝕜 := 𝕜) (H := E)
  rcases le_or_gt (Module.rank 𝕜 B⁺.range) n with hV | hV
  · -- If the range of `B⁺` had rank at most `n`, then `aₙ(T) ≤ c`: on its orthogonal complement,
    -- the kernel of `B⁺`, the Rayleigh form of `B` is nonpositive.
    have hbound : ‖T ∘L B⁺.rangeᗮ.subtypeL‖ ≤ c := by
      refine opNorm_le_bound _ hc0 fun ⟨x, hx⟩ ↦ ?_
      have hBx : B⁺ x = 0 := by
        rwa [orthogonal_range, (CFC.posPart_nonneg B).isSelfAdjoint.adjoint_eq] at hx
      have h := re_inner_nonpos_of_posPart_apply_eq_zero hB hBx
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow]
      simp only [comp_apply, Submodule.subtypeL_apply, ← Submodule.norm_coe]
      linarith [hTB x]
    have h : (T.singularValue n : ℝ) ≤ ‖T ∘L B⁺.rangeᗮ.subtypeL‖ :=
      T.singularValue_le_nnnorm_comp_orthogonal hV
    linarith
  · -- Otherwise the range of `B⁺` contains `n + 1` linearly independent vectors, and on it `T`
    -- is `c`-coercive.
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank (n := n + 1)
      (by exact_mod_cast Cardinal.natCast_add_one_le_iff.mpr hV)
    refine ⟨c, hrc, fun i ↦ v i, hv.map' _ (Submodule.ker_subtype _), fun x hx ↦ ?_⟩
    have hxB : x ∈ B⁺.range := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (v i).2) hx
    have h := re_inner_nonneg_of_mem_range_posPart hxB
    rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, mul_pow]
    linarith [hTB x]

end TauCeti

namespace ContinuousLinearMap

/-- **The Ky Fan triangle inequality for approximation numbers.** For bounded operators out of a
Hilbert space carrying the continuous functional calculus (for instance any complex Hilbert
space) into an inner product space, `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`. -/
theorem kyFanGauge_add_le (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k :=
  TauCeti.HasMinMaxLowerBound.of_completeSpace.kyFanGauge_add_le S T k

end ContinuousLinearMap

end
