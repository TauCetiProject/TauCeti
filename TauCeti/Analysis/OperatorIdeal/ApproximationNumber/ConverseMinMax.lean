/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
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

The result needs no spectral theory, so it holds over every `RCLike` field, and the target space
need not be complete. In particular it covers every finite-dimensional source space.

## Main declarations

* `TauCeti.HasMinMaxLowerBound.of_completeSpace`: a Hilbert space has the converse min–max
  localization property towards every inner product space.
* `ContinuousLinearMap.kyFanGauge_add_le`: the Ky Fan triangle inequality
  `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)` for operators out of a Hilbert space.

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

namespace TauCeti

open ContinuousLinearMap

/-- **Converse min–max localization on Hilbert spaces.** If `E` is a Hilbert space, then for every
bounded `T : E →L[𝕜] F` into an inner product space and every `0 ≤ r < aₙ(T)`, the map `T` is
`s`-coercive with `r < s` on the span of `n + 1` linearly independent vectors. -/
theorem HasMinMaxLowerBound.of_completeSpace : HasMinMaxLowerBound 𝕜 E F := by
  classical
  refine hasMinMaxLowerBound_iff.mpr fun T n r hr0 hr ↦ ?_
  obtain ⟨c, hrc, hca⟩ := exists_between hr
  have hc0 : 0 ≤ c := hr0.trans hrc.le
  -- Compose with the completion of `F` so that `T` has an adjoint; inner products are unchanged.
  set T' : E →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL.comp T
  set D : E →L[𝕜] E := T'† ∘L T' - ((c ^ 2 : ℝ) : 𝕜) • 1
  have hD : ∀ y w, ⟪D y, w⟫_𝕜 = ⟪T y, T w⟫_𝕜 - ((c ^ 2 : ℝ) : 𝕜) * ⟪y, w⟫_𝕜 := fun y w ↦ by
    simp [D, T', inner_sub_left, inner_smul_left, adjoint_inner_left]
  -- `P k`: `T` is strictly `c`-coercive on the span of `k` linearly independent vectors.
  let P : ℕ → Prop := fun k ↦ ∃ v : Fin k → E, LinearIndependent 𝕜 v ∧
    ∀ x ∈ Submodule.span 𝕜 (Set.range v), x ≠ 0 → c ^ 2 * ‖x‖ ^ 2 < ‖T x‖ ^ 2
  have hPk : P (Nat.findGreatest P (n + 1)) :=
    Nat.findGreatest_spec (Nat.zero_le _) ⟨Fin.elim0, linearIndependent_empty_type, by simp⟩
  rcases (Nat.findGreatest_le (P := P) (n + 1)).eq_or_lt with hk | hk
  · -- A maximal family has `n + 1` vectors, on whose span `T` is `c`-coercive.
    rw [hk] at hPk
    obtain ⟨v, hv, hvc⟩ := hPk
    refine ⟨c, hrc, v, hv, fun x hx ↦ ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, mul_pow]
    exact (hvc x hx hx0).le
  · -- Otherwise a maximal family `v` has at most `n` vectors. The `D`-images of its span form a
    -- subspace `U` of rank at most `n`, and `T` has norm at most `c` on `Uᗮ`: a vector `w` of
    -- `Uᗮ` with `c ‖w‖ < ‖T w‖` would extend `v`. So `aₙ(T) ≤ c`.
    obtain ⟨v, hv, hvc⟩ := hPk
    set U := (Submodule.span 𝕜 (Set.range v)).map (D : E →ₗ[𝕜] E)
    have hU : Module.rank 𝕜 U ≤ n := (rank_map_le _ _).trans <| by
      rw [rank_span hv, Cardinal.mk_fintype, Set.card_range_of_injective hv.injective,
        Fintype.card_fin]
      exact_mod_cast Nat.lt_succ_iff.mp hk
    have hbound : ‖T ∘L Uᗮ.subtypeL‖ ≤ c := by
      refine opNorm_le_bound _ hc0 fun ⟨w, hw⟩ ↦ ?_
      simp only [comp_apply, Submodule.subtypeL_apply, ← Submodule.norm_coe]
      have hcross : ∀ y ∈ Submodule.span 𝕜 (Set.range v),
          ⟪T w, T y⟫_𝕜 = ((c ^ 2 : ℝ) : 𝕜) * ⟪w, y⟫_𝕜 := fun y hy ↦ by
        have h := Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem hy) hw
        rw [ContinuousLinearMap.coe_coe, hD, sub_eq_zero] at h
        rw [← inner_conj_symm, h, map_mul, conj_ofReal, inner_conj_symm]
      by_contra! hlt
      have hw2 : c ^ 2 * ‖w‖ ^ 2 < ‖T w‖ ^ 2 := by
        rw [← mul_pow]; exact pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
      refine Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hk ⟨Fin.cons w v,
        linearIndependent_finCons.mpr ⟨hv, fun hwv ↦ ?_⟩, fun x hx hx0 ↦ ?_⟩
      · have h := congrArg re (hcross w hwv)
        rw [re_ofReal_mul, inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
        linarith
      · rw [Fin.range_cons, Submodule.mem_span_insert] at hx
        obtain ⟨a, y, hy, rfl⟩ := hx
        have hx : ‖T (a • w + y)‖ ^ 2 - c ^ 2 * ‖a • w + y‖ ^ 2 =
            ‖a‖ ^ 2 * (‖T w‖ ^ 2 - c ^ 2 * ‖w‖ ^ 2) + (‖T y‖ ^ 2 - c ^ 2 * ‖y‖ ^ 2) := by
          rw [map_add, map_smul, norm_add_sq (𝕜 := 𝕜), norm_add_sq (𝕜 := 𝕜), inner_smul_left,
            inner_smul_left, hcross y hy, norm_smul, norm_smul, mul_left_comm, re_ofReal_mul]
          ring
        have hy0 : 0 ≤ ‖T y‖ ^ 2 - c ^ 2 * ‖y‖ ^ 2 := by
          rcases eq_or_ne y 0 with rfl | hy0
          · simp
          · linarith [hvc y hy hy0]
        rcases eq_or_ne a 0 with rfl | ha
        · simp only [zero_smul, zero_add] at hx0 ⊢
          linarith [hvc y hy hx0]
        · have : 0 < ‖a‖ ^ 2 * (‖T w‖ ^ 2 - c ^ 2 * ‖w‖ ^ 2) :=
            mul_pos (by positivity) (by linarith)
          linarith
    have h : (T.singularValue n : ℝ) ≤ ‖T ∘L Uᗮ.subtypeL‖ :=
      T.singularValue_le_nnnorm_comp_orthogonal hU
    linarith

end TauCeti

namespace ContinuousLinearMap

/-- **The Ky Fan triangle inequality for approximation numbers.** For bounded operators out of a
Hilbert space into an inner product space, `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)`. -/
theorem kyFanGauge_add_le (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k :=
  TauCeti.HasMinMaxLowerBound.of_completeSpace.kyFanGauge_add_le S T k

end ContinuousLinearMap

end
