/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.Int
public import TauCeti.Analysis.Normed.Group.Pi
import TauCeti.Analysis.Normed.Operator.RingOpNorm
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Additive maps on a subgroup of an integer lattice are bounded by the sup norm

Let `n : G →+ (κ → ℤ)` be an injective additive map with `κ` finite, which identifies `G` with a
subgroup of the integer lattice `κ → ℤ`. Every additive map `f` from `G` to a seminormed group is
bounded by the sup norm of `n`: there is a constant `C` with `‖f g‖ ≤ C * ‖n g‖` for all `g`
(`AddMonoidHom.exists_norm_le_mul_norm_of_injective`). For real-valued `f` this is because `ℝ`
is divisible, hence an injective `ℤ`-module, so `f` extends along `n` to an additive map on all
of `κ → ℤ`; such a map is bounded by the sup norm, with the sum of the norms of the images of
the standard basis vectors as constant (`LinearMap.norm_pi_apply_le_sum` over `ℤ`). In general
`G` is free of finite rank, as a subgroup of `κ → ℤ`, and `f` is bounded through the coordinates
of a basis, which are real-valued after casting. A nonzero integer vector has sup norm at least `1`
(`TauCeti.one_le_pi_norm_of_ne_zero`), so these are bounds on the whole lattice with no restriction
on the size of the coefficients, and `‖n g‖` is a norm detecting `g ≠ 0`.

The bound is the arithmetic of the winding argument by which Ozsváth and Szabó make a Heegaard
diagram admissible. For two additive maps `n` and `b` from `G` to `κ → ℤ` with `n` injective,
and a real number `t`, consider the real numbers `b g i + t * |n g i|` and
`b g i - t * |n g i|`: when `G` is the group of periodic domains, `n g i` is the multiplicity of
the boundary of `g` on the `i`-th attaching curve, and winding `t` times in both directions along
a curve dual to it produces regions with multiplicities `b g i + t * n g i` and
`b g i - t * n g i`, which are these two numbers in some order. At a coordinate `i` where
`|n g i|` attains the sup norm of `n g`, the first is at least `(t - B) * ‖n g‖` and the second
at most `-((t - B) * ‖n g‖)`, for a constant `B` depending only on `n` and `b`
(`AddMonoidHom.exists_forall_exists_le_add_mul_abs_and_sub_mul_abs_le`). So winding amounts `t`
larger than `B` make the positive and negative multiplicities of every nonzero `g` grow linearly
in `‖n g‖`, uniformly in `g`, and dominate any additive functional, such as the Maslov index.

## Main results

* `AddMonoidHom.exists_norm_le_mul_norm_of_injective`: an additive map on a subgroup of an
  integer lattice is bounded by the sup norm.
* `AddMonoidHom.exists_forall_exists_le_add_mul_abs_and_sub_mul_abs_le`: the winding estimate.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §5, Lemmas 5.4 and 5.6 (winding
  along curves dual to the attaching curves makes a diagram weakly, respectively strongly,
  admissible).
-/

public section

open Finset

namespace AddMonoidHom

variable {G κ F : Type*} [AddCommGroup G] [Fintype κ]

/-- The real-valued case of `AddMonoidHom.exists_norm_le_mul_norm_of_injective`: as `ℝ` is
divisible, `f` extends along `n` to an additive map on all of `κ → ℤ`. -/
private theorem exists_abs_le_mul_norm_of_injective (f : G →+ ℝ) {n : G →+ (κ → ℤ)}
    (hn : Function.Injective n) : ∃ C, 0 ≤ C ∧ ∀ g, |f g| ≤ C * ‖n g‖ := by
  classical
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom n hn f
  refine ⟨∑ i, ‖ψ (Pi.single i 1)‖, sum_nonneg fun i _ ↦ norm_nonneg _, fun g ↦ ?_⟩
  rw [← hψ, comp_apply, ← Real.norm_eq_abs]
  exact ψ.toIntLinearMap.norm_pi_apply_le_sum (n g)

/-- **Additive maps on a subgroup of an integer lattice are bounded by the sup norm.** If
`n : G →+ (κ → ℤ)` is injective and `κ` is finite, every additive map `f` from `G` to a
seminormed group satisfies `‖f g‖ ≤ C * ‖n g‖` for some constant `C ≥ 0` and all `g`. -/
theorem exists_norm_le_mul_norm_of_injective [SeminormedAddCommGroup F] (f : G →+ F)
    {n : G →+ (κ → ℤ)} (hn : Function.Injective n) :
    ∃ C, 0 ≤ C ∧ ∀ g, ‖f g‖ ≤ C * ‖n g‖ := by
  -- `G` embeds in `κ → ℤ`, so it is free of finite rank; expand `g` in a basis `e` and bound
  -- each coordinate by the real-valued case.
  have : Module.Finite ℤ G := Module.Finite.of_injective n.toIntLinearMap hn
  have : Module.IsTorsionFree ℤ G := hn.moduleIsTorsionFree n fun r g ↦ map_zsmul n r g
  let e := Module.Free.chooseBasis ℤ G
  choose C hC₀ hC using fun j ↦
    exists_abs_le_mul_norm_of_injective ((Int.castAddHom ℝ).comp (e.coord j).toAddMonoidHom) hn
  refine ⟨∑ j, C j * ‖f (e j)‖, sum_nonneg fun j _ ↦ by have := hC₀ j; positivity,
    fun g ↦ ?_⟩
  conv_lhs => rw [← e.sum_repr g, map_sum]
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [map_zsmul]
  refine (norm_zsmul_le _ _).trans ?_
  rw [mul_right_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  simpa [Int.norm_eq_abs] using hC j g

/-- **The winding estimate.** Let `n, b : G →+ (κ → ℤ)` be additive with `n` injective. There is
a constant `B ≥ 0` such that every `g ≠ 0` has a coordinate `i` at which, for every real `t`,
`b g i + t * |n g i| ≥ (t - B) * ‖n g‖` and `b g i - t * |n g i| ≤ -((t - B) * ‖n g‖)`. -/
theorem exists_forall_exists_le_add_mul_abs_and_sub_mul_abs_le {n : G →+ (κ → ℤ)}
    (hn : Function.Injective n) (b : G →+ (κ → ℤ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g, g ≠ 0 → ∃ i, ∀ t : ℝ,
      (t - B) * ‖n g‖ ≤ b g i + t * |(n g i : ℝ)| ∧
        b g i - t * |(n g i : ℝ)| ≤ -((t - B) * ‖n g‖) := by
  obtain ⟨B, hB, hb⟩ := exists_norm_le_mul_norm_of_injective b hn
  refine ⟨B, hB, fun g hg ↦ ?_⟩
  obtain ⟨i₀, -⟩ := Function.ne_iff.mp ((map_ne_zero_iff n hn).mpr hg)
  have : Nonempty κ := ⟨i₀⟩
  obtain ⟨i, hi⟩ := Pi.exists_norm_apply_eq_norm (n g)
  rw [Int.norm_eq_abs] at hi
  have hbi : |(b g i : ℝ)| ≤ B * ‖n g‖ := by
    rw [← Int.norm_eq_abs]
    exact (norm_le_pi_norm (b g) i).trans (hb g)
  refine ⟨i, fun t ↦ ⟨?_, ?_⟩⟩ <;> rw [hi] <;> linarith [abs_le.mp hbi]

end AddMonoidHom
