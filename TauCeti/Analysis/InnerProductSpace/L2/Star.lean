/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# Complex conjugation on `L²`

Pointwise complex conjugation `star` on `L²(ν)` interacts with the inner product by
`⟪star f, star g⟫ = ⟪g, f⟫`, and the bilinear pairing `⟪star f, g⟫ = ∫ f g` is symmetric.
Consequently the pointwise conjugate of a Hilbert basis of `L²(ν)` is again a Hilbert basis.

## Main declarations

* `MeasureTheory.Lp.inner_star_star`: `⟪star f, star g⟫ = ⟪g, f⟫`.
* `MeasureTheory.Lp.inner_star_comm`: `⟪star f, g⟫ = ⟪star g, f⟫`.
* `HilbertBasis.star`: the complex conjugate of a Hilbert basis of `L²`.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

variable {β 𝕜 : Type*} [RCLike 𝕜] {mβ : MeasurableSpace β} {ν : Measure β}

namespace MeasureTheory.Lp

/-- Conjugating both arguments of the `L²` inner product swaps them. -/
@[simp]
theorem inner_star_star (f g : Lp 𝕜 2 ν) : ⟪star f, star g⟫_𝕜 = ⟪g, f⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_star f, coeFn_star g] with y hf hg
  simp [hf, hg, RCLike.inner_apply, mul_comm]

/-- Conjugating the first argument of the `L²` inner product gives the bilinear pairing
`∫ f g`, which is symmetric. -/
theorem inner_star_comm (f g : Lp 𝕜 2 ν) : ⟪star f, g⟫_𝕜 = ⟪star g, f⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_star f, coeFn_star g] with y hf hg
  simp [hf, hg, RCLike.inner_apply, mul_comm]

end MeasureTheory.Lp

namespace HilbertBasis

variable {ι : Type*}

/-- The pointwise complex conjugate of a Hilbert basis of `L²(ν)` is again a Hilbert basis. -/
protected def star (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν) :=
  HilbertBasis.mkOfOrthogonalEqBot (v := fun i ↦ star (b i))
    (by
      classical
      have hb := orthonormal_iff_ite.1 b.orthonormal
      refine orthonormal_iff_ite.2 fun i j ↦ ?_
      rw [Lp.inner_star_star, hb j i]
      simp only [eq_comm])
    (by
      refine (Submodule.eq_bot_iff _).2 fun h hh ↦ ?_
      rw [Submodule.mem_orthogonal] at hh
      rw [← star_star h, star_eq_zero]
      refine b.eq_zero_of_forall_inner_eq_zero fun i ↦ ?_
      rw [Lp.inner_star_comm]
      exact hh _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp]
theorem star_apply (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) (i : ι) : b.star i = star (b i) := by
  rw [HilbertBasis.star, HilbertBasis.coe_mkOfOrthogonalEqBot]

end HilbertBasis
