/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import Mathlib.Tactic.FieldSimp
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Positivity
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Wenzl.Realization
import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Zero
import TauCeti.Analysis.RCLike.Basic

/-!
# Positivity of the Ocneanu trace on Wenzl's positive-real parameter set

For a real nonzero parameter `q : ℂˣ` (`IsSelfAdjoint (q : ℂ)`) with `Q = q ^ 2 > 0` and any
projection parameter `η ∈ TauCeti.wenzlPositiveSet Q`, the Ocneanu trace with Markov parameter
`z = q * η - q⁻¹ * (1 - η)` is `⋆`-positive on `TauCeti.InfiniteTypeAHeckeAlgebra ℂ q`
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg`, bundled as
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPositiveFunctional`).

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
-/

public section

open scoped ComplexOrder

namespace TauCeti.InfiniteTypeAHeckeAlgebra

/-- **Positivity of the Ocneanu trace across Wenzl's positive-real parameter set.** For real nonzero
`q : ℂˣ` with `(Q : ℂ) = (q : ℂ) ^ 2` and `η ∈ wenzlPositiveSet Q`, the Ocneanu trace at
`z = q * η - q⁻¹ * (1 - η)` is nonnegative on every `star x * x`. -/
theorem ocneanuTrace_star_mul_self_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (star x * x) := by
  have hQ0 : 0 < Q := RCLike.pos_of_ofReal_eq_sq_of_isSelfAdjoint q.ne_zero Fact.out hQ
  obtain ⟨n, y, rfl⟩ := exists_toInfinite_eq x
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul]; by_cases hreg : Q = 1 ∧ η = 1 / 2
  · rcases hreg with ⟨rfl, rfl⟩
    have hz0 : (q : ℂ) * ((1 / 2 : ℝ) : ℂ) - (↑q⁻¹ : ℂ) * (1 - ((1 / 2 : ℝ) : ℂ)) = 0 := by
      have _ := q.ne_zero; rw [Units.val_inv_eq_inv_val]; push_cast; field_simp
      linear_combination (by simpa using hQ.symm : (q : ℂ) ^ 2 = 1)
    rw [hz0, map_mul, TypeAHeckeAlgebra.toInfinite_star]
    exact ocneanuTrace_zero_star_mul_self_nonneg _
  · obtain ⟨r⟩ := TypeAHeckeAlgebra.nonempty_countableAtomicRealization_ocneanuTrace hQ0 hQ hη hreg
    exact r.trace_eq (star y * y) ▸ TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg
      r.pos q r.summable_norm_weight (fun a ↦ Complex.zero_le_real.mpr (r.weight_pos a).le) y

/-- The complex Ocneanu trace on `InfiniteTypeAHeckeAlgebra ℂ q` bundled as a
`StarPositiveFunctional` for real nonzero `q : ℂˣ` and `η ∈ wenzlPositiveSet Q`. -/
noncomputable def ocneanuPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    StarPositiveFunctional (InfiniteTypeAHeckeAlgebra ℂ q) where
  toLinearMap := ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
  square_nonneg := ocneanuTrace_star_mul_self_nonneg hQ hη

/-- Forgetting positivity recovers the underlying Ocneanu trace. -/
@[simp] theorem toLinearMap_ocneanuPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {Q : ℝ} (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    (ocneanuPositiveFunctional q hQ hη).toLinearMap = ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ)
      * (1 - η)) := (rfl)

/-- Evaluating `ocneanuPositiveFunctional` at an element recovers `ocneanuTrace`. -/
@[simp] theorem ocneanuPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) : ocneanuPositiveFunctional q hQ hη x =
      ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) x := (rfl)

end TauCeti.InfiniteTypeAHeckeAlgebra
