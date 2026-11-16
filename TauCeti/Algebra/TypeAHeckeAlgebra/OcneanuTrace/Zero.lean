/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.Algebra.TypeAHeckeAlgebra.Regular.Form
public import TauCeti.RingTheory.TraceFunctional.Radical

/-!
# Positivity and faithfulness of the zero-parameter Ocneanu trace

At `z = 0`, the Ocneanu trace agrees on every finite stage with the canonical symmetrizing trace
(`TauCeti.TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero`). Consequently it is `⋆`-positive
over any commutative `StarOrderedRing` with star-fixed parameter
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_zero_star_mul_self_nonneg`), and over `ℝ` or `ℂ`
its trace form is anisotropic
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_zero_star_mul_self_eq_zero_iff`) and its trace
radical is trivial (`TauCeti.InfiniteTypeAHeckeAlgebra.traceRadical_ocneanuTrace_zero`).
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

/-- **Positivity of the `z = 0` Ocneanu trace** over any commutative `StarOrderedRing`. -/
theorem ocneanuTrace_zero_star_mul_self_nonneg {R : Type*} [CommRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] {q : Rˣ} [Fact (IsSelfAdjoint (q : R))]
    (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ ocneanuTrace R q 0 (star x * x) := by
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx; obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul,
    ← TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero (permCoxeterSystem n),
    TypeAHeckeAlgebra.canonicalTrace_star_mul]
  exact Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _

/-- Over `ℝ` or `ℂ` (`RCLike 𝕜`), the `z = 0` Ocneanu trace form is anisotropic. -/
@[simp]
theorem ocneanuTrace_zero_star_mul_self_eq_zero_iff {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ}
    [Fact (IsSelfAdjoint (q : 𝕜))] (x : InfiniteTypeAHeckeAlgebra 𝕜 q) :
    ocneanuTrace 𝕜 q 0 (star x * x) = 0 ↔ x = 0 := by
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx; obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul,
    ← TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero (permCoxeterSystem n),
    TypeAHeckeAlgebra.canonicalTrace_star_mul_self_eq_zero_iff,
    map_eq_zero_iff _ (TypeAHeckeAlgebra.toInfinite_injective 𝕜 q n)]

/-- **Faithfulness of the `z = 0` Ocneanu trace** over `ℝ` or `ℂ`. -/
theorem traceRadical_ocneanuTrace_zero {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ}
    [Fact (IsSelfAdjoint (q : 𝕜))] :
    (ocneanuTrace 𝕜 q 0).traceRadical (isMarkovTrace_ocneanuTrace 0).map_mul_comm = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ (ocneanuTrace_zero_star_mul_self_eq_zero_iff x).mp ?_
  rw [LinearMap.mem_traceRadical] at hx
  rw [(isMarkovTrace_ocneanuTrace 0).map_mul_comm]
  exact hx (star x)

end TauCeti.InfiniteTypeAHeckeAlgebra
