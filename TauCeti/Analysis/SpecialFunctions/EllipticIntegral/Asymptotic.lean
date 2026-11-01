/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre

/-!
# A vanishing boundary term for the complete elliptic integral

Although `K(k)` diverges as `k → 1⁻`, the product `(1 - k²) K(k)` tends to zero.
This boundary term occurs when evaluating the constant in Legendre's relation between
complete elliptic integrals of complementary moduli.

The elementary bound `K(k) ≤ π / (2 √(1 - k²))` suffices: multiplication by `1 - k²`
gives an upper bound tending to zero. No logarithmic asymptotic expansion is needed.

## References

* NIST *Digital Library of Mathematical Functions*, §§19.7 and 19.12.
-/

public section

namespace TauCeti.Real

open _root_.Real Filter Set
open scoped Topology

/-- The singularity of `K` at modulus one is killed by the factor `1 - k²`.
This is the vanishing boundary term used in Legendre's relation. -/
theorem tendsto_one_sub_sq_mul_legendreK_nhdsLT_one :
    Tendsto (fun k : ℝ ↦ (1 - k ^ 2) * legendreK k) (𝓝[<] 1) (𝓝 0) := by
  have hupper : Tendsto (fun k : ℝ ↦ π / 2 * √(1 - k ^ 2)) (𝓝[<] 1) (𝓝 0) := by
    have h := (by fun_prop : Continuous fun k : ℝ ↦ π / 2 * √(1 - k ^ 2)).tendsto 1
    simpa using h.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ k : ℝ in 𝓝[<] 1, k ∈ Ioo 0 1 := Ioo_mem_nhdsLT one_pos
  refine tendsto_const_nhds.squeeze' hupper ?_ ?_
  · filter_upwards [hmem] with k hk
    have hk' : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
    exact mul_nonneg (by linarith) (legendreK_pos hk').le
  · filter_upwards [hmem] with k hk
    have hk' : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
    have hs : 0 < √(1 - k ^ 2) := sqrt_pos.2 (by linarith)
    calc
      (1 - k ^ 2) * legendreK k ≤ (1 - k ^ 2) * (π / 2 / √(1 - k ^ 2)) :=
        mul_le_mul_of_nonneg_left (legendreK_le_pi_div_two_div_sqrt hk') (by linarith)
      _ = π / 2 * √(1 - k ^ 2) := by
        field_simp [hs.ne']
        nlinarith [sq_sqrt (by linarith : 0 ≤ 1 - k ^ 2)]

end TauCeti.Real
