/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Basic
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Examples: the energy identity of a two-form on a product with a circle

On a product `X = S¹ × Y` with unit vector field `T = ∂ₛ`, the unperturbed Seiberg–Witten
equations give the integrated identity
`0 = ‖∇_T ψ‖² + ‖B_A ψ‖² + ‖ι_T F_A‖² + 2π² ⟨c₁(L)², [X]⟩`. Its curvature terms come from the
pointwise identity `2 ⟨ds ∧ ι_T F, F⁺⟩ dvol = |ι_T F|² dvol + (F ∧ F) / 2` for a real two-form `F`
(`Orientation.inner_ιMulti_twoVectorContraction_add_hodgeStar`). This file checks that identity
on a two-form split along the circle, `F = ds ∧ a + b`, where `a` is a covector and `b` a
two-vector of `Y`, as `F = i F_A` is for a connection pulled back to `X` up to its `ds`-component.

Work in an oriented four-dimensional real inner product space `V` with a unit vector `s`, standing
for `ds`, a vector `a ⟂ s` and a two-vector `b` with `s ⌟ b = 0`. Then, writing `s ∧ a` for
`ιMulti ℝ 2 ![s, a]`:

* `ι_T F = a`: the contraction of `F` by `s` is `a` (`twoVectorContraction_ιMulti_add_apply`);
* `F ∧ F = 2 ds ∧ a ∧ b`: the squares of `s ∧ a` and of `b` vanish, the latter because `b` lives
  on the three-dimensional complement of `s`, and the two-forms `s ∧ a` and `b` commute
  (`TauCeti.ExteriorAlgebra.ι_mul_ι_add_mul_self`), so `vol (F ∧ F) = 2 vol (s ∧ a ∧ b)` for any
  volume form `vol` (`wedgePairing_ιMulti_add_self`);
* hence `2 ⟨ds ∧ a, F⁺⟩ dvol = |a|² dvol + ds ∧ a ∧ b`, with `2 F⁺ = F + ⋆F`
  (`inner_ιMulti_add_hodgeStar_ιMulti_add`): both sides of the pointwise identity equal
  `|a|² dvol + ds ∧ a ∧ b`.

## References

* S. Baldridge, *Seiberg–Witten invariants, orbifolds, and circle actions*, Trans. Amer. Math.
  Soc. 355 (2003), 1669–1697.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

namespace TauCeti.Examples.ProductEnergy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {s a : V} {b : ⋀[ℝ]^2 V}

/-- **`ι_T F = a`.** If `s` is a unit vector, `a ⟂ s` and `s ⌟ b = 0`, then the contraction of
`F = s ∧ a + b` by `s` is `a`. -/
theorem twoVectorContraction_ιMulti_add_apply (hs : ‖s‖ = 1) (hsa : ⟪s, a⟫ = 0)
    (hb : twoVectorContraction b s = 0) :
    twoVectorContraction (ιMulti ℝ 2 ![s, a] + b) s = a := by
  rw [twoVectorContraction_add, LinearMap.add_apply, hb, twoVectorContraction_ιMulti]
  simp [hsa, hs]

variable [FiniteDimensional ℝ V]

/-- **`F ∧ F = 2 ds ∧ a ∧ b`.** In a four-dimensional space with a volume equivalence `vol`, if
`s ≠ 0` and `s ⌟ b = 0`, then `F = s ∧ a + b` satisfies `vol (F ∧ F) = 2 vol (s ∧ a ∧ b)`. -/
theorem wedgePairing_ιMulti_add_self (vol : ⋀[ℝ]^(finrank ℝ V) V ≃ₗ[ℝ] ℝ)
    (hkk : 2 + 2 = finrank ℝ V) (hs : s ≠ 0) (hb : twoVectorContraction b s = 0) :
    wedgePairing vol hkk (ιMulti ℝ 2 ![s, a] + b) (ιMulti ℝ 2 ![s, a] + b) =
      2 * wedgePairing vol hkk (ιMulti ℝ 2 ![s, a]) b := by
  -- The functional `‖s‖⁻² ⟪s, ·⟫` takes the value `1` on `s` and kills `b`.
  have hss : ((‖s‖ ^ 2)⁻¹ • innerₗ V s) s = 1 := by
    rw [LinearMap.smul_apply, innerₗ_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul,
      inv_mul_cancel₀ (by positivity)]
  have hdb : CliffordAlgebra.contractLeft ((‖s‖ ^ 2)⁻¹ • innerₗ V s)
      (b : ExteriorAlgebra ℝ V) = 0 := by
    rw [map_smul, LinearMap.smul_apply, ← TauCeti.ι_twoVectorContraction, hb, map_zero, smul_zero]
  have hwedge : wedge ℝ V 2 2 (ιMulti ℝ 2 ![s, a] + b) (ιMulti ℝ 2 ![s, a] + b) =
      2 • wedge ℝ V 2 2 (ιMulti ℝ 2 ![s, a]) b := by
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower, exteriorPower.coe_wedge, exteriorPower.coe_wedge,
      Submodule.coe_add, exteriorPower.coe_ιMulti_two]
    exact TauCeti.ExteriorAlgebra.ι_mul_ι_add_mul_self hss (by omega) a b.property hdb
  simp only [LinearMap.compr₂_apply, hwedge, map_nsmul, nsmul_eq_mul, Nat.cast_ofNat]

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **The pointwise energy identity for `F = ds ∧ a + b`.** In an oriented four-dimensional space,
if `s` is a unit vector, `a ⟂ s` and `s ⌟ b = 0`, then `F = s ∧ a + b` satisfies
`⟪s ∧ a, F + ⋆F⟫ = ‖a‖² + vol (s ∧ a ∧ b)`: both sides of
`2 ⟨ds ∧ ι_T F, F⁺⟩ dvol = |ι_T F|² dvol + (F ∧ F) / 2` equal `|a|² dvol + ds ∧ a ∧ b`. -/
theorem inner_ιMulti_add_hodgeStar_ιMulti_add (hkk : 2 + 2 = finrank ℝ V) (hs : ‖s‖ = 1)
    (hsa : ⟪s, a⟫ = 0) (hb : twoVectorContraction b s = 0) :
    ⟪ιMulti ℝ 2 ![s, a], ιMulti ℝ 2 ![s, a] + b + o.hodgeStar hkk (ιMulti ℝ 2 ![s, a] + b)⟫ =
      ‖a‖ ^ 2 + wedgePairing o.volumeEquiv hkk (ιMulti ℝ 2 ![s, a]) b := by
  have hs₀ : s ≠ 0 := norm_ne_zero_iff.1 (hs ▸ one_ne_zero)
  have h := o.inner_ιMulti_twoVectorContraction_add_hodgeStar hkk hs (ιMulti ℝ 2 ![s, a] + b)
  rw [twoVectorContraction_ιMulti_add_apply hs hsa hb,
    wedgePairing_ιMulti_add_self o.volumeEquiv hkk hs₀ hb] at h
  rw [h]
  ring

end TauCeti.Examples.ProductEnergy
