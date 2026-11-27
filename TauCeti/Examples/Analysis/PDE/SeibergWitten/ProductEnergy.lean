/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Basic
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
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
  (`wedgePairing_ιMulti_add_self`);
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

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

open _root_.ExteriorAlgebra (ι ι_add_mul_swap ι_sq_zero ι_mul_eq_involute_mul) in
/-- **`F ∧ F = 2 ds ∧ a ∧ b`.** In an oriented four-dimensional space, if `s ≠ 0` and
`s ⌟ b = 0`, then `F = s ∧ a + b` satisfies `vol (F ∧ F) = 2 vol (s ∧ a ∧ b)`. -/
theorem wedgePairing_ιMulti_add_self (hkk : 2 + 2 = finrank ℝ V) (hs : s ≠ 0)
    (hb : twoVectorContraction b s = 0) :
    wedgePairing o.volumeEquiv hkk (ιMulti ℝ 2 ![s, a] + b) (ιMulti ℝ 2 ![s, a] + b) =
      2 * wedgePairing o.volumeEquiv hkk (ιMulti ℝ 2 ![s, a]) b := by
  -- The computation takes place in the exterior algebra, with `g = s ∧ a`.
  set g : ExteriorAlgebra ℝ V := ι ℝ s * ι ℝ a with hg
  -- The functional `⟪s, ·⟫` takes the value `1` on `‖s‖⁻² s`.
  have hss : innerₗ V s ((‖s‖ ^ 2)⁻¹ • s) = 1 := by
    rw [map_smul, innerₗ_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul,
      inv_mul_cancel₀ (by positivity)]
  -- `s ⌟ b = 0` in the exterior algebra, so `b ∧ b = 0` in dimension four.
  have hdb : CliffordAlgebra.contractLeft (innerₗ V s) (b : ExteriorAlgebra ℝ V) = 0 := by
    rw [← TauCeti.ι_twoVectorContraction, hb, map_zero]
  have hbb : (b : ExteriorAlgebra ℝ V) * b = 0 :=
    TauCeti.ExteriorAlgebra.mul_eq_zero_of_contractLeft_eq_zero hss (by omega) b.property
      b.property hdb hdb
  -- `g ∧ g = 0`, since `s ∧ s = 0`.
  have hgg : g * g = 0 := by
    have h := ι_add_mul_swap (R := ℝ) a s
    rw [add_eq_zero_iff_eq_neg] at h
    calc g * g = ι ℝ s * (ι ℝ a * ι ℝ s) * ι ℝ a := by simp only [hg, mul_assoc]
      _ = 0 := by rw [h, mul_neg, ← mul_assoc, ι_sq_zero, zero_mul, neg_zero, zero_mul]
  -- A two-form is fixed by the grade involution, so it commutes with the two-form `g`.
  have hinv :
      CliffordAlgebra.involute (Q := (0 : QuadraticForm ℝ V)) (b : ExteriorAlgebra ℝ V) = b := by
    rw [TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower b.property]
    simp
  have hcomm : (b : ExteriorAlgebra ℝ V) * g = g * b := by
    have hs' := ι_mul_eq_involute_mul s (b : ExteriorAlgebra ℝ V)
    have ha' := ι_mul_eq_involute_mul a (b : ExteriorAlgebra ℝ V)
    rw [hinv] at hs' ha'
    rw [hg, ← mul_assoc, ← hs', mul_assoc, ← ha', mul_assoc]
  have hwedge : wedge ℝ V 2 2 (ιMulti ℝ 2 ![s, a] + b) (ιMulti ℝ 2 ![s, a] + b) =
      2 • wedge ℝ V 2 2 (ιMulti ℝ 2 ![s, a]) b := by
    apply Subtype.ext
    simp only [exteriorPower.coe_wedge, Submodule.coe_add, exteriorPower.ιMulti_apply_coe,
      _root_.ExteriorAlgebra.ιMulti_apply,
      List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Submodule.coe_smul_of_tower, ← hg]
    rw [add_mul, mul_add, mul_add, hgg, hbb, hcomm, two_smul]
    abel
  simp only [LinearMap.compr₂_apply, hwedge, map_nsmul, nsmul_eq_mul, Nat.cast_ofNat]

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
  rw [twoVectorContraction_ιMulti_add_apply hs hsa hb, wedgePairing_ιMulti_add_self o hkk hs₀ hb]
    at h
  rw [h]
  ring

end TauCeti.Examples.ProductEnergy
