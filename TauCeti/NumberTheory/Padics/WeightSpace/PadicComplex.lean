/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic
import TauCeti.Analysis.Normed.Ring.CompactMonoid

/-!
# Restriction of `ℂ_p`-valued weights to `𝓞_ℂ_p`

Because `ℤ_pˣ` is compact, every continuous `ℂ_p`-valued weight `κ : WeightSpace p ℂ_p` takes
values in the closed unit circle, hence in the valuation ring `𝓞_ℂ_p`
(`TauCeti.WeightSpace.coe_mem_padicComplexInt`). Restricting its values defines
`TauCeti.WeightSpace.toPadicComplexInt : WeightSpace p ℂ_p → WeightSpace p 𝓞_ℂ_p`, with
`TauCeti.WeightSpace.coe_toPadicComplexInt_apply`.
-/

public section

namespace TauCeti.WeightSpace

variable {p : ℕ} [Fact p.Prime]

/-- Every `ℂ_p`-valued weight takes values in `𝓞_ℂ_p`. -/
theorem coe_mem_padicComplexInt (κ : WeightSpace p ℂ_[p]) (x : ℤ_[p]ˣ) :
    (κ x : ℂ_[p]) ∈ 𝓞_ℂ_[p] :=
  PadicComplexInt.mem_iff_norm_le_one.mpr
    (ContinuousMonoidHom.norm_apply_eq_one_of_compactSpace κ x).le

/-- Restriction of a `ℂ_p`-valued weight `κ : ℤ_pˣ →ₜ* ℂ_pˣ` to the unit group `(𝓞_ℂ_p)ˣ`. -/
noncomputable def toPadicComplexInt (κ : WeightSpace p ℂ_[p]) : WeightSpace p 𝓞_ℂ_[p] where
  toMonoidHom :=
    { toFun x :=
        ⟨⟨(κ x : ℂ_[p]), κ.coe_mem_padicComplexInt x⟩,
         ⟨(κ x⁻¹ : ℂ_[p]), κ.coe_mem_padicComplexInt x⁻¹⟩,
         Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := Units.ext <| Subtype.ext <| by simp
      map_mul' x y := Units.ext <| Subtype.ext <| by simp }
  continuous_toFun := Units.continuous_iff.mpr
    ⟨(Units.continuous_val.comp κ.continuous).subtype_mk _,
     ((Units.continuous_val.comp κ.continuous).comp continuous_inv).subtype_mk _⟩

/-- Viewing `κ.toPadicComplexInt x` back in `ℂ_p` recovers `κ x`. -/
@[simp]
theorem coe_toPadicComplexInt_apply (κ : WeightSpace p ℂ_[p]) (x : ℤ_[p]ˣ) :
    ((κ.toPadicComplexInt x : 𝓞_ℂ_[p]) : ℂ_[p]) = κ x :=
  (rfl)

end TauCeti.WeightSpace
