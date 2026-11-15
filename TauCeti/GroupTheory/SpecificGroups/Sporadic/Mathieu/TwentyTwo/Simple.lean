/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Mathieu.TwentyTwo.Basic
public import TauCeti.GroupTheory.GroupAction.Simple.Basic

/-!
# Simplicity of the canonical permutation model of `M₂₂`

The canonical `TauCeti.Sporadic.M22` permutation model is simple. Its faithful doubly transitive
action on `22` points is primitive, and `11` divides its order `443520` exactly once. Thus every
nontrivial normal subgroup has index coprime to `11` and contains the element `a * b` of order
`11`. Normal generation by this element then forces that subgroup to be the whole model.

Normal generation is certified by a short identity: `a` is a product of two conjugates of
`a * b` by words in the canonical ATLAS generators. Then `b = a⁻¹ * (a * b)` also belongs to
its normal closure. The identity is checked in the actual permutation model, with Mathlib's
composition convention. This proves simplicity of that model, not recognition of an abstract
presentation.

The proof follows the primitive-action normal-generation argument used for the native `M11`
model and applies `TauCeti.isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card`.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, §1.6, for normal subgroups of primitive
  permutation groups.
* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  representation `M22G1-p22B0`, for the canonical generators documented in the basic module.
-/

public section

namespace TauCeti.Sporadic

namespace M22

/-- The first ATLAS generator is a product of two conjugates of `a * b` in the model. -/
private theorem a_eq_mul_conj : ∃ c₁ c₂ : M22, (⟨a, a_mem⟩ : M22) =
    c₁ * ⟨a * b, mul_mem a_mem b_mem⟩ * c₁⁻¹ *
      (c₂ * ⟨a * b, mul_mem a_mem b_mem⟩ * c₂⁻¹) := by
  refine ⟨⟨b, b_mem⟩ * ⟨b, b_mem⟩ * ⟨a, a_mem⟩ * ⟨b, b_mem⟩ * ⟨a, a_mem⟩,
    ⟨b, b_mem⟩ * ⟨b, b_mem⟩ * ⟨a, a_mem⟩ * ⟨b, b_mem⟩⁻¹, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [a_def, b_def]
  decide +kernel

/-- The element `a * b` of order `11` generates the model as a normal subgroup. -/
theorem normalClosure_a_mul_b_eq_top :
    Subgroup.normalClosure {(⟨a * b, mul_mem a_mem b_mem⟩ : M22)} = ⊤ := by
  set N := Subgroup.normalClosure {(⟨a * b, mul_mem a_mem b_mem⟩ : M22)}
  have hr : (⟨a * b, mul_mem a_mem b_mem⟩ : M22) ∈ N := Subgroup.subset_normalClosure rfl
  have hconj (c : M22) : c * ⟨a * b, mul_mem a_mem b_mem⟩ * c⁻¹ ∈ N :=
    Subgroup.normalClosure_normal.conj_mem _ hr c
  have ha : (⟨a, a_mem⟩ : M22) ∈ N := by
    obtain ⟨c₁, c₂, h⟩ := a_eq_mul_conj
    exact h ▸ mul_mem (hconj c₁) (hconj c₂)
  have hb : (⟨b, b_mem⟩ : M22) ∈ N := by
    convert mul_mem (inv_mem ha) hr using 1
    exact Subtype.ext (by simp)
  -- The two generators of the ambient subgroup generate their copies in its carrier.
  have hgen : Subgroup.closure (M22.subtype ⁻¹' {a, b}) = ⊤ := by
    rw [M22_def]
    exact Subgroup.closure_preimage_eq_top _
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le N).mpr
  rintro ⟨x, hx⟩ hx'
  simp only [Set.mem_preimage, Subgroup.coe_subtype, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx'
  rcases hx' with rfl | rfl
  exacts [ha, hb]

end M22

/-- The canonical `22`-point permutation model of `M₂₂` is simple. -/
instance isSimpleGroup_M22 : IsSimpleGroup M22 := by
  exact TauCeti.isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card (X := Fin 22)
    Nat.prime_eleven (by simp) (by rw [card_M22]; norm_num) _
    (by
      apply Subtype.val_injective
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [M22.orderOf_a_mul_b]))
    M22.normalClosure_a_mul_b_eq_top

end TauCeti.Sporadic
