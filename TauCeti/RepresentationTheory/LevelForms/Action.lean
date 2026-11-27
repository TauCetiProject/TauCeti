/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import TauCeti.RepresentationTheory.LevelForms
import Mathlib.RepresentationTheory.Stabilizer
import Mathlib.RepresentationTheory.Subrepresentation
import TauCeti.RepresentationTheory.LevelForms.Dimension

/-!
# Translation and fixed spaces of level forms

Let `J' ≤ J` be levels, with `J` normalizing `J'`, and extend the right coefficient action to
`J`. The weighted translations by `J` preserve the forms of level `J'`. If `z` generates `J/J'`,
its fixed space consists exactly of the forms of level `J`. With trivial arithmetic stabilizers,
its dimension is therefore the dimension at level `J'` divided by `[J : J']`.

The fixed-space argument is the one used for scalar translations in
`New.Data.finrank_ker_one_sub_scalingGenerator_le` of [grh-lean](https://github.com/lsernau/grh-lean)
(`72fead102f663d5c7a407964a13dc0cf9d977207`, `New/UpperBound/Size/ShortColumns.lean`).
-/

public section

open MulOpposite Module TauCeti

namespace Representation

variable {G : Type*} [Group G] {J J' : Subgroup G}

section Action

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ρ : Representation R Jᵐᵒᵖ M) (Γ : Subgroup G) (h : J' ≤ J)

/-- Weighted translation by `J` preserves the forms at the normal sublevel `J'`. -/
def levelFormsAction (hn : J ≤ Subgroup.normalizer (J' : Set G)) :
    Representation R J (levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ) :=
  let S : Subrepresentation (levelAction ρ) :=
    { toSubmodule := levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ
      apply_mem_toSubmodule := fun u f hf ↦ by
        rw [mem_levelForms_iff] at hf ⊢
        refine ⟨fun γ hγ g ↦ by simp [mul_assoc, hf.1 γ hγ], fun v g ↦ ?_⟩
        let w : J' := ⟨(u : G)⁻¹ * v * u, (Subgroup.mem_normalizer_iff''.1
          (hn u.property) v).1 v.property⟩
        have hgu : g * v * u = g * u * w := by simp [w, mul_assoc]
        have huw : Subgroup.inclusion h w * u⁻¹ = u⁻¹ * Subgroup.inclusion h v := by
          apply Subtype.ext
          simp [w, mul_assoc]
        simp only [levelAction_apply, hgu, hf.2 w, MonoidHom.comp_apply]
        -- Evaluate the opposite homomorphism at `op w` and `op v`.
        calc
          _ = ρ (op (Subgroup.inclusion h w * u⁻¹)) (f (g * u)) := apply_op_apply_op ..
          _ = ρ (op (u⁻¹ * Subgroup.inclusion h v)) (f (g * u)) := by rw [huw]
          _ = _ := (apply_op_apply_op ..).symm }
  S.toRepresentation

/-- The action on forms is the restriction of the weighted translation on functions. -/
@[simp]
theorem coe_levelFormsAction_apply (hn : J ≤ Subgroup.normalizer (J' : Set G)) (u : J)
    (f : levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ) :
    (levelFormsAction ρ Γ h hn u f : G → M) = levelAction ρ u (f : G → M) :=
  (rfl)

/-- Every element of the smaller level acts trivially on its forms. -/
@[simp]
theorem levelFormsAction_apply_inclusion (hn : J ≤ Subgroup.normalizer (J' : Set G)) (u : J')
    (f : levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ) :
    levelFormsAction ρ Γ h hn (Subgroup.inclusion h u) f = f := by
  apply Subtype.ext
  rw [coe_levelFormsAction_apply, levelAction_apply_eq_self_iff]
  exact levelForms_apply_mul_right f u

/-- When `z` and `J'` generate `J`, a form at level `J'` is fixed by `z` exactly when it is the
restriction of a form at level `J`. -/
theorem fixedSubmodule_levelFormsAction_eq_range (hn : J ≤ Subgroup.normalizer (J' : Set G))
    (z : J) (hz : J'.subgroupOf J ⊔ Subgroup.zpowers z = ⊤) :
    (levelFormsAction ρ Γ h hn z).fixedSubmodule = LinearMap.range (levelFormsRes ρ Γ h) := by
  ext f
  rw [LinearMap.mem_fixedSubmodule_iff, LinearMap.mem_range]
  constructor
  · intro hf
    have hstab : J'.subgroupOf J ⊔ Subgroup.zpowers z ≤
        (levelFormsAction ρ Γ h hn).stabilizer f := by
      refine sup_le (fun u hu ↦ ?_) (Subgroup.zpowers_le.2 (mem_stabilizer.mpr hf))
      exact mem_stabilizer.mpr (levelFormsAction_apply_inclusion ρ Γ h hn ⟨u, hu⟩ f)
    rw [hz] at hstab
    have hfix (u : J) : levelAction ρ u (f : G → M) = f := by
      rw [← coe_levelFormsAction_apply ρ Γ h hn, mem_stabilizer.mp (hstab (Subgroup.mem_top u))]
    refine ⟨⟨f, mem_levelForms_iff_levelAction.mpr
      ⟨fun γ hγ ↦ levelForms_apply_mul_left f hγ, hfix⟩⟩, ?_⟩
    exact Subtype.ext (coe_levelFormsRes_apply ρ Γ h _)
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    rw [coe_levelFormsAction_apply, coe_levelFormsRes_apply]
    exact (mem_levelForms_iff_levelAction.mp g.property).2 z

end Action

/-- At levels with trivial arithmetic stabilizers, the dimension of the fixed space of a
weighted translation generating `J/J'`, multiplied by the index `[J : J']`, is the dimension of
all forms at level `J'`. -/
theorem relIndex_mul_finrank_fixedSubmodule_levelFormsAction
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (ρ : Representation K Jᵐᵒᵖ M) (Γ : Subgroup G) (h : J' ≤ J)
    (hn : J ≤ Subgroup.normalizer (J' : Set G)) (z : J)
    [J'.IsFiniteRelIndex J] [Finite (DoubleCoset.Quotient (Γ : Set G) J)]
    (hz : J'.subgroupOf J ⊔ Subgroup.zpowers z = ⊤)
    (hfree : ∀ g : G, mackeySubgroup g J Γ = ⊥) :
    J'.relIndex J * finrank K (levelFormsAction ρ Γ h hn z).fixedSubmodule =
      finrank K (levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ) := by
  have hfree' (g : G) : mackeySubgroup g J' Γ = ⊥ := by
    refine le_bot_iff.mp (le_trans (fun u hu ↦ ?_) (hfree g).le)
    obtain ⟨hΓ, hu'⟩ := mem_mackeySubgroup_iff.mp hu
    exact mem_mackeySubgroup_iff.mpr ⟨hΓ, h hu'⟩
  rw [fixedSubmodule_levelFormsAction_eq_range ρ Γ h hn z hz,
    ← (LinearEquiv.ofInjective _ (levelFormsRes_injective ρ Γ h)).finrank_eq]
  have hlarge := finrank_levelForms_eq_orbitMass_mul_of_mackeySubgroup_eq_bot ρ Γ hfree
  have hsmall := finrank_levelForms_eq_relIndex_mul_orbitMass_mul ρ Γ h hfree'
  exact_mod_cast (calc
    (J'.relIndex J : ℚ) * finrank K (ρ.levelForms Γ) =
        J'.relIndex J * orbitMass J (G ⧸ Γ) * finrank K M := by rw [hlarge, mul_assoc]
    _ = _ := hsmall.symm)

end Representation
