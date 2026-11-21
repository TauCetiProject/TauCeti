/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Integral.Basic
public import TauCeti.NumberTheory.ModularForms.CuspComplementDescent

import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Integral forms under restriction and trace

Let `R ⊆ ℂ` be a subring. A modular form on `Γ` is integral at every cusp
(`TauCeti.ModularForm.integralAtCusps`) when the `q`-expansions of all its translates `f ∣ γ`,
`γ ∈ SL₂(ℤ)`, have coefficients in `R`. This notion does not depend on the group: for `Γ' ≤ Γ`,
the expansion at a cusp for `Γ'` is the expansion for `Γ` in a power of `q`, so a form is
integral at every cusp exactly when its restriction to `Γ'` is
(`TauCeti.ModularForm.restrict_mem_integralAtCusps_iff`).

For `Γ(N) ≤ Γ ≤ SL₂(ℤ)`, the slashes `f ∣ γ` by `γ ∈ SL₂(ℤ)` preserve the forms on `Γ(N)`
integral at every cusp, since they only permute the cusp expansions. The trace from `Γ(N)` to
`Γ`, restricted back to `Γ(N)`, is a sum of such slashes, so it carries integral forms to
integral forms (`TauCeti.ModularForm.traceₗ_mem_integralAtCusps`). Since the trace of the
restriction of a form on `Γ` is that form times the index, spanning by integral forms passes from
`Γ(N)` to `Γ` (`TauCeti.ModularForm.span_integralAtCusps_eq_top_of_Gamma`).

This reduces the spanning statement that Deligne and Serre need for their lattice of forms
integral at every cusp, on `Γ₁(N)`, to the principal congruence subgroup `Γ(N)`, where the
rationality of `q`-expansions at all cusps is classically stated.

## Main results

* `TauCeti.ModularForm.restrict_mem_integralAtCusps_iff`: restriction to a smaller arithmetic
  subgroup preserves and reflects integrality at every cusp.
* `TauCeti.ModularForm.gammaSlashₗ_mem_integralAtCusps`: slashing by `SL₂(ℤ)` preserves the forms
  on `Γ(N)` integral at every cusp.
* `TauCeti.ModularForm.traceₗ_mem_integralAtCusps`: the trace from `Γ(N)` to `Γ ⊇ Γ(N)`
  preserves integrality at every cusp.
* `TauCeti.ModularForm.mem_span_integralAtCusps_of_restrict_mem`: a form on `Γ` whose
  restriction to `Γ(N)` is in the span of the integral forms is in the span of the integral forms
  on `Γ`.
* `TauCeti.ModularForm.span_integralAtCusps_eq_top_of_Gamma`,
  `TauCeti.ModularForm.cuspFormSubmodule_le_span_integralAtCusps_of_Gamma`: if the integral forms
  span `M_k(Γ(N))`, or a space containing `S_k(Γ(N))`, the same holds on `Γ`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, §2.7.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Theorem 3.52.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.ModularForm

variable {R : Subring ℂ} {k : ℤ}

variable {N : ℕ} [NeZero N]

/-- Slashing by `γ ∈ SL₂(ℤ)` preserves the forms on `Γ(N)` integral at every cusp: the
expansion of `f ∣ γ` at the cusp `δ` is the expansion of `f` at the cusp `γ δ`. -/
theorem gammaSlashₗ_mem_integralAtCusps (γ : SL(2, ℤ)) {f : ModularForm Γ(N) k}
    (hf : f ∈ integralAtCusps R Γ(N) k) : gammaSlashₗ γ f ∈ integralAtCusps R Γ(N) k := by
  rw [mem_integralAtCusps_iff_qExpansion_coeff_mem le_rfl] at hf ⊢
  intro δ n
  have hslash : ⇑(translate (gammaSlashₗ γ f) (mapGL ℝ δ)) = translate f (mapGL ℝ (γ * δ)) := by
    rw [coe_translate, coe_translate, coe_gammaSlashₗ, map_mul, SlashAction.slash_mul]
  rw [hslash]
  exact hf _ n

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

/-- **The trace preserves integrality at every cusp.** For `Γ(N) ≤ Γ ≤ SL₂(ℤ)`, the trace to `Γ`
of a form on `Γ(N)` integral at every cusp is integral at every cusp: restricted back to `Γ(N)`,
it is a sum of slashes of the form by elements of `Γ`. -/
theorem traceₗ_mem_integralAtCusps (hΓ : Gamma N ≤ Γ) {f : ModularForm Γ(N) k}
    (hf : f ∈ integralAtCusps R Γ(N) k) :
    traceₗ (Γ : Subgroup (GL (Fin 2) ℝ)) f ∈ integralAtCusps R Γ k := by
  rw [← restrict_mem_integralAtCusps_iff (Subgroup.map_mono hΓ)]
  exact restrict_traceₗ_mem (E := integralAtCusps R Γ(N) k)
    (fun γ _ _ hg ↦ gammaSlashₗ_mem_integralAtCusps γ hg) hΓ hf

/-- **Integral spans descend from `Γ(N)` to `Γ`.** For `Γ(N) ≤ Γ ≤ SL₂(ℤ)`, if the restriction to
`Γ(N)` of a form `f` on `Γ` is a `ℂ`-linear combination of forms integral at every cusp, then so is
`f`, now with forms on `Γ`: `f` is the trace of its restriction, divided by the index. -/
theorem mem_span_integralAtCusps_of_restrict_mem (hΓ : Gamma N ≤ Γ) {f : ModularForm Γ k}
    (hf : ModularForm.restrict (Subgroup.map_mono hΓ) f ∈
      Submodule.span ℂ (integralAtCusps R Γ(N) k : Set (ModularForm Γ(N) k))) :
    f ∈ Submodule.span ℂ (integralAtCusps R Γ k : Set (ModularForm Γ k)) := by
  have hle : (Submodule.span ℂ (integralAtCusps R Γ(N) k : Set (ModularForm Γ(N) k))).map
      (traceₗ (Γ : Subgroup (GL (Fin 2) ℝ))) ≤
        Submodule.span ℂ (integralAtCusps R Γ k : Set (ModularForm Γ k)) := by
    rw [Submodule.map_span_le]
    exact fun g hg ↦ Submodule.subset_span (traceₗ_mem_integralAtCusps hΓ hg)
  have htr := hle (Submodule.mem_map_of_mem hf)
  rw [traceₗ_restrict] at htr
  have hidx : (((Gamma N : Subgroup (GL (Fin 2) ℝ))).relIndex Γ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.relIndex_ne_zero
  rw [← inv_smul_smul₀ hidx f]
  exact Submodule.smul_mem _ _ htr

/-- **Spanning by integral forms passes from `Γ(N)` to `Γ`.** For `Γ(N) ≤ Γ ≤ SL₂(ℤ)`, if the
forms on `Γ(N)` whose `q`-expansions at every cusp have coefficients in `R` span `M_k(Γ(N))` over
`ℂ`, then the forms on `Γ` with this property span `M_k(Γ)`. -/
theorem span_integralAtCusps_eq_top_of_Gamma (hΓ : Gamma N ≤ Γ)
    (h : Submodule.span ℂ (integralAtCusps R Γ(N) k : Set (ModularForm Γ(N) k)) = ⊤) :
    Submodule.span ℂ (integralAtCusps R Γ k : Set (ModularForm Γ k)) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ mem_span_integralAtCusps_of_restrict_mem hΓ (h ▸ Submodule.mem_top)

/-- **Integral spans of cusp forms pass from `Γ(N)` to `Γ`.** For `Γ(N) ≤ Γ ≤ SL₂(ℤ)`, if the cusp
forms on `Γ(N)` lie in the `ℂ`-span of the forms integral at every cusp, then so do the cusp
forms on `Γ`, since restriction keeps cusp forms cuspidal. -/
theorem cuspFormSubmodule_le_span_integralAtCusps_of_Gamma (hΓ : Gamma N ≤ Γ)
    (h : cuspFormSubmodule Γ(N) k ≤
      Submodule.span ℂ (integralAtCusps R Γ(N) k : Set (ModularForm Γ(N) k))) :
    cuspFormSubmodule Γ k ≤ Submodule.span ℂ (integralAtCusps R Γ k : Set (ModularForm Γ k)) :=
  fun _ hf ↦ mem_span_integralAtCusps_of_restrict_mem hΓ
    (h (restrict_mem_cuspFormSubmodule (Subgroup.map_mono hΓ) hf))

end TauCeti.ModularForm
