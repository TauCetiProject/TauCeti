/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import TauCeti.NumberTheory.ModularForms.CuspFormSubmodule
public import TauCeti.NumberTheory.ModularForms.DiamondOperators
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Descending complements of the cusp forms from `Γ(N)`

Let `Γ` be a subgroup of `SL(2, ℤ)` containing `Γ(N)`, and let `E` be a complement of the cusp
forms in `M_k(Γ(N))` that is stable under slashing by `Γ`, such as the span of the Eisenstein
series of level `Γ(N)`, which is stable under all of `SL(2, ℤ)`. Then the forms on `Γ` whose
restriction to `Γ(N)` lies in `E` form a complement of the cusp forms in `M_k(Γ)`. For
`Γ = Γ₁(N)`, if `E` is stable under `Γ₀(N)`, this complement is stable under the diamond
operators, so it also splits each nebentypus space `M_k(N, χ)` against the image of `S_k(N, χ)`.
This is how the cusp–Eisenstein decomposition passes from `Γ(N)` to congruence
subgroups and to prescribed nebentypus, in every weight.

Spanning descends by the trace from `Γ(N)` to `Γ`. Restricted back to `Γ(N)`, the trace of a form
`f` is a sum of slashes of `f` by elements of `Γ`, so it stays in `E`; the trace of a cusp
form is a cusp form; and the trace of the restriction of a form on `Γ` is that form times the
index. The diamond operators slash by elements of `Γ₀(N)`, so they preserve both the descended
complement and the cusp forms, and a diamond-stable complement of the cusp forms splits each
nebentypus space (`isCompl_comap_subtype_range_cuspToModFormCharSpace`).

## Main definitions

* `TauCeti.ModularForm.gammaSlashₗ`: slashing by `γ ∈ SL(2, ℤ)` as an endomorphism of
  `M_k(Γ(N))`.

## Main results

* `TauCeti.ModularForm.gammaSlashₗ_one`, `TauCeti.ModularForm.gammaSlashₗ_mul`,
  `TauCeti.ModularForm.gammaSlashₗ_of_mem_Gamma`: `gammaSlashₗ` is a right action of
  `SL(2, ℤ)` on which `Γ(N)` acts trivially.
* `TauCeti.ModularForm.restrict_diamondOp_eq_gammaSlashₗ`: restricted to `Γ(N)`, a diamond
  operator is slashing by a representative in `Γ₀(N)`.
* `TauCeti.ModularForm.restrict_traceₗ_mem`: the trace from `Γ(N)` to `Γ`, restricted back
  to `Γ(N)`, preserves a slash-stable subspace.
* `TauCeti.ModularForm.isCompl_comap_restrictₗ_cuspFormSubmodule`: a `Γ`-stable
  complement of the cusp forms of level `Γ(N)` descends to a complement of the cusp forms on
  `Γ ⊇ Γ(N)`.
* `TauCeti.ModularForm.diamondOp_mem_comap_restrictₗ`: on `Γ₁(N)`, the descended complement
  is stable under the diamond operators.
* `TauCeti.ModularForm.isCompl_comap_restrictₗ_charSpace_range_cuspToModFormCharSpace`: the
  descended complement splits `M_k(N, χ)` against the image of `S_k(N, χ)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 4.2, 4.5 and 4.6.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open scoped MatrixGroups Pointwise

namespace TauCeti.ModularForm

variable {N : ℕ} {k : ℤ}

/-- Slashing by `γ ∈ SL(2, ℤ)` as an endomorphism of `M_k(Γ(N))`, which `γ` normalizes. -/
def gammaSlashₗ (γ : SL(2, ℤ)) : Module.End ℂ (ModularForm ((Gamma N).map (mapGL ℝ)) k) :=
  (ModularForm.restrictₗ _ ℂ (Gamma_map_inv_conjAct_eq N γ).ge).comp
    (ModularForm.translateₗ (mapGL ℝ γ) (by simp))

/-- The underlying function of `gammaSlashₗ γ f` is the slash `f ∣[k] γ`. -/
@[simp]
theorem coe_gammaSlashₗ (γ : SL(2, ℤ)) (f : ModularForm ((Gamma N).map (mapGL ℝ)) k) :
    ⇑(gammaSlashₗ γ f) = ⇑f ∣[k] mapGL ℝ γ := by
  rw [gammaSlashₗ, LinearMap.comp_apply, ModularForm.restrictₗ_apply, ModularForm.coe_restrict,
    ModularForm.translateₗ_apply, ModularForm.coe_translate]

/-- Slashing by the identity is the identity. -/
@[simp]
theorem gammaSlashₗ_one : gammaSlashₗ (N := N) (k := k) 1 = LinearMap.id := by
  ext f : 1
  apply DFunLike.coe_injective
  rw [coe_gammaSlashₗ, map_one, SlashAction.slash_one, LinearMap.id_apply]

/-- Slashing is a right action: slashing by `γ * δ` is slashing by `γ`, then by `δ`. -/
theorem gammaSlashₗ_mul (γ δ : SL(2, ℤ)) :
    gammaSlashₗ (N := N) (k := k) (γ * δ) = gammaSlashₗ δ ∘ₗ gammaSlashₗ γ := by
  ext f : 1
  apply DFunLike.coe_injective
  rw [LinearMap.comp_apply, coe_gammaSlashₗ, coe_gammaSlashₗ, coe_gammaSlashₗ, map_mul,
    SlashAction.slash_mul]

/-- Elements of `Γ(N)` act trivially on `M_k(Γ(N))`. -/
theorem gammaSlashₗ_of_mem_Gamma {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) k) : gammaSlashₗ γ f = f := by
  apply DFunLike.coe_injective
  rw [coe_gammaSlashₗ]
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

/-- Restricted to `Γ(N)`, the diamond operator `⟨d⟩` on `M_k(Γ₁(N))` is slashing by any
representative `g ∈ Γ₀(N)` of `d`. -/
theorem restrict_diamondOp_eq_gammaSlashₗ (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.restrict (Subgroup.map_mono (Gamma_le_Gamma1 N)) (diamondOp k d f) =
      gammaSlashₗ (g : SL(2, ℤ))
        (ModularForm.restrict (Subgroup.map_mono (Gamma_le_Gamma1 N)) f) := by
  apply DFunLike.coe_injective
  rw [ModularForm.coe_restrict, coe_gammaSlashₗ, ModularForm.coe_restrict, coe_diamondOp k d g hg]

variable [NeZero N] {Γ : Subgroup SL(2, ℤ)}
  {E : Submodule ℂ (ModularForm ((Gamma N).map (mapGL ℝ)) k)}

/-- Restricted back to `Γ(N)`, the trace from `Γ(N)` to a larger subgroup `Γ` of `SL(2, ℤ)` maps
a subspace stable under slashing by `Γ` into itself: it is a sum of slashes by elements of `Γ`. -/
theorem restrict_traceₗ_mem (hE : ∀ γ ∈ Γ, ∀ f ∈ E, gammaSlashₗ γ f ∈ E)
    (hΓ : Gamma N ≤ Γ) {f : ModularForm ((Gamma N).map (mapGL ℝ)) k} (hf : f ∈ E) :
    ModularForm.restrict (Subgroup.map_mono hΓ) (traceₗ (Γ.map (mapGL ℝ)) f) ∈ E := by
  classical
  let _ := Fintype.ofFinite
    (Γ.map (mapGL ℝ) ⧸ ((Gamma N).map (mapGL ℝ)).subgroupOf (Γ.map (mapGL ℝ)))
  have hq (q : Γ.map (mapGL ℝ) ⧸ ((Gamma N).map (mapGL ℝ)).subgroupOf (Γ.map (mapGL ℝ))) :
      ∃ γ ∈ Γ, SlashInvariantForm.quotientFunc f q = ⇑(gammaSlashₗ γ f) := by
    induction q using QuotientGroup.induction_on' with
    | H h =>
      obtain ⟨γ, hγ, hmap⟩ := h.property
      refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
      rw [SlashInvariantForm.quotientFunc_mk, coe_gammaSlashₗ, ← hmap, map_inv]
  choose γ hγΓ hγ using hq
  have htrace : ModularForm.restrict (Subgroup.map_mono hΓ) (traceₗ (Γ.map (mapGL ℝ)) f) =
      ∑ q, gammaSlashₗ (γ q) f := by
    apply DFunLike.coe_injective
    rw [ModularForm.coe_restrict, traceₗ_apply, ModularForm.coe_trace, FunLike.coe_sum]
    simp_rw [hγ]
  rw [htrace]
  exact Submodule.sum_mem _ fun q _ ↦ hE (γ q) (hγΓ q) f hf

/-- **Descent of a complement of the cusp forms.** Let `Γ ⊇ Γ(N)` be a subgroup of `SL(2, ℤ)`. If
`E` is a complement of the cusp forms in `M_k(Γ(N))` stable under slashing by `Γ`, then the forms
on `Γ` whose restriction to `Γ(N)` lies in `E` form a complement of the cusp forms in `M_k(Γ)`. -/
theorem isCompl_comap_restrictₗ_cuspFormSubmodule
    (hE : IsCompl E (cuspFormSubmodule ((Gamma N).map (mapGL ℝ)) k))
    (hslash : ∀ γ ∈ Γ, ∀ f ∈ E, gammaSlashₗ γ f ∈ E) (hΓ : Gamma N ≤ Γ) :
    IsCompl (E.comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono hΓ)))
      (cuspFormSubmodule (Γ.map (mapGL ℝ)) k) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro f hfE hfS
    have hzero := Submodule.disjoint_def.mp hE.disjoint _ hfE
      (ModularForm.restrict_mem_cuspFormSubmodule (Subgroup.map_mono hΓ) hfS)
    exact (ModularForm.restrict_eq_zero_iff (Subgroup.map_mono hΓ)).mp hzero
  · refine codisjoint_iff.mpr (eq_top_iff.mpr fun f _ ↦ ?_)
    have hf : ModularForm.restrict (Subgroup.map_mono hΓ) f ∈
        E ⊔ cuspFormSubmodule ((Gamma N).map (mapGL ℝ)) k := by
      rw [codisjoint_iff.mp hE.codisjoint]
      exact Submodule.mem_top
    obtain ⟨e, he, s, hs, hes⟩ := Submodule.mem_sup.mp hf
    -- tracing `restrict f = e + s` back to `Γ` gives `[Γ : Γ(N)] • f`
    have htrace := congrArg (traceₗ (Γ.map (mapGL ℝ))) hes
    rw [map_add, traceₗ_restrict] at htrace
    have he' : traceₗ (Γ.map (mapGL ℝ)) e ∈
        E.comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono hΓ)) := by
      rw [Submodule.mem_comap, ModularForm.restrictₗ_apply]
      exact restrict_traceₗ_mem hslash hΓ he
    have hindex : (((Gamma N).map (mapGL ℝ)).relIndex (Γ.map (mapGL ℝ)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Subgroup.relIndex_ne_zero
    have hmem := Submodule.smul_mem _
      (((Gamma N).map (mapGL ℝ)).relIndex (Γ.map (mapGL ℝ)) : ℂ)⁻¹
      (htrace ▸ Submodule.add_mem_sup he' (ModularForm.traceₗ_mem_cuspFormSubmodule hs))
    simpa only [inv_smul_smul₀ hindex] using hmem

section Gamma1

omit [NeZero N] in
/-- On `Γ₁(N)`, the diamond operators preserve the forms whose restriction to `Γ(N)` lies in a
subspace stable under slashing by `Γ₀(N)`. -/
theorem diamondOp_mem_comap_restrictₗ (hslash : ∀ γ ∈ Gamma0 N, ∀ f ∈ E, gammaSlashₗ γ f ∈ E)
    (d : (ZMod N)ˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ E.comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono (Gamma_le_Gamma1 N)))) :
    diamondOp k d f ∈
      E.comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono (Gamma_le_Gamma1 N))) := by
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  rw [Submodule.mem_comap, ModularForm.restrictₗ_apply] at hf ⊢
  rw [restrict_diamondOp_eq_gammaSlashₗ d g hg]
  exact hslash _ g.2 _ hf

/-- **Descent to a nebentypus.** If `E` is a complement of the cusp forms in `M_k(Γ(N))` stable
under slashing by `Γ₀(N)`, then the forms of nebentypus `χ` whose restriction to `Γ(N)` lies in
`E` form a complement of the image of `S_k(N, χ)` in `M_k(N, χ)`. -/
theorem isCompl_comap_restrictₗ_charSpace_range_cuspToModFormCharSpace
    (hE : IsCompl E (cuspFormSubmodule ((Gamma N).map (mapGL ℝ)) k))
    (hslash : ∀ γ ∈ Gamma0 N, ∀ f ∈ E, gammaSlashₗ γ f ∈ E) (χ : (ZMod N)ˣ →* ℂˣ) :
    IsCompl ((E.comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono (Gamma_le_Gamma1 N)))).comap
      (modFormCharSpace k χ).subtype) (LinearMap.range (cuspToModFormCharSpace k χ)) :=
  isCompl_comap_subtype_range_cuspToModFormCharSpace
    (isCompl_comap_restrictₗ_cuspFormSubmodule hE
      (fun γ hγ ↦ hslash γ (Gamma1_in_Gamma0 N hγ)) (Gamma_le_Gamma1 N))
    (fun d _ hf ↦ diamondOp_mem_comap_restrictₗ hslash d hf) χ

end Gamma1

end TauCeti.ModularForm
