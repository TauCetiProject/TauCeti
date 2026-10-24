/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Count
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Span
import TauCeti.NumberTheory.ModularForms.CharacterDecomp
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Independence
import TauCeti.NumberTheory.ModularForms.Cusps.Codimension
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# The Eisenstein series with character span the Eisenstein space

In weight `k ≥ 3` and at a level `N ∉ {1, 2, 4}`, the normalized raised Eisenstein series
`E_k^(ψ, φ, t)`, indexed by `TauCeti.EisensteinSeries.CharIndex N k`, span the Eisenstein
subspace `TauCeti.EisensteinSeries.congruenceEisensteinSubspace` of `M_k(Γ₁(N))`, the
complement of the cusp forms (Diamond–Shurman, Theorem 4.5.2). Together with their linear
independence they form a basis of it, so that

`dim M_k(Γ₁(N)) = dim S_k(Γ₁(N)) + ε∞(Γ₁(N))`,

where `ε∞(Γ₁(N))` is the number of cusps of `Γ₁(N)`. Restricted to a nebentypus `χ`, the
series of nebentypus `χ` span the Eisenstein part of `M_k(N, χ)`: the span
`TauCeti.eisensteinSubspace χ` is exactly the intersection of `M_k(N, χ)` with the Eisenstein
subspace, and so is complementary to the image of `S_k(N, χ)`.

The proof compares dimensions. The series lie in the Eisenstein subspace and are linearly
independent, and there are as many of them as there are cusps
(`TauCeti.EisensteinSeries.CharIndex.card_eq_card_cuspOrbit_Gamma1`). Conversely the Eisenstein
subspace meets the cusp forms trivially, so the constant terms embed it into the functions on the
cusps (`TauCeti.ModularForm.finrank_le_card_cuspOrbit_of_disjoint`). For a fixed nebentypus, a
form of nebentypus `χ` in the span of all the series lies in the span of those of nebentypus `χ`,
because the character spaces `M_k(N, ψ)` are independent.

## Main results

* `TauCeti.EisensteinSeries.span_range_form_eq_congruenceEisensteinSubspace`: the series span
  the Eisenstein subspace of `M_k(Γ₁(N))`.
* `TauCeti.EisensteinSeries.finrank_congruenceEisensteinSubspace_Gamma1`: its dimension is the
  number of cusps of `Γ₁(N)`.
* `TauCeti.finrank_modularForm_Gamma1_eq_finrank_cuspForm_add_card_cuspOrbit`:
  `dim M_k(Γ₁(N)) = dim S_k(Γ₁(N)) + ε∞(Γ₁(N))`.
* `TauCeti.eisensteinSubspace_eq_comap_congruenceEisensteinSubspace`: the series of nebentypus
  `χ` span the Eisenstein part of `M_k(N, χ)`.
* `TauCeti.isCompl_eisensteinSubspace_range_cuspToModFormCharSpace`: the cusp–Eisenstein
  decomposition `M_k(N, χ) = S_k(N, χ) ⊕ E_k(N, χ)` with `E_k(N, χ)` spanned by the series.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 4.5, Theorem 4.5.2, and Section 3.8 for the cusps of `Γ₁(N)`.
-/

public section

open CongruenceSubgroup Matrix.SpecialLinearGroup

namespace TauCeti.EisensteinSeries

variable {N k : ℕ} [NeZero N]

/-- **The Eisenstein series with character span the Eisenstein space** (Diamond–Shurman,
Theorem 4.5.2): in weight `k ≥ 3` and at a level `N ∉ {1, 2, 4}`, the normalized raised series
`E_k^(ψ, φ, t)` span the Eisenstein subspace of `M_k(Γ₁(N))`, the complement of the cusp forms. -/
theorem span_range_form_eq_congruenceEisensteinSubspace (hN : 2 < N) (hN4 : N ≠ 4)
    (hk : 3 ≤ (k : ℤ)) :
    Submodule.span ℂ (Set.range fun a : CharIndex N k ↦ a.form hk) =
      congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk := by
  have := Fintype.ofFinite (CharIndex N k)
  refine Submodule.eq_of_le_of_finrank_le
    (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun a ↦
      a.form_mem_congruenceEisensteinSubspace hk)) ?_
  rw [finrank_span_eq_card (CharIndex.linearIndependent_form hk), ← Nat.card_eq_fintype_card,
    CharIndex.card_eq_card_cuspOrbit_Gamma1 hN hN4]
  exact ModularForm.finrank_le_card_cuspOrbit_of_disjoint (Gamma1 N) k
    (disjoint_congruenceEisensteinSubspace_cuspFormSubmodule _ hk)

/-- In weight `k ≥ 3` and at a level `N ∉ {1, 2, 4}`, the Eisenstein subspace of `M_k(Γ₁(N))` has
dimension the number of cusps of `Γ₁(N)`. -/
theorem finrank_congruenceEisensteinSubspace_Gamma1 (hN : 2 < N) (hN4 : N ≠ 4)
    (hk : 3 ≤ (k : ℤ)) :
    Module.finrank ℂ (congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk) =
      Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit := by
  have := Fintype.ofFinite (CharIndex N k)
  rw [← span_range_form_eq_congruenceEisensteinSubspace hN hN4 hk,
    finrank_span_eq_card (CharIndex.linearIndependent_form hk), ← Nat.card_eq_fintype_card,
    CharIndex.card_eq_card_cuspOrbit_Gamma1 hN hN4]

end TauCeti.EisensteinSeries

namespace TauCeti

open TauCeti.EisensteinSeries

variable {N k : ℕ} [NeZero N]

/-- **The Eisenstein part of the dimension of `M_k(Γ₁(N))`**: in weight `k ≥ 3` and at a level
`N ∉ {1, 2, 4}`, the modular forms on `Γ₁(N)` have dimension `ε∞(Γ₁(N))` more than the cusp
forms, where `ε∞(Γ₁(N))` is the number of cusps of `Γ₁(N)`. -/
theorem finrank_modularForm_Gamma1_eq_finrank_cuspForm_add_card_cuspOrbit (hN : 2 < N)
    (hN4 : N ≠ 4) (hk : 3 ≤ (k : ℤ)) :
    Module.finrank ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) +
        Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit := by
  rw [← finrank_congruenceEisensteinSubspace_Gamma1 hN hN4 hk,
    (_root_.ModularForm.CuspForm.equivCuspFormSubmodule _ _).finrank_eq, add_comm]
  exact (Submodule.finrank_add_eq_of_isCompl
    (isCompl_congruenceEisensteinSubspace_cuspFormSubmodule _ hk)).symm

/-- **The Eisenstein series of nebentypus `χ` span the Eisenstein part of `M_k(N, χ)`**: in
weight `k ≥ 3` and at a level `N ∉ {1, 2, 4}`, a form of nebentypus `χ` lies in the Eisenstein
subspace of `M_k(Γ₁(N))` exactly when it is a linear combination of the series `E_k^(ψ, φ, t)`
whose induced nebentypus is `χ`. -/
theorem eisensteinSubspace_eq_comap_congruenceEisensteinSubspace (χ : (ZMod N)ˣ →* ℂˣ)
    (hN : 2 < N) (hN4 : N ≠ 4) (hk : 3 ≤ (k : ℤ)) :
    eisensteinSubspace χ hk =
      (congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk).comap
        (modFormCharSpace (k : ℤ) χ).subtype := by
  refine le_antisymm (eisensteinSubspace_le_congruenceEisensteinSubspace χ hk) fun f hf ↦ ?_
  -- The span of the series of nebentypus `ψ`, as a subspace of `M_k(Γ₁(N))` inside `M_k(N, ψ)`.
  let W (ψ : (ZMod N)ˣ →* ℂˣ) := (eisensteinSubspace ψ hk).map (modFormCharSpace (k : ℤ) ψ).subtype
  have hWle (ψ : (ZMod N)ˣ →* ℂˣ) : W ψ ≤ modFormCharSpace (k : ℤ) ψ :=
    Submodule.map_subtype_le _ _
  -- Every series lies in the span of those sharing its nebentypus.
  have hE : congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk ≤ ⨆ ψ, W ψ := by
    rw [← span_range_form_eq_congruenceEisensteinSubspace hN hN4 hk, Submodule.span_le,
      Set.range_subset_iff]
    exact fun a ↦ Submodule.mem_iSup_of_mem a.nebentypus
      ⟨a.inCharSpace hk rfl, mem_eisensteinSubspace _ hk a rfl, a.coe_inCharSpace hk rfl⟩
  -- Independence of the character spaces cuts `⨆ ψ, W ψ` down to `W χ` inside `M_k(N, χ)`.
  have hcut : (⨆ ψ, W ψ) ⊓ modFormCharSpace (k : ℤ) χ = W χ := by
    rw [iSup_split_single W χ, sup_inf_assoc_of_le _ (hWle χ), sup_eq_left]
    exact ((iSupIndep_modFormCharSpace (k : ℤ) χ).symm.mono_left
      (iSup₂_mono fun ψ _ ↦ hWle ψ)).le_bot.trans bot_le
  have hfW : (f : ModularForm _ (k : ℤ)) ∈ W χ := hcut ▸ Submodule.mem_inf.mpr ⟨hE hf, f.2⟩
  obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp hfW
  rwa [← Subtype.ext hgf]

/-- **The cusp–Eisenstein decomposition of `M_k(N, χ)`**: in weight `k ≥ 3` and at a level
`N ∉ {1, 2, 4}`, the span of the Eisenstein series of nebentypus `χ` is a complement of the image
of `S_k(N, χ)` in `M_k(N, χ)`. -/
theorem isCompl_eisensteinSubspace_range_cuspToModFormCharSpace (χ : (ZMod N)ˣ →* ℂˣ)
    (hN : 2 < N) (hN4 : N ≠ 4) (hk : 3 ≤ (k : ℤ)) :
    IsCompl (eisensteinSubspace χ hk) (LinearMap.range (cuspToModFormCharSpace (k : ℤ) χ)) := by
  rw [eisensteinSubspace_eq_comap_congruenceEisensteinSubspace χ hN hN4 hk]
  exact isCompl_congruenceEisensteinSubspace_charSpace_range_cuspToModFormCharSpace hk χ

end TauCeti
