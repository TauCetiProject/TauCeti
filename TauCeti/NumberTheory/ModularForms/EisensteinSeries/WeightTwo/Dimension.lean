/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Congruence
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Subspace
import TauCeti.NumberTheory.ModularForms.CharacterDecomp
import TauCeti.NumberTheory.ModularForms.Cusps.WeightTwo
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Raising
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# The weight-two cusp–Eisenstein decomposition with nebentypus

In weight two, the Eisenstein series of the indices `(ψ, φ, t)` of
`TauCeti.EisensteinSeries.CharIndex N 2` (`TauCeti.EisensteinSeries.CharIndex.weightTwoForm`:
the normalized raised series `E₂^{ψ,φ,t}` for a pair other than the trivial one, and the
corrected series `E₂(z) - t E₂(t z)` for the trivial pair) span the weight-two Eisenstein
subspace `TauCeti.EisensteinSeries.congruenceG2Subspace` of `M₂(Γ₁(N))`, the complement of the
cusp forms (Diamond–Shurman, Theorem 4.6.2). At every level `N` this gives

`dim M₂(Γ₁(N)) = dim S₂(Γ₁(N)) + ε∞(Γ₁(N)) - 1`,

where `ε∞(Γ₁(N))` is the number of cusps of `Γ₁(N)`. Restricted to a nebentypus `χ`, the span
`TauCeti.weightTwoEisensteinSubspace χ` of the series of nebentypus `χ` is a complement of the
image of `S₂(N, χ)` in `M₂(N, χ)`: this is the decomposition `M₂(N, χ) = S₂(N, χ) ⊕ E₂(N, χ)`.

The proof compares dimensions, as in weight `k ≥ 3`
(`TauCeti.EisensteinSeries.span_range_form_eq_congruenceEisensteinSubspace`). Each series is, as a
function, a weighted series `G₂^W` of a level dividing `N`
(`TauCeti.EisensteinSeries.coe_charG2MFRaise`,
`TauCeti.EisensteinSeries.coe_correctedE2_eq_smul_weightedG2`), so it lies in the Eisenstein
subspace (`TauCeti.EisensteinSeries.mem_congruenceG2Subspace_of_coe_eq_weightedG2`). The nonzero
series, those of the indices other than `(1, 1, 1)`, are linearly independent
(`TauCeti.EisensteinSeries.CharIndex.linearIndepOn_weightTwoForm`). Conversely, the constant terms
embed the Eisenstein subspace into the functions on the cusps, and the weight-two residue relation
cuts the image by one dimension (`TauCeti.ModularForm.finrank_le_natCard_sub_one_of_disjoint`).
The indices are as many as the cusps: through the cusp count at `N ∉ {1, 2, 4}`
(`TauCeti.EisensteinSeries.CharIndex.card_eq_card_cuspOrbit_Gamma1`), and through explicit cusp
representatives at the levels `1`, `2` and `4`.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.weightTwoForm_mem_congruenceG2Subspace`: the weight-two
  series of every index lies in the weight-two Eisenstein subspace.
* `TauCeti.EisensteinSeries.span_range_weightTwoForm_eq_congruenceG2Subspace`: the series span
  the weight-two Eisenstein subspace of `M₂(Γ₁(N))`.
* `TauCeti.EisensteinSeries.finrank_congruenceG2Subspace`: its dimension is the number of indices
  minus one.
* `TauCeti.finrank_weight_two_modularForm_Gamma1_eq_finrank_cuspForm_add_card_cuspOrbit_sub_one`:
  `dim M₂(Γ₁(N)) = dim S₂(Γ₁(N)) + ε∞(Γ₁(N)) - 1`.
* `TauCeti.weightTwoEisensteinSubspace_eq_comap_congruenceG2Subspace`: the series of nebentypus
  `χ` span the Eisenstein part of `M₂(N, χ)`.
* `TauCeti.isCompl_weightTwoEisensteinSubspace_range_cuspToModFormCharSpace`: the weight-two
  cusp–Eisenstein decomposition `M₂(N, χ) = S₂(N, χ) ⊕ E₂(N, χ)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.6,
  Theorem 4.6.2, and §3.8 for the cusps of `Γ₁(N)`.
-/

public section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- **The weight-two Eisenstein series are Eisenstein**: the weight-two series of every index
lies in the weight-two Eisenstein subspace of `M₂(Γ₁(N))`. -/
theorem CharIndex.weightTwoForm_mem_congruenceG2Subspace (a : CharIndex N 2) :
    a.weightTwoForm ∈ congruenceG2Subspace (Gamma_le_Gamma1 N) := by
  have : NeZero a.t := NeZero.of_dvd a.t_dvd
  by_cases h : a.psi = 1 ∧ a.phi = 1
  · rw [CharIndex.weightTwoForm_of_eq_one a h]
    refine mem_congruenceG2Subspace_of_coe_eq_weightedG2 (M := a.t * 1) (by simpa using a.t_dvd) _
      (W := (-(a.t : ℂ) / (2 * riemannZeta 2)) • raisedWeight a.t 1) ?_
    rw [ModularForm.coe_restrict, ModularForm.coe_restrict, coe_correctedE2_eq_smul_weightedG2,
      weightedG2_smul]
  · have h' := not_and_or.mp h
    have : NeZero (a.u * a.v) := NeZero.of_dvd (dvd_of_mul_left_dvd a.level_dvd)
    rw [CharIndex.weightTwoForm_of_ne_one a h', normalizedCharG2MFRaise_eq_smul]
    exact Submodule.smul_mem _ _ (mem_congruenceG2Subspace_of_coe_eq_weightedG2 a.level_dvd _
      (coe_charG2MFRaise _ _ a.level_dvd h'))

/-- At the levels `1`, `2` and `4`, the cusps `∞`, `0` and `1/2` give as many cusp
representatives of `Γ₁(N)` as there are weight-two Eisenstein indices. -/
private theorem exists_cuspOrbitOfSL2Z_Gamma1_reps (hN : ¬(2 < N ∧ N ≠ 4)) :
    ∃ r : Fin (Nat.card (CharIndex N 2)) → SL(2, ℤ),
      ∀ γ : SL(2, ℤ), ∃ i, (Gamma1 N).cuspOrbitOfSL2Z (r i) = (Gamma1 N).cuspOrbitOfSL2Z γ := by
  obtain rfl | rfl | rfl : N = 1 ∨ N = 2 ∨ N = 4 := by have := NeZero.ne N; omega
  · rw [CharIndex.card_one, ite_eq_left even_two]
    exact ⟨fun _ ↦ 1, fun γ ↦ ⟨0, cuspOrbitOfSL2Z_Gamma1_one γ⟩⟩
  · rw [CharIndex.card_two, ite_eq_left even_two]
    exact ⟨![1, ModularGroup.S],
      fun γ ↦ (cuspOrbitOfSL2Z_Gamma1_two γ).elim (fun h ↦ ⟨0, h⟩) fun h ↦ ⟨1, h⟩⟩
  · rw [CharIndex.card_four, ite_eq_left even_two]
    -- The cusp `1/2 = α • ∞` is the third representative.
    let α : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by norm_num [Matrix.det_fin_two_of]⟩
    have hα : ((α 1 0 : ℤ) : ZMod 4) = 2 := rfl
    exact ⟨![1, ModularGroup.S, α], fun γ ↦ (cuspOrbitOfSL2Z_Gamma1_four γ).elim (fun h ↦ ⟨0, h⟩)
      fun h ↦ h.elim (fun h ↦ ⟨1, h⟩)
        fun h ↦ ⟨2, cuspOrbitOfSL2Z_Gamma1_four_eq_of_intCast_eq_two hα h⟩⟩

/-- `Γ₁(N)` has at most as many cusps as there are weight-two Eisenstein indices. -/
private theorem card_cuspOrbit_Gamma1_le_card_charIndex :
    Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit ≤ Nat.card (CharIndex N 2) := by
  by_cases hN : 2 < N ∧ N ≠ 4
  · exact (CharIndex.card_eq_card_cuspOrbit_Gamma1 hN.1 hN.2).ge
  obtain ⟨r, hr⟩ := exists_cuspOrbitOfSL2Z_Gamma1_reps hN
  refine (Nat.card_le_card_of_surjective (fun i ↦ (Gamma1 N).cuspOrbitOfSL2Z (r i))
    fun C ↦ ?_).trans_eq (Nat.card_eq_fintype_card.trans (Fintype.card_fin _))
  obtain ⟨γ, rfl⟩ := (Gamma1 N).cuspOrbitOfSL2Z_surjective C
  exact hr γ

/-- The weight-two Eisenstein subspace of `M₂(Γ₁(N))` has dimension at most the number of
indices minus one. Away from the levels `1`, `2` and `4` the indices are as many as the cusps;
at those levels the constant terms are read at explicit cusp representatives. -/
private theorem finrank_congruenceG2Subspace_le :
    Module.finrank ℂ (congruenceG2Subspace (Gamma_le_Gamma1 N)) ≤
      Nat.card (CharIndex N 2) - 1 := by
  have hV := (isCompl_congruenceG2Subspace_cuspFormSubmodule (Gamma_le_Gamma1 N)).disjoint
  by_cases hN : 2 < N ∧ N ≠ 4
  · rw [CharIndex.card_eq_card_cuspOrbit_Gamma1 hN.1 hN.2]
    exact ModularForm.finrank_le_card_cuspOrbit_sub_one_of_disjoint (Gamma1 N) hV
  obtain ⟨r, hr⟩ := exists_cuspOrbitOfSL2Z_Gamma1_reps hN
  simpa using ModularForm.finrank_le_natCard_sub_one_of_disjoint (Gamma1 N) r hr hV

/-- The span of the weight-two series has dimension the number of indices minus one: only the
series of `(1, 1, 1)` vanishes, and the others are linearly independent. -/
private theorem finrank_span_range_weightTwoForm :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (CharIndex.weightTwoForm (N := N)))) =
      Nat.card (CharIndex N 2) - 1 := by
  classical
  let _ : Fintype (CharIndex N 2) := Fintype.ofFinite _
  let one : CharIndex N 2 := CharIndex.one even_two
  have hne (a : CharIndex N 2) : a.weightTwoForm ≠ 0 ↔ a ≠ one :=
    (CharIndex.weightTwoForm_eq_zero_iff_eq_one a).not
  let g (a : {a : CharIndex N 2 // a ≠ one}) : {a : CharIndex N 2 | a.weightTwoForm ≠ 0} :=
    ⟨a.1, (hne a.1).mpr a.2⟩
  have hg : Function.Injective g := fun a b hab ↦
    Subtype.ext (by simpa [g] using congrArg Subtype.val hab)
  have hli : LinearIndependent ℂ fun a : {a : CharIndex N 2 // a ≠ one} ↦ a.1.weightTwoForm :=
    CharIndex.linearIndepOn_weightTwoForm.comp g hg
  have hspan : Submodule.span ℂ (Set.range (CharIndex.weightTwoForm (N := N))) =
      Submodule.span ℂ (Set.range fun a : {a : CharIndex N 2 // a ≠ one} ↦ a.1.weightTwoForm) := by
    refine le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun a ↦ ?_))
      (Submodule.span_mono (Set.range_subset_iff.mpr fun a ↦ ⟨a.1, rfl⟩))
    by_cases ha : a = one
    · rw [(CharIndex.weightTwoForm_eq_zero_iff_eq_one a).mpr ha]
      exact zero_mem _
    · exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  rw [hspan, finrank_span_eq_card hli, Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype_compl]

/-- **The weight-two Eisenstein series span the Eisenstein space** (Diamond–Shurman,
Theorem 4.6.2): the series `E₂^{ψ,φ,t}` and `E₂(z) - t E₂(t z)` span the weight-two Eisenstein
subspace of `M₂(Γ₁(N))`, the complement of the cusp forms. -/
theorem span_range_weightTwoForm_eq_congruenceG2Subspace :
    Submodule.span ℂ (Set.range (CharIndex.weightTwoForm (N := N))) =
      congruenceG2Subspace (Gamma_le_Gamma1 N) :=
  Submodule.eq_of_le_of_finrank_le
    (Submodule.span_le.mpr (Set.range_subset_iff.mpr
      CharIndex.weightTwoForm_mem_congruenceG2Subspace))
    (finrank_span_range_weightTwoForm (N := N) ▸ finrank_congruenceG2Subspace_le)

/-- The weight-two Eisenstein subspace of `M₂(Γ₁(N))` has dimension the number of Eisenstein
indices minus one. -/
theorem finrank_congruenceG2Subspace :
    Module.finrank ℂ (congruenceG2Subspace (Gamma_le_Gamma1 N)) =
      Nat.card (CharIndex N 2) - 1 := by
  rw [← span_range_weightTwoForm_eq_congruenceG2Subspace (N := N), finrank_span_range_weightTwoForm]

end TauCeti.EisensteinSeries

namespace TauCeti

open TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- **The Eisenstein part of the dimension of `M₂(Γ₁(N))`**: the weight-two modular forms on
`Γ₁(N)` have dimension `ε∞(Γ₁(N)) - 1` more than the cusp forms, where `ε∞(Γ₁(N))` is the number
of cusps of `Γ₁(N)`. -/
theorem finrank_weight_two_modularForm_Gamma1_eq_finrank_cuspForm_add_card_cuspOrbit_sub_one :
    Module.finrank ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) =
      Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) +
        (Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit - 1) := by
  refine le_antisymm
    (ModularForm.finrank_weight_two_le_finrank_cuspForm_add_card_cuspOrbit_sub_one (Gamma1 N)) ?_
  rw [(_root_.ModularForm.CuspForm.equivCuspFormSubmodule _ _).finrank_eq,
    ← Submodule.finrank_add_eq_of_isCompl
      (isCompl_congruenceG2Subspace_cuspFormSubmodule (Gamma_le_Gamma1 N)),
    finrank_congruenceG2Subspace]
  have := card_cuspOrbit_Gamma1_le_card_charIndex (N := N)
  omega

/-- **The weight-two Eisenstein series of nebentypus `χ` span the Eisenstein part of
`M₂(N, χ)`**: a form of nebentypus `χ` lies in the weight-two Eisenstein subspace of `M₂(Γ₁(N))`
exactly when it is a linear combination of the series `E₂^{ψ,φ,t}` and `E₂(z) - t E₂(t z)` of
nebentypus `χ`. -/
theorem weightTwoEisensteinSubspace_eq_comap_congruenceG2Subspace (χ : (ZMod N)ˣ →* ℂˣ) :
    weightTwoEisensteinSubspace χ =
      (congruenceG2Subspace (Gamma_le_Gamma1 N)).comap (modFormCharSpace 2 χ).subtype := by
  refine le_antisymm (weightTwoEisensteinSubspace_le χ fun a _ ↦ Submodule.mem_comap.mpr ?_)
    fun f hf ↦ ?_
  · rw [Submodule.subtype_apply, CharIndex.coe_weightTwoInCharSpace]
    exact a.weightTwoForm_mem_congruenceG2Subspace
  have hcut := span_range_inf_modFormCharSpace CharIndex.weightTwoForm CharIndex.nebentypus
    CharIndex.weightTwoForm_mem_modFormCharSpace χ
  rw [span_range_weightTwoForm_eq_congruenceG2Subspace] at hcut
  have hrange : Set.range ((modFormCharSpace 2 χ).subtype ∘
      fun a : {a : CharIndex N 2 // a.nebentypus = χ} ↦ a.1.weightTwoInCharSpace a.2) =
        CharIndex.weightTwoForm '' {a | a.nebentypus = χ} := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, by simp⟩
  have hfχ : (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) ∈
      (weightTwoEisensteinSubspace χ).map (modFormCharSpace 2 χ).subtype := by
    rw [weightTwoEisensteinSubspace_def, Submodule.map_span, ← Set.range_comp, hrange, ← hcut]
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_comap.mp hf, f.2⟩
  obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp hfχ
  rwa [← Subtype.ext hgf]

/-- **The weight-two cusp–Eisenstein decomposition of `M₂(N, χ)`**: the span of the weight-two
Eisenstein series of nebentypus `χ` is a complement of the image of `S₂(N, χ)` in `M₂(N, χ)`. -/
theorem isCompl_weightTwoEisensteinSubspace_range_cuspToModFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) :
    IsCompl (weightTwoEisensteinSubspace χ) (LinearMap.range (cuspToModFormCharSpace 2 χ)) := by
  rw [weightTwoEisensteinSubspace_eq_comap_congruenceG2Subspace χ]
  exact isCompl_congruenceG2Subspace_charSpace_range_cuspToModFormCharSpace χ

end TauCeti
