/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Parabolic.Classification

/-!
# Conjugating standard parabolics of a Tits system into one another

For a Tits system with distinguished subgroup `B` and subsets `J, J'` of the simple reflections,
`g P_J g⁻¹ ⊆ P_{J'}` holds exactly when `J ⊆ J'` and `g ∈ P_{J'}`. In particular a conjugate of
`B` lying in a subgroup `P ⊇ B` is conjugate by an element of `P`, and two conjugate standard
parabolics are equal, with the conjugating element in the parabolic.

The key step, `TauCeti.TitsSystem.mem_of_conj_subgroupB_le`, is proved by induction on the length
of the Weyl element `w` with `g ∈ B w B`. Writing `w = s w'` with `s` simple and `w'` shorter, the
cell `B w B · B w⁻¹ B` lies in `P` and contains `B s B · B s B ⊇ B s B`, so `B s B ⊆ P`. Peeling
off a factor from `B s B` leaves an element of `B w' B` that still conjugates `B` into `P`.

These are statements about an arbitrary Tits system, with no topology, field or finiteness.

## Main declarations

* `TauCeti.TitsSystem.mem_of_conj_subgroupB_le`: if `g B g⁻¹ ⊆ P` for a subgroup `P ⊇ B`,
  then `g ∈ P`.
* `TauCeti.TitsSystem.conj_smul_standardParabolic_le_iff`: `g P_J g⁻¹ ≤ P_{J'}` iff `J ⊆ J'`
  and `g ∈ P_{J'}`, with the elementwise form `conj_standardParabolic_le_iff`.
* `TauCeti.TitsSystem.conj_standardParabolic_eq_iff`: `g P_J g⁻¹ = P_{J'}` iff `J = J'` and
  `g ∈ P_J`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, nos. 5--6.
* A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), Corollaire 5.18.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

local prefix:100 "ℓ " => T.simpleGenerators.wordLength

/-- If `g B g⁻¹ ⊆ P` for a subgroup `P ⊇ B` and `g ∈ B (s w) B` with `s` simple and
`ℓ w ≤ ℓ (s w)`, then `B s B ⊆ P`. -/
private theorem bruhatCell_subset_of_conj_subgroupB_le {P : Subgroup G}
    (hB : T.subgroupB ≤ P) {s w : T.WeylGroup} (hs : s ∈ T.simple)
    (hw : ℓ w ≤ ℓ (s * w)) {g : G} (hg : g ∈ T.bruhatCell (s * w))
    (hconj : ∀ b ∈ T.subgroupB, g * b * g⁻¹ ∈ P) :
    T.bruhatCell s ⊆ P := by
  have hcell := T.bruhatCell_mul_eq_of_wordLength_le hs hw
  rw [T.bruhatCell_eq_doubleCoset hg] at hcell
  obtain ⟨n, _, hn⟩ := T.exists_mem_bruhatCell w
  -- An element `x n` with `x ∈ B s B` has the form `b₁ g b₂`.
  have hdc : ∀ x ∈ T.bruhatCell s, ∃ b₁ ∈ T.subgroupB, ∃ b₂ ∈ T.subgroupB,
      x * n = b₁ * g * b₂ := by
    intro x hx
    have hxn : x * n ∈ DoubleCoset.doubleCoset g T.subgroupB T.subgroupB :=
      hcell ▸ Set.mul_mem_mul hx hn
    exact DoubleCoset.mem_doubleCoset.mp hxn
  intro x hx
  have hx2 : x ∈ T.bruhatCell s * T.bruhatCell s := by
    rw [T.bruhatCell_mul_self_eq_union_of_mem_simple hs]
    exact Or.inr hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx2
  have hv' : v⁻¹ ∈ T.bruhatCell s := by
    simpa only [T.inv_bruhatCell, T.inv_simple hs] using Set.inv_mem_inv.mpr hv
  obtain ⟨b₁, hb₁, b₂, hb₂, h₁⟩ := hdc u hu
  obtain ⟨b₃, hb₃, b₄, hb₄, h₂⟩ := hdc v⁻¹ hv'
  have huv : u * v = b₁ * (g * (b₂ * b₄⁻¹) * g⁻¹) * b₃⁻¹ := by
    calc u * v = (u * n) * (v⁻¹ * n)⁻¹ := by group
      _ = _ := by rw [h₁, h₂]; group
  rw [huv]
  exact P.mul_mem (P.mul_mem (hB hb₁)
    (hconj _ (T.subgroupB.mul_mem hb₂ (T.subgroupB.inv_mem hb₄)))) (P.inv_mem (hB hb₃))

/-- If a conjugate `g B g⁻¹` of the distinguished subgroup `B` lies in a subgroup `P ⊇ B`, then
`g ∈ P`. -/
theorem mem_of_conj_subgroupB_le {P : Subgroup G} (hB : T.subgroupB ≤ P) {g : G}
    (hconj : ∀ b ∈ T.subgroupB, g * b * g⁻¹ ∈ P) : g ∈ P := by
  obtain ⟨w, hg, -⟩ := T.existsUnique_mem_bruhatCell g
  obtain ⟨l, hl, hlen, rfl⟩ := T.exists_prod_eq_of_wordLength w
  induction l generalizing g with
  | nil =>
    rw [List.prod_nil, T.bruhatCell_one] at hg
    exact hB hg
  | cons s l ih =>
    have hs := hl s List.mem_cons_self
    have hl' : ∀ t ∈ l, t ∈ T.simple := fun t ht ↦ hl t (List.mem_cons_of_mem s ht)
    have hbound := T.wordLength_simple_mul_le hs l.prod
    have htail := T.wordLength_prod_le hl'
    simp only [List.length_cons, List.prod_cons] at hlen hg
    have hle : ℓ l.prod ≤ ℓ (s * l.prod) := by omega
    have hsP := T.bruhatCell_subset_of_conj_subgroupB_le hB hs hle hg hconj
    rw [← T.bruhatCell_mul_eq_of_wordLength_le hs hle] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hg
    have hxP := hsP hx
    refine P.mul_mem hxP (ih ?_ hl' hy (by omega))
    intro b hb
    have h := hconj b hb
    rwa [mul_inv_rev, ← mul_assoc, P.mul_mem_cancel_right (P.inv_mem hxP), mul_assoc x,
      mul_assoc x, P.mul_mem_cancel_left hxP] at h

/-- **Conjugation into a standard parabolic.** For subsets `J, J'` of the simple reflections,
`g P_J g⁻¹ ≤ P_{J'}` holds exactly when `J ⊆ J'` and `g ∈ P_{J'}`. For `J = ∅` this says that
`g B g⁻¹ ≤ P_{J'}` forces `g ∈ P_{J'}`; applied to `g` and `g⁻¹` it says that conjugate standard
parabolics are equal (Bourbaki, Ch. IV §2, nos. 5--6; Borel--Tits 1965, Corollaire 5.18 (ii)). -/
@[simp]
theorem conj_smul_standardParabolic_le_iff (J J' : Set T.simple) (g : G) :
    MulAut.conj g • T.standardParabolic J ≤ T.standardParabolic J' ↔
      J ⊆ J' ∧ g ∈ T.standardParabolic J' := by
  refine ⟨fun h ↦ ?_, fun ⟨hJ, hg⟩ ↦
    Subgroup.conj_smul_le_of_le (T.standardParabolic_monotone hJ) ⟨g, hg⟩⟩
  have h' : ∀ p ∈ T.standardParabolic J, g * p * g⁻¹ ∈ T.standardParabolic J' :=
    fun p hp ↦ h (Subgroup.smul_mem_pointwise_smul p _ _ hp)
  have hg : g ∈ T.standardParabolic J' :=
    T.mem_of_conj_subgroupB_le (T.subgroupB_le_standardParabolic J')
      fun b hb ↦ h' b (T.subgroupB_le_standardParabolic J hb)
  refine ⟨(T.standardParabolic_le_standardParabolic_iff J J').mp fun p hp ↦ ?_, hg⟩
  have := h' p hp
  rwa [(T.standardParabolic J').mul_mem_cancel_right ((T.standardParabolic J').inv_mem hg),
    (T.standardParabolic J').mul_mem_cancel_left hg] at this

/-- The elementwise form of `conj_smul_standardParabolic_le_iff`: `g p g⁻¹ ∈ P_{J'}` for every
`p ∈ P_J` exactly when `J ⊆ J'` and `g ∈ P_{J'}`. -/
@[simp]
theorem conj_standardParabolic_le_iff (J J' : Set T.simple) (g : G) :
    (∀ p ∈ T.standardParabolic J, g * p * g⁻¹ ∈ T.standardParabolic J') ↔
      J ⊆ J' ∧ g ∈ T.standardParabolic J' := by
  rw [← T.conj_smul_standardParabolic_le_iff]
  refine ⟨fun h y hy ↦ ?_, fun h p hp ↦ h (Subgroup.smul_mem_pointwise_smul p _ _ hp)⟩
  obtain ⟨p, hp, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hy
  exact h p hp

/-- **Conjugate standard parabolics are equal.** For subsets `J, J'` of the simple reflections,
`g P_J g⁻¹ = P_{J'}` holds exactly when `J = J'` and `g ∈ P_J`. -/
@[simp]
theorem conj_standardParabolic_eq_iff (J J' : Set T.simple) (g : G) :
    MulAut.conj g • T.standardParabolic J = T.standardParabolic J' ↔
      J = J' ∧ g ∈ T.standardParabolic J := by
  constructor
  · intro h
    obtain ⟨hJ, hg⟩ := (T.conj_smul_standardParabolic_le_iff J J' g).mp h.le
    have hge : MulAut.conj g⁻¹ • T.standardParabolic J' = T.standardParabolic J := by
      rw [← h, map_inv, inv_smul_smul]
    obtain ⟨hJ', -⟩ := (T.conj_smul_standardParabolic_le_iff J' J g⁻¹).mp hge.le
    have hJJ : J = J' := hJ.antisymm hJ'
    exact ⟨hJJ, hJJ ▸ hg⟩
  · rintro ⟨rfl, hg⟩
    exact Subgroup.conj_smul_eq_self_of_mem hg

end TauCeti.TitsSystem
