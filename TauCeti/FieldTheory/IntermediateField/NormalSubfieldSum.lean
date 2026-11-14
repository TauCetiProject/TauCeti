/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import TauCeti.FieldTheory.IntermediateField.NormalSubfield

/-!
# Weighted isomorphism-class sums over a normal intermediate field

Let `Ω / K` be a normal field extension and `U` a normal intermediate field of `Ω / K` with
finitely many `K`-automorphisms. For any intermediate field `M` of `Ω / K` with `U ≤ M`, the
`U`-isomorphism classes of intermediate fields `E` of `Ω / U` whose underlying `K`-field
`E.restrictScalars K` is `K`-isomorphic to `M` form an orbit of size
`#Aut_K(U) / #{τ ∈ Aut_K(U) | τ extends to M}`
(`IntermediateField.ncard_isomorphic_restrictScalars_mul_natCard_eq`),
each having `#Aut_U(extendScalars hUM)` automorphisms over `U`
(`IntermediateField.natCard_extendScalars_algEquiv_eq_of_algEquiv_restrictScalars`), while
`#Aut_K(M) = #Aut_U(extendScalars hUM) · #{τ ∈ Aut_K(U) | τ extends to M}`
(`IntermediateField.natCard_algEquiv_eq_mul_of_le`).

Summing `w(E) / #Aut_U(E)` for any `K`-isomorphism-invariant weight `w` valued in `ℝ≥0∞` over
`U`-isomorphism representatives therefore multiplies the corresponding sum of `w(M) / #Aut_K(M)`
over `K`-isomorphism representatives by `#Aut_K(U)`: the index of the extendable-automorphism
subgroup cancels term-by-term between orbit sizes and automorphism counts.

## Main results

* `TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_le`:
  `#Aut_K(U) · ∑'_{M ∈ R_K} w(M) / #Aut_K(M) = ∑'_{E ∈ R_U} w(E) / #Aut_U(E)`.
* `TauCeti.tsum_div_natCard_algEquiv_eq_inv_mul_of_le`:
  `∑'_{M ∈ R_K} w(M) / #Aut_K(M) = (#Aut_K(U))⁻¹ · ∑'_{E ∈ R_U} w(E) / #Aut_U(E)`.
-/

public section
noncomputable section

open IntermediateField
open scoped ENNReal

namespace TauCeti

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Normal K Ω]

/-- On a single `K`-isomorphism class representative `M` containing a normal intermediate field `U`
with `Finite (U ≃ₐ[K] U)`, summing `w(E) / #Aut_U(E)` over the `U`-isomorphism representatives
`E ∈ R_U` lying in the `K`-class of `M` gives `#Aut_K(U) · (w(M) / #Aut_K(M))`: there are
`#Aut_K(U) / #Stab(M)` such `U`-classes, each with `#Aut_U(M)` automorphisms over `U`, and
`#Aut_K(M) = #Aut_U(M) · #Stab(M)`. -/
private theorem tsum_fiber_div_natCard_algEquiv_eq {U M : IntermediateField K Ω} [Normal K U]
    [Finite (U ≃ₐ[K] U)] (hUM : U ≤ M) {R_U : Set (IntermediateField U Ω)}
    (hRU : ∀ E : IntermediateField U Ω, Nonempty (M ≃ₐ[K] E.restrictScalars K) →
      ∃! F, F ∈ R_U ∧ Nonempty (E ≃ₐ[U] F))
    (w : IntermediateField K Ω → ℝ≥0∞)
    (hw : ∀ {L₁ L₂ : IntermediateField K Ω}, (L₁ ≃ₐ[K] L₂) → w L₁ = w L₂) :
    ∑' E : {E ∈ R_U | Nonempty (M ≃ₐ[K] E.restrictScalars K)},
        w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1) =
      (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞) * (w M / Nat.card (M ≃ₐ[K] M)) := by
  let C : Set (IntermediateField U Ω) := {E ∈ R_U | Nonempty (M ≃ₐ[K] E.restrictScalars K)}
  have hU_ne : Nat.card (U ≃ₐ[K] U) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  have horbit : C.ncard * Nat.card {τ : U ≃ₐ[K] U //
      ∃ σ : M ≃ₐ[K] M, ∀ x : U, (σ ⟨x.1, hUM x.2⟩ : Ω) = τ x} = Nat.card (U ≃ₐ[K] U) :=
    ncard_isomorphic_restrictScalars_mul_natCard_eq hUM hRU
  have hAutM := natCard_algEquiv_eq_mul_of_le hUM
  have hs_ne : Nat.card {τ : U ≃ₐ[K] U //
      ∃ σ : M ≃ₐ[K] M, ∀ x : U, (σ ⟨x.1, hUM x.2⟩ : Ω) = τ x} ≠ 0 :=
    Nat.card_ne_zero.2 ⟨⟨⟨1, ⟨.refl, fun _ ↦ rfl⟩⟩⟩, inferInstance⟩
  have hC_fin : C.Finite :=
    Set.finite_of_ncard_ne_zero (left_ne_zero_of_mul (horbit.symm ▸ hU_ne))
  have hconst (E : C) :
      w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1) =
        w M / Nat.card (extendScalars hUM ≃ₐ[U] extendScalars hUM) := by
    obtain ⟨e⟩ := E.2.2
    rw [(hw e).symm, (natCard_extendScalars_algEquiv_eq_of_algEquiv_restrictScalars hUM e).symm]
  rw [tsum_congr hconst, ENNReal.tsum_set_const, ← hC_fin.cast_ncard_eq]
  set a : ℝ≥0∞ := (Nat.card (extendScalars hUM ≃ₐ[U] extendScalars hUM) : ℝ≥0∞)
  set s : ℝ≥0∞ := (Nat.card {τ : U ≃ₐ[K] U //
    ∃ σ : M ≃ₐ[K] M, ∀ x : U, (σ ⟨x.1, hUM x.2⟩ : Ω) = τ x} : ℝ≥0∞)
  have ha_top : a ≠ ⊤ := ENNReal.natCast_ne_top _
  have hs_top : s ≠ ⊤ := ENNReal.natCast_ne_top _
  have hs0 : s ≠ 0 := Nat.cast_ne_zero.2 hs_ne
  have hcs : (C.ncard : ℝ≥0∞) * s = Nat.card (U ≃ₐ[K] U) := by
    simp only [s, ← Nat.cast_mul, horbit]
  have has : (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) = a * s := by
    simp only [a, s, ← Nat.cast_mul, hAutM]
  rw [has]
  calc
    (C.ncard : ℝ≥0∞) * (w M / a)
      = (C.ncard : ℝ≥0∞) * (w M * a⁻¹) * 1 := by rw [div_eq_mul_inv, mul_one]
    _ = (C.ncard : ℝ≥0∞) * (w M * a⁻¹) * (s * s⁻¹) := by
          rw [ENNReal.mul_inv_cancel hs0 hs_top]
    _ = ((C.ncard : ℝ≥0∞) * s) * (w M * (a⁻¹ * s⁻¹)) := by ac_rfl
    _ = (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞) * (w M / (a * s)) := by
          rw [hcs, ← ENNReal.mul_inv (.inr hs_top) (.inl ha_top), ← div_eq_mul_inv]

/-- **Weighted class-sum relation over a normal intermediate field.** Let `Ω / K` be normal and let
`U` be a normal intermediate field of `Ω / K` with `Finite (U ≃ₐ[K] U)`. For any
`K`-isomorphism-closed family `S` of intermediate fields of `Ω / K`, any set `R_K ⊆ S` of
`K`-isomorphism representatives of `S` with `U ≤ M` for all `M ∈ R_K`, any set `R_U` of
`U`-isomorphism representatives of `{E : IntermediateField U Ω | E.restrictScalars K ∈ S}`, and any
`K`-isomorphism-invariant weight `w : IntermediateField K Ω → ℝ≥0∞`,
`#Aut_K(U) · ∑'_{M ∈ R_K} w(M) / #Aut_K(M) = ∑'_{E ∈ R_U} w(E) / #Aut_U(E)`. -/
theorem mul_tsum_div_natCard_algEquiv_eq_of_le {U : IntermediateField K Ω} [Normal K U]
    [Finite (U ≃ₐ[K] U)] {S R_K : Set (IntermediateField K Ω)}
    (hS_iso : ∀ {L M : IntermediateField K Ω}, L ∈ S → (L ≃ₐ[K] M) → M ∈ S)
    (hRK_le : ∀ M ∈ R_K, U ≤ M)
    (hRK_sub : R_K ⊆ S)
    (hRK : ∀ L ∈ S, ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M))
    {R_U : Set (IntermediateField U Ω)}
    (hRU_sub : ∀ E ∈ R_U, E.restrictScalars K ∈ S)
    (hRU : ∀ E : IntermediateField U Ω, E.restrictScalars K ∈ S →
      ∃! F, F ∈ R_U ∧ Nonempty (E ≃ₐ[U] F))
    (w : IntermediateField K Ω → ℝ≥0∞)
    (hw : ∀ {L M : IntermediateField K Ω}, (L ≃ₐ[K] M) → w L = w M) :
    (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞) * ∑' M : R_K, w M.1 / Nat.card (M.1 ≃ₐ[K] M.1) =
      ∑' E : R_U, w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1) := by
  let g (E : IntermediateField U Ω) : ℝ≥0∞ :=
    w (E.restrictScalars K) / Nat.card (E ≃ₐ[U] E)
  let C (M : IntermediateField K Ω) : Set (IntermediateField U Ω) :=
    {E ∈ R_U | Nonempty (M ≃ₐ[K] E.restrictScalars K)}
  have hU_eq : R_U = ⋃ M ∈ R_K, C M := by
    ext E
    simp only [Set.mem_iUnion, exists_prop, C]
    refine ⟨fun hE ↦ ?_, fun ⟨_, _, hE, _⟩ ↦ hE⟩
    obtain ⟨M, ⟨hM, ⟨e⟩⟩, -⟩ := hRK (E.restrictScalars K) (hRU_sub E hE)
    exact ⟨M, hM, hE, ⟨e.symm⟩⟩
  have hdisj : R_K.PairwiseDisjoint C := by
    rintro M₁ hM₁ M₂ hM₂ hne
    refine Set.disjoint_left.2 ?_
    rintro E ⟨hE, ⟨e₁⟩⟩ ⟨-, ⟨e₂⟩⟩
    obtain ⟨_, -, huniq⟩ := hRK (E.restrictScalars K) (hRU_sub E hE)
    exact hne ((huniq M₁ ⟨hM₁, ⟨e₁.symm⟩⟩).trans (huniq M₂ ⟨hM₂, ⟨e₂.symm⟩⟩).symm)
  have hRHS : (∑' E : R_U, w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1)) =
      ∑' E : R_U, g E := rfl
  rw [hRHS, ← ENNReal.tsum_mul_left, hU_eq, tsum_biUnion hdisj]
  refine tsum_congr fun M ↦ ?_
  exact (tsum_fiber_div_natCard_algEquiv_eq (hRK_le M.1 M.2)
    (fun E ⟨e⟩ ↦ hRU E (hS_iso (hRK_sub M.2) e)) w hw).symm

/-- **Weighted class-sum relation over a normal intermediate field (divided form).** Divided form of
`TauCeti.mul_tsum_div_natCard_algEquiv_eq_of_le`:
`∑'_{M ∈ R_K} w(M) / #Aut_K(M) = (#Aut_K(U))⁻¹ · ∑'_{E ∈ R_U} w(E) / #Aut_U(E)`. -/
theorem tsum_div_natCard_algEquiv_eq_inv_mul_of_le {U : IntermediateField K Ω} [Normal K U]
    [Finite (U ≃ₐ[K] U)] {S R_K : Set (IntermediateField K Ω)}
    (hS_iso : ∀ {L M : IntermediateField K Ω}, L ∈ S → (L ≃ₐ[K] M) → M ∈ S)
    (hRK_le : ∀ M ∈ R_K, U ≤ M)
    (hRK_sub : R_K ⊆ S)
    (hRK : ∀ L ∈ S, ∃! M, M ∈ R_K ∧ Nonempty (L ≃ₐ[K] M))
    {R_U : Set (IntermediateField U Ω)}
    (hRU_sub : ∀ E ∈ R_U, E.restrictScalars K ∈ S)
    (hRU : ∀ E : IntermediateField U Ω, E.restrictScalars K ∈ S →
      ∃! F, F ∈ R_U ∧ Nonempty (E ≃ₐ[U] F))
    (w : IntermediateField K Ω → ℝ≥0∞)
    (hw : ∀ {L M : IntermediateField K Ω}, (L ≃ₐ[K] M) → w L = w M) :
    ∑' M : R_K, w M.1 / Nat.card (M.1 ≃ₐ[K] M.1) =
      (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞)⁻¹ *
        ∑' E : R_U, w (E.1.restrictScalars K) / Nat.card (E.1 ≃ₐ[U] E.1) := by
  have hU_ne : (Nat.card (U ≃ₐ[K] U) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩)
  rw [← mul_tsum_div_natCard_algEquiv_eq_of_le hS_iso hRK_le hRK_sub hRK hRU_sub hRU w hw,
    ← mul_assoc, ENNReal.inv_mul_cancel hU_ne (ENNReal.natCast_ne_top _), one_mul]

end TauCeti
