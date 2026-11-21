/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.PropertyT.Basic
import TauCeti.GroupTheory.PositiveDefinite.Basic
import TauCeti.GroupTheory.PropertyT.PositiveDefinite
import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Finite-index permanence of relative property (T)

When the ambient discrete group `Γ` is countable (in every Hilbert-space universe `u`), or under a
normality hypothesis in the group's own universe `v`, relative property (T) is invariant under
passing to finite-index subgroups and overgroups, both for the target subgroup `Λ ≤ Γ` and for the
ambient discrete group `Γ`:

1. **Finite relative index in the target subgroup**: if `K` has finite relative index in `Λ`
   (`K.IsFiniteRelIndex Λ`, i.e., `[Λ : K ⊓ Λ] < ∞`), then relative property (T) of `K` in `Γ`
   implies relative property (T) of `Λ` in `Γ` (and the converse holds when `K ≤ Λ`), whenever `Γ`
   is countable (in any universe `u`) or `K` is normal in `Γ` (starting from the universe `v` of
   `Γ`). Given an almost invariant unit vector `ξ`, quantitative relative property (T) of `K`
   yields a `K`-invariant vector `v` within `1 / 2` of `ξ`, and averaging `ρ (s x) v` over a finite
   set of left-coset representatives of `K.subgroupOf Λ` in `Λ` produces a nonzero `Λ`-invariant
   vector.
2. **Finite index in the ambient group**: if `H ≤ Γ` has `[Γ : H] < ∞` (`H.FiniteIndex`), then
   `Λ.subgroupOf H` has relative property (T) in `H` if and only if `Λ` has relative property (T)
   in `Γ`, whenever `Γ` is countable (in any universe `u`) or `Λ` is normal in `Γ` (for Hilbert
   spaces in the universe `v` of `Γ`). From `H` to `Γ`, pushing forward `Λ.subgroupOf H` along
   `H.subtype` gives `Λ ⊓ H`, which has finite relative index in `Λ`. From `Γ` to `H`, inducing a
   normalized positive-definite function `φ : H → ℂ` to `Γ` via `TauCeti.inducedFun` along a
   section fixing the identity coset controls `1 - (φ h).re` by
   `[Γ : H] * (1 - (inducedFun s φ h).re)` for `h ∈ Λ.subgroupOf H`.

When `K` (respectively `Λ`) is normal, quantitative approximation requires no countability
assumption on `Γ` for Hilbert spaces in the universe `v` of `Γ`; in particular, Kazhdan's theorem
that property (T) (`Λ = ⊤`) is a finite-index invariant holds for arbitrary discrete groups in the
universe `v` of `Γ` without countability.

## Main statements

* `Subgroup.RelativePropertyT.of_isFiniteRelIndex`,
  `Subgroup.relativePropertyT_iff_of_isFiniteRelIndex` (for countable `Γ`, in any universe `u`), and
  `_of_normal` (for normal `K` without countability, starting from the universe `v` of `Γ`):
  transfer and equivalence under finite relative index `K.IsFiniteRelIndex Λ`.
* `Subgroup.relativePropertyT_subgroupOf_iff` (for countable `Γ`, in any universe `u`) and
  `Subgroup.relativePropertyT_subgroupOf_iff_of_normal` (for normal `Λ` without countability, in
  the universe `v` of `Γ`): invariance under passing to a finite-index ambient subgroup `H ≤ Γ`.
* `Subgroup.relativePropertyT_top_iff_of_finiteIndex`: Kazhdan's theorem that property (T) in the
  universe `v` of `Γ` is a finite-index invariant of arbitrary discrete groups, with no
  countability hypothesis.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §14.1 (Exercise 14.3 and
  Proposition 14.1.5).
* P. Jolissaint, *On Property (T) for pairs of topological groups*, Enseign. Math. (2) 51 (2005),
  31–45, Proposition 2.4.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Theorem 1.7.1.
-/

public section

namespace Subgroup

universe u v

open ContRepresentation
open scoped ComplexOrder

variable {Γ : Type v} [Group Γ]

/-! ### Auxiliary lemmas for coset averaging and positive-definite induction -/

section Helpers

/-- Averaging a `K`-invariant vector within `1 / 2` of an almost invariant unit vector over left
cosets of `K.subgroupOf Λ` in `Λ` produces a nonzero `Λ`-invariant vector. -/
private theorem relativePropertyT_of_exists_invariant_half {K Λ : Subgroup Γ}
    [K.IsFiniteRelIndex Λ] {F₁ : Finset Γ} {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hK : ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (ρ : ContRepresentation ℂ Γ V), ρ.IsUnitary →
        ∀ ξ : V, ‖ξ‖ = 1 → (∀ g ∈ F₁, ‖ρ g ξ - ξ‖ < δ₁) →
          ∃ v ∈ (ρ.restrict K.subtype).invariants, ‖v - ξ‖ < 1 / 2) :
    Λ.RelativePropertyT.{u} := by
  classical
  let Q := Λ ⧸ K.subgroupOf Λ
  let : Fintype Q := Subgroup.fintypeQuotientOfFiniteIndex
  let F : Finset Γ := F₁ ∪ Finset.univ.image fun x : Q ↦ (x.out : Γ)
  let δ : ℝ := min δ₁ (1 / 4)
  have hδ : 0 < δ := lt_min hδ₁ (by norm_num)
  refine (isKazhdanPair_of_exists_invariant_norm_sub_lt_one (F := F)
    fun V _ _ _ ρ hρ ξ hξ hξF ↦ ?_).relativePropertyT hδ
  obtain ⟨v, hvK, hvξ⟩ := hK V ρ hρ ξ hξ fun g hg ↦
    (hξF g (Finset.mem_union_left _ hg)).trans_le (min_le_left _ _)
  let ρΛ := (ρ.restrict Λ.subtype).toRepresentation
  let w : V := (Fintype.card Q : ℂ)⁻¹ • Representation.relNorm ρΛ (K.subgroupOf Λ) v
  have hvK' : ∀ h : K.subgroupOf Λ, ρΛ h v = v := fun h ↦
    hvK ⟨h.1.1, h.2⟩
  have hwΛ : w ∈ (ρ.restrict Λ.subtype).invariants := fun g ↦ by
    dsimp only [w]
    rw [map_smul]
    congr 1
    exact Representation.relNorm_apply_eq_self ρΛ hvK' g
  have hcard_ne : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hw_sub : w - ξ = (Fintype.card Q : ℂ)⁻¹ • ∑ x : Q, (ρ (x.out : Γ) v - ξ) := by
    simp only [w, Representation.relNorm_apply, ρΛ, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul,
      inv_mul_cancel₀ hcard_ne, one_smul]
    rfl
  have hterm_lt (x : Q) : ‖ρ (x.out : Γ) v - ξ‖ < 3 / 4 := by
    have hsx_mem : (x.out : Γ) ∈ F :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    have hsx_lt : ‖ρ (x.out : Γ) ξ - ξ‖ < 1 / 4 := (hξF _ hsx_mem).trans_le (min_le_right _ _)
    have hsplit : ρ (x.out : Γ) v - ξ = ρ (x.out : Γ) (v - ξ) + (ρ (x.out : Γ) ξ - ξ) := by
      rw [map_sub]
      abel
    rw [hsplit]
    calc ‖ρ (x.out : Γ) (v - ξ) + (ρ (x.out : Γ) ξ - ξ)‖
        ≤ ‖ρ (x.out : Γ) (v - ξ)‖ + ‖ρ (x.out : Γ) ξ - ξ‖ := norm_add_le _ _
      _ = ‖v - ξ‖ + ‖ρ (x.out : Γ) ξ - ξ‖ := by rw [hρ.norm_map]
      _ < 3 / 4 := by linarith
  have hw_lt : ‖w - ξ‖ < 3 / 4 := by
    have hpos : (0 : ℝ) < Fintype.card Q := Nat.cast_pos.mpr Fintype.card_pos
    rw [hw_sub, norm_smul, norm_inv, RCLike.norm_natCast, inv_mul_lt_iff₀ hpos]
    calc ‖∑ x : Q, (ρ (x.out : Γ) v - ξ)‖
        ≤ ∑ x : Q, ‖ρ (x.out : Γ) v - ξ‖ := norm_sum_le _ _
      _ < ∑ _x : Q, (3 / 4 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ ↦ hterm_lt x
      _ = Fintype.card Q * (3 / 4) := by simp
  exact ⟨w, hwΛ, hw_lt.trans (by norm_num)⟩

/-- Inducing positive-definite functions from a finite-index subgroup `H ≤ Γ` via
`TauCeti.inducedFun` transfers quantitative positive-definite approximation from `Λ` to
`Λ.subgroupOf H`. -/
private theorem posSemidef_approx_subgroupOf {Λ H : Subgroup Γ} [H.FiniteIndex]
    (hΛ : ∀ ε : ℝ, 0 < ε →
      ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧
        ∀ φ : Γ → ℂ, (Matrix.of fun a b : Γ ↦ φ (a⁻¹ * b)).PosSemidef → φ 1 = 1 →
          (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (F_H : Finset H) (δ : ℝ), 0 < δ ∧
        ∀ φ : H → ℂ, (Matrix.of fun a b : H ↦ φ (a⁻¹ * b)).PosSemidef → φ 1 = 1 →
          (∀ k ∈ F_H, ‖φ k - 1‖ < δ) → ∀ h ∈ Λ.subgroupOf H, ‖φ h - 1‖ < ε := by
  classical
  let : Fintype (Γ ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  let N : ℕ := Fintype.card (Γ ⧸ H)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr Fintype.card_pos
  -- Choose a section `s : Γ ⧸ H → Γ` fixing the identity coset `x₀`.
  let x₀ : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  let s : Γ ⧸ H → Γ := Function.update Quotient.out x₀ 1
  have hs (x : Γ ⧸ H) : (s x : Γ ⧸ H) = x := by
    by_cases hx : x = x₀
    · subst hx; simp [s, x₀]
    · simp [s, hx]
  have hs1 : s x₀ = 1 := Function.update_self x₀ 1 Quotient.out
  intro ε hε
  obtain ⟨F, δ, hδ, hFδ⟩ := hΛ (ε ^ 2 / (2 * N)) (by positivity)
  let c (g : Γ) (x : Γ ⧸ H) : H :=
    ⟨(s (g • x))⁻¹ * g * s x, TauCeti.inv_mul_mul_mem_of_section hs g x⟩
  let F_H : Finset H := F.biUnion fun g ↦ Finset.univ.image (c g)
  refine ⟨F_H, δ, hδ, fun φ hφ h1 hφF h hh ↦ ?_⟩
  -- Induce `φ` to `Γ` via `s`; closeness on `F_H` makes `ψ` close to `1` on `F`, hence on `Λ`.
  let ψ : Γ → ℂ := TauCeti.inducedFun s φ
  have hψF (g : Γ) (hg : g ∈ F) : ‖ψ g - 1‖ < δ :=
    TauCeti.norm_inducedFun_sub_one_lt hs fun x ↦
      hφF (c g x) (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩)
  have hψh : ‖ψ (h : Γ) - 1‖ < ε ^ 2 / (2 * N) :=
    hFδ ψ (TauCeti.posSemidef_inducedFun s hφ) ((TauCeti.inducedFun_one s φ).trans h1) hψF h hh
  -- Convert the bound on `ψ h` back to `‖φ h - 1‖` via the real-part averaging inequality.
  have hre_ψ : 1 - (ψ (h : Γ)).re < ε ^ 2 / (2 * N) :=
    lt_of_le_of_lt (by simpa [norm_sub_rev] using Complex.re_le_norm (1 - ψ h)) hψh
  have hre_h : 1 - (φ h).re ≤ (N : ℝ) * (1 - (ψ (h : Γ)).re) :=
    TauCeti.one_sub_re_le_card_mul_one_sub_re_inducedFun hs hs1 hφ h1 h
  have hre_lt : 1 - (φ h).re < ε ^ 2 / 2 := by
    have hmul : (N : ℝ) * (ε ^ 2 / (2 * N)) = ε ^ 2 / 2 := by field_simp [hNpos.ne']
    nlinarith
  have hnorm_sq : ‖φ h - 1‖ ^ 2 ≤ 2 * (1 - (φ h).re) := hφ.norm_sub_one_sq_le h1 h
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp (by linarith)

end Helpers

/-! ### Finite relative index in the target subgroup -/

/-- If a normal subgroup `K` has finite relative index in `Λ` (`K.IsFiniteRelIndex Λ`) and relative
property (T) in the universe `v` of `Γ`, then `Λ` has relative property (T) in every Hilbert-space
universe `u`, with no countability assumption on `Γ` (and without requiring `K ≤ Λ`). -/
theorem RelativePropertyT.of_isFiniteRelIndex_of_normal {K : Subgroup Γ} [K.Normal]
    (hK : K.RelativePropertyT.{v}) (Λ : Subgroup Γ) [K.IsFiniteRelIndex Λ] :
    Λ.RelativePropertyT.{u} := by
  obtain ⟨F₁, δ₁, hδ₁, hKP⟩ := K.relativePropertyT_iff_exists_isKazhdanPair.{v, v}.mp hK
  exact relativePropertyT_of_exists_invariant_half (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hδ₁)
    fun V _ _ _ ρ hρ ξ _ hξF ↦
      hKP.exists_invariant_norm_sub_lt hδ₁ hρ (by norm_num) ξ hξF

/-- Without countability, if `K` is normal in `Γ` and has finite relative index in `Λ` (`K ≤ Λ`),
then `K` has relative property (T) if and only if `Λ` does, for Hilbert spaces in the universe `v`
of `Γ`. -/
theorem relativePropertyT_iff_of_isFiniteRelIndex_of_normal {K Λ : Subgroup Γ} [K.Normal]
    (hKL : K ≤ Λ) [K.IsFiniteRelIndex Λ] :
    K.RelativePropertyT.{v} ↔ Λ.RelativePropertyT.{v} :=
  ⟨fun hK ↦ hK.of_isFiniteRelIndex_of_normal Λ, fun hΛ ↦ hΛ.mono hKL⟩

/-- **Finite-relative-index permanence.** In a countable discrete group `Γ`, if `K` has finite
relative index in `Λ` (`K.IsFiniteRelIndex Λ`) and `K` has relative property (T), then `Λ` has
relative property (T) (without requiring `K ≤ Λ`). -/
theorem RelativePropertyT.of_isFiniteRelIndex [Countable Γ] {K : Subgroup Γ}
    (hK : K.RelativePropertyT.{u}) (Λ : Subgroup Γ) [K.IsFiniteRelIndex Λ] :
    Λ.RelativePropertyT.{u} := by
  obtain ⟨F₁, δ₁, hδ₁, hF₁⟩ :=
    (K.relativePropertyT_iff_forall_exists_invariant_norm_sub_lt.{u}).mp hK (1 / 2) (by norm_num)
  exact relativePropertyT_of_exists_invariant_half hδ₁ hF₁

/-- In a countable discrete group `Γ`, if `K ≤ Λ` has finite relative index in `Λ`, then `K` has
relative property (T) if and only if `Λ` does. -/
theorem relativePropertyT_iff_of_isFiniteRelIndex [Countable Γ] {K Λ : Subgroup Γ}
    (hKL : K ≤ Λ) [K.IsFiniteRelIndex Λ] :
    K.RelativePropertyT.{u} ↔ Λ.RelativePropertyT.{u} :=
  ⟨fun hK ↦ hK.of_isFiniteRelIndex Λ, fun hΛ ↦ hΛ.mono hKL⟩

/-! ### Finite index in the ambient group -/

/-- Without countability, for a normal subgroup `Λ` and a finite-index subgroup `H` of `Γ`,
`Λ.subgroupOf H` has relative property (T) in `H` if and only if `Λ` has relative property (T) in
`Γ`, for Hilbert spaces in the universe `v` of `Γ`. -/
theorem relativePropertyT_subgroupOf_iff_of_normal (Λ H : Subgroup Γ) [Λ.Normal]
    [H.FiniteIndex] :
    (Λ.subgroupOf H).RelativePropertyT.{v} ↔ Λ.RelativePropertyT.{v} := by
  have hdown {G' : Type v} [Group G'] (M L : Subgroup G') [M.Normal] [L.FiniteIndex]
      (hM : M.RelativePropertyT.{v}) : (M.subgroupOf L).RelativePropertyT.{v} :=
    (relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt_of_normal (M.subgroupOf L)).mpr
      (posSemidef_approx_subgroupOf
        ((relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt_of_normal M).mp hM))
  refine ⟨fun hΛH ↦ ?_, hdown Λ H⟩
  -- Pass down from `H` to `H.normalCore` so that `Λ ⊓ H.normalCore` is normal in `Γ`.
  let N := H.normalCore
  have : N.IsFiniteRelIndex H := isFiniteRelIndex_of_finiteIndex
  let N_H : Subgroup H := N.subgroupOf H
  have hΛNH : ((Λ.subgroupOf H).subgroupOf N_H).RelativePropertyT.{v} :=
    hdown (Λ.subgroupOf H) N_H hΛH
  have hmap : ((Λ.subgroupOf H).subgroupOf N_H).map (H.subtype.comp N_H.subtype) = Λ ⊓ N := by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.subgroupOf_map_subtype,
      Subgroup.map_subgroupOf_eq_of_le H.normalCore_le, inf_assoc,
      inf_of_le_right H.normalCore_le]
  have hinfT : (Λ ⊓ N).RelativePropertyT.{v} := by
    rw [← hmap]
    exact hΛNH.map (H.subtype.comp N_H.subtype)
  have : (Λ ⊓ N).IsFiniteRelIndex Λ :=
    IsFiniteRelIndex.inf inferInstance isFiniteRelIndex_of_finiteIndex
  exact hinfT.of_isFiniteRelIndex_of_normal Λ

/-- **Kazhdan's finite-index theorem.** For a finite-index subgroup `H` of an arbitrary discrete
group `Γ` (with no countability assumption), `H` has property (T) if and only if `Γ` has property
(T), for Hilbert spaces in the universe `v` of `Γ`. -/
theorem relativePropertyT_top_iff_of_finiteIndex (H : Subgroup Γ) [H.FiniteIndex] :
    (⊤ : Subgroup H).RelativePropertyT.{v} ↔ (⊤ : Subgroup Γ).RelativePropertyT.{v} := by
  simpa using relativePropertyT_subgroupOf_iff_of_normal (⊤ : Subgroup Γ) H

/-- **Ambient finite-index invariance of relative property (T).** For any subgroup `Λ` and any
finite-index subgroup `H` of a countable discrete group `Γ`, `Λ.subgroupOf H` has relative property
(T) in `H` if and only if `Λ` has relative property (T) in `Γ`. -/
theorem relativePropertyT_subgroupOf_iff [Countable Γ] (Λ H : Subgroup Γ) [H.FiniteIndex] :
    (Λ.subgroupOf H).RelativePropertyT.{u} ↔ Λ.RelativePropertyT.{u} := by
  refine ⟨fun hΛH ↦ ?_, fun hΛ ↦ ?_⟩
  · have hinfT : (Λ ⊓ H).RelativePropertyT.{u} := by
      rw [← Subgroup.subgroupOf_map_subtype]
      exact hΛH.map H.subtype
    have : (Λ ⊓ H).IsFiniteRelIndex Λ :=
      IsFiniteRelIndex.inf inferInstance isFiniteRelIndex_of_finiteIndex
    exact hinfT.of_isFiniteRelIndex Λ
  · exact ((Λ.subgroupOf H).relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt.{u}).mpr
      (posSemidef_approx_subgroupOf
        ((Λ.relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt.{u}).mp hΛ))

end Subgroup
