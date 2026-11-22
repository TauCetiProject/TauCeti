/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.KazhdanPair
public import TauCeti.RepresentationTheory.Continuous.Unitary.Induced
import TauCeti.GroupTheory.PositiveDefinite.Basic
import TauCeti.GroupTheory.PropertyT.PositiveDefinite

/-!
# Relative property (T) and subgroups of finite index

Relative property (T) is insensitive to passing to and from subgroups of finite index:

* **Finite-index overgroups.** For a normal subgroup `N` of an arbitrary group `Γ`, quantitative
  Kazhdan approximation and coset averaging (`exists_invariant_norm_sub_lt_of_finiteIndex`) transfer
  relative property (T) to every subgroup `Λ` in which `N ⊓ Λ` has finite index
  (`Subgroup.RelativePropertyT.of_relIndex_ne_zero`). When `Γ` is countable, the same holds for
  arbitrary subgroups `K` with `K.IsFiniteRelIndex Λ`
  (`Subgroup.RelativePropertyT.of_isFiniteRelIndex`), using the quantitative characterization in
  `TauCeti/GroupTheory/PropertyT/PositiveDefinite.lean`.
* **Finite-index subgroups.** If a normal subgroup `Λ` of `Γ` has relative property (T) and `K` has
  finite index in `Γ`, inducing a representation of `K` with almost invariant vectors to `Γ` shows
  that `Λ ⊓ K` has relative property (T) in `K` (`Subgroup.RelativePropertyT.subgroupOf`), which
  yields equivalence for normal `Λ` (`Subgroup.relativePropertyT_subgroupOf_iff_of_normal`) and
  Kazhdan's theorem that property (T) is a finite-index invariant of arbitrary discrete groups
  (`Subgroup.relativePropertyT_top_iff_of_finiteIndex`). When `Γ` is countable, inducing
  positive-definite functions via `TauCeti.inducedFun` gives the same equivalence for arbitrary
  subgroups `Λ` without normality (`Subgroup.relativePropertyT_subgroupOf_iff`).

## Main statements

* `Subgroup.RelativePropertyT.of_relIndex_ne_zero`: relative property (T) passes from a normal
  subgroup `N` to every subgroup in which `N` has finite relative index, in arbitrary Hilbert-space
  universes without countability.
* `Subgroup.RelativePropertyT.subgroupOf`: relative property (T) of a normal subgroup `Λ` passes to
  `Λ ⊓ K` inside a subgroup `K` of finite index.
* `Subgroup.relativePropertyT_top_iff_of_finiteIndex`: a group has property (T) if and only if a
  subgroup of finite index has property (T).
* `Subgroup.relativePropertyT_iff_of_isFiniteRelIndex_of_normal`,
  `Subgroup.relativePropertyT_subgroupOf_iff_of_normal`: universe-`v` finite-index equivalences for
  normal subgroups without countability.
* `Subgroup.RelativePropertyT.of_isFiniteRelIndex`,
  `Subgroup.relativePropertyT_iff_of_isFiniteRelIndex`,
  `Subgroup.relativePropertyT_subgroupOf_iff`: finite-index transfer and equivalences for
  arbitrary subgroups of countable groups.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §14.1 (Exercise 14.3 and
  Proposition 14.1.5).
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Theorem 1.7.1.
* P. Jolissaint, *On Property (T) for pairs of topological groups*, Enseign. Math. (2) 51 (2005),
  31–45, Proposition 2.4.
-/

public section

namespace Subgroup

universe u v w

open ContRepresentation
open scoped ComplexOrder

variable {Γ : Type v} [Group Γ]

/-- Common coset-averaging step for finite-relative-index permanence: if `(F₁, δ₁)`-invariant unit
vectors lie within `1 / 4` of a `K`-invariant vector and `K` has finite relative index in `Λ`,
then `Λ` has relative property (T). -/
private theorem relativePropertyT_of_exists_invariant_norm_sub_quarter {K Λ : Subgroup Γ}
    [K.IsFiniteRelIndex Λ] {F₁ : Finset Γ} {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hF₁ : ∀ (V : Type w) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (ρ : ContRepresentation ℂ Γ V), ρ.IsUnitary →
        ∀ ξ : V, ‖ξ‖ = 1 → (∀ g ∈ F₁, ‖ρ g ξ - ξ‖ < δ₁) →
          ∃ v ∈ (ρ.restrict K.subtype).invariants, ‖v - ξ‖ < 1 / 4) :
    Λ.RelativePropertyT.{w} := by
  classical
  let Q := Λ ⧸ K.subgroupOf Λ
  let : Fintype Q := Subgroup.fintypeQuotientOfFiniteIndex
  let F : Finset Γ := F₁ ∪ Finset.univ.image fun x : Q ↦ (x.out : Γ)
  let δ : ℝ := min δ₁ (1 / 4)
  have hδ : 0 < δ := lt_min hδ₁ (by norm_num)
  refine (isKazhdanPair_of_exists_invariant_norm_sub_lt_one (F := F)
    fun V _ _ _ ρ hρ ξ hξ hξF ↦ ?_).relativePropertyT hδ
  obtain ⟨v, hvK, hvξ⟩ := hF₁ V ρ hρ ξ hξ fun g hg ↦
    (hξF g (Finset.mem_union_left _ hg)).trans_le (min_le_left _ _)
  have hvK' : v ∈ ((ρ.restrict Λ.subtype).restrict (K.subgroupOf Λ).subtype).invariants :=
    fun h ↦ hvK ⟨_, mem_subgroupOf.mp h.property⟩
  have hmove (q : Q) : ‖ρ.restrict Λ.subtype q.out v - v‖ < 3 / 4 := by
    have hq : ‖ρ (q.out : Γ) ξ - ξ‖ < 1 / 4 :=
      (hξF _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ q)))).trans_le
        (min_le_right _ _)
    have h1 := norm_sub_le_norm_sub_add_norm_sub (ρ (q.out : Γ) v) (ρ (q.out : Γ) ξ) v
    have h2 := norm_sub_le_norm_sub_add_norm_sub (ρ (q.out : Γ) ξ) ξ v
    rw [← map_sub, hρ.norm_map] at h1
    rw [restrict_apply_apply, coe_subtype]
    linarith [norm_sub_rev v ξ]
  obtain ⟨w, hw, hwv⟩ :=
    (ρ.restrict Λ.subtype).exists_invariant_norm_sub_lt_of_finiteIndex hvK' hmove
  exact ⟨w, hw, (norm_sub_le_norm_sub_add_norm_sub w v ξ).trans_lt (by linarith)⟩

/-! ### Normal subgroups in arbitrary discrete groups -/

/-- **Relative property (T) passes to finite-index overgroups.** If a normal subgroup `N` has
relative property (T) in the universe `v` of `Γ`, then every subgroup `Λ` in which `N ⊓ Λ` has
finite index has relative property (T) in every Hilbert-space universe `u`, with no countability
assumption on `Γ` (and without requiring `N ≤ Λ`). -/
theorem RelativePropertyT.of_relIndex_ne_zero {N Λ : Subgroup Γ} [N.Normal]
    (hN : N.RelativePropertyT.{v}) (hNΛ : N.relIndex Λ ≠ 0) :
    Λ.RelativePropertyT.{u} := by
  have : N.IsFiniteRelIndex Λ := ⟨hNΛ⟩
  obtain ⟨F, δ, hδ, hK⟩ := (relativePropertyT_iff_exists_isKazhdanPair.{v, v} N).mp hN
  have hKu : N.IsKazhdanPair.{u} F δ := hK.of_universe
  refine relativePropertyT_of_exists_invariant_norm_sub_quarter (K := N) (Λ := Λ) (F₁ := F)
    (mul_pos hδ (by norm_num : (0 : ℝ) < 1 / 4)) fun V _ _ _ ρ hρ ξ _ hξF ↦ ?_
  obtain ⟨η, hη, hξη⟩ := hKu.exists_mem_invariants_norm_sub_lt hρ (by norm_num) hξF
  exact ⟨η, hη, by rwa [norm_sub_rev]⟩

/-- **Relative property (T) passes to subgroups of finite index.** If a normal subgroup `Λ` of `Γ`
has relative property (T) and `K` has finite index in `Γ`, then `Λ ⊓ K` has relative property (T)
in `K`. -/
theorem RelativePropertyT.subgroupOf {Λ : Subgroup Γ} [Λ.Normal]
    (hΛ : Λ.RelativePropertyT.{max u v}) (K : Subgroup Γ) [K.FiniteIndex] :
    (Λ.subgroupOf K).RelativePropertyT.{max u v} := by
  classical
  let := K.fintypeQuotientOfFiniteIndex
  refine (relativePropertyT_def _).mpr fun H _ _ _ ρ hρ hρa ↦ ?_
  -- The induced representation of `Γ` has almost invariant vectors, hence a nonzero `Λ`-invariant
  -- vector `f`; a nonzero value of `f` is fixed by `Λ ⊓ K`.
  obtain ⟨f, hf0, hf⟩ := (relativePropertyT_def Λ).mp hΛ (PiLp 2 fun _ : Γ ⧸ K ↦ H) (induced ρ)
    (isUnitary_induced hρ) (hasAlmostInvariantVectors_induced hρa)
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf0 (PiLp.ext h)
  exact ⟨f x, hx, apply_mem_invariants_of_mem_invariants_induced ρ hf x⟩

/-- **Property (T) and subgroups of finite index.** A group has property (T) if and only if a
subgroup of finite index has property (T). -/
theorem relativePropertyT_top_iff_of_finiteIndex (K : Subgroup Γ) [K.FiniteIndex] :
    (⊤ : Subgroup Γ).RelativePropertyT.{max u v} ↔
      (⊤ : Subgroup K).RelativePropertyT.{max u v} := by
  refine ⟨fun h ↦ by simpa using h.subgroupOf K, fun h ↦ ?_⟩
  -- Property (T) of `K` gives relative property (T) of `K`, hence of its normal core, in `Γ`.
  have hK : K.RelativePropertyT.{max u v} := by
    simpa [map_top, range_subtype] using h.map K.subtype
  refine ((relativePropertyT_max_iff.{u, v} _).mp (hK.mono K.normalCore_le)).of_relIndex_ne_zero ?_
  rw [relIndex_top_right]
  exact FiniteIndex.index_ne_zero

/-- Without countability, if `K` is normal in `Γ` and has finite relative index in `Λ` (`K ≤ Λ`),
then `K` has relative property (T) if and only if `Λ` does, for Hilbert spaces in the universe `v`
of `Γ`. -/
theorem relativePropertyT_iff_of_isFiniteRelIndex_of_normal {K Λ : Subgroup Γ} [K.Normal]
    (hKL : K ≤ Λ) [K.IsFiniteRelIndex Λ] :
    K.RelativePropertyT.{v} ↔ Λ.RelativePropertyT.{v} :=
  ⟨fun hK ↦ hK.of_relIndex_ne_zero IsFiniteRelIndex.relIndex_ne_zero, fun hΛ ↦ hΛ.mono hKL⟩

/-- Without countability, for a normal subgroup `Λ` and a finite-index subgroup `H` of `Γ`,
`Λ.subgroupOf H` has relative property (T) in `H` if and only if `Λ` has relative property (T) in
`Γ`, for Hilbert spaces in the universe `v` of `Γ`. -/
theorem relativePropertyT_subgroupOf_iff_of_normal (Λ H : Subgroup Γ) [Λ.Normal]
    [H.FiniteIndex] :
    (Λ.subgroupOf H).RelativePropertyT.{v} ↔ Λ.RelativePropertyT.{v} := by
  have hdown {G' : Type v} [Group G'] (M L : Subgroup G') [M.Normal] [L.FiniteIndex]
      (hM : M.RelativePropertyT.{v}) : (M.subgroupOf L).RelativePropertyT.{v} :=
    (relativePropertyT_max_iff.{v, v} (M.subgroupOf L)).mp
      (((relativePropertyT_max_iff.{v, v} M).mpr hM).subgroupOf L)
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
  exact hinfT.of_relIndex_ne_zero IsFiniteRelIndex.relIndex_ne_zero

/-! ### Arbitrary subgroups in countable discrete groups -/

section Countable

/-- **Finite-relative-index permanence.** In a countable discrete group `Γ`, if `K` has finite
relative index in `Λ` (`K.IsFiniteRelIndex Λ`) and `K` has relative property (T), then `Λ` has
relative property (T) (without requiring `K ≤ Λ`). -/
theorem RelativePropertyT.of_isFiniteRelIndex [Countable Γ] {K : Subgroup Γ}
    (hK : K.RelativePropertyT.{u}) (Λ : Subgroup Γ) [K.IsFiniteRelIndex Λ] :
    Λ.RelativePropertyT.{u} := by
  obtain ⟨F₁, δ₁, hδ₁, hF₁⟩ :=
    (K.relativePropertyT_iff_forall_exists_invariant_norm_sub_lt.{u}).mp hK (1 / 4) (by norm_num)
  exact relativePropertyT_of_exists_invariant_norm_sub_quarter hδ₁ hF₁

/-- In a countable discrete group `Γ`, if `K ≤ Λ` has finite relative index in `Λ`, then `K` has
relative property (T) if and only if `Λ` does. -/
theorem relativePropertyT_iff_of_isFiniteRelIndex [Countable Γ] {K Λ : Subgroup Γ}
    (hKL : K ≤ Λ) [K.IsFiniteRelIndex Λ] :
    K.RelativePropertyT.{u} ↔ Λ.RelativePropertyT.{u} :=
  ⟨fun hK ↦ hK.of_isFiniteRelIndex Λ, fun hΛ ↦ hΛ.mono hKL⟩

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

end Countable

end Subgroup
