/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.PropertyT.Basic
import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.GroupTheory.PositiveDefinite.Basic
import TauCeti.GroupTheory.PropertyT.KazhdanPair
import TauCeti.GroupTheory.PropertyT.PositiveDefinite

/-!
# Finite-index permanence of relative property (T)

Relative property (T) is invariant under passing to finite-index subgroups and overgroups, both for
the target subgroup `Λ ≤ Γ` and for the ambient discrete group `Γ`:

1. **Finite relative index in the target subgroup**: if `K` has finite relative index in `Λ`
   (`K.IsFiniteRelIndex Λ`, i.e., `[Λ : K ⊓ Λ] < ∞`), then relative property (T) of `K` in `Γ`
   implies relative property (T) of `Λ` in `Γ` (and the converse holds when `K ≤ Λ`). Given an
   almost invariant unit vector `ξ`, quantitative relative property (T) of `K` yields a
   `K`-invariant vector `v` within `1 / 2` of `ξ`, and averaging `ρ (s x) v` over a finite set of
   left-coset representatives of `K.subgroupOf Λ` in `Λ` produces a nonzero `Λ`-invariant vector.
2. **Finite index in the ambient group**: if `H ≤ Γ` has `[Γ : H] < ∞` (`H.FiniteIndex`), then
   `Λ.subgroupOf H` has relative property (T) in `H` if and only if `Λ` has relative property (T)
   in `Γ`. From `H` to `Γ`, pushing forward `Λ.subgroupOf H` along `H.subtype` gives `Λ ⊓ H`, which
   has finite relative index in `Λ`. From `Γ` to `H`, inducing a normalized positive-definite
   function `φ : H → ℂ` to `Γ` via `TauCeti.inducedFun` along a section fixing the identity coset
   controls `1 - (φ h).re` by `[Γ : H] * (1 - (inducedFun s φ h).re)` for `h ∈ Λ.subgroupOf H`.

When `K` (respectively `Λ`) is normal, quantitative approximation requires no countability
assumption on `Γ`; in particular, Kazhdan's theorem that property (T) (`Λ = ⊤`) is a finite-index
invariant holds for arbitrary discrete groups without countability.

## Main statements

* `Subgroup.RelativePropertyT.of_isFiniteRelIndex`,
  `Subgroup.relativePropertyT_iff_of_isFiniteRelIndex` (and `_of_normal`): transfer and equivalence
  under finite relative index `K.IsFiniteRelIndex Λ`.
* `Subgroup.relativePropertyT_subgroupOf_iff` (and `_of_normal`): invariance under passing to a
  finite-index ambient subgroup `H ≤ Γ`.
* `Subgroup.relativePropertyT_top_iff_of_finiteIndex`: Kazhdan's theorem that property (T) is a
  finite-index invariant of discrete groups, with no countability hypothesis.

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
  let s : Q → Λ := Quotient.out
  have hs (x : Q) : (s x : Q) = x := QuotientGroup.out_eq' x
  let F : Finset Γ := F₁ ∪ Finset.univ.image fun x : Q ↦ (s x : Γ)
  let δ : ℝ := min δ₁ (1 / 4)
  have hδ : 0 < δ := lt_min hδ₁ (by norm_num)
  refine IsKazhdanPair.relativePropertyT
    ((isKazhdanPair_def Λ F δ).mpr fun V _ _ _ ρ hρ ⟨ξ, hξ, hξF⟩ ↦ ?_) hδ
  obtain ⟨v, hvK, hvξ⟩ := hK V ρ hρ ξ hξ fun g hg ↦
    (hξF g (Finset.mem_union_left _ hg)).trans_le (min_le_left _ _)
  let w : V := (Fintype.card Q : ℂ)⁻¹ • ∑ x : Q, ρ (s x : Γ) v
  have hwΛ : w ∈ (ρ.restrict Λ.subtype).invariants := fun g ↦ by
    dsimp only [w]
    rw [restrict_apply_apply, Subgroup.coe_subtype, map_smul, map_sum]
    congr 1
    have hstep (x : Q) : ρ (g : Γ) (ρ (s x : Γ) v) = ρ (s (g • x) : Γ) v := by
      have hk : (s (g • x) : Γ)⁻¹ * (g : Γ) * (s x : Γ) ∈ K := by
        simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using
          TauCeti.inv_mul_mul_mem_of_section hs g x
      have hfix : ρ ((s (g • x) : Γ)⁻¹ * (g : Γ) * (s x : Γ)) v = v := by
        simpa only [restrict_apply_apply, Subgroup.coe_subtype] using hvK ⟨_, hk⟩
      calc ρ (g : Γ) (ρ (s x : Γ) v)
          = ρ (s (g • x) : Γ) (ρ ((s (g • x) : Γ)⁻¹ * (g : Γ) * (s x : Γ)) v) := by
              simp [← mul_apply_eq_comp, ← map_mul, mul_assoc]
        _ = ρ (s (g • x) : Γ) v := by rw [hfix]
    simp_rw [hstep]
    exact Fintype.sum_equiv (MulAction.toPerm g : Equiv.Perm Q) _ _ fun x ↦ rfl
  have hcard_ne : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hw_sub : w - ξ = (Fintype.card Q : ℂ)⁻¹ • ∑ x : Q, (ρ (s x : Γ) v - ξ) := by
    simp only [w, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul, inv_mul_cancel₀ hcard_ne, one_smul]
  have hterm_lt (x : Q) : ‖ρ (s x : Γ) v - ξ‖ < 3 / 4 := by
    have hsx_mem : (s x : Γ) ∈ F :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    have hsx_lt : ‖ρ (s x : Γ) ξ - ξ‖ < 1 / 4 := (hξF _ hsx_mem).trans_le (min_le_right _ _)
    have hsplit : ρ (s x : Γ) v - ξ = ρ (s x : Γ) (v - ξ) + (ρ (s x : Γ) ξ - ξ) := by
      rw [map_sub]
      abel
    rw [hsplit]
    calc ‖ρ (s x : Γ) (v - ξ) + (ρ (s x : Γ) ξ - ξ)‖
        ≤ ‖ρ (s x : Γ) (v - ξ)‖ + ‖ρ (s x : Γ) ξ - ξ‖ := norm_add_le _ _
      _ = ‖v - ξ‖ + ‖ρ (s x : Γ) ξ - ξ‖ := by rw [hρ.norm_map]
      _ < 3 / 4 := by linarith
  have hw_lt : ‖w - ξ‖ < 3 / 4 := by
    have hpos : (0 : ℝ) < Fintype.card Q := Nat.cast_pos.mpr Fintype.card_pos
    rw [hw_sub, norm_smul, norm_inv, RCLike.norm_natCast, inv_mul_lt_iff₀ hpos]
    calc ‖∑ x : Q, (ρ (s x : Γ) v - ξ)‖
        ≤ ∑ x : Q, ‖ρ (s x : Γ) v - ξ‖ := norm_sum_le _ _
      _ < ∑ _x : Q, (3 / 4 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ ↦ hterm_lt x
      _ = Fintype.card Q * (3 / 4) := by simp
  exact ⟨w, fun hw0 ↦ by simp [hw0, hξ] at hw_lt; linarith, hwΛ⟩

/-- For a normalized positive-definite function `φ` on a group `G'`, `0 ≤ 1 - (φ k).re` and
`‖φ k - 1‖ ^ 2 ≤ 2 * (1 - (φ k).re)`. -/
private theorem one_sub_re_nonneg_and_norm_sub_one_sq_le {G' : Type*} [Group G'] {φ : G' → ℂ}
    (hφ : (Matrix.of fun a b : G' ↦ φ (a⁻¹ * b)).PosSemidef) (h1 : φ 1 = 1) (k : G') :
    0 ≤ 1 - (φ k).re ∧ ‖φ k - 1‖ ^ 2 ≤ 2 * (1 - (φ k).re) := by
  have hle : ‖φ k‖ ≤ 1 := by
    simpa using hφ.norm_le_one_of_apply_self_eq_one (a := 1) (b := k) (by simp [h1]) (by simp [h1])
  refine ⟨by linarith [Complex.re_le_norm (φ k)], ?_⟩
  have hsq : (φ k).re ^ 2 + (φ k).im ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (norm_nonneg (φ k)) hle 2
    rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq, one_pow] at h
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

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
  let x₀ : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  let s : Γ ⧸ H → Γ := Function.update Quotient.out x₀ 1
  have hs (x : Γ ⧸ H) : (s x : Γ ⧸ H) = x := by
    by_cases hx : x = x₀
    · subst hx; simp [s, x₀]
    · dsimp only [s]
      rw [Function.update_of_ne hx]
      exact QuotientGroup.out_eq' x
  have hs1 : s x₀ = 1 := Function.update_self x₀ 1 Quotient.out
  intro ε hε
  obtain ⟨F, δ, hδ, hFδ⟩ := hΛ (ε ^ 2 / (2 * N)) (by positivity)
  let c (g : Γ) (x : Γ ⧸ H) : H :=
    ⟨(s (g • x))⁻¹ * g * s x, TauCeti.inv_mul_mul_mem_of_section hs g x⟩
  let F_H : Finset H := F.biUnion fun g ↦ Finset.univ.image (c g)
  refine ⟨F_H, δ, hδ, fun φ hφ h1 hφF h hh ↦ ?_⟩
  let ψ : Γ → ℂ := TauCeti.inducedFun s φ
  have hψF (g : Γ) (hg : g ∈ F) : ‖ψ g - 1‖ < δ :=
    TauCeti.norm_inducedFun_sub_one_lt hs fun x ↦
      hφF (c g x) (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩)
  have hψh : ‖ψ (h : Γ) - 1‖ < ε ^ 2 / (2 * N) :=
    hFδ ψ (TauCeti.posSemidef_inducedFun s hφ) ((TauCeti.inducedFun_one s φ).trans h1) hψF h hh
  have hre_ψ : 1 - (ψ (h : Γ)).re < ε ^ 2 / (2 * N) := by
    calc 1 - (ψ (h : Γ)).re = (1 - ψ (h : Γ)).re := by simp
      _ ≤ ‖1 - ψ (h : Γ)‖ := Complex.re_le_norm _
      _ = ‖ψ (h : Γ) - 1‖ := norm_sub_rev _ _
      _ < ε ^ 2 / (2 * N) := hψh
  have hc1 : c (h : Γ) x₀ = h := by
    have hsmul1 : (h : Γ) • x₀ = x₀ := by
      dsimp only [x₀]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      exact QuotientGroup.eq.mpr (by simp)
    ext
    simp [c, hsmul1, hs1]
  have hsum_re : ∑ x : Γ ⧸ H, (1 - (φ (c (h : Γ) x)).re) = (N : ℝ) * (1 - (ψ (h : Γ)).re) := by
    have hext (x : Γ ⧸ H) :
        Function.extend Subtype.val φ 0 ((s ((h : Γ) • x))⁻¹ * (h : Γ) * s x) =
          φ (c (h : Γ) x) :=
      Subtype.val_injective.extend_apply φ 0 (c (h : Γ) x)
    have hψ_re : (ψ (h : Γ)).re = (N : ℝ)⁻¹ * ∑ x : Γ ⧸ H, (φ (c (h : Γ) x)).re := by
      simp [ψ, TauCeti.inducedFun_apply, hext, N, Complex.re_sum]
    rw [hψ_re, mul_sub, mul_one, mul_inv_cancel_left₀ hNpos.ne', Finset.sum_sub_distrib]
    simp [N]
  have hre_h : 1 - (φ h).re ≤ (N : ℝ) * (1 - (ψ (h : Γ)).re) := by
    nth_rw 1 [← hc1]
    rw [← hsum_re]
    exact Finset.single_le_sum
      (fun x _ ↦ (one_sub_re_nonneg_and_norm_sub_one_sq_le hφ h1 _).1)
      (Finset.mem_univ x₀)
  have hre_lt : 1 - (φ h).re < ε ^ 2 / 2 := by
    have hmul : (N : ℝ) * (ε ^ 2 / (2 * N)) = ε ^ 2 / 2 := by field_simp [hNpos.ne']
    nlinarith
  have hnorm_sq := (one_sub_re_nonneg_and_norm_sub_one_sq_le hφ h1 h).2
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
then `K` has relative property (T) if and only if `Λ` does. -/
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
`Γ`. -/
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
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
      Subgroup.coe_subtype, Subgroup.mem_inf]
    exact ⟨by rintro ⟨⟨⟨x, _⟩, hxN⟩, hxΛ, rfl⟩; exact ⟨hxΛ, hxN⟩,
      fun ⟨hgΛ, hgN⟩ ↦ ⟨⟨⟨g, H.normalCore_le hgN⟩, hgN⟩, hgΛ, rfl⟩⟩
  have hinfT : (Λ ⊓ N).RelativePropertyT.{v} := by
    rw [← hmap]
    exact hΛNH.map (H.subtype.comp N_H.subtype)
  have : (Λ ⊓ N).IsFiniteRelIndex Λ :=
    IsFiniteRelIndex.inf inferInstance isFiniteRelIndex_of_finiteIndex
  exact hinfT.of_isFiniteRelIndex_of_normal Λ

/-- **Kazhdan's finite-index theorem.** For a finite-index subgroup `H` of an arbitrary discrete
group `Γ` (with no countability assumption), `H` has property (T) if and only if `Γ` has property
(T). -/
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
