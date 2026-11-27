/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Graded.LinearMap
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.ModularLattice

/-!
# Kernels of perturbations by terms of higher degree

Let `V = ⨁ₙ Vₙ` be a finite-dimensional vector space graded by the integers, let `T` be an
endomorphism homogeneous of degree `d`, and let `S` be an endomorphism raising degrees by more
than `d`: it maps `Vₙ` into `⨁_{m > n + d} Vₘ`. Then the kernel of `T + S` is no larger than the
kernel of `T` (`LinearMap.IsHomogeneous.finrank_ker_add_le`).

The kernel of `T + S` is filtered by the subspaces `F n = ⨁_{m ≥ n} Vₘ`, and the leading
component in `Vₙ` of an element of `ker (T + S) ∩ F n` lies in `ker T`. So each graded piece of
this filtration of `ker (T + S)` embeds into `ker T ∩ Vₙ`, and the pieces `ker T ∩ Vₙ` are
independent. Equivalently, `T` is the leading term of `T + S` for the filtration, and the rank of
a filtered map is at least the rank of its leading term.

This is the linear algebra behind the semicontinuity of centralizer dimensions along a grading:
for a Lie algebra graded by the eigenvalues of `ad h`, an element `e + y` with `e` homogeneous and
`y` of strictly higher degree has a centralizer no larger than that of `e`.

## Main results

* `LinearMap.IsHomogeneous.finrank_ker_add_le`: `dim ker (T + S) ≤ dim ker T`.
* `Submodule.finrank_inf_le_finrank_inf_of_sup_eq_of_disjoint`: the inductive step, comparing the
  dimensions of `A ⊓ F` and `B ⊓ F` along one step `F₀ = V₀ ⊕ F₁` of a filtration.
* `iSupIndep.exists_biSup_ge_eq_top_and_biSup_ge_eq_bot`: the filtration `⨆ m ≥ n, 𝒜 m` of a
  finite-dimensional space by an independent spanning family is everything for small `n` and zero
  for large `n`.
-/

public section

open Module Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-! ### The filtration by degree -/

/-- An independent family `𝒜` spanning a finite-dimensional space has finitely many nonzero
members, so its part `⨆ m ≥ n, 𝒜 m` of degree at least `n` is everything for small `n` and zero
for large `n`. -/
theorem iSupIndep.exists_biSup_ge_eq_top_and_biSup_ge_eq_bot [FiniteDimensional K V]
    {𝒜 : ℤ → Submodule K V} (h𝒜 : iSupIndep 𝒜) (h𝒜top : ⨆ n, 𝒜 n = ⊤) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ ⨆ m ≥ lo, 𝒜 m = ⊤ ∧ ⨆ m ≥ hi, 𝒜 m = ⊥ := by
  have hfin : {n | 𝒜 n ≠ ⊥}.Finite := by
    have := h𝒜.fintypeNeBotOfFiniteDimensional
    exact Set.toFinite _
  obtain ⟨hi, hhi⟩ := hfin.bddAbove
  obtain ⟨lo, hlo⟩ := hfin.bddBelow
  refine ⟨min lo (hi + 1), hi + 1, min_le_right _ _, ?_, ?_⟩
  · refine eq_top_iff.mpr (h𝒜top ▸ iSup_le fun m ↦ ?_)
    by_cases hm : 𝒜 m = ⊥
    · simp [hm]
    · exact le_iSup₂_of_le (f := fun m (_ : m ≥ min lo (hi + 1)) ↦ 𝒜 m) m
        ((min_le_left _ _).trans (hlo hm)) le_rfl
  · refine eq_bot_iff.mpr (iSup₂_le fun m hm ↦ ?_)
    by_contra h
    have := hhi (show 𝒜 m ≠ ⊥ from fun h' ↦ h h'.le)
    omega

namespace Submodule

/-- **Comparing dimensions along one step of a filtration.** Let `F₀ = V₀ ⊕ F₁` be an internal
direct sum, and let `A` and `B` be subspaces such that the component in `V₀` of every element of
`A ⊓ F₀` modulo `F₁` lies in `B`, that is `V₀ ⊓ (A ⊓ F₀ ⊔ F₁) ≤ B`. If `A ⊓ F₁` has dimension at
most that of `B ⊓ F₁`, then `A ⊓ F₀` has dimension at most that of `B ⊓ F₀`. -/
theorem finrank_inf_le_finrank_inf_of_sup_eq_of_disjoint [FiniteDimensional K V]
    {A B V₀ F₀ F₁ : Submodule K V}
    (hF : V₀ ⊔ F₁ = F₀) (hdisj : Disjoint V₀ F₁) (hB : V₀ ⊓ (A ⊓ F₀ ⊔ F₁) ≤ B)
    (ih : finrank K ↥(A ⊓ F₁) ≤ finrank K ↥(B ⊓ F₁)) :
    finrank K ↥(A ⊓ F₀) ≤ finrank K ↥(B ⊓ F₀) := by
  have hF₁ : F₁ ≤ F₀ := hF ▸ le_sup_right
  -- `A ⊓ F₀` and its leading part `J` span the same space modulo `F₁`, by modularity
  set J := V₀ ⊓ (A ⊓ F₀ ⊔ F₁)
  have hsup : A ⊓ F₀ ⊔ F₁ = J ⊔ F₁ := by
    calc A ⊓ F₀ ⊔ F₁ = (F₁ ⊔ V₀) ⊓ (A ⊓ F₀ ⊔ F₁) := by
          rw [sup_comm F₁, hF]
          exact (inf_eq_right.mpr (sup_le inf_le_right hF₁)).symm
      _ = J ⊔ F₁ := by rw [sup_inf_assoc_of_le _ le_sup_right, sup_comm]
  have hA := finrank_sup_add_finrank_inf_eq (A ⊓ F₀) F₁
  rw [inf_assoc, inf_eq_right.mpr hF₁] at hA
  have hJ := finrank_sup_add_finrank_inf_eq J F₁
  rw [(hdisj.mono_left inf_le_left).eq_bot, finrank_bot, ← hsup] at hJ
  -- on the side of `B`, the pieces in `V₀` and in `F₁` are independent
  have hBsup := finrank_sup_add_finrank_inf_eq (B ⊓ V₀) (B ⊓ F₁)
  rw [(hdisj.mono inf_le_right inf_le_right).eq_bot, finrank_bot] at hBsup
  have hBle : finrank K ↥(B ⊓ V₀ ⊔ B ⊓ F₁) ≤ finrank K ↥(B ⊓ F₀) := finrank_mono
    (sup_le (inf_le_inf_left _ (hF ▸ le_sup_left)) (inf_le_inf_left _ hF₁))
  have hJle := finrank_mono (le_inf hB (inf_le_left : J ≤ V₀))
  omega

end Submodule

namespace LinearMap

variable [FiniteDimensional K V] {𝒜 : ℤ → Submodule K V}

/-! ### Perturbations of homogeneous maps -/

/-- **A perturbation by terms of higher degree does not enlarge the kernel.** Let `𝒜` be an
independent family of subspaces indexed by the integers which spans the finite-dimensional space
`V`, let `T` be homogeneous of degree `d`, and let `S` map `𝒜 n` into the span of the `𝒜 m` with
`m > n + d`. Then `ker (T + S)` has dimension at most that of `ker T`. -/
theorem IsHomogeneous.finrank_ker_add_le (h𝒜 : iSupIndep 𝒜) (h𝒜top : ⨆ n, 𝒜 n = ⊤)
    {T S : V →ₗ[K] V} {d : ℤ} (hT : IsHomogeneous T 𝒜 𝒜 d)
    (hS : ∀ ⦃n : ℤ⦄ ⦃v : V⦄, v ∈ 𝒜 n → S v ∈ ⨆ (m : ℤ) (_ : n + d < m), 𝒜 m) :
    finrank K (ker (T + S)) ≤ finrank K (ker T) := by
  -- the decreasing filtration `F n = ⨆ m ≥ n, 𝒜 m`, preserved by `T` and raised by `S`
  set F : ℤ → Submodule K V := fun n ↦ ⨆ (m : ℤ) (_ : n ≤ m), 𝒜 m
  have hTF (n : ℤ) : F n ≤ (F (n + d)).comap T := iSup₂_le fun m hm _ hx ↦
    le_iSup₂_of_le (f := fun m (_ : n + d ≤ m) ↦ 𝒜 m) (m + d) (by omega) le_rfl (hT.map_mem hx)
  have hSF (n : ℤ) : F n ≤ (F (n + d + 1)).comap S := iSup₂_le fun m hm _ hx ↦
    (iSup₂_le fun m' hm' ↦ le_iSup₂_of_le (f := fun m (_ : n + d + 1 ≤ m) ↦ 𝒜 m) m' (by omega)
      le_rfl : (⨆ (m' : ℤ) (_ : m + d < m'), 𝒜 m') ≤ F (n + d + 1)) (hS hx)
  -- the leading component in `𝒜 n` of an element of `ker (T + S) ⊓ F n` lies in `ker T`
  have step (n : ℤ) (ih : finrank K ↥(ker (T + S) ⊓ F (n + 1)) ≤ finrank K ↥(ker T ⊓ F (n + 1))) :
      finrank K ↥(ker (T + S) ⊓ F n) ≤ finrank K ↥(ker T ⊓ F n) := by
    refine finrank_inf_le_finrank_inf_of_sup_eq_of_disjoint (biSup_ge_eq_sup 𝒜 n).symm
      (h𝒜.disjoint_biSup (y := {m | n < m}) (lt_irrefl n)) (fun v hv ↦ ?_) ih
    obtain ⟨hvn, hv⟩ := mem_inf.mp hv
    obtain ⟨a, ha, w, hw, rfl⟩ := mem_sup.mp hv
    obtain ⟨haker, haF⟩ := mem_inf.mp ha
    have hTa : T a = -S a := eq_neg_of_add_eq_zero_left (by simpa using haker)
    have h₁ : T (a + w) ∈ F (n + d + 1) := by
      rw [map_add, hTa]
      exact add_mem (neg_mem (hSF n haF)) (by simpa [add_right_comm] using hTF (n + 1) hw)
    exact disjoint_def.mp (h𝒜.disjoint_biSup (y := {m | n + d < m}) (lt_irrefl (n + d))) _
      (hT.map_mem hvn) h₁
  -- downward induction from a degree above the support to one below it
  obtain ⟨lo, hi, hlohi, hFtop, hFbot⟩ := h𝒜.exists_biSup_ge_eq_top_and_biSup_ge_eq_bot h𝒜top
  replace hFtop : F lo = ⊤ := hFtop
  replace hFbot : F hi = ⊥ := hFbot
  have key (k : ℕ) : finrank K ↥(ker (T + S) ⊓ F (hi - k)) ≤ finrank K ↥(ker T ⊓ F (hi - k)) := by
    induction k with
    | zero =>
      rw [Nat.cast_zero, sub_zero, hFbot, inf_bot_eq, inf_bot_eq]
    | succ k ih =>
      refine step _ ?_
      rwa [show hi - ((k + 1 : ℕ) : ℤ) + 1 = hi - k by push_cast; ring]
  have hk := key (hi - lo).toNat
  rw [show hi - ((hi - lo).toNat : ℤ) = lo by rw [Int.toNat_of_nonneg (by omega)]; ring] at hk
  rwa [hFtop, inf_top_eq, inf_top_eq] at hk

end LinearMap
