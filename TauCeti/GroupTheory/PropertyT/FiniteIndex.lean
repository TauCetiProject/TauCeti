/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.KazhdanPair
public import TauCeti.RepresentationTheory.Continuous.Unitary.Induced

/-!
# Relative property (T) and subgroups of finite index

Relative property (T) is insensitive to passing to and from subgroups of finite index:

* **Finite-index overgroups.** If a normal subgroup `N` of `Γ` has relative property (T), so does
  every subgroup `Λ` in which `N ⊓ Λ` has finite index. Almost invariant vectors are close to
  `N`-invariant vectors, by the quantitative form of relative property (T) for normal subgroups,
  and averaging an `N`-invariant vector over coset representatives of `N ⊓ Λ` in `Λ` produces a
  nearby `Λ`-invariant vector.
* **Finite-index subgroups.** If a normal subgroup `Λ` of `Γ` has relative property (T) and `K` has
  finite index in `Γ`, then `Λ ⊓ K` has relative property (T) in `K`. A representation of `K` with
  almost invariant vectors induces one of `Γ` with almost invariant vectors; a nonzero vector of the
  induced representation fixed by `Λ` has a nonzero value, and its values are fixed by `Λ ⊓ K`.

Together these give the classical statement that a group has property (T) if and only if one, or
equivalently every, subgroup of finite index has property (T)
(`Subgroup.relativePropertyT_top_iff_of_finiteIndex`).

Relative property (T) is used with Hilbert spaces in a universe containing the group, which
contains the Hilbert direct sums behind the Kazhdan pair characterization and the spaces of the
induced representations.

## Main statements

* `Subgroup.RelativePropertyT.of_relIndex_ne_zero`: relative property (T) passes from a normal
  subgroup `N` to every subgroup in which `N` has finite relative index.
* `Subgroup.RelativePropertyT.subgroupOf`: relative property (T) of a normal subgroup `Λ` passes to
  `Λ ⊓ K` inside a subgroup `K` of finite index.
* `Subgroup.relativePropertyT_top_iff_of_finiteIndex`: a group has property (T) if and only if a
  subgroup of finite index has property (T).

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §14.1.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Theorem 1.7.1.
-/

public section

namespace Subgroup

universe u v

open ContRepresentation

variable {Γ : Type v} [Group Γ]

/-- **Relative property (T) passes to finite-index overgroups.** If a normal subgroup `N` has
relative property (T), then so does every subgroup `Λ` in which `N ⊓ Λ` has finite index. -/
theorem RelativePropertyT.of_relIndex_ne_zero {N Λ : Subgroup Γ} [N.Normal]
    (hN : N.RelativePropertyT.{max u v}) (hNΛ : N.relIndex Λ ≠ 0) :
    Λ.RelativePropertyT.{max u v} := by
  classical
  have : (N.subgroupOf Λ).FiniteIndex := ⟨hNΛ⟩
  obtain ⟨F, δ, hδ, hK⟩ := (relativePropertyT_iff_exists_isKazhdanPair N).mp hN
  refine (relativePropertyT_def Λ).mpr fun H _ _ _ ρ hρ hρa ↦ ?_
  -- A unit vector `ξ` moved little by `F` and by the chosen representatives of `Λ ⧸ N ⊓ Λ`.
  let Q := Λ ⧸ N.subgroupOf Λ
  let := (N.subgroupOf Λ).fintypeQuotientOfFiniteIndex
  obtain ⟨ξ, hξ1, hξ⟩ := (hasAlmostInvariantVectors_def ρ).mp hρa
    (F ∪ Finset.univ.image fun q : Q ↦ ((q.out : Λ) : Γ)) (min δ 1 / 4) (by positivity)
  -- It lies within `1 / 4` of an `N`-invariant vector `η`.
  obtain ⟨η, hη, hξη⟩ := hK.exists_mem_invariants_norm_sub_lt hρ (by norm_num : (0 : ℝ) < 1 / 4)
    fun g hg ↦ (hξ g (Finset.mem_union_left _ hg)).trans_le (by linarith [min_le_left δ 1])
  -- Each representative moves `η` by less than `3 / 4`, so averaging gives a `Λ`-invariant `w`
  -- within `3 / 4` of `η`, hence within `1` of the unit vector `ξ`, so `w ≠ 0`.
  have hηΛ : η ∈ ((ρ.restrict Λ.subtype).restrict (N.subgroupOf Λ).subtype).invariants :=
    fun h ↦ hη ⟨_, mem_subgroupOf.mp h.property⟩
  have hmove (q : Q) : ‖ρ.restrict Λ.subtype q.out η - η‖ < 3 / 4 := by
    have hq : ‖ρ ((q.out : Λ) : Γ) ξ - ξ‖ < 1 / 4 :=
      (hξ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ q)))).trans_le
        (by linarith [min_le_right δ 1])
    have h1 := norm_sub_le_norm_sub_add_norm_sub (ρ ((q.out : Λ) : Γ) η) (ρ ((q.out : Λ) : Γ) ξ) η
    have h2 := norm_sub_le_norm_sub_add_norm_sub (ρ ((q.out : Λ) : Γ) ξ) ξ η
    rw [← map_sub, hρ.norm_map] at h1
    rw [restrict_apply_apply, coe_subtype]
    linarith [norm_sub_rev η ξ]
  obtain ⟨w, hw, hwη⟩ :=
    (ρ.restrict Λ.subtype).exists_invariant_norm_sub_lt_of_finiteIndex hηΛ hmove
  refine ⟨w, fun hw0 ↦ ?_, hw⟩
  rw [hw0, zero_sub, norm_neg] at hwη
  linarith [norm_sub_norm_le ξ η]

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
  refine (hK.mono K.normalCore_le).of_relIndex_ne_zero ?_
  rw [relIndex_top_right]
  exact FiniteIndex.index_ne_zero

end Subgroup
