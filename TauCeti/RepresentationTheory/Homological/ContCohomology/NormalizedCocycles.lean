/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Defs
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Normalized `1`-cocycles vanishing at a scalar-acting element

When an element `γ : G` acts on an `R`-module `M` by a scalar `ζ : R` such that `ζ - 1` is a
unit, every `1`-coboundary vanishing at `γ` is zero, and every `1`-cochain differs by a unique
`1`-coboundary from one vanishing at `γ`. Consequently, for any subgroup `W` of `G → M` containing
the `1`-coboundaries `B¹` and any additive homomorphism `π` whose kernel on `W` is `B¹`, the
subgroup of elements of `W` vanishing at `γ` maps bijectively onto `W.map π`.

## Main definitions and results

* `TauCeti.ContCohomology.vanishingAt`: the subgroup of maps `f : G → M` with `f γ = 0`.
* `TauCeti.ContCohomology.eq_zero_of_mem_B1_of_apply_eq_zero`: if `γ` acts as `ζ • ·` with
  `IsUnit (ζ - 1)`, a `1`-coboundary vanishing at `γ` is zero.
* `TauCeti.ContCohomology.exists_sub_mem_B1_apply_eq_zero`: every map `f : G → M` differs by a
  `1`-coboundary from one vanishing at `γ`.
* `TauCeti.ContCohomology.map_inf_vanishingAt_eq_map`: if `B1 G M ≤ W` and `B1 G M ≤ π.ker`,
  then `(W ⊓ vanishingAt G M γ).map π = W.map π`.
* `TauCeti.ContCohomology.natCard_inf_vanishingAt_eq_natCard_map`: if moreover
  `W ⊓ π.ker ≤ B1 G M`, then `Nat.card ↥(W ⊓ vanishingAt G M γ) = Nat.card (W.map π)`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, file
  `src/Lib/ClassField/GaloisCohomology/ClassCounts.lean` (declarations `vanishingAt`,
  `eq_zero_of_mem_B1_of_apply_eq_zero`, `exists_sub_mem_B1_apply_eq_zero`,
  `map_inf_vanishingAt_eq_map`, `card_inf_vanishingAt_eq_card_map`); Apache 2.0,
  Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti.ContCohomology

/-- The additive subgroup of functions `G → M` vanishing at `γ`. -/
def vanishingAt (G M : Type*) [AddCommGroup M] (γ : G) : AddSubgroup (G → M) :=
  (Pi.evalAddMonoidHom (fun _ : G ↦ M) γ).ker

@[simp]
theorem mem_vanishingAt {G M : Type*} [AddCommGroup M] {γ : G} {f : G → M} :
    f ∈ vanishingAt G M γ ↔ f γ = 0 :=
  Iff.rfl

section ScalarAction

variable {R G M : Type*} [Ring R] [AddCommGroup M] [Module R M] [DistribSMul G M]
variable {γ : G} {ζ : R}

/-- If `γ` acts on `M` by scalar multiplication by `ζ` with `ζ - 1` a unit, then any
`1`-coboundary vanishing at `γ` is identically zero. -/
theorem eq_zero_of_mem_B1_of_apply_eq_zero (hγ : ∀ m : M, γ • m = ζ • m) (hζ : IsUnit (ζ - 1))
    {f : G → M} (hf : f ∈ B1 G M) (hfγ : f γ = 0) : f = 0 := by
  rw [← range_d0] at hf
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.mp hf
  have hm0 : m = 0 := hζ.smul_left_cancel.mp <| by
    rw [smul_zero, sub_smul, one_smul, ← hγ, ← d0_apply]
    exact hfγ
  ext g
  simp [d0_apply, hm0]

/-- If `γ` acts on `M` by scalar multiplication by `ζ` with `ζ - 1` a unit, then every map
`f : G → M` differs by a `1`-coboundary from one vanishing at `γ`. -/
theorem exists_sub_mem_B1_apply_eq_zero (hγ : ∀ m : M, γ • m = ζ • m) (hζ : IsUnit (ζ - 1))
    (f : G → M) : ∃ b ∈ B1 G M, f - b ∈ vanishingAt G M γ := by
  let m : M := hζ.unit⁻¹ • f γ
  have hm : (ζ - 1) • m = f γ := by
    rw [← hζ.unit_spec, ← Units.smul_def, smul_inv_smul]
  refine ⟨d0 G M m, d0_mem_B1 m, ?_⟩
  rw [mem_vanishingAt, Pi.sub_apply, d0_apply, hγ, ← hm, sub_smul, one_smul, sub_self]

/-- If `γ` acts by `ζ` with `ζ - 1` a unit, `B¹ ≤ W`, and `π` kills `B¹`, then the subgroup of
elements of `W` vanishing at `γ` has the same image under `π` as `W`. -/
theorem map_inf_vanishingAt_eq_map {H : Type*} [AddGroup H] (hγ : ∀ m : M, γ • m = ζ • m)
    (hζ : IsUnit (ζ - 1)) (π : (G → M) →+ H) (hπ : B1 G M ≤ π.ker) {W : AddSubgroup (G → M)}
    (hBW : B1 G M ≤ W) :
    (W ⊓ vanishingAt G M γ).map π = W.map π := by
  refine le_antisymm (AddSubgroup.map_mono inf_le_left) ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨b, hb, hfb⟩ := exists_sub_mem_B1_apply_eq_zero hγ hζ f
  have hπb : π b = 0 := AddMonoidHom.mem_ker.mp (hπ hb)
  exact ⟨f - b, ⟨W.sub_mem hf (hBW hb), hfb⟩, by rw [map_sub, hπb, sub_zero]⟩

/-- If `γ` acts by `ζ` with `ζ - 1` a unit, `B¹ ≤ W`, and `π` has kernel `B¹` on `W`, then
`W ⊓ vanishingAt G M γ` has the same cardinality as `W.map π`. -/
theorem natCard_inf_vanishingAt_eq_natCard_map {H : Type*} [AddGroup H]
    (hγ : ∀ m : M, γ • m = ζ • m) (hζ : IsUnit (ζ - 1)) (π : (G → M) →+ H)
    (hπ_le : B1 G M ≤ π.ker) {W : AddSubgroup (G → M)} (hBW : B1 G M ≤ W)
    (hker_le : W ⊓ π.ker ≤ B1 G M) :
    Nat.card ↥(W ⊓ vanishingAt G M γ) = Nat.card (W.map π) := by
  let g : ↥(W ⊓ vanishingAt G M γ) →+ W.map π :=
    (π.comp (W ⊓ vanishingAt G M γ).subtype).codRestrict (W.map π) fun x ↦
      ⟨x.val, x.property.left, rfl⟩
  have hg_inj : Function.Injective g := by
    rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [AddSubgroup.mem_bot, Subtype.ext_iff]
    have hxB : x.val ∈ B1 G M := hker_le ⟨x.property.left, congrArg Subtype.val hx⟩
    exact eq_zero_of_mem_B1_of_apply_eq_zero hγ hζ hxB x.property.right
  have hg_surj : Function.Surjective g := by
    intro y
    have hy : y.val ∈ (W ⊓ vanishingAt G M γ).map π := by
      rw [map_inf_vanishingAt_eq_map hγ hζ π hπ_le hBW]
      exact y.property
    obtain ⟨f, hf, hfy⟩ := hy
    exact ⟨⟨f, hf⟩, Subtype.ext hfy⟩
  exact Nat.card_congr (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩)

end ScalarAction

end TauCeti.ContCohomology
